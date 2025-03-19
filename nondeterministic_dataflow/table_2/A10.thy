theory A10

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)


section \<open>Axiom A10: Equality test to acopy\<close>

lemma same_prefix_prefix:
  "prefix ((ys >> xs) p) ((zs >> xs) p) = prefix (ys p) (zs p)"
  by (simp add: BULK_BENQ_def)

lemma suffix_BTL[simp]: 
  "buf p \<noteq> [] \<Longrightarrow> suffix ((BTL p buf) p) (buf p)"
  unfolding BTL_def by simp

definition nsuffix where
  "nsuffix n xs ys = (suffix xs ys \<and> n = length ys - length xs)"

lemma nsuffix_0[simp]: "nsuffix 0 xs ys \<longleftrightarrow> xs = ys"
  unfolding nsuffix_def using suffix_take by fastforce

definition nprefix where
  "nprefix n xs ys = (prefix xs ys \<and> n = length ys - length xs)"

lemma nprefix_0[simp]: "nprefix 0 xs ys \<longleftrightarrow> xs = ys"
  unfolding nprefix_def by (metis diff_is_0_eq prefix_length_le prefix_length_prefix prefix_order.eq_iff)

declare BULK_BENQ_left_empty[simp del] BULK_BENQ_right_empty[simp del] list_emb_Nil2[simp del]

definition "length_consumed n xs ys = length (filter (case_prod (=)) (zip (take n xs) (take n ys)))"

lemma length_consumed_0[simp]:
  "length_consumed 0 xs ys = 0"
  unfolding length_consumed_def by simp

lemma length_consumed_Suc[simp]:
  "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> hd xs \<noteq> hd ys \<Longrightarrow> length_consumed (Suc n) xs ys = length_consumed n (tl xs) (tl ys)"
  unfolding length_consumed_def by (simp add: take_Suc)

lemma length_consumed_leq:
  "length_consumed n xs ys \<le> n"
  unfolding length_consumed_def by (metis length_filter_le length_take length_zip min.bounded_iff)

definition "tested n xs ys = map fst (filter (case_prod (=)) (zip (take n xs) (take n ys)))"

lemma tested_diff_Suc:
  "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> hd xs \<noteq> hd ys \<Longrightarrow> tested (Suc n) xs ys = tested n (tl xs) (tl ys)"
  unfolding tested_def by (simp add: take_Suc)

lemma tested_eq_Suc:
  "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> hd xs = hd ys \<Longrightarrow> tested (Suc n) xs ys = hd xs # tested n (tl xs) (tl ys)"
  unfolding tested_def by (simp add: take_Suc)

lemma tested_diff_Suc_gen:
  "length xs > n \<Longrightarrow> length ys > n \<Longrightarrow> xs ! n \<noteq> ys ! n \<Longrightarrow> tested (Suc n) xs ys = tested n xs ys"
  unfolding tested_def
  apply (induct n arbitrary: xs ys)
   apply (auto simp: take_Suc hd_conv_nth)
  subgoal for n xs ys
    apply (cases xs; cases ys; simp)
    done
  done

lemma tested_eq_Suc_gen:
  "length xs > n \<Longrightarrow> length ys > n \<Longrightarrow> xs ! n = ys ! n \<Longrightarrow> tested (Suc n) xs ys = tested n xs ys @ [xs ! n]"
  unfolding tested_def
  apply (induct n arbitrary: xs ys)
   apply (auto simp: take_Suc hd_conv_nth)
  subgoal for n xs ys
    apply (cases xs; cases ys; simp)
    done
  done

lemma length_tested_0[simp]:
  "tested 0 xs ys = []"
  unfolding tested_def by simp

lemma wstep_Tau_aeq_op_acopy_op:
  "p \<notin> defaults \<Longrightarrow> n \<le> length (X p) \<Longrightarrow> n \<le> length (Y p) \<Longrightarrow>
  (step Tau)\<^sup>*\<^sup>*
  (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))))
  (map_op projl projr (comp_op Some (\<lambda> p'. if p' = p then (Z p') @ tested n (X p') (Y p') else Z p') (aeq_op (case_sum (\<lambda> p'. if p' = p then drop n (X p') else X p') (\<lambda> p'. if p' = p then drop n (Y p') else Y p'))) (acopy_op (case_sum V W))))"
  apply (induction n)
  subgoal
    apply (subst length_tested_0)
    apply (subst append.right_neutral)
    apply (subst drop_0)+
    by simp
  subgoal for n
    apply (rule rtranclp.intros(2)[of _ _ \<open>map_op projl projr (comp_op Some (\<lambda> p'. if p' = p then (Z p') @ tested n (X p') (Y p') else Z p') (aeq_op (case_sum (\<lambda> p'. if p' = p then drop n (X p') else X p') (\<lambda> p'. if p' = p then drop n (Y p') else Y p'))) (acopy_op (case_sum V W)))\<close>])
     apply simp
    apply (cases \<open>bhd (drop n (X p)) = bhd (drop n (Y p))\<close>)
    subgoal
      apply (rule step_map_op[of Tau])
       apply (rule step_Tau_comp_op_L[of p \<open>bhd (drop n (X p))\<close>])
          apply (rule step_aeq_op_Write)
      unfolding BHD_def BTL_def BENQ_def
               apply simp_all
       apply (subst drop_Suc)+
       apply (subst tl_drop)+
       apply (rule arg_cong2[of _ _ _ _ case_sum])
      by (auto simp add: fun_eq_iff hd_drop_conv_nth tested_eq_Suc_gen)
    subgoal
      apply (rule step_map_op[of Tau])
       apply (rule step_comp_op_L_Tau)
         apply (rule step_aeq_op_Silent)
      unfolding BHD_def BTL_def
             apply auto[8]
       apply (subst drop_Suc)+
       apply (subst tl_drop)+
       apply (rule arg_cong2[of _ _ _ _ case_sum])
      by (auto simp add: fun_eq_iff hd_drop_conv_nth tested_diff_Suc_gen)
    done
  done

lemma move_all_buffers:
  assumes  "p \<notin> defaults"
  shows "(step Tau)\<^sup>*\<^sup>*
     (map_op projl projr
       (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))
     (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := []))) (case_sum (B4(p := [])) (D4(p := []))))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) (D2(p := [])))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) (D1(p := [])))))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op (D3(p := [])))))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) (C5(p := (C1 >> C2 >> C3 >> C4 >> C5) p)))) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := (B1 >> B2 >> B3 >> B4 >> B5) p)) (D5(p := (D1 >> D2 >> D3 >> D4 >> D5) p)))) (id_op BD2))))))"
proof -
  have "(step Tau)\<^sup>*\<^sup>*
     (map_op projl projr
       (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))
      (map_op projl projr
       (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := (A1 >> A2) p)) B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))" (is "(step Tau)\<^sup>*\<^sup>* ?op ?op'")
    using assms proof (induct "A1 p" arbitrary: A1 A2)
    case Nil
    then show ?case by (smt (verit, best) BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem)
  next
    case (Cons a x A1 A2)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_comp_op_L_Tau)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_L)
              apply (rule step_comp_op_L_Out)
                 apply (rule step_acopy_op_Write[where p="Inl p"])
                    apply simp_all
       apply fastforce
      apply (smt (z3) BAPPEND_BENQ_BHD BENQ_def BTL_access BTL_def BTL_empty case_sum_BENQ_L fun_upd_upd list.sel(3) not_Cons_self2)
      done
  qed
  also have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := (A1 >> A2 >> A3) p))) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
    using assms proof (induct "(A1 >> A2) p" arbitrary: A1 A2 A3)
    case Nil
    then show ?case 
      by (smt (verit, best) BULK_BENQ_assoc BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem_iff)
  next
    case (Cons a xa A1 A2 A3)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_comp_op_L_Tau)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Inp)
                   apply (rule step_map_op)
                    apply (rule step_comp_op_L_Inp)
                      apply (rule step_id_op_Read)
                       apply simp_all
       apply (auto simp add: BULK_BENQ_left_empty)[1]
      apply simp
      apply (cases "A2 p")
      subgoal
        apply (drule meta_spec[of _ "BTL p A1"])
        apply (drule meta_spec[of _ "A2"])
        apply (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def fun_upd_same fun_upd_same fun_upd_upd list.sel(2) list.sel(3) not_Cons_self2)
        done
      subgoal
        apply (drule meta_spec[of _ "A1"])
        apply (drule meta_spec[of _ "BTL p A2"])
        apply (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BTL_def BULK_BENQ_def fun_upd_same fun_upd_upd list.distinct(1) list.sel(3))
        done
      done
  qed
  also (rtranclp_trans) have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := (A1 >> A2 >> A3 >> A4) p)) C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
    using assms proof (induct "(A1 >> A2 >> A3) p" arbitrary: A1 A2 A3 A4)
    case Nil
    then show ?case 
      by (smt (verit, best) BULK_BENQ_assoc BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem_iff)
  next
    case (Cons a xa A1 A2 A3 A4)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_Tau_comp_op_L)
           apply (rule step_map_op)
            apply (rule step_comp_op_R_Out)
              apply (rule step_map_op)
               apply (rule step_comp_op_L_Out)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_L_Out)
                      apply (rule step_id_op_Write)
                         apply simp_all
       apply (metis BULK_BENQ_left_empty neq_Nil_conv)
      apply simp
      apply (cases "A3 p")
      subgoal
        by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_access BTL_def Cons.hyps(1) assms fun_upd_same fun_upd_upd list.sel(2) list.sel(3) not_Cons_self2)
      subgoal
        by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def BULK_BENQ_empty \<open>\<lbrakk>\<And>A1 A2 A3 A4. xa = ((A1 >> A2) >> A3) p \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := ((A1 >> A2) >> A3) p))) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))) (map_op projl projr (comp_op Some (case_sum (case_sum (A4(p := (((A1 >> A2) >> A3) >> A4) p)) C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))); a # xa = ((A1 >> A2) >> A3) p; p \<notin> defaults; A3 p = []\<rbrakk> \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum (BENQ p (BHD p (A3(p := ((A1 >> A2) >> A3) p))) A4) C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL p (A3(p := ((A1 >> A2) >> A3) p)))) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))) (map_op projl projr (comp_op Some (case_sum (case_sum (A4(p := (((A1 >> A2) >> A3) >> A4) p)) C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))\<close> fun_upd_same fun_upd_upd list.sel(3))
      done
  qed
  also (rtranclp_trans) have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
    using assms proof (induct "(A1 >> A2 >> A3 >> A4) p" arbitrary: A1 A2 A3 A4 A5)
    case Nil
    then show ?case 
      by (smt (verit, best) BULK_BENQ_assoc BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem_iff)
  next
    case (Cons a xa A1 A2 A3 A4 A5)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_Tau_comp_op_R)
             apply (rule step_comp_op_L_Inp)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Inp)
                  apply (rule step_aeq_op_Read_L)
                   apply simp_all
       apply (metis Cons.hyps(2) fun_upd_same neq_Nil_conv old.sum.simps(5))
      apply (cases "A4 p")
      subgoal
        apply (cases "A3 p")
        subgoal
          by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_BAPPEND_2_cases BHD_def BTL_def BTL_empty case_sum_BTL_L fun_upd_same fun_upd_triv fun_upd_upd list.sel(3) not_Cons_self2)
        subgoal
          by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def case_sum_updateL fun_upd_same fun_upd_upd list.sel(2) list.sel(3) not_Cons_self2)
        done
      subgoal
        by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def BULK_BENQ_empty \<open>\<lbrakk>\<And>A1 A2 A3 A4 A5. xa = (((A1 >> A2) >> A3) >> A4) p \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum (A4(p := (((A1 >> A2) >> A3) >> A4) p)) C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))) (map_op projl projr (comp_op Some (case_sum (case_sum (A4(p := [])) C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := ((((A1 >> A2) >> A3) >> A4) >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))); a # xa = (((A1 >> A2) >> A3) >> A4) p; p \<notin> defaults; A4 p = []\<rbrakk> \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (BTL (Inl p) (case_sum (A4(p := (((A1 >> A2) >> A3) >> A4) p)) C4)) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (BENQ p (BHD p (A4 (p := (((A1 >> A2) >> A3) >> A4) p))) A5) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))) (map_op projl projr (comp_op Some (case_sum (case_sum (A4(p := [])) C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := ((((A1 >> A2) >> A3) >> A4) >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))\<close> case_sum_updateL fun_upd_same fun_upd_upd list.sel(3))
      done
  qed
  also (rtranclp_trans) have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := (B1 >> B2) p))) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
    using assms proof (induct "B1 p" arbitrary: B1 B2)
    case Nil
    then show ?case by (smt (verit, best) BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem)
  next
    case (Cons a x B1 B2)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_comp_op_L_Tau)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_L)
              apply (rule step_comp_op_L_Out)
                 apply (rule step_acopy_op_Write[where p="Inr p"])
                    apply simp_all
       apply fastforce
      apply (smt (z3) BAPPEND_BENQ_BHD BENQ_def BTL_def case_sum_BENQ_L case_sum_BENQ_R fun_upd_def fun_upd_upd list.distinct(1) list.sel(3))
      done
  qed
  also (rtranclp_trans) have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := (B1 >> B2 >> B3) p)) C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
    using assms proof (induct "(B1 >> B2) p" arbitrary: B1 B2 B3)
    case Nil
    then show ?case 
      by (smt (verit, best) BULK_BENQ_assoc BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem_iff)
  next
    case (Cons a xa B1 B2 B3)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_comp_op_L_Tau)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply simp_all
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_map_op)
            apply (rule step_comp_op_R_Inp)
               apply simp_all
        apply (rule step_transp_op_Read[where p="Inl _"])
         apply simp_all
       apply (auto simp add: BULK_BENQ_left_empty)[1]
      apply (cases "B2 p")
      subgoal
        apply (drule meta_spec[of _ "BTL p B1"])
        apply (drule meta_spec[of _ "B2"])
        apply (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def fun_upd_same fun_upd_same fun_upd_upd list.sel(2) list.sel(3) not_Cons_self2)
        done
      subgoal
        apply (drule meta_spec[of _ "B1"])
        apply (drule meta_spec[of _ "BTL p B2"])
        apply (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BTL_def BULK_BENQ_def fun_upd_same fun_upd_upd list.distinct(1) list.sel(3))
        done
      done
  qed
  also (rtranclp_trans) have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) C4) (case_sum (B4(p := (B1 >> B2 >> B3 >> B4) p)) D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
    using assms proof (induct "(B1 >> B2 >> B3) p" arbitrary: B1 B2 B3 B4)
    case Nil
    then show ?case 
      by (smt (verit, best) BULK_BENQ_assoc BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem_iff)
  next
    case (Cons a xa B1 B2 B3 B4)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_Tau_comp_op_L)
           apply (rule step_map_op)
            apply (rule step_comp_op_R_Out)
              apply (rule step_map_op)
               apply (rule step_comp_op_L_Out)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Out)
                     apply (rule step_transp_op_Write[where p="Inl p"])
                         apply simp_all
       apply (metis BHD_BAPPEND_2_cases list.discI)
      apply simp
      apply (cases "B3 p")
      subgoal
        by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_access BTL_def Cons.hyps(1) assms fun_upd_same fun_upd_upd list.sel(2) list.sel(3) not_Cons_self2)
      subgoal
        by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def BULK_BENQ_empty \<open>\<lbrakk>\<And>B1 B2 B3 B4. xa = ((B1 >> B2) >> B3) p \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum (A4(p := [])) C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := ((B1 >> B2) >> B3) p)) C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := ((((A1 >> A2) >> A3) >> A4) >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))) (map_op projl projr (comp_op Some (case_sum (case_sum (A4(p := [])) C4) (case_sum (B4(p := (((B1 >> B2) >> B3) >> B4) p)) D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := ((((A1 >> A2) >> A3) >> A4) >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))); a # xa = ((B1 >> B2) >> B3) p; p \<notin> defaults; B3 p = []\<rbrakk> \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum (A4(p := [])) C4) (case_sum (BENQ p (BHD p (B3(p := ((B1 >> B2) >> B3) p))) B4) D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (BTL p (B3(p := ((B1 >> B2) >> B3) p))) C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := ((((A1 >> A2) >> A3) >> A4) >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))) (map_op projl projr (comp_op Some (case_sum (case_sum (A4(p := [])) C4) (case_sum (B4(p := (((B1 >> B2) >> B3) >> B4) p)) D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := ((((A1 >> A2) >> A3) >> A4) >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))\<close> fun_upd_same fun_upd_upd list.sel(3))
      done
  qed
  also (rtranclp_trans) have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) C4) (case_sum (B4(p := [])) D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := (B1 >> B2 >> B3 >> B4 >> B5) p)) D5)) (id_op BD2))))))"
    using assms proof (induct "(B1 >> B2 >> B3 >> B4) p" arbitrary: B1 B2 B3 B4 B5)
    case Nil
    then show ?case 
      by (smt (verit, best) BULK_BENQ_assoc BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem_iff)
  next
    case (Cons a xa B1 B2 B3 B4 B5)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_Tau_comp_op_R)
             apply (rule step_comp_op_R_Inp)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Inp)
                   apply (rule step_aeq_op_Read_L)
                    apply simp_all
       apply (metis Cons.hyps(2) fun_upd_same neq_Nil_conv old.sum.simps(5))
      apply (cases "B4 p")
      subgoal
        apply (cases "B3 p")
        subgoal
          by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_BAPPEND_2_cases BHD_def BTL_def BTL_empty case_sum_BTL_L fun_upd_same fun_upd_triv fun_upd_upd list.sel(3) not_Cons_self2)
        subgoal
          by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def case_sum_updateL fun_upd_same fun_upd_upd list.sel(2) list.sel(3) not_Cons_self2)
        done
      subgoal
        by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_BULK_BENQ_right_not_empty BHD_def BTL_access BTL_def BULK_BENQ_assoc BULK_BENQ_empty BULK_BENQ_eq_left BULK_BENQ_eq_right assms case_sum_BTL_L case_sum_updateL fun_upd_idem_iff fun_upd_same fun_upd_same fun_upd_triv fun_upd_upd list.sel(2) list.sel(3) not_Cons_self2)
      done
  qed
  also (rtranclp_trans) have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) C4) (case_sum (B4(p := [])) D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := (C1 >> C2) p)) D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := (B1 >> B2 >> B3 >> B4 >> B5) p)) D5)) (id_op BD2))))))"
    using assms proof (induct "C1 p" arbitrary: C1 C2)
    case Nil
    then show ?case by (smt (verit, best) BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem)
  next
    case (Cons a x C1 C2)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_comp_op_L_Tau)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_L)
              apply (rule step_comp_op_R_Out)
                apply (rule step_acopy_op_Write[where p="Inl p"])
                   apply simp_all
       apply fastforce
      apply (smt (z3) BAPPEND_BENQ_BHD BENQ_def BTL_def case_sum_BENQ_L case_sum_BENQ_R fun_upd_def fun_upd_upd list.distinct(1) list.sel(3))
      done
  qed
  also (rtranclp_trans) have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) C4) (case_sum (B4(p := [])) D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := (C1 >> C2 >> C3) p)))))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := (B1 >> B2 >> B3 >> B4 >> B5) p)) D5)) (id_op BD2))))))"
    using assms proof (induct "(C1 >> C2) p" arbitrary: C1 C2 C3)
    case Nil
    then show ?case 
      by (smt (verit, best) BULK_BENQ_assoc BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem_iff)
  next
    case (Cons a xa C1 C2 C3)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_comp_op_L_Tau)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply simp_all
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_map_op)
            apply (rule step_comp_op_R_Inp)
               apply simp_all
        apply (rule step_transp_op_Read[where p="Inr _"])
         apply simp_all
       apply (auto simp add: BULK_BENQ_left_empty)[1]
      apply (cases "C2 p")
      subgoal
        apply (drule meta_spec[of _ "BTL p C1"])
        apply (drule meta_spec[of _ "C2"])
        apply (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def fun_upd_same fun_upd_same fun_upd_upd list.sel(2) list.sel(3) not_Cons_self2)
        done
      subgoal
        apply (drule meta_spec[of _ "C1"])
        apply (drule meta_spec[of _ "BTL p C2"])
        apply (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BTL_def BULK_BENQ_def fun_upd_same fun_upd_upd list.distinct(1) list.sel(3))
        done
      done
  qed
  also (rtranclp_trans) have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := (C1 >> C2 >> C3 >> C4) p))) (case_sum (B4(p := [])) D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := (B1 >> B2 >> B3 >> B4 >> B5) p)) D5)) (id_op BD2))))))"
    using assms proof (induct "(C1 >> C2 >> C3) p" arbitrary: C1 C2 C3 C4)
    case Nil
    then show ?case 
      by (smt (verit, best) BULK_BENQ_assoc BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem_iff)
  next
    case (Cons a xa C1 C2 C3 C4)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_Tau_comp_op_L)
           apply (rule step_map_op)
            apply (rule step_comp_op_R_Out)
              apply (rule step_map_op)
               apply (rule step_comp_op_L_Out)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Out)
                     apply (rule step_transp_op_Write[where p="Inr p"])
                         apply simp_all
       apply (metis BHD_BAPPEND_2_cases list.discI)
      apply simp
      apply (cases "C3 p")
      subgoal
        by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_access BTL_def Cons.hyps(1) assms fun_upd_same fun_upd_upd list.sel(2) list.sel(3) not_Cons_self2)
      subgoal
        by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def BULK_BENQ_empty \<open>\<lbrakk>\<And>C1 C2 C3 C4. xa = ((C1 >> C2) >> C3) p \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum (A4(p := [])) C4) (case_sum (B4(p := [])) D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := ((C1 >> C2) >> C3) p)))))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := ((((A1 >> A2) >> A3) >> A4) >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := ((((B1 >> B2) >> B3) >> B4) >> B5) p)) D5)) (id_op BD2)))))) (map_op projl projr (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := (((C1 >> C2) >> C3) >> C4) p))) (case_sum (B4(p := [])) D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := ((((A1 >> A2) >> A3) >> A4) >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := ((((B1 >> B2) >> B3) >> B4) >> B5) p)) D5)) (id_op BD2)))))); a # xa = ((C1 >> C2) >> C3) p; p \<notin> defaults; C3 p = []\<rbrakk> \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum (A4(p := [])) (BENQ p (BHD p (C3(p := ((C1 >> C2) >> C3) p))) C4)) (case_sum (B4(p := [])) D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (BTL p (C3(p := ((C1 >> C2) >> C3) p))))))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := ((((A1 >> A2) >> A3) >> A4) >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := ((((B1 >> B2) >> B3) >> B4) >> B5) p)) D5)) (id_op BD2)))))) (map_op projl projr (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := (((C1 >> C2) >> C3) >> C4) p))) (case_sum (B4(p := [])) D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := ((((A1 >> A2) >> A3) >> A4) >> A5) p)) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := ((((B1 >> B2) >> B3) >> B4) >> B5) p)) D5)) (id_op BD2))))))\<close> fun_upd_same fun_upd_upd list.sel(3))
      done
  qed
  also (rtranclp_trans) have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := []))) (case_sum (B4(p := [])) D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) (C5(p := (C1 >> C2 >> C3 >> C4 >> C5) p)))) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := (B1 >> B2 >> B3 >> B4 >> B5) p)) D5)) (id_op BD2))))))"
    using assms proof (induct "(C1 >> C2 >> C3 >> C4) p" arbitrary: C1 C2 C3 C4 C5)
    case Nil
    then show ?case 
      by (smt (verit, best) BULK_BENQ_assoc BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem_iff)
  next
    case (Cons a xa C1 C2 C3 C4 C5)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_Tau_comp_op_R)
             apply (rule step_comp_op_L_Inp)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Inp)
                  apply (rule step_aeq_op_Read_R)
                   apply simp_all
       apply simp
       apply (metis BULK_BENQ_right_empty list.distinct(1))
      apply (cases "C4 p")
      subgoal
        apply (cases "C3 p")
        subgoal
          apply (cases "C2 p")
          subgoal
            by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_BULK_BENQ_left_empty BHD_def BTL_access BTL_def BTL_empty BULK_BENQ_assoc case_sum_BTL_L case_sum_updateL case_sum_updateR fun_upd_idem_iff fun_upd_same fun_upd_triv fun_upd_upd list.sel(3) not_Cons_self old.sum.simps(5) sum.case(2))
          subgoal
            by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def BTL_empty BULK_BENQ_right_empty case_sum_updateR fun_upd_idem_iff fun_upd_same fun_upd_upd list.sel(3) not_Cons_self)
          done
        subgoal
          by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def BTL_empty BULK_BENQ_right_empty case_sum_updateR fun_upd_idem_iff fun_upd_same fun_upd_upd list.sel(3) not_Cons_self)
        done
      subgoal
        by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def BTL_empty BULK_BENQ_right_empty case_sum_updateR fun_upd_idem_iff fun_upd_same fun_upd_upd list.sel(3) not_Cons_self)
      done
  qed
  also (rtranclp_trans) have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := []))) (case_sum (B4(p := [])) D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) (D2(p := (D1 >> D2) p)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) (D1(p := [])))))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) (C5(p := (C1 >> C2 >> C3 >> C4 >> C5) p)))) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := (B1 >> B2 >> B3 >> B4 >> B5) p)) D5)) (id_op BD2))))))"
    using assms proof (induct "D1 p" arbitrary: D1 D2)
    case Nil
    then show ?case by (smt (verit, best) BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem)
  next
    case (Cons a x D1 D2)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_comp_op_L_Tau)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_L)
              apply (rule step_comp_op_R_Out)
                apply (rule step_acopy_op_Write[where p="Inr p"])
                   apply simp_all
       apply fastforce
      apply (smt (z3) BAPPEND_BENQ_BHD BENQ_def BTL_def case_sum_BENQ_L case_sum_BENQ_R fun_upd_def fun_upd_upd list.distinct(1) list.sel(3))
      done
  qed
  also (rtranclp_trans) have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := []))) (case_sum (B4(p := [])) D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) (D2(p := [])))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) (D1(p := [])))))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op (D3(p := (D1 >> D2 >> D3) p)))))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) (C5(p := (C1 >> C2 >> C3 >> C4 >> C5) p)))) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := (B1 >> B2 >> B3 >> B4 >> B5) p)) D5)) (id_op BD2))))))"
    using assms proof (induct "(D1 >> D2) p" arbitrary: D1 D2 D3)
    case Nil
    then show ?case 
      by (smt (verit, best) BULK_BENQ_assoc BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem_iff)
  next
    case (Cons a xa D1 D2 D3)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_comp_op_L_Tau)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply simp_all
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Inp)
            apply (rule step_id_op_Read)
             apply simp_all
       apply (auto simp add: BULK_BENQ_left_empty)[1]
      apply (cases "D2 p")
      subgoal
        apply (drule meta_spec[of _ "BTL p D1"])
        apply (drule meta_spec[of _ "D2"])
        apply (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_access BTL_def BTL_def BTL_empty BULK_BENQ_assoc BULK_BENQ_empty BULK_BENQ_eq_left BULK_BENQ_right_empty Cons.hyps(1) assms case_sum_updateL case_sum_updateR case_sum_updateR fun_upd_same fun_upd_same fun_upd_upd fun_upd_upd list.sel(3) not_Cons_self sum.case(2))
        done
      subgoal
        apply (drule meta_spec[of _ "D1"])
        apply (drule meta_spec[of _ "BTL p D2"])
        apply (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_access BTL_def BTL_def BTL_empty BULK_BENQ_assoc BULK_BENQ_empty BULK_BENQ_eq_left BULK_BENQ_right_empty Cons.hyps(1) assms case_sum_updateL case_sum_updateR case_sum_updateR fun_upd_same fun_upd_same fun_upd_upd fun_upd_upd list.sel(3) not_Cons_self sum.case(2))
        done
      done
  qed
  also (rtranclp_trans) have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := []))) (case_sum (B4(p := [])) (D4(p := (D1 >> D2 >> D3 >> D4) p))))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) (D2(p := [])))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) (D1(p := [])))))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op (D3(p := [])))))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) (C5(p := (C1 >> C2 >> C3 >> C4 >> C5) p)))) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := (B1 >> B2 >> B3 >> B4 >> B5) p)) D5)) (id_op BD2))))))"
    using assms proof (induct "(D1 >> D2 >> D3) p" arbitrary: D1 D2 D3 D4)
    case Nil
    then show ?case 
      by (smt (verit, best) BULK_BENQ_assoc BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem_iff)
  next
    case (Cons a xa D1 D2 D3 D4)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_Tau_comp_op_L)
           apply (rule step_map_op)
            apply (rule step_comp_op_R_Out)
              apply (rule step_map_op)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write)
                    apply simp_all
       apply (metis BHD_BAPPEND_2_cases list.discI)
      apply simp
      apply (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_access BTL_def Cons.hyps(1) assms fun_upd_same fun_upd_upd list.sel(2) list.sel(3) not_Cons_self2)
      done
  qed
  also (rtranclp_trans) have "(step Tau)\<^sup>*\<^sup>* \<dots> 
      (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := []))) (case_sum (B4(p := [])) (D4(p := []))))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) (D2(p := [])))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) (D1(p := [])))))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op (D3(p := [])))))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) (C5(p := (C1 >> C2 >> C3 >> C4 >> C5) p)))) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := (B1 >> B2 >> B3 >> B4 >> B5) p)) (D5(p := (D1 >> D2 >> D3 >> D4 >> D5) p)))) (id_op BD2))))))"
    using assms proof (induct "(D1 >> D2 >> D3 >> D4) p" arbitrary: D1 D2 D3 D4 D5)
    case Nil
    then show ?case 
      by (smt (verit, best) BULK_BENQ_assoc BULK_BENQ_left_empty Nitpick.rtranclp_unfold fun_upd_idem_iff)
  next
    case (Cons a xa D1 D2 D3 D4 D5)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_Tau_comp_op_R)
             apply (rule step_comp_op_R_Inp)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Inp)
                   apply (rule step_aeq_op_Read_R)
                    apply simp_all
       apply simp
       apply (metis BULK_BENQ_right_empty list.distinct(1))
      apply (cases "D4 p")
      subgoal
        apply (cases "D3 p")
        subgoal
          apply (cases "D2 p")
          subgoal
            by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_BULK_BENQ_left_empty BHD_def BTL_access BTL_def BTL_empty BULK_BENQ_assoc case_sum_BTL_L case_sum_updateL case_sum_updateR fun_upd_idem_iff fun_upd_same fun_upd_triv fun_upd_upd list.sel(3) not_Cons_self old.sum.simps(5) sum.case(2))
          subgoal
            by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def BTL_empty BULK_BENQ_right_empty case_sum_updateR fun_upd_idem_iff fun_upd_same fun_upd_upd list.sel(3) not_Cons_self)
          done
        subgoal
          by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def BTL_empty BULK_BENQ_right_empty case_sum_updateR fun_upd_idem_iff fun_upd_same fun_upd_upd list.sel(3) not_Cons_self)
        done
      subgoal
        by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def BTL_empty BULK_BENQ_right_empty case_sum_updateR fun_upd_idem_iff fun_upd_same fun_upd_upd list.sel(3) not_Cons_self)
      done
  qed
  finally (rtranclp_trans) show ?thesis by blast
qed

(* TODO move or write proof without this lemma *)
lemma arg_cong3:
  \<open>x = x' \<Longrightarrow> y = y' \<Longrightarrow> z = z' \<Longrightarrow> f x y z = f x' y' z'\<close>
  by simp

lemma move_some_buffers:
  assumes \<open>p \<notin> defaults\<close>
  shows \<open>(step Tau)\<^sup>*\<^sup>*
     (map_op projl projr
       (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))
     (map_op projl projr
       (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (AC1(p := [])) (aeq_op (case_sum A5 C5)) (id_op (AC2(p := (AC1 >> AC2) p))))) (map_op projl projr (comp_op Some (BD1(p := [])) (aeq_op (case_sum B5 D5)) (id_op (BD2(p := (BD1 >> BD2) p))))))))\<close>
proof -
  have \<open>(step Tau)\<^sup>*\<^sup>*
     (map_op projl projr
       (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))
     (map_op projl projr
       (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (AC1(p := [])) (aeq_op (case_sum A5 C5)) (id_op (AC2(p := (AC1 >> AC2) p))))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))\<close>
    using assms proof (induct \<open>AC1 p\<close> arbitrary: AC1 AC2)
    case Nil
    then show ?case
      by (simp add: BULK_BENQ_left_empty fun_upd_idem)
  next
    case (Cons a x)
    then show ?case
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_comp_op_R_Tau)
          apply (rule step_comp_op_L_Tau)
            apply (rule step_map_op)
             apply (rule step_Tau_comp_op_R)
                  apply (rule step_id_op_Read)
                   apply simp_all
       apply fastforce
      by (smt (verit, ccfv_SIG) BAPPEND_BENQ_BHD BENQ_def BTL_access BTL_def fun_upd_upd list.sel(2) list.sel(3) not_Cons_self2)
  qed
  also have \<open>(step Tau)\<^sup>*\<^sup>* \<dots>
     (map_op projl projr
       (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (AC1(p := [])) (aeq_op (case_sum A5 C5)) (id_op (AC2(p := (AC1 >> AC2) p))))) (map_op projl projr (comp_op Some (BD1(p := [])) (aeq_op (case_sum B5 D5)) (id_op (BD2(p := (BD1 >> BD2) p))))))))\<close>
    using assms proof (induct \<open>BD1 p\<close> arbitrary: BD1 BD2)
    case Nil
    then show ?case
      by (simp add: BULK_BENQ_left_empty fun_upd_idem)
  next
    case (Cons a x)
    then show ?case
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_comp_op_R_Tau)
          apply (rule step_comp_op_R_Tau)
            apply (rule step_map_op)
             apply (rule step_Tau_comp_op_R)
                  apply (rule step_id_op_Read)
                   apply simp_all
       apply fastforce
      by (smt (verit, ccfv_SIG) BAPPEND_BENQ_BHD BENQ_def BTL_access BTL_def fun_upd_upd list.sel(2) list.sel(3) not_Cons_self2)
  qed
  finally (rtranclp_trans) show ?thesis by blast
qed

lemma wstep_Tau_acopy_op_id_op_transp_op_aeq_op2:
  assumes \<open>p \<notin> defaults\<close>
    and \<open>n \<le> length ((A1 >> A2 >> A3 >> A4 >> A5) p)\<close>
    and \<open>n \<le> length ((C1 >> C2 >> C3 >> C4 >> C5) p)\<close>
    and \<open>m \<le> length ((B1 >> B2 >> B3 >> B4 >> B5) p)\<close>
    and \<open>m \<le> length ((D1 >> D2 >> D3 >> D4 >> D5) p)\<close>
  shows \<open>(step Tau)\<^sup>*\<^sup>*
      (map_op projl projr
        (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
          (map_op projl projr
            (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
              (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
          (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))
     (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := []))) (case_sum (B4(p := [])) (D4(p := []))))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) (D2(p := [])))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) (D1(p := [])))))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op (D3(p := [])))))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (AC1(p := [])) (aeq_op (case_sum (A5(p := drop n ((A1 >> A2 >> A3 >> A4 >> A5) p))) (C5(p := drop n ((C1 >> C2 >> C3 >> C4 >> C5) p))))) (id_op (AC2(p := (AC1 >> AC2) p @ tested n ((A1 >> A2 >> A3 >> A4 >> A5) p) ((C1 >> C2 >> C3 >> C4 >> C5) p)))))) (map_op projl projr (comp_op Some (BD1(p := [])) (aeq_op (case_sum (B5(p := drop m ((B1 >> B2 >> B3 >> B4 >> B5) p))) (D5(p := drop m ((D1 >> D2 >> D3 >> D4 >> D5) p))))) (id_op (BD2(p := (BD1 >> BD2) p @ tested m ((B1 >> B2 >> B3 >> B4 >> B5) p) ((D1 >> D2 >> D3 >> D4 >> D5) p)))))))))\<close>
proof -
  have \<open>(step Tau)\<^sup>*\<^sup>*
     (map_op projl projr
       (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))
     (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := []))) (case_sum (B4(p := [])) (D4(p := []))))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) (D2(p := [])))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) (D1(p := [])))))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op (D3(p := [])))))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (A5(p := (A1 >> A2 >> A3 >> A4 >> A5) p)) (C5(p := (C1 >> C2 >> C3 >> C4 >> C5) p)))) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := (B1 >> B2 >> B3 >> B4 >> B5) p)) (D5(p := (D1 >> D2 >> D3 >> D4 >> D5) p)))) (id_op BD2))))))\<close>
    using assms move_all_buffers by metis
  also have \<open>(step Tau)\<^sup>*\<^sup>* \<dots>
     (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := []))) (case_sum (B4(p := [])) (D4(p := []))))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) (D2(p := [])))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) (D1(p := [])))))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op (D3(p := [])))))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (AC1(p := AC1 p @ tested n ((A1 >> A2 >> A3 >> A4 >> A5) p) ((C1 >> C2 >> C3 >> C4 >> C5) p))) (aeq_op (case_sum (A5(p := drop n ((A1 >> A2 >> A3 >> A4 >> A5) p))) (C5(p := drop n ((C1 >> C2 >> C3 >> C4 >> C5) p))))) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := (B1 >> B2 >> B3 >> B4 >> B5) p)) (D5(p := (D1 >> D2 >> D3 >> D4 >> D5) p)))) (id_op BD2))))))\<close>
    using assms proof (induct n)
    case 0
    then show ?case
      by (simp add: drop_0)
  next
    case (Suc n)
    then show ?case
      apply -
      apply (rule rtranclp.intros(2)[of _ _ \<open>map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := []))) (case_sum (B4(p := [])) (D4(p := []))))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) (D2(p := [])))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) (D1(p := [])))))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op (D3(p := [])))))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (AC1(p := AC1 p @ tested n ((A1 >> A2 >> A3 >> A4 >> A5) p) ((C1 >> C2 >> C3 >> C4 >> C5) p))) (aeq_op (case_sum (A5(p := drop n ((A1 >> A2 >> A3 >> A4 >> A5) p))) (C5(p := drop n ((C1 >> C2 >> C3 >> C4 >> C5) p))))) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (B5(p := (B1 >> B2 >> B3 >> B4 >> B5) p)) (D5(p := (D1 >> D2 >> D3 >> D4 >> D5) p)))) (id_op BD2)))))\<close>])
       apply linarith
      apply (rule step_map_op[of Tau])
       apply (rule step_comp_op_R_Tau)
         apply (rule step_comp_op_L_Tau)
           apply (rule step_map_op[of Tau])
            apply (cases \<open>bhd (drop n ((A1 >> A2 >> A3 >> A4 >> A5) p)) = bhd (drop n ((C1 >> C2 >> C3 >> C4 >> C5) p))\<close>)
      subgoal
        apply (rule step_Tau_comp_op_L[of p \<open>bhd (drop n ((A1 >> A2 >> A3 >> A4 >> A5) p))\<close>])
           apply (rule step_aeq_op_Write)
                apply (simp_all add: BHD_def)
         apply (smt (verit, best) BTL_def BULK_BENQ_assoc drop_Suc fun_upd_def fun_upd_upd tl_drop)
        apply (simp add: BENQ_def)
        apply (subst tested_eq_Suc_gen)
           apply (simp_all add: hd_drop_conv_nth)
        by fastforce
      subgoal
        apply (rule step_comp_op_L_Tau)
          apply (rule step_aeq_op_Silent)
              apply (simp_all add: BHD_def)
            apply (metis BHD_def fun_upd_same)
           apply fastforce+
         apply (smt (verit, del_insts) BTL_def BULK_BENQ_assoc drop_Suc fun_upd_def fun_upd_upd tl_drop)
        apply (subst tested_diff_Suc_gen)
           apply (simp_all add: hd_drop_conv_nth)
        by fastforce
           apply simp_all
      using BULK_BENQ_assoc apply force
      apply (rule arg_cong[of _ _ \<open>map_op projl projr\<close>])
      apply (rule arg_cong3[of _ _ _ _ _ _ \<open>comp_op Some\<close>])
        apply blast+
      apply (rule arg_cong[of _ _ \<open>map_op reassoc reassoc\<close>])
      apply (rule arg_cong2[of _ _ _ _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. [])\<close>])
       apply (rule arg_cong[of _ _ \<open>map_op assoc assoc\<close>])
       apply (rule arg_cong2[of _ _ _ _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. [])\<close>])
        apply (metis fun_upd_def)+
      done
  qed
  also (rtranclp_trans) have \<open>(step Tau)\<^sup>*\<^sup>* \<dots>
     (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := []))) (case_sum (B4(p := [])) (D4(p := []))))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) (D2(p := [])))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) (D1(p := [])))))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op (D3(p := [])))))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (AC1(p := AC1 p @ tested n ((A1 >> A2 >> A3 >> A4 >> A5) p) ((C1 >> C2 >> C3 >> C4 >> C5) p))) (aeq_op (case_sum (A5(p := drop n ((A1 >> A2 >> A3 >> A4 >> A5) p))) (C5(p := drop n ((C1 >> C2 >> C3 >> C4 >> C5) p))))) (id_op AC2))) (map_op projl projr (comp_op Some (BD1(p := BD1 p @ tested m ((B1 >> B2 >> B3 >> B4 >> B5) p) ((D1 >> D2 >> D3 >> D4 >> D5) p))) (aeq_op (case_sum (B5(p := drop m ((B1 >> B2 >> B3 >> B4 >> B5) p))) (D5(p := drop m ((D1 >> D2 >> D3 >> D4 >> D5) p))))) (id_op BD2))))))\<close>
    using assms proof (induct m)
    case 0
    then show ?case
      by (simp add: drop_0)
  next
    case (Suc m)
    then show ?case
      apply -
      apply (rule rtranclp.intros(2)[of _ _ \<open>map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := []))) (case_sum (B4(p := [])) (D4(p := []))))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) (D2(p := [])))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) (D1(p := [])))))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op (D3(p := [])))))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (AC1(p := AC1 p @ tested n ((A1 >> A2 >> A3 >> A4 >> A5) p) ((C1 >> C2 >> C3 >> C4 >> C5) p))) (aeq_op (case_sum (A5(p := drop n ((A1 >> A2 >> A3 >> A4 >> A5) p))) (C5(p := drop n ((C1 >> C2 >> C3 >> C4 >> C5) p))))) (id_op AC2))) (map_op projl projr (comp_op Some (BD1(p := BD1 p @ tested m ((B1 >> B2 >> B3 >> B4 >> B5) p) ((D1 >> D2 >> D3 >> D4 >> D5) p))) (aeq_op (case_sum (B5(p := drop m ((B1 >> B2 >> B3 >> B4 >> B5) p))) (D5(p := drop m ((D1 >> D2 >> D3 >> D4 >> D5) p))))) (id_op BD2)))))\<close>])
       apply linarith
      apply (rule step_map_op[of Tau])
       apply (rule step_comp_op_R_Tau)
         apply (rule step_comp_op_R_Tau)
           apply (rule step_map_op[of Tau])
            apply (cases \<open>bhd (drop m ((B1 >> B2 >> B3 >> B4 >> B5) p)) = bhd (drop m ((D1 >> D2 >> D3 >> D4 >> D5) p))\<close>)
      subgoal
        apply (rule step_Tau_comp_op_L[of p \<open>bhd (drop m ((B1 >> B2 >> B3 >> B4 >> B5) p))\<close>])
           apply (rule step_aeq_op_Write)
                apply (simp_all add: BHD_def)
         apply (smt (verit, best) BTL_def BULK_BENQ_assoc drop_Suc fun_upd_def fun_upd_upd tl_drop)
        apply (simp add: BENQ_def)
        apply (subst tested_eq_Suc_gen)
           apply (simp_all add: hd_drop_conv_nth)
        by fastforce
      subgoal
        apply (rule step_comp_op_L_Tau)
          apply (rule step_aeq_op_Silent)
              apply (simp_all add: BHD_def)
            apply (metis BHD_def fun_upd_same)
           apply fastforce+
         apply (smt (verit, del_insts) BTL_def BULK_BENQ_assoc drop_Suc fun_upd_def fun_upd_upd tl_drop)
        apply (subst tested_diff_Suc_gen)
           apply (simp_all add: hd_drop_conv_nth)
        by fastforce
           apply simp_all
       apply (rule arg_cong[of _ _ \<open>map_op projl projr\<close>])
       apply (rule arg_cong3[of _ _ _ _ _ _ \<open>comp_op Some\<close>])
         apply fastforce
        apply (rule arg_cong[of _ _ aeq_op])
      using BULK_BENQ_assoc apply force
       apply simp
      apply (rule arg_cong[of _ _ \<open>map_op projl projr\<close>])
      apply (rule arg_cong3[of _ _ _ _ _ _ \<open>comp_op Some\<close>])
        apply blast+
      apply (rule arg_cong[of _ _ \<open>map_op reassoc reassoc\<close>])
      apply (rule arg_cong2[of _ _ _ _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. [])\<close>])
       apply (rule arg_cong[of _ _ \<open>map_op assoc assoc\<close>])
       apply (rule arg_cong2[of _ _ _ _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. [])\<close>])
        apply (metis fun_upd_def)+
      done
  qed
  also (rtranclp_trans) have \<open>(step Tau)\<^sup>*\<^sup>* \<dots>
     (map_op projl projr
       (comp_op Some (case_sum (case_sum (A4(p := [])) (C4(p := []))) (case_sum (B4(p := [])) (D4(p := []))))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum (A2(p := [])) (B2(p := []))) (case_sum (C2(p := [])) (D2(p := [])))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (A1(p := [])) (B1(p := [])))) (acopy_op (case_sum (C1(p := [])) (D1(p := [])))))
             (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A3(p := []))) (transp_op (case_sum (B3(p := [])) (C3(p := [])))))) (id_op (D3(p := [])))))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (AC1(p := [])) (aeq_op (case_sum (A5(p := drop n ((A1 >> A2 >> A3 >> A4 >> A5) p))) (C5(p := drop n ((C1 >> C2 >> C3 >> C4 >> C5) p))))) (id_op (AC2(p := (AC1 >> AC2) p @ tested n ((A1 >> A2 >> A3 >> A4 >> A5) p) ((C1 >> C2 >> C3 >> C4 >> C5) p)))))) (map_op projl projr (comp_op Some (BD1(p := [])) (aeq_op (case_sum (B5(p := drop m ((B1 >> B2 >> B3 >> B4 >> B5) p))) (D5(p := drop m ((D1 >> D2 >> D3 >> D4 >> D5) p))))) (id_op (BD2(p := (BD1 >> BD2) p @ tested m ((B1 >> B2 >> B3 >> B4 >> B5) p) ((D1 >> D2 >> D3 >> D4 >> D5) p)))))))))\<close>
    using assms move_some_buffers[of p \<open>A4(p := [])\<close> \<open>C4(p := [])\<close> \<open>B4(p := [])\<close> \<open>D4(p := [])\<close> \<open>A2(p := [])\<close> \<open>B2(p := [])\<close> \<open>C2(p := [])\<close> \<open>D2(p := [])\<close> \<open>A1(p := [])\<close> \<open>B1(p := [])\<close> \<open>C1(p := [])\<close> \<open>D1(p := [])\<close> \<open>A3(p := [])\<close> \<open>B3(p := [])\<close> \<open>C3(p := [])\<close> \<open>D3(p := [])\<close> \<open>AC1(p := bulk_benq (tested n ((A1 >> A2 >> A3 >> A4 >> A5) p) ((C1 >> C2 >> C3 >> C4 >> C5) p)) (AC1 p))\<close> \<open>A5(p := drop n ((A1 >> A2 >> A3 >> A4 >> A5) p))\<close> \<open>C5(p := drop n ((C1 >> C2 >> C3 >> C4 >> C5) p))\<close> AC2 \<open>BD1(p := bulk_benq (tested m ((B1 >> B2 >> B3 >> B4 >> B5) p) ((D1 >> D2 >> D3 >> D4 >> D5) p)) (BD1 p))\<close> \<open>B5(p := drop m ((B1 >> B2 >> B3 >> B4 >> B5) p))\<close> \<open>D5(p := drop m ((D1 >> D2 >> D3 >> D4 >> D5) p))\<close> BD2]
    by (simp add: BULK_BENQ_bulk_benq)
  finally (rtranclp_trans) show ?thesis by blast
qed

named_theorems A10_prems

lemma A10_gen:
  assumes "A = A1 >> A2 >> A3 >> A4 >> A5"
    and "B = B1 >> B2 >> B3 >> B4 >> B5"
    and "C = C1 >> C2 >> C3 >> C4 >> C5"
    and "D = D1 >> D2 >> D3 >> D4 >> D5"
    and "AC = AC1 >> AC2"
    and "BD = BD1 >> BD2"
    and "\<forall> p. \<exists> m n. (m = 0 \<or> n = 0) \<and> drop n (A p) = (X p) \<and> drop n (C p) = Y p \<and> drop m (B p) = X p \<and> drop m (D p) = Y p \<and> 
        AC p @ tested n (A p) (C p) = (Z >> V) p \<and> BD p @ tested m (B p) (D p) = (Z >> W) p \<and>
        n \<le> length (A p) \<and> n \<le> length (C p) \<and> m \<le> length (B p) \<and> m \<le> length (D p)"
  shows  "map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<approx>
   map_op projl projr
   (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
     (map_op projl projr
       (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
         (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
     (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))"
  using assms proof (coinduction arbitrary: A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V A B C D AC BD  rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have [A10_prems]: "\<exists>op2'. wstep (Inp (Inl pa) y) (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) (map_op projl projr (comp_op Some Z (aeq_op (case_sum (BENQ pa y X) Y)) (acopy_op (case_sum V W)))) op2'"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "pa \<notin> defaults"
      for pa :: 'a
        and y :: 'b
      using that
      apply -
      apply (intro exI conjI[rotated] wbc_base)
         defer
         apply (rule refl)+
       apply fastforce
      apply (intro allI)
      subgoal for p
        apply (drule spec[of _ p])
        apply (elim conjE exE)
        subgoal for m n
          apply (rule exI[of _ m])
          apply (rule exI[of _ n])
          apply simp
          apply (intro conjI)
               apply (simp_all add: tested_def flip: BAPPEND_BENQ)
          subgoal
            by (metis BENQ_access BENQ_diff_access diff_is_0_eq' drop_0 drop_append)
          subgoal
            by (metis BENQ_access BENQ_diff_access diff_is_0_eq' drop_0 drop_append)
          subgoal
            by (smt (verit, ccfv_threshold) BENQ_access BENQ_diff_access append_eq_append_conv_if append_take_drop_id length_append_singleton length_take min_def not_less_eq_eq)
          subgoal
            by (smt (verit, ccfv_threshold) BENQ_access BENQ_diff_access append_eq_append_conv_if append_take_drop_id length_append_singleton length_take min_def not_less_eq_eq)
          subgoal
            by (metis BENQ_access BENQ_diff_access length_append_singleton less_Suc_eq_le less_or_eq_imp_le)
          subgoal
            by (metis BENQ_access BENQ_diff_access length_append_singleton less_Suc_eq_le less_or_eq_imp_le)
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. wstep (Inp (Inr pa) y) (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) (map_op projl projr (comp_op Some Z (aeq_op (case_sum X (BENQ pa y Y))) (acopy_op (case_sum V W)))) op2'"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "pa \<notin> defaults"
      for pa :: 'a
        and y :: 'b
      using that
      apply -
      apply (intro exI conjI[rotated] wbc_base)
         defer
         apply (rule refl)+
       apply fastforce
      apply (intro allI)
      subgoal for p
        apply (drule spec[of _ p])
        apply (elim conjE exE)
        subgoal for m n
          apply (rule exI[of _ m])
          apply (rule exI[of _ n])
          apply simp
          apply (intro conjI)
               apply (simp_all add: tested_def flip: BAPPEND_BENQ)
          subgoal
            by (metis BENQ_access BENQ_diff_access diff_is_0_eq' drop_0 drop_append)
          subgoal
            by (metis BENQ_access BENQ_diff_access diff_is_0_eq' drop_0 drop_append)
          subgoal
            by (smt (verit, ccfv_threshold) BENQ_access BENQ_diff_access append_eq_append_conv_if append_take_drop_id length_append_singleton length_take min_def not_less_eq_eq)
          subgoal
            by (smt (verit, ccfv_threshold) BENQ_access BENQ_diff_access append_eq_append_conv_if append_take_drop_id length_append_singleton length_take min_def not_less_eq_eq)
          subgoal
            by (metis BENQ_access BENQ_diff_access length_append_singleton less_Suc_eq_le less_or_eq_imp_le)
          subgoal
            by (metis BENQ_access BENQ_diff_access length_append_singleton less_Suc_eq_le less_or_eq_imp_le)
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. wstep (Out (Inl pa) (BHD pa V)) (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum (BTL pa V) W)))) op2'"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "V pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that
      apply -
      apply (frule spec[of _ pa])
      apply (elim exE disjE conjE)
      subgoal for m n
        apply (cases \<open>AC2 pa \<noteq> []\<close>)
        subgoal
          apply (intro exI conjI[rotated] wbc_base)
             defer
             apply (rule refl)+
           apply (rule step_wstep)
           apply (rule step_map_op[of \<open>Out (Inr (Inl pa)) (BHD pa AC2)\<close>])
            apply fastforce
           apply auto[1]
           apply (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty hd_append2)
          apply (rule allI)
          subgoal for p
            apply (cases \<open>p = pa\<close>)
            subgoal
              apply (rule exI[of _ m])
              apply (rule exI[of _ n])
              apply auto[1]
              by (smt (verit) BAPPEND_BTL BTL_access BULK_BENQ_empty tl_append2)
            subgoal
              apply (drule spec[of _ p])
              apply (elim conjE exE)
              subgoal for m' n'
                apply (rule exI[of _ m'])
                apply (rule exI[of _ n'])
                apply (simp add: BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        subgoal
          apply (cases \<open>AC1 pa \<noteq> []\<close>)
          subgoal
            apply (intro exI conjI[rotated] wbc_base)
               defer
               apply (rule refl)+
             apply (rule step_tau_step_io_wstep[of _ \<open>map_op projl projr
       (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2))
             (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc
               (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (BTL pa AC1) (aeq_op (case_sum A5 C5)) (id_op (BENQ pa (BHD pa AC1) AC2))))
           (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))\<close>])
              apply auto[1]
              apply fastforce
             apply (rule step_map_op[of \<open>Out (Inr (Inl pa)) (BHD pa AC1)\<close>])
              apply auto[3]
             apply (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty hd_append2)
            subgoal for p
              apply (cases \<open>p = pa\<close>)
              subgoal
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply auto[1]
                by (metis (no_types, opaque_lifting) BTL_access BULK_BENQ_def self_append_conv2 tl_append2)
              subgoal
                apply (drule spec[of _ p])
                apply (elim conjE exE)
                subgoal for m' n'
                  apply (rule exI[of _ m'])
                  apply (rule exI[of _ n'])
                  apply (simp add: BTL_def BULK_BENQ_def)
                  done
                done
              done
            done
          subgoal
            apply (cases n)
            subgoal
              apply (rule FalseE)
              by (metis BULK_BENQ_empty append_self_conv2 length_tested_0)
            subgoal for n'
              apply (intro exI conjI[rotated] wbc_base)
                 defer
                 apply (rule refl)+
               apply (rule wstep_trans(1))
                apply (rule wstep_Tau_acopy_op_id_op_transp_op_aeq_op2[of _ n _ _ _ _ _ _ _ _ _ _ m])
                    apply simp_all
               apply (rule step_map_op[of \<open>Out (Inr (Inl pa)) (BHD pa V)\<close>])
                apply (rule step_comp_op_R_Out)
                  apply (rule step_comp_op_L_Out)
                     apply (rule step_map_op[of \<open>Out (Inr pa) (BHD pa V)\<close>])
                      apply (rule step_comp_op_R_Out)
                        apply (rule step_id_op_Write)
                           apply (simp_all add: BHD_def)
               apply (metis BHD_BULK_BENQ_right_not_empty BHD_def)
              apply (rule allI)
              subgoal for p
                apply (cases \<open>p = pa\<close>)
                subgoal
                  apply (rule exI[of _ 0])
                  apply (rule exI[of _ 0])
                  apply auto[1]
                       apply (metis BULK_BENQ_left_empty fun_upd_same)
                      apply (metis BULK_BENQ_left_empty fun_upd_same)
                     apply (metis BULK_BENQ_left_empty fun_upd_same)
                    apply (metis BULK_BENQ_left_empty fun_upd_same)
                   apply (metis BAPPEND_BTL BTL_access BULK_BENQ_left_empty fun_upd_same)
                  by (metis BULK_BENQ_left_empty fun_upd_same)
                subgoal
                  apply (drule spec[of _ p])
                  apply (elim conjE exE)
                  subgoal for m' n''
                    apply (rule exI[of _ m'])
                    apply (rule exI[of _ n''])
                    apply (simp add: BTL_def BULK_BENQ_def)
                    done
                  done
                done
              done
            done
          done
        done
      subgoal for m n
        apply (cases \<open>AC2 pa \<noteq> []\<close>)
        subgoal
          apply (intro exI conjI[rotated] wbc_base)
             defer
             apply (rule refl)+
           apply (rule step_wstep)
           apply (rule step_map_op[of \<open>Out (Inr (Inl pa)) (BHD pa AC2)\<close>])
            apply fastforce
           apply auto[1]
           apply (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty)
          apply (rule allI)
          subgoal for p
            apply (cases \<open>p = pa\<close>)
            subgoal
              apply (rule exI[of _ m])
              apply (rule exI[of _ n])
              apply auto[1]
              by (smt (verit) BAPPEND_BTL BTL_access BULK_BENQ_empty tl_append2)
            subgoal
              apply (drule spec[of _ p])
              apply (elim conjE exE)
              subgoal for m' n'
                apply (rule exI[of _ m'])
                apply (rule exI[of _ n'])
                apply (simp add: BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        subgoal
          apply (cases \<open>AC1 pa \<noteq> []\<close>)
          subgoal
            apply (intro exI conjI[rotated] wbc_base)
               defer
               apply (rule refl)+
             apply (rule step_tau_step_io_wstep[of _ \<open>map_op projl projr
       (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2))
             (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc
               (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (BTL pa AC1) (aeq_op (case_sum A5 C5)) (id_op (BENQ pa (BHD pa AC1) AC2))))
           (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))\<close>])
              apply auto[1]
              apply fastforce
             apply (rule step_map_op[of \<open>Out (Inr (Inl pa)) (BHD pa AC1)\<close>])
              apply auto[3]
             apply (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty)
            subgoal for p
              apply (cases \<open>p = pa\<close>)
              subgoal
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply auto[1]
                by (metis (no_types, opaque_lifting) BTL_access BULK_BENQ_def self_append_conv2 tl_append2)
              subgoal
                apply (drule spec[of _ p])
                apply (elim conjE exE)
                subgoal for m' n'
                  apply (rule exI[of _ m'])
                  apply (rule exI[of _ n'])
                  apply (simp add: BTL_def BULK_BENQ_def)
                  done
                done
              done
            done
          subgoal
            apply (rule FalseE)
            by (metis BULK_BENQ_empty append_self_conv2 length_tested_0)
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. wstep (Out (Inr pa) (BHD pa W)) (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V (BTL pa W))))) op2'"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "W pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that
      apply -
      apply (frule spec[of _ pa])
      apply (elim exE disjE conjE)
      subgoal for m n
        apply (cases \<open>BD2 pa \<noteq> []\<close>)
        subgoal
          apply (intro exI conjI[rotated] wbc_base)
             defer
             apply (rule refl)+
           apply (rule step_wstep)
           apply (rule step_map_op[of \<open>Out (Inr (Inr pa)) (BHD pa BD2)\<close>])
            apply fastforce
           apply auto[1]
           apply (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty)
          apply (rule allI)
          subgoal for p
            apply (cases \<open>p = pa\<close>)
            subgoal
              apply (rule exI[of _ m])
              apply (rule exI[of _ n])
              apply auto[1]
              by (smt (verit) BAPPEND_BTL BTL_access BULK_BENQ_empty tl_append2)
            subgoal
              apply (drule spec[of _ p])
              apply (elim conjE exE)
              subgoal for m' n'
                apply (rule exI[of _ m'])
                apply (rule exI[of _ n'])
                apply (simp add: BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        subgoal
          apply (cases \<open>BD1 pa \<noteq> []\<close>)
          subgoal
            apply (intro exI conjI[rotated] wbc_base)
               defer
               apply (rule refl)+
             apply (rule step_tau_step_io_wstep[of _ \<open>map_op projl projr
       (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2))
             (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc
               (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2)))
           (map_op projl projr (comp_op Some (BTL pa BD1) (aeq_op (case_sum B5 D5)) (id_op (BENQ pa (BHD pa BD1) BD2))))))\<close>])
              apply auto[1]
              apply fastforce
             apply (rule step_map_op[of \<open>Out (Inr (Inr pa)) (BHD pa BD1)\<close>])
              apply auto[3]
             apply (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty)
            subgoal for p
              apply (cases \<open>p = pa\<close>)
              subgoal
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply auto[1]
                by (metis (no_types, opaque_lifting) BTL_access BULK_BENQ_def self_append_conv2 tl_append2)
              subgoal
                apply (drule spec[of _ p])
                apply (elim conjE exE)
                subgoal for m' n'
                  apply (rule exI[of _ m'])
                  apply (rule exI[of _ n'])
                  apply (simp add: BTL_def BULK_BENQ_def)
                  done
                done
              done
            done
          subgoal
            apply (rule FalseE)
            by (metis BULK_BENQ_empty append_self_conv2 length_tested_0)
          done
        done
      subgoal for m n
        apply (cases \<open>BD2 pa \<noteq> []\<close>)
        subgoal
          apply (intro exI conjI[rotated] wbc_base)
             defer
             apply (rule refl)+
           apply (rule step_wstep)
           apply (rule step_map_op[of \<open>Out (Inr (Inr pa)) (BHD pa BD2)\<close>])
            apply fastforce
           apply auto[1]
           apply (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty hd_append2)
          apply (rule allI)
          subgoal for p
            apply (cases \<open>p = pa\<close>)
            subgoal
              apply (rule exI[of _ m])
              apply (rule exI[of _ n])
              apply auto[1]
              by (smt (verit) BAPPEND_BTL BTL_access BULK_BENQ_empty tl_append2)
            subgoal
              apply (drule spec[of _ p])
              apply (elim conjE exE)
              subgoal for m' n'
                apply (rule exI[of _ m'])
                apply (rule exI[of _ n'])
                apply (simp add: BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        subgoal
          apply (cases \<open>BD1 pa \<noteq> []\<close>)
          subgoal
            apply (intro exI conjI[rotated] wbc_base)
               defer
               apply (rule refl)+
             apply (rule step_tau_step_io_wstep[of _ \<open>map_op projl projr
       (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4))
         (map_op projl projr
           (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2))
             (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1)))
             (map_op reassoc reassoc
               (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3)))))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2)))
           (map_op projl projr (comp_op Some (BTL pa BD1) (aeq_op (case_sum B5 D5)) (id_op (BENQ pa (BHD pa BD1) BD2))))))\<close>])
              apply auto[1]
              apply fastforce
             apply (rule step_map_op[of \<open>Out (Inr (Inr pa)) (BHD pa BD1)\<close>])
              apply auto[3]
             apply (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty hd_append2)
            subgoal for p
              apply (cases \<open>p = pa\<close>)
              subgoal
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply auto[1]
                by (metis (no_types, opaque_lifting) BTL_access BULK_BENQ_def self_append_conv2 tl_append2)
              subgoal
                apply (drule spec[of _ p])
                apply (elim conjE exE)
                subgoal for m' n'
                  apply (rule exI[of _ m'])
                  apply (rule exI[of _ n'])
                  apply (simp add: BTL_def BULK_BENQ_def)
                  done
                done
              done
            done
          subgoal
            apply (cases m)
            subgoal
              apply (rule FalseE)
              by (metis BULK_BENQ_empty append_self_conv2 length_tested_0)
            subgoal for m'
              apply (intro exI conjI[rotated] wbc_base)
                 defer
                 apply (rule refl)+
               apply (rule wstep_trans(1))
                apply (rule wstep_Tau_acopy_op_id_op_transp_op_aeq_op2[of _ n _ _ _ _ _ _ _ _ _ _ m])
                    apply simp_all
               apply (rule step_map_op[of \<open>Out (Inr (Inr pa)) (BHD pa W)\<close>])
                apply (rule step_comp_op_R_Out)
                  apply (rule step_comp_op_R_Out)
                     apply (rule step_map_op[of \<open>Out (Inr pa) (BHD pa W)\<close>])
                      apply (rule step_comp_op_R_Out)
                        apply (rule step_id_op_Write)
                           apply (simp_all add: BHD_def)
               apply (metis BHD_BULK_BENQ_right_not_empty BHD_def)
              apply (rule allI)
              subgoal for p
                apply (cases \<open>p = pa\<close>)
                subgoal
                  apply (rule exI[of _ 0])
                  apply (rule exI[of _ 0])
                  apply auto[1]
                       apply (metis BULK_BENQ_left_empty fun_upd_same)
                      apply (metis BULK_BENQ_left_empty fun_upd_same)
                     apply (metis BULK_BENQ_left_empty fun_upd_same)
                    apply (metis BULK_BENQ_left_empty fun_upd_same)
                   apply (metis BULK_BENQ_left_empty fun_upd_same)
                  by (metis BAPPEND_BTL BTL_access BULK_BENQ_left_empty fun_upd_same)
                subgoal
                  apply (drule spec[of _ p])
                  apply (elim conjE exE)
                  subgoal for m'' n'
                    apply (rule exI[of _ m''])
                    apply (rule exI[of _ n'])
                    apply (simp add: BTL_def BULK_BENQ_def)
                    done
                  done
                done
              done
            done
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) (map_op projl projr (comp_op Some (BENQ pa (BHD pa Y) Z) (aeq_op (case_sum (BTL pa X) (BTL pa Y))) (acopy_op (case_sum V W)))) op2'"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "X pa \<noteq> []"
        and "Y pa \<noteq> []"
        and "BHD pa X = BHD pa Y"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that 
      apply -
      apply (drule spec[of _ pa])
      apply (elim conjE exE disjE)
      subgoal for m n
        apply (intro exI conjI)
         apply (rule rtranclp_trans)
          apply (rule rtranclp_trans)
           apply (rule move_all_buffers[where p=pa])
           apply assumption
          apply (rule wstep_Tau_acopy_op_id_op_transp_op_aeq_op2[where n=n and m=m])
              apply assumption
             apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
            apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
           apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
          apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
         apply (rule step_map_op)
          apply simp_all
         apply (rule step_comp_op_R_Tau)
           apply simp_all
         apply (rule step_comp_op_R_Tau)
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_L)
               apply (rule step_aeq_op_Write)
                    apply assumption
                   apply simp_all
         apply (simp add: BHD_def BULK_BENQ_def)
        apply (rule wbc_base)
        apply (intro exI conjI)
          apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases "p = pa")
          subgoal
            apply (rule exI[of _ 0])
            apply (rule exI[of _ "Suc 0"])
            apply (simp add: drop_Suc BTL_access BULK_BENQ_left_empty)
            apply (intro conjI)
            subgoal
              by (simp add: BHD_def BULK_BENQ_def tested_eq_Suc)
            subgoal
              by (simp add: BHD_def BULK_BENQ_def tested_eq_Suc)
            subgoal
              using Suc_le_eq by blast
            subgoal
              using Suc_le_eq by blast
            done
          subgoal
            using that apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply (simp add: BENQ_diff_access BTL_diff_access flip: BAPPEND_BENQ)
              apply (intro conjI)
                       apply (smt (verit, del_insts) BTL_def BULK_BENQ_bulk_benq fun_upd_apply)+
              done
            done
          done
        done
      subgoal for m n
        apply (intro exI conjI)
         apply (rule rtranclp_trans)
          apply (rule rtranclp_trans)
           apply (rule move_all_buffers[where p=pa])
           apply assumption
          apply (rule wstep_Tau_acopy_op_id_op_transp_op_aeq_op2[where n=n and m=m])
              apply assumption
             apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
            apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
           apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
          apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
         apply (rule step_map_op)
          apply simp_all
         apply (rule step_comp_op_R_Tau)
           apply simp_all
         apply (rule step_comp_op_L_Tau)
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_L)
               apply (rule step_aeq_op_Write)
                    apply assumption
                   apply simp_all
         apply (simp add: BHD_def BULK_BENQ_def)
        apply (rule wbc_base)
        apply (intro exI conjI)
          apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases "p = pa")
          subgoal
            apply (rule exI[of _ "Suc 0"])
            apply (rule exI[of _ "0"])
            apply (simp add: drop_Suc BTL_access BULK_BENQ_left_empty)
            apply (intro conjI)
            subgoal
              by (simp add: BHD_def BULK_BENQ_def tested_eq_Suc)
            subgoal
              by (simp add: BHD_def BULK_BENQ_def tested_eq_Suc)
            subgoal
              using Suc_le_eq by blast
            subgoal
              using Suc_le_eq by blast
            done
          subgoal
            using that apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply (simp add: BENQ_diff_access BTL_diff_access flip: BAPPEND_BENQ)
              apply (intro conjI)
                       apply (smt (verit, del_insts) BTL_def BULK_BENQ_bulk_benq fun_upd_apply)+
              done
            done
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) (map_op projl projr (comp_op Some (BTL pa Z) (aeq_op (case_sum X Y)) (acopy_op (case_sum (BENQ pa (BHD pa Z) V) (BENQ pa (BHD pa Z) W))))) op2'"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "Z pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that 
      apply -
      apply (drule spec[of _ pa])
      apply (elim conjE exE disjE)
      subgoal for m n
        apply simp
        apply (intro exI conjI)
         apply (rule rtranclp_trans)
          apply (rule move_all_buffers[where p=pa])
          apply assumption
         apply (rule wstep_Tau_acopy_op_id_op_transp_op_aeq_op2[where n=n and m=m])
             apply assumption
            apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
           apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
          apply force
         apply force
        apply (rule wbc_base)
        apply (intro exI conjI)
          apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases "p = pa")
          subgoal
            apply (rule exI[of _ 0])
            apply (rule exI[of _ "0"])
            apply (simp add: drop_Suc BTL_access BULK_BENQ_left_empty)
            done
          subgoal
            using that apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply (simp add: BENQ_diff_access BTL_diff_access flip: BAPPEND_BENQ)
              apply (intro conjI)
                       apply (smt (verit, del_insts) BTL_def BULK_BENQ_bulk_benq fun_upd_apply)+
              done
            done
          done
        done
      subgoal for m n
        apply simp
        apply (intro exI conjI)
         apply (rule rtranclp_trans)
          apply (rule move_all_buffers[where p=pa])
          apply assumption
         apply (rule wstep_Tau_acopy_op_id_op_transp_op_aeq_op2[where n=n and m=m])
             apply assumption
            apply blast
           apply blast
          apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
         apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
        apply (rule wbc_base)
        apply (intro exI conjI)
          apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases "p = pa")
          subgoal
            apply (rule exI[of _ 0])
            apply (rule exI[of _ "0"])
            apply (simp add: drop_Suc BTL_access BULK_BENQ_left_empty)
            done
          subgoal
            using that apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply (simp add: BENQ_diff_access BTL_diff_access flip: BAPPEND_BENQ)
              apply (intro conjI)
                       apply (smt (verit, del_insts) BTL_def BULK_BENQ_bulk_benq fun_upd_apply)+
              done
            done
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2)))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) (map_op projl projr (comp_op Some Z (aeq_op (case_sum (BTL pa X) (BTL pa Y))) (acopy_op (case_sum V W)))) op2'"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "X pa \<noteq> []"
        and "Y pa \<noteq> []"
        and "BHD pa X \<noteq> BHD pa Y"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that 
      apply -
      apply (drule spec[of _ pa])
      apply (elim conjE exE disjE)
      subgoal for m n
        apply (intro exI conjI)
         apply (rule rtranclp_trans)
          apply (rule rtranclp_trans)
           apply (rule move_all_buffers[where p=pa])
           apply assumption
          apply (rule wstep_Tau_acopy_op_id_op_transp_op_aeq_op2[where n=n and m=m])
              apply assumption
             apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
            apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
           apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
          apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Tau)
            apply (rule step_comp_op_R_Tau)
              apply (rule step_map_op)
               apply (rule step_comp_op_L_Tau)
                 apply (rule step_aeq_op_Silent)
                     apply assumption
                    apply simp_all
         apply (metis BHD_def BULK_BENQ_bulk_benq append_self_conv fun_upd_apply)
        apply (rule wbc_base)
        apply (intro exI conjI)
          apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases "p = pa")
          subgoal
            apply (rule exI[of _ 0])
            apply (rule exI[of _ "Suc 0"])
            apply simp
            apply (intro conjI)
            subgoal
              by (simp add: BHD_def BULK_BENQ_left_empty BTL_def drop_Suc)
            subgoal
              by (simp add: BHD_def BULK_BENQ_left_empty BTL_def drop_Suc)
            subgoal
              by (simp add: BHD_def BULK_BENQ_left_empty BTL_def drop_Suc)
            subgoal
              by (simp add: BHD_def BULK_BENQ_left_empty BTL_def drop_Suc)
            subgoal
              by (simp add: BHD_def BULK_BENQ_left_empty tested_diff_Suc)
            subgoal
              by (metis BULK_BENQ_left_empty fun_upd_same)
            subgoal
              by (simp add: BULK_BENQ_left_empty Suc_leI)
            subgoal
              by (simp add: BULK_BENQ_left_empty Suc_leI)
            done
          subgoal
            using that apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply (simp add: BENQ_diff_access BTL_diff_access flip: BAPPEND_BENQ)
              apply (intro conjI)
                       apply (smt (verit, del_insts) BTL_def BULK_BENQ_bulk_benq fun_upd_apply)+
              done
            done
          done
        done
      subgoal for m n
        apply (intro exI conjI)
         apply (rule rtranclp_trans)
          apply (rule rtranclp_trans)
           apply (rule move_all_buffers[where p=pa])
           apply assumption
          apply (rule wstep_Tau_acopy_op_id_op_transp_op_aeq_op2[where n=n and m=m])
              apply assumption
             apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
            apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
           apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
          apply (metis BULK_BENQ_assoc BULK_BENQ_left_empty fun_upd_same)
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Tau)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_comp_op_L_Tau)
                 apply (rule step_aeq_op_Silent)
                     apply assumption
                    apply simp_all
         apply (simp add: BHD_def BULK_BENQ_left_empty)
        apply (rule wbc_base)
        apply (intro exI conjI)
          apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases "p = pa")
          subgoal
            apply (rule exI[of _ "Suc 0"])
            apply (rule exI[of _ "0"])
            apply (simp add: drop_Suc BTL_access BULK_BENQ_left_empty)
            apply (intro conjI)
            subgoal
              by (metis BHD_def length_tested_0 tested_diff_Suc)
            subgoal
              using Suc_le_eq by blast
            subgoal
              using Suc_le_eq by blast
            done
          subgoal
            using that apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply (simp add:  BENQ_diff_access BTL_diff_access flip: BAPPEND_BENQ)
              apply (intro conjI)
                       apply (smt (verit, del_insts) BTL_def BULK_BENQ_bulk_benq fun_upd_apply)+
              done
            done
          done
        done
      done
    show ?thesis
      apply -
      subgoal premises prems
        using SIM1 apply -
        apply (auto 0 0 elim !: step_aeq_op_elim step_acopy_op_elim step_transp_op_cases step_map_op_elim step_comp_op_elim step_id_op_cases split: if_splits sum.splits)
              apply (rule A10_prems; assumption)+
        done
      done
  qed
next
  case SIM2
  then show ?case
  proof -
    have [A10_prems]: "\<exists>op2'. wstep (Inp (Inl pb) x) (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (BENQ (Inr pb) x (BENQ (Inl pb) x (case_sum A1 B1)))) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "(pb::'a) \<notin> defaults"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and p :: "'a + 'a"
        and x :: 'b
        and op1' :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                    'b) IO"
        and op''a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                     (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                     'b) op"
        and pa :: "'a + 'a"
        and op1'a :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and pb :: 'a
        and xb :: 'b
        and op1'b :: "('a, 'a + 'a, 'b) op"
      using that
      apply -
      apply (drule spec[of _ pb])
      apply (elim disjE conjE exE)
      subgoal for m n
        apply simp
        apply (intro exI conjI)
         apply (rule step_wstep)
         apply force
        apply (rule wbc_base)
        apply (intro exI conjI)
          apply (rule refl)+
        apply (intro allI)
        subgoal for pc
          apply (cases \<open>pc = pb\<close>)
          subgoal
            apply (rule exI[of _ 0])
            apply (rule exI[of _ n])
            apply auto[1]
            subgoal
              by (simp flip: BAPPEND_BENQ)
            subgoal
              by (simp add: BULK_BENQ_def)
            subgoal
              by (simp add: tested_def flip: BAPPEND_BENQ)
            subgoal
              by (simp add: BULK_BENQ_def)
            done
          subgoal
            using that(1) apply -
            apply (drule spec[of _ pc])
            apply (elim conjE exE)
            subgoal for m' n'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply (simp add: BENQ_diff_access flip: BAPPEND_BENQ)
              done
            done
          done
        done
      subgoal for m n
        apply simp
        apply (intro exI conjI)
         apply (rule step_wstep)
         apply force
        apply (rule wbc_base)
        apply (intro exI conjI)
          apply (rule refl)+
        apply (intro allI)
        subgoal for pc
          apply (cases \<open>pc = pb\<close>)
          subgoal
            apply hypsubst_thin
            apply simp
            apply (rule exI[of _ m])
            apply simp
            apply (rule exI[of _ 0])
            apply simp
            apply (intro conjI)
               apply (simp_all flip: BAPPEND_BENQ)
            unfolding tested_def
            apply auto
            done
          subgoal
            using that(1) apply -
            apply (drule spec[of _ pc])
            apply (elim conjE exE)
            subgoal for m' n'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply (simp add: BENQ_diff_access flip: BAPPEND_BENQ)
              done
            done
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. wstep (Inp (Inr pb) x) (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (BENQ (Inr pb) x (case_sum (BENQ pb x C1) D1)))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "(pb::'a) \<notin> defaults"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and p :: "'a + 'a"
        and x :: 'b
        and op1' :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                    'b) IO"
        and op''a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                     (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                     'b) op"
        and pa :: "'a + 'a"
        and op1'a :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and pb :: 'a
        and xb :: 'b
        and op2' :: "('a, 'a + 'a, 'b) op"
      using that
      apply -
      apply (drule spec[of _ pb])
      apply (elim disjE conjE exE)
      subgoal for m n
        apply simp
        apply (intro exI conjI)
         apply (rule step_wstep)
         apply force
        apply (rule wbc_base)
        apply (intro exI conjI)
          apply (rule refl)+
        apply (intro allI)
        subgoal for pc
          apply (cases \<open>pc = pb\<close>)
          subgoal
            apply (rule exI[of _ 0])
            apply (rule exI[of _ n])
            apply auto[1]
            subgoal
              by (simp flip: BAPPEND_BENQ)
            subgoal
              by (simp add: BULK_BENQ_def)
            subgoal
              by (simp add: tested_def flip: BAPPEND_BENQ)
            subgoal
              by (simp add: BULK_BENQ_def)
            done
          subgoal
            using that(1) apply -
            apply (drule spec[of _ pc])
            apply (elim conjE exE)
            subgoal for m' n'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply (simp add: BENQ_diff_access flip: BAPPEND_BENQ)
              done
            done
          done
        done
      subgoal for m n
        apply simp
        apply (intro exI conjI)
         apply (rule step_wstep)
         apply force
        apply (rule wbc_base)
        apply (intro exI conjI)
          apply (rule refl)+
        apply (intro allI)
        subgoal for pc
          apply (cases \<open>pc = pb\<close>)
          subgoal
            apply hypsubst_thin
            apply simp
            apply (rule exI[of _ m])
            apply simp
            apply (rule exI[of _ 0])
            apply simp
            apply (intro conjI)
               apply (simp_all flip: BAPPEND_BENQ)
            unfolding tested_def
            apply auto
            done
          subgoal
            using that(1) apply -
            apply (drule spec[of _ pc])
            apply (elim conjE exE)
            subgoal for m' n'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply (simp add: BENQ_diff_access flip: BAPPEND_BENQ)
              done
            done
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. wstep (Out (Inr pa) (BHD pa BD2)) (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op (BTL pa BD2)))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "pa \<notin> defaults"
        and "BD2 pa \<noteq> []"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and p :: "'a + 'a"
        and x :: 'b
        and op2' :: "(('a + 'a) + 'a + 'a, 'a + 'a, 'b) op"
        and pa :: 'a
        and op2'a :: "('a + 'a, 'a, 'b) op"
        and io'a :: "(('a + 'a) + 'a, 'a + 'a, 'b) IO"
        and op''a :: "(('a + 'a) + 'a, 'a + 'a, 'b) op"
        and pb :: 'a
        and op2'b :: "('a, 'a, 'b) op"
        and pc :: 'a
      using that
      apply -
      apply (frule spec[of _ pa])
      apply (elim exE disjE conjE)
      subgoal for m n
        apply (cases \<open>W pa \<noteq> []\<close>)
        subgoal
          apply (rule exI[of _ \<open>map_op projl projr
          (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V (BTL pa W))))\<close>])
          apply (rule conjI)
          subgoal
            apply (rule step_wstep)
            apply auto[1]
            by (metis BHD_BULK_BENQ_right_not_empty BHD_def)
          subgoal
            apply (rule wbc_base)
            apply (intro exI conjI)
              apply (rule refl)+
            apply (intro allI)
            subgoal for pd
              apply (cases \<open>pd = pa\<close>)
              subgoal
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply simp
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                apply (drule spec[of _ pd])
                apply (elim conjE exE)
                subgoal for m' n'
                  apply (rule exI[of _ m'])
                  apply (rule exI[of _ n'])
                  apply (simp add: BTL_def BULK_BENQ_def)
                  done
                done
              done
            done
          done
        subgoal
          apply (rule exI[of _ \<open>map_op projl projr
       (comp_op Some (BTL pa Z) (aeq_op (case_sum X Y)) (acopy_op (case_sum (BENQ pa (BHD pa Z) V) W)))\<close>])
          apply (rule conjI)
          subgoal
            apply (rule step_tau_step_io_wstep[of _ \<open>map_op projl projr (comp_op Some (BTL pa Z) (aeq_op (case_sum X Y)) (acopy_op (case_sum (BENQ pa (BHD pa Z) V) (BENQ pa (BHD pa Z) W))))\<close>])
             apply auto[2]
            apply (metis BULK_BENQ_empty)
            by (metis BHD_BULK_BENQ_right_not_empty BHD_def BULK_BENQ_right_empty)
          subgoal
            apply (rule wbc_base)
            apply (intro exI conjI)
            apply (rule refl)+
            apply (intro allI)
            subgoal for pd
              apply (cases \<open>pd = pa\<close>)
              subgoal
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply simp
                by (metis BAPPEND_BENQ_BHD BAPPEND_BTL BTL_access BULK_BENQ_empty)
              subgoal
                apply (drule spec[of _ pd])
                apply (elim conjE exE)
                subgoal for m' n'
                  apply (rule exI[of _ m'])
                  apply (rule exI[of _ n'])
                  apply (simp add: BTL_def BULK_BENQ_def)
                  by (metis BENQ_def fun_upd_other)
                done
              done
            done
          done
        done
      subgoal for m n
        apply (cases \<open>W pa \<noteq> []\<close>)
        subgoal
          apply (rule exI[of _ \<open>map_op projl projr
          (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V (BTL pa W))))\<close>])
          apply (rule conjI)
          subgoal
            apply (rule step_wstep)
            apply auto[1]
            by (metis BHD_BULK_BENQ_right_not_empty BHD_def BULK_BENQ_empty hd_append2)
          subgoal
            apply (rule wbc_base)
            apply (intro exI conjI)
            apply (rule refl)+
            apply (intro allI)
            subgoal for pd
              apply (cases \<open>pd = pa\<close>)
              subgoal
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply simp
                by (smt (verit, ccfv_threshold) BTL_access BULK_BENQ_bulk_benq BULK_BENQ_empty tl_append2)
              subgoal
                apply (drule spec[of _ pd])
                apply (elim conjE exE)
                subgoal for m' n'
                  apply (rule exI[of _ m'])
                  apply (rule exI[of _ n'])
                  apply (simp add: BTL_def BULK_BENQ_def)
                  done
                done
              done
            done
          done
        subgoal
          apply (cases \<open>Z pa \<noteq> []\<close>)
          subgoal
            apply (rule exI[of _ \<open>map_op projl projr
         (comp_op Some (BTL pa Z) (aeq_op (case_sum X Y)) (acopy_op (case_sum (BENQ pa (BHD pa Z) V) W)))\<close>])
            apply (rule conjI)
            subgoal
              apply (rule step_tau_step_io_wstep[of _ \<open>map_op projl projr (comp_op Some (BTL pa Z) (aeq_op (case_sum X Y)) (acopy_op (case_sum (BENQ pa (BHD pa Z) V) (BENQ pa (BHD pa Z) W))))\<close>])
              apply auto[2]
              by (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty hd_append2)
            subgoal
              apply (rule wbc_base)
              apply (intro exI conjI)
              apply (rule refl)+
              apply (intro allI)
              subgoal for pd
                apply (cases \<open>pd = pa\<close>)
                subgoal
                  apply (rule exI[of _ m])
                  apply (rule exI[of _ n])
                  apply simp
                  by (smt (z3) BAPPEND_BTL BTL_access BULK_BENQ_empty tl_append2)
                subgoal
                  apply (drule spec[of _ pd])
                  apply (elim conjE exE)
                  subgoal for m' n'
                    apply (rule exI[of _ m'])
                    apply (rule exI[of _ n'])
                    apply (simp add: BTL_def BULK_BENQ_def)
                    by (metis BENQ_def fun_upd_other)
                  done
                done
              done
            done
          subgoal
            apply (rule FalseE)
            apply simp
            apply (metis BULK_BENQ_empty append_is_Nil_conv)
            done
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. wstep (Out (Inl pa) (BHD pa AC2)) (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op (BTL pa AC2)))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "(pa::'a) \<notin> defaults"
        and "AC2 pa \<noteq> []"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and p :: "'a + 'a"
        and x :: 'b
        and op2' :: "(('a + 'a) + 'a + 'a, 'a + 'a, 'b) op"
        and pa :: 'a
        and op1' :: "('a + 'a, 'a, 'b) op"
        and io'a :: "(('a + 'a) + 'a, 'a + 'a, 'b) IO"
        and op''a :: "(('a + 'a) + 'a, 'a + 'a, 'b) op"
        and pb :: 'a
        and op2'a :: "('a, 'a, 'b) op"
        and pc :: 'a
      using that
      apply -
      apply (frule spec[of _ pa])
      apply (elim exE disjE conjE)
      subgoal for m n
        apply (cases \<open>V pa \<noteq> []\<close>)
        subgoal
          apply (rule exI[of _ \<open>map_op projl projr
          (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum (BTL pa V) W)))\<close>])
          apply (rule conjI)
          subgoal
            apply (rule step_wstep)
            apply auto[1]
            by (metis BHD_BULK_BENQ_right_not_empty BHD_def BULK_BENQ_empty hd_append2)
          subgoal
            apply (rule wbc_base)
            apply (intro exI conjI)
            apply (rule refl)+
            apply (intro allI)
            subgoal for pd
              apply (cases \<open>pd = pa\<close>)
              subgoal
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply simp
                by (smt (verit, ccfv_threshold) BTL_access BULK_BENQ_bulk_benq BULK_BENQ_empty tl_append2)
              subgoal
                apply (drule spec[of _ pd])
                apply (elim conjE exE)
                subgoal for m' n'
                  apply (rule exI[of _ m'])
                  apply (rule exI[of _ n'])
                  apply (simp add: BTL_def BULK_BENQ_def)
                  done
                done
              done
            done
          done
        subgoal
          apply (cases \<open>Z pa \<noteq> []\<close>)
          subgoal
            apply (rule exI[of _ \<open>map_op projl projr
         (comp_op Some (BTL pa Z) (aeq_op (case_sum X Y)) (acopy_op (case_sum V (BENQ pa (BHD pa Z) W))))\<close>])
            apply (rule conjI)
            subgoal
              apply (rule step_tau_step_io_wstep[of _ \<open>map_op projl projr (comp_op Some (BTL pa Z) (aeq_op (case_sum X Y)) (acopy_op (case_sum (BENQ pa (BHD pa Z) V) (BENQ pa (BHD pa Z) W))))\<close>])
              apply auto[2]
              by (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty hd_append2)
            subgoal
              apply (rule wbc_base)
              apply (intro exI conjI)
              apply (rule refl)+
              apply (intro allI)
              subgoal for pd
                apply (cases \<open>pd = pa\<close>)
                subgoal
                  apply (rule exI[of _ m])
                  apply (rule exI[of _ n])
                  apply simp
                  by (smt (z3) BAPPEND_BTL BTL_access BULK_BENQ_empty tl_append2)
                subgoal
                  apply (drule spec[of _ pd])
                  apply (elim conjE exE)
                  subgoal for m' n'
                    apply (rule exI[of _ m'])
                    apply (rule exI[of _ n'])
                    apply (simp add: BTL_def BULK_BENQ_def)
                    by (metis BENQ_def fun_upd_other)
                  done
                done
              done
            done
          subgoal
            apply (rule FalseE)
            apply simp
            apply (metis BULK_BENQ_empty append_is_Nil_conv)
            done
          done
        done
      subgoal for m n
        apply (cases \<open>V pa \<noteq> []\<close>)
        subgoal
          apply (rule exI[of _ \<open>map_op projl projr
          (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum (BTL pa V) W)))\<close>])
          apply (rule conjI)
          subgoal
            apply (rule step_wstep)
            apply auto[1]
            by (metis BHD_BULK_BENQ_right_not_empty BHD_def)
          subgoal
            apply (rule wbc_base)
            apply (intro exI conjI)
            apply (rule refl)+
            apply (intro allI)
            subgoal for pd
              apply (cases \<open>pd = pa\<close>)
              subgoal
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply simp
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                apply (drule spec[of _ pd])
                apply (elim conjE exE)
                subgoal for m' n'
                  apply (rule exI[of _ m'])
                  apply (rule exI[of _ n'])
                  apply (simp add: BTL_def BULK_BENQ_def)
                  done
                done
              done
            done
          done
        subgoal
          apply (rule exI[of _ \<open>map_op projl projr
       (comp_op Some (BTL pa Z) (aeq_op (case_sum X Y)) (acopy_op (case_sum V (BENQ pa (BHD pa Z) W))))\<close>])
          apply (rule conjI)
          subgoal
            apply (rule step_tau_step_io_wstep[of _ \<open>map_op projl projr (comp_op Some (BTL pa Z) (aeq_op (case_sum X Y)) (acopy_op (case_sum (BENQ pa (BHD pa Z) V) (BENQ pa (BHD pa Z) W))))\<close>])
            apply auto[2]
            apply (metis BULK_BENQ_empty)
            by (metis BHD_BULK_BENQ_right_not_empty BHD_def BULK_BENQ_right_empty)
          subgoal
            apply (rule wbc_base)
            apply (intro exI conjI)
            apply (rule refl)+
            apply (intro allI)
            subgoal for pd
              apply (cases \<open>pd = pa\<close>)
              subgoal
                apply (rule exI[of _ m])
                apply (rule exI[of _ n])
                apply simp
                by (metis BAPPEND_BENQ_BHD BAPPEND_BTL BTL_access BULK_BENQ_empty)
              subgoal
                apply (drule spec[of _ pd])
                apply (elim conjE exE)
                subgoal for m' n'
                  apply (rule exI[of _ m'])
                  apply (rule exI[of _ n'])
                  apply (simp add: BTL_def BULK_BENQ_def)
                  by (metis BENQ_def fun_upd_other)
                done
              done
            done
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (BENQ (Inr (Inr pb)) (BHD pb D3) (case_sum (case_sum A4 C4) (case_sum B4 D4))) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op (BTL pb D3)))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "(pb::'a) \<notin> defaults"
        and "D3 pb \<noteq> []"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and p :: "('a + 'a) + 'a + 'a"
        and x :: 'b
        and op1' :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and q :: "('a + 'a) + 'a + 'a"
        and io'a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                    'b) IO"
        and op''a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                     (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                     'b) op"
        and pa :: "('a + 'a) + 'a + 'a"
        and op2' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                    'b) IO"
        and op''b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                     'b) op"
        and pb :: 'a
        and xb :: 'b
        and op2'a :: "('a, 'a, 'b) op"
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply simp
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (BENQ (Inl (Inr x1a)) (BHD x1a C3) (case_sum (case_sum A4 C4) (case_sum B4 D4))) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 (BTL x1a C3))))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "(x1a::'a) \<notin> defaults"
        and "C3 x1a \<noteq> []"
        and "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and p :: "('a + 'a) + 'a + 'a"
        and x :: 'b
        and op1' :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and q :: "('a + 'a) + 'a + 'a"
        and io'a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                    'b) IO"
        and op''a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                     (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                     'b) op"
        and pa :: "('a + 'a) + 'a + 'a"
        and op2' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                    'b) IO"
        and op''b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                     'b) op"
        and pb :: "('a + 'a) + 'a"
        and op1'a :: "(('a + 'a) + 'a, ('a + 'a) + 'a, 'b) op"
        and io'c :: "('a + 'a + 'a, 'a + 'a + 'a, 'b) IO"
        and op''c :: "('a + 'a + 'a, 'a + 'a + 'a, 'b) op"
        and pc :: "'a + 'a"
        and xc :: 'b
        and op2'a :: "('a + 'a, 'a + 'a, 'b) op"
        and p' :: "'a + 'a"
        and x1 :: "'a + 'a"
        and x1a :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply simp
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (BENQ (Inr (Inl x2)) (BHD x2 B3) (case_sum (case_sum A4 C4) (case_sum B4 D4))) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum (BTL x2 B3) C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "(x2::'a) \<notin> defaults"
        and "B3 x2 \<noteq> []"
        and "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and p :: "('a + 'a) + 'a + 'a"
        and x :: 'b
        and op1' :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and q :: "('a + 'a) + 'a + 'a"
        and io'a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                    'b) IO"
        and op''a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                     (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                     'b) op"
        and pa :: "('a + 'a) + 'a + 'a"
        and op2' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                    'b) IO"
        and op''b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                     'b) op"
        and pb :: "('a + 'a) + 'a"
        and op1'a :: "(('a + 'a) + 'a, ('a + 'a) + 'a, 'b) op"
        and io'c :: "('a + 'a + 'a, 'a + 'a + 'a, 'b) IO"
        and op''c :: "('a + 'a + 'a, 'a + 'a + 'a, 'b) op"
        and pc :: "'a + 'a"
        and xc :: 'b
        and op2'a :: "('a + 'a, 'a + 'a, 'b) op"
        and p' :: "'a + 'a"
        and x2 :: 'a
        and x2a :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply simp
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (BENQ (Inl (Inl pc)) (BHD pc A3) (case_sum (case_sum A4 C4) (case_sum B4 D4))) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL pc A3)) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "(pc::'a) \<notin> defaults"
        and "A3 pc \<noteq> []"
        and "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and p :: "('a + 'a) + 'a + 'a"
        and x :: 'b
        and op1' :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and q :: "('a + 'a) + 'a + 'a"
        and io'a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                    'b) IO"
        and op''a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                     (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                     'b) op"
        and pa :: "('a + 'a) + 'a + 'a"
        and op2' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                    'b) IO"
        and op''b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                     'b) op"
        and pb :: "('a + 'a) + 'a"
        and op1'a :: "(('a + 'a) + 'a, ('a + 'a) + 'a, 'b) op"
        and io'c :: "('a + 'a + 'a, 'a + 'a + 'a, 'b) IO"
        and op''c :: "('a + 'a + 'a, 'a + 'a + 'a, 'b) op"
        and pc :: 'a
        and xc :: 'b
        and op1'b :: "('a, 'a, 'b) op"
        and x1 :: "'a + 'a"
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply simp
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1 A4) C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (BENQ x1 (BHD x1 A4) A5) C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "(x1::'a) \<notin> defaults"
        and "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "A4 x1 \<noteq> []"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and p :: "('a + 'a) + 'a + 'a"
        and x :: 'b
        and op2' :: "(('a + 'a) + 'a + 'a, 'a + 'a, 'b) op"
        and pa :: "'a + 'a"
        and op1' :: "('a + 'a, 'a, 'b) op"
        and io'a :: "(('a + 'a) + 'a, 'a + 'a, 'b) IO"
        and op''a :: "(('a + 'a) + 'a, 'a + 'a, 'b) op"
        and pb :: "'a + 'a"
        and op1'a :: "('a + 'a, 'a, 'b) op"
        and pc :: 'a
        and x1 :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 (BTL x2 C4)) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 (BENQ x2 (BHD x2 C4) C5))) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "(x2::'a) \<notin> defaults"
        and "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "C4 x2 \<noteq> []"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and p :: "('a + 'a) + 'a + 'a"
        and x :: 'b
        and op2' :: "(('a + 'a) + 'a + 'a, 'a + 'a, 'b) op"
        and pa :: "'a + 'a"
        and op1' :: "('a + 'a, 'a, 'b) op"
        and io'a :: "(('a + 'a) + 'a, 'a + 'a, 'b) IO"
        and op''a :: "(('a + 'a) + 'a, 'a + 'a, 'b) op"
        and pb :: "'a + 'a"
        and op1'a :: "('a + 'a, 'a, 'b) op"
        and pc :: 'a
        and x2 :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum (BTL x1 B4) D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (BENQ x1 (BHD x1 B4) B5) D5)) (id_op BD2))))))"
      if "(x1::'a) \<notin> defaults"
        and "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "B4 x1 \<noteq> []"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and p :: "('a + 'a) + 'a + 'a"
        and x :: 'b
        and op2' :: "(('a + 'a) + 'a + 'a, 'a + 'a, 'b) op"
        and pa :: "'a + 'a"
        and op2'a :: "('a + 'a, 'a, 'b) op"
        and io'a :: "(('a + 'a) + 'a, 'a + 'a, 'b) IO"
        and op''a :: "(('a + 'a) + 'a, 'a + 'a, 'b) op"
        and pb :: "'a + 'a"
        and op1' :: "('a + 'a, 'a, 'b) op"
        and pc :: 'a
        and x1 :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 (BTL x2 D4))) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 (BENQ x2 (BHD x2 D4) D5))) (id_op BD2))))))"
      if "(x2::'a) \<notin> defaults"
        and "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "D4 x2 \<noteq> []"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and p :: "('a + 'a) + 'a + 'a"
        and x :: 'b
        and op2' :: "(('a + 'a) + 'a + 'a, 'a + 'a, 'b) op"
        and pa :: "'a + 'a"
        and op2'a :: "('a + 'a, 'a, 'b) op"
        and io'a :: "(('a + 'a) + 'a, 'a + 'a, 'b) IO"
        and op''a :: "(('a + 'a) + 'a, 'a + 'a, 'b) op"
        and pb :: "'a + 'a"
        and op1' :: "('a + 'a, 'a, 'b) op"
        and pc :: 'a
        and x2 :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (BENQ (Inr (Inl pc)) (BHD pc C1) (case_sum (case_sum A2 B2) (case_sum C2 D2))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum (BTL pc C1) D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "C1 pc \<noteq> []"
        and "(pc::'a) \<notin> defaults"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and op1' :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                    'b) IO"
        and op''a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                     (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                     'b) op"
        and pa :: "('a + 'a) + 'a + 'a"
        and xa :: 'b
        and op1'a :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and q :: "('a + 'a) + 'a + 'a"
        and pb :: "'a + 'a"
        and op2' :: "('a, 'a + 'a, 'b) op"
        and pc :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply simp
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (BENQ (Inr (Inr pc)) (BHD pc D1) (case_sum (case_sum A2 B2) (case_sum C2 D2))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 (BTL pc D1)))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "D1 pc \<noteq> []"
        and "(pc::'a) \<notin> defaults"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and op1' :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                    'b) IO"
        and op''a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                     (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                     'b) op"
        and pa :: "('a + 'a) + 'a + 'a"
        and xa :: 'b
        and op1'a :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and q :: "('a + 'a) + 'a + 'a"
        and pb :: "'a + 'a"
        and op2' :: "('a, 'a + 'a, 'b) op"
        and pc :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply simp
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (BENQ (Inl (Inl pc)) (BHD pc A1) (case_sum (case_sum A2 B2) (case_sum C2 D2))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum (BTL pc A1) B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "A1 pc \<noteq> []"
        and "(pc::'a) \<notin> defaults"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and op1' :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                    'b) IO"
        and op''a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                     (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                     'b) op"
        and pa :: "('a + 'a) + 'a + 'a"
        and xa :: 'b
        and op1'a :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and q :: "('a + 'a) + 'a + 'a"
        and pb :: "'a + 'a"
        and op1'b :: "('a, 'a + 'a, 'b) op"
        and pc :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply simp
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (BENQ (Inl (Inr pc)) (BHD pc B1) (case_sum (case_sum A2 B2) (case_sum C2 D2))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 (BTL pc B1))) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "B1 pc \<noteq> []"
        and "(pc::'a) \<notin> defaults"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and op1' :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                    'b) IO"
        and op''a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                     (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                     'b) op"
        and pa :: "('a + 'a) + 'a + 'a"
        and xa :: 'b
        and op1'a :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and q :: "('a + 'a) + 'a + 'a"
        and pb :: "'a + 'a"
        and op1'b :: "('a, 'a + 'a, 'b) op"
        and pc :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply simp
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum (BTL x1b A2) B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ x1b (BHD x1b A2) A3)) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "(x1b::'a) \<notin> defaults"
        and "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "A2 x1b \<noteq> []"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and op1' :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                    'b) IO"
        and op''a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                     (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                     'b) op"
        and pa :: "('a + 'a) + 'a + 'a"
        and xa :: 'b
        and op2' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                    'b) IO"
        and op''b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                     'b) op"
        and pb :: "('a + 'a) + 'a"
        and op1'a :: "(('a + 'a) + 'a, ('a + 'a) + 'a, 'b) op"
        and io'c :: "('a + 'a + 'a, 'a + 'a + 'a, 'b) IO"
        and op''c :: "('a + 'a + 'a, 'a + 'a + 'a, 'b) op"
        and pc :: 'a
        and xc :: 'b
        and op1'b :: "('a, 'a, 'b) op"
        and x1 :: "'a + 'a"
        and x1a :: "'a + 'a"
        and x1b :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 (BTL x2 B2)) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum (BENQ x2 (BHD x2 B2) B3) C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "(x2::'a) \<notin> defaults"
        and "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "B2 x2 \<noteq> []"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and op1' :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                    'b) IO"
        and op''a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                     (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                     'b) op"
        and pa :: "('a + 'a) + 'a + 'a"
        and xa :: 'b
        and op2' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                    'b) IO"
        and op''b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                     'b) op"
        and pb :: "('a + 'a) + 'a"
        and op1'a :: "(('a + 'a) + 'a, ('a + 'a) + 'a, 'b) op"
        and io'c :: "('a + 'a + 'a, 'a + 'a + 'a, 'b) IO"
        and op''c :: "('a + 'a + 'a, 'a + 'a + 'a, 'b) op"
        and pc :: "'a + 'a"
        and xc :: 'b
        and op2'a :: "('a + 'a, 'a + 'a, 'b) op"
        and x1 :: "'a + 'a"
        and x1a :: "'a + 'a"
        and x1b :: 'a
        and x2 :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum (BTL x1 C2) D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 (BENQ x1 (BHD x1 C2) C3))))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "(x1::'a) \<notin> defaults"
        and "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "C2 x1 \<noteq> []"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and op1' :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                    'b) IO"
        and op''a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                     (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                     'b) op"
        and pa :: "('a + 'a) + 'a + 'a"
        and xa :: 'b
        and op2' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                    'b) IO"
        and op''b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                     'b) op"
        and pb :: "('a + 'a) + 'a"
        and op1'a :: "(('a + 'a) + 'a, ('a + 'a) + 'a, 'b) op"
        and io'c :: "('a + 'a + 'a, 'a + 'a + 'a, 'b) IO"
        and op''c :: "('a + 'a + 'a, 'a + 'a + 'a, 'b) op"
        and pc :: "'a + 'a"
        and xc :: 'b
        and op2'a :: "('a + 'a, 'a + 'a, 'b) op"
        and x2 :: "'a + 'a"
        and x2a :: 'a
        and x2b :: 'a
        and x1 :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 (BTL x2a D2))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op (BENQ x2a (BHD x2a D2) D3)))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "(x2a::'a) \<notin> defaults"
        and "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "D2 x2a \<noteq> []"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and op1' :: "('a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                    'b) IO"
        and op''a :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                     (('a + 'a) + 'a + 'a) + ('a + 'a) + 'a + 'a,
                     'b) op"
        and pa :: "('a + 'a) + 'a + 'a"
        and xa :: 'b
        and op2' :: "(('a + 'a) + 'a + 'a, ('a + 'a) + 'a + 'a, 'b) op"
        and io'b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                    'b) IO"
        and op''b :: "((('a + 'a) + 'a) + 'a, (('a + 'a) + 'a) + 'a,
                     'b) op"
        and pb :: 'a
        and xb :: 'b
        and op2'a :: "('a, 'a, 'b) op"
        and x2 :: "'a + 'a"
        and x2a :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply (intro allI)
      subgoal for pd
        apply (drule spec[of _ pd])
        apply (elim conjE exE)
        subgoal for m' n'
          apply (rule exI[of _ m'])
          apply (rule exI[of _ n'])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (BENQ pb (BHD pb C5) AC1) (aeq_op (case_sum (BTL pb A5) (BTL pb C5))) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "A5 pb \<noteq> []"
        and "C5 pb \<noteq> []"
        and "BHD pb A5 = BHD pb C5"
        and "(pb::'a) \<notin> defaults"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and op2' :: "(('a + 'a) + 'a + 'a, 'a + 'a, 'b) op"
        and op1' :: "('a + 'a, 'a, 'b) op"
        and io'a :: "(('a + 'a) + 'a, 'a + 'a, 'b) IO"
        and op''a :: "(('a + 'a) + 'a, 'a + 'a, 'b) op"
        and pb :: 'a
        and xb :: 'b
        and op1'a :: "('a + 'a, 'a, 'b) op"
        and pc :: 'a
        and xc :: 'b
      using that
      apply -
      apply (frule spec[of _ pb])
      apply (elim exE disjE conjE)
      subgoal for m n
        apply hypsubst_thin
        apply simp
        apply (cases n)
        subgoal
          apply (intro exI conjI)
          apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
          apply (rule step_Tau_comp_op_L)
          apply (rule step_aeq_op_Write)
          apply assumption
          apply simp_all
          subgoal
            by (metis BULK_BENQ_empty)
          subgoal
            by (metis BULK_BENQ_empty)
          subgoal
            by (metis (no_types, lifting) BHD_BAPPEND_2_cases BHD_def BULK_BENQ_empty)
          subgoal
            apply (rule wbc_base)
            apply (intro exI conjI)
            apply (rule refl)+
            apply (intro allI)
            subgoal for pd
              apply (cases \<open>pb = pd\<close>)
              subgoal
                apply simp
                apply (rule exI[of _ 1])
                apply (rule exI[of _ 0])
                apply (simp add: drop_Suc flip: tl_drop)
                apply (intro conjI)
                subgoal
                  by (metis BAPPEND_BTL BTL_access)
                subgoal
                  by (metis BAPPEND_BTL BTL_access)
                subgoal
                  by (simp add: BTL_def)
                subgoal
                  by (simp add: BTL_def)
                subgoal
                  by (metis BAPPEND_BENQ BENQ_access BHD_def BULK_BENQ_bulk_benq hd_append2)
                subgoal
                  apply (subst tested_eq_Suc_gen)
                  subgoal
                    by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                  subgoal
                    by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                  subgoal
                    by (smt (verit) BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty drop_all hd_conv_nth hd_drop_conv_nth le_neq_implies_less)
                  subgoal
                    by (metis BAPPEND_BENQ BENQ_access BHD_def BULK_BENQ_empty append_self_conv2 hd_conv_nth length_tested_0)
                  done
                subgoal
                  by (metis BULK_BENQ_empty Suc_leI length_greater_0_conv)
                subgoal
                  by (metis BULK_BENQ_empty Suc_leI length_greater_0_conv)
                done
              subgoal
                apply (drule spec[of _ pd])
                apply (elim conjE exE)
                subgoal for m' n'
                  apply (rule exI[of _ m'])
                  apply (rule exI[of _ n'])
                  apply simp
                  apply (intro conjI)
                  apply (simp_all add: BENQ_diff_access BTL_def BULK_BENQ_def)
                  done
                done
              done
            done
          done
        subgoal for n'
          apply (intro exI conjI)
          apply (rule rtranclp.intros(1))
          apply (rule wbc_base)
          apply (intro exI conjI)
          apply (rule refl)+
          apply (intro allI)
          subgoal for pd
            apply (cases \<open>pb = pd\<close>)
            subgoal
              apply simp
              apply (rule exI[of _ 0])
              apply (rule exI[of _ n'])
              apply (simp add: drop_Suc)
              apply (intro conjI)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                apply (subst (asm) tested_eq_Suc)
                apply simp_all
                apply (metis BHD_def BULK_BENQ_bulk_benq hd_append2)
                unfolding BENQ_def BHD_def BTL_def BULK_BENQ_def
                by (smt (verit) Cons_eq_appendI append_assoc append_eq_append_conv2 fun_upd_same hd_append2 self_append_conv tl_append2)
              subgoal
                by (metis BAPPEND_BTL BTL_access BULK_BENQ_empty Nitpick.size_list_simp(2) not_less_eq_eq)
              subgoal
                by (metis BAPPEND_BTL BTL_access BULK_BENQ_empty Nitpick.size_list_simp(2) not_less_eq_eq)
              done
            subgoal
              apply (drule spec[of _ pd])
              apply (elim conjE exE)
              subgoal for m' n''
                apply (rule exI[of _ m'])
                apply (rule exI[of _ n''])
                apply simp
                apply (intro conjI)
                apply (simp_all add: BENQ_diff_access BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        done
      subgoal for m n
        apply hypsubst_thin
        apply simp
        apply (intro exI conjI)
        apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
        apply (rule step_Tau_comp_op_L)
        apply (rule step_aeq_op_Write)
        apply assumption
        apply simp_all
        subgoal
          by (metis BULK_BENQ_empty)
        subgoal
          by (metis BULK_BENQ_empty)
        subgoal
          by (metis BHD_BULK_BENQ_right_not_empty BHD_def)
        subgoal
          apply (rule wbc_base)
          apply (intro exI conjI)
          apply (rule refl)+
          apply (intro allI)
          subgoal for pd
            apply (cases \<open>pb = pd\<close>)
            subgoal
              apply simp
              apply (rule exI[of _ \<open>Suc m\<close>])
              apply (rule exI[of _ 0])
              apply (simp add: drop_Suc flip: tl_drop)
              apply (intro conjI)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                by (simp add: BTL_def)
              subgoal
                by (simp add: BTL_def)
              subgoal
                by (metis BAPPEND_BENQ BENQ_access BHD_def BULK_BENQ_bulk_benq hd_append2)
              subgoal
                apply (subst tested_eq_Suc_gen)
                subgoal
                  by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                subgoal
                  by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                subgoal
                  by (smt (verit) BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty drop_all hd_drop_conv_nth le_neq_implies_less)
                subgoal
                  unfolding BENQ_def BHD_def BULK_BENQ_def
                  by (smt (verit, best) append_eq_appendI append_is_Nil_conv drop_eq_Nil fun_upd_same hd_drop_conv_nth le_eq_less_or_eq)
                done
              subgoal
                by (metis BULK_BENQ_empty drop_all not_less_eq_eq)
              subgoal
                by (metis BULK_BENQ_empty drop_all not_less_eq_eq)
              done
            subgoal
              apply (drule spec[of _ pd])
              apply (elim conjE exE)
              subgoal for m' n'
                apply (rule exI[of _ m'])
                apply (rule exI[of _ n'])
                apply simp
                apply (intro conjI)
                apply (simp_all add: BENQ_diff_access BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (BTL pc AC1) (aeq_op (case_sum A5 C5)) (id_op (BENQ pc (BHD pc AC1) AC2)))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "AC1 pc \<noteq> []"
        and "(pc::'a) \<notin> defaults"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and op2' :: "(('a + 'a) + 'a + 'a, 'a + 'a, 'b) op"
        and op1' :: "('a + 'a, 'a, 'b) op"
        and io'a :: "(('a + 'a) + 'a, 'a + 'a, 'b) IO"
        and op''a :: "(('a + 'a) + 'a, 'a + 'a, 'b) op"
        and pb :: 'a
        and xb :: 'b
        and op2'a :: "('a, 'a, 'b) op"
        and pc :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply (intro allI)
      subgoal for p
        apply (drule spec[of _ p])
        apply (elim conjE exE)
        subgoal for m n
          apply (rule exI[of _ m])
          apply (rule exI[of _ n])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum (BTL pc A5) (BTL pc C5))) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "A5 pc \<noteq> []"
        and "C5 pc \<noteq> []"
        and "BHD pc A5 \<noteq> BHD pc C5"
        and "(pc::'a) \<notin> defaults"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and op2' :: "(('a + 'a) + 'a + 'a, 'a + 'a, 'b) op"
        and op1' :: "('a + 'a, 'a, 'b) op"
        and io'a :: "(('a + 'a) + 'a, 'a + 'a, 'b) IO"
        and op''a :: "(('a + 'a) + 'a, 'a + 'a, 'b) op"
        and op1'a :: "('a + 'a, 'a, 'b) op"
        and pc :: 'a
      using that
      apply -
      apply (frule spec[of _ pc])
      apply (elim exE disjE conjE)
      subgoal for m n
        apply hypsubst_thin
        apply simp
        apply (cases n)
        subgoal
          apply (intro exI conjI)
          apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
          apply (rule step_comp_op_L_Tau)
          apply (rule step_aeq_op_Silent)
          apply assumption
          apply simp_all
          subgoal
            by (metis BULK_BENQ_empty)
          subgoal
            by (metis BULK_BENQ_empty)
          subgoal
            by (metis (no_types, lifting) BHD_BAPPEND_2_cases BHD_def BULK_BENQ_empty)
          subgoal
            apply (rule wbc_base)
            apply (intro exI conjI)
            apply (rule refl)+
            apply (intro allI)
            subgoal for pd
              apply (cases \<open>pc = pd\<close>)
              subgoal
                apply simp
                apply (rule exI[of _ 1])
                apply (rule exI[of _ 0])
                apply (simp add: drop_Suc flip: tl_drop)
                apply (intro conjI)
                subgoal
                  by (metis BAPPEND_BTL BTL_access)
                subgoal
                  by (metis BAPPEND_BTL BTL_access)
                subgoal
                  by (simp add: BTL_def)
                subgoal
                  by (simp add: BTL_def)
                subgoal
                  apply (subst tested_diff_Suc_gen)
                  subgoal
                    by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                  subgoal
                    by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                  subgoal
                    by (smt (verit) BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty drop_all hd_conv_nth hd_drop_conv_nth le_neq_implies_less)
                  apply simp
                  done
                subgoal
                  by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq Suc_le_eq)
                subgoal
                  by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq Suc_le_eq)
                done
              subgoal
                apply (drule spec[of _ pd])
                apply (elim conjE exE)
                subgoal for m' n'
                  apply (rule exI[of _ m'])
                  apply (rule exI[of _ n'])
                  apply simp
                  apply (intro conjI)
                  apply (simp_all add: BTL_def BULK_BENQ_def)
                  done
                done
              done
            done
          done
        subgoal for n'
          apply (intro exI conjI)
          apply (rule rtranclp.intros(1))
          apply (rule wbc_base)
          apply (intro exI conjI)
          apply (rule refl)+
          apply (intro allI)
          subgoal for pd
            apply (cases \<open>pc = pd\<close>)
            subgoal
              apply simp
              apply (rule exI[of _ 0])
              apply (rule exI[of _ n'])
              apply (simp add: drop_Suc)
              apply (intro conjI)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                apply (subst (asm) tested_diff_Suc)
                apply simp_all
                apply (metis BHD_def BULK_BENQ_bulk_benq hd_append2)
                apply (metis BAPPEND_BTL BTL_access)
                done
              subgoal
                by (metis BAPPEND_BTL BTL_access BULK_BENQ_empty Nitpick.size_list_simp(2) not_less_eq_eq)
              subgoal
                by (metis BAPPEND_BTL BTL_access BULK_BENQ_empty Nitpick.size_list_simp(2) not_less_eq_eq)
              done
            subgoal
              apply (drule spec[of _ pd])
              apply (elim conjE exE)
              subgoal for m' n''
                apply (rule exI[of _ m'])
                apply (rule exI[of _ n''])
                apply simp
                apply (intro conjI)
                apply (simp_all add: BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        done
      subgoal for m n
        apply hypsubst_thin
        apply simp
        apply (intro exI conjI)
        apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
        apply (rule step_comp_op_L_Tau)
        apply (rule step_aeq_op_Silent)
        apply assumption
        apply simp_all
        subgoal
          by (metis BULK_BENQ_empty)
        subgoal
          by (metis BULK_BENQ_empty)
        subgoal
          by (metis (no_types, lifting) BHD_BAPPEND_2_cases BHD_def BULK_BENQ_empty)
        subgoal
          apply (rule wbc_base)
          apply (intro exI conjI)
          apply (rule refl)+
          apply (intro allI)
          subgoal for pd
            apply (cases \<open>pc = pd\<close>)
            subgoal
              apply simp
              apply (rule exI[of _ \<open>Suc m\<close>])
              apply (rule exI[of _ 0])
              apply (simp add: drop_Suc flip: tl_drop)
              apply (intro conjI)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                by (simp add: BTL_def)
              subgoal
                by (simp add: BTL_def)
              subgoal
                apply (subst tested_diff_Suc_gen)
                subgoal
                  by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                subgoal
                  by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                subgoal
                  by (smt (verit) BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty drop_all hd_drop_conv_nth le_neq_implies_less)
                apply assumption
                done
              subgoal
                by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq Suc_le_eq)
              subgoal
                by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq Suc_le_eq)
              done
            subgoal
              apply (drule spec[of _ pd])
              apply (elim conjE exE)
              subgoal for m' n'
                apply (rule exI[of _ m'])
                apply (rule exI[of _ n'])
                apply simp
                apply (intro conjI)
                apply (simp_all add: BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some (BENQ pb (BHD pb D5) BD1) (aeq_op (case_sum (BTL pb B5) (BTL pb D5))) (id_op BD2))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "B5 pb \<noteq> []"
        and "D5 pb \<noteq> []"
        and "BHD pb B5 = BHD pb D5"
        and "(pb::'a) \<notin> defaults"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and op2' :: "(('a + 'a) + 'a + 'a, 'a + 'a, 'b) op"
        and op2'a :: "('a + 'a, 'a, 'b) op"
        and io'a :: "(('a + 'a) + 'a, 'a + 'a, 'b) IO"
        and op''a :: "(('a + 'a) + 'a, 'a + 'a, 'b) op"
        and pb :: 'a
        and xb :: 'b
        and op1' :: "('a + 'a, 'a, 'b) op"
        and pc :: 'a
        and xc :: 'b
      using that
      apply -
      apply (frule spec[of _ pb])
      apply (elim exE disjE conjE)
      subgoal for m n
        apply hypsubst_thin
        apply simp
        apply (intro exI conjI)
        apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
        apply (rule step_Tau_comp_op_L)
        apply (rule step_aeq_op_Write)
        apply assumption
        apply simp_all
        subgoal
          by (metis BULK_BENQ_empty)
        subgoal
          by (metis BULK_BENQ_empty)
        subgoal
          by (metis BHD_BULK_BENQ_right_not_empty BHD_def)
        subgoal
          apply (rule wbc_base)
          apply (intro exI conjI)
          apply (rule refl)+
          apply (intro allI)
          subgoal for pd
            apply (cases \<open>pb = pd\<close>)
            subgoal
              apply simp
              apply (rule exI[of _ 0])
              apply (rule exI[of _ \<open>Suc n\<close>])
              apply (simp add: drop_Suc flip: tl_drop)
              apply (intro conjI)
              subgoal
                by (simp add: BTL_def)
              subgoal
                by (simp add: BTL_def)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                apply (subst tested_eq_Suc_gen)
                subgoal
                  by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                subgoal
                  by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                subgoal
                  by (smt (verit) BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty drop_all hd_drop_conv_nth le_neq_implies_less)
                subgoal
                  unfolding BENQ_def BHD_def BULK_BENQ_def
                  by (smt (verit, best) append_eq_appendI append_is_Nil_conv drop_eq_Nil fun_upd_same hd_drop_conv_nth le_eq_less_or_eq)
                done
              subgoal
                by (metis BAPPEND_BENQ BENQ_access BHD_def BULK_BENQ_bulk_benq hd_append2)
              subgoal
                by (metis BULK_BENQ_empty drop_all not_less_eq_eq)
              subgoal
                by (metis BULK_BENQ_empty drop_all not_less_eq_eq)
              done
            subgoal
              apply (drule spec[of _ pd])
              apply (elim conjE exE)
              subgoal for m' n'
                apply (rule exI[of _ m'])
                apply (rule exI[of _ n'])
                apply simp
                apply (intro conjI)
                apply (simp_all add: BENQ_diff_access BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        done
      subgoal for m n
        apply hypsubst_thin
        apply simp
        apply (cases m)
        subgoal
          apply (intro exI conjI)
          apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
          apply (rule step_Tau_comp_op_L)
          apply (rule step_aeq_op_Write)
          apply assumption
          apply simp_all
          subgoal
            by (metis BULK_BENQ_empty)
          subgoal
            by (metis BULK_BENQ_empty)
          subgoal
            by (metis (no_types, lifting) BHD_BAPPEND_2_cases BHD_def BULK_BENQ_empty)
          subgoal
            apply (rule wbc_base)
            apply (intro exI conjI)
            apply (rule refl)+
            apply (intro allI)
            subgoal for pd
              apply (cases \<open>pb = pd\<close>)
              subgoal
                apply simp
                apply (rule exI[of _ 0])
                apply (rule exI[of _ 1])
                apply (simp add: drop_Suc flip: tl_drop)
                apply (intro conjI)
                subgoal
                  apply (simp add: BTL_def)
                  done
                subgoal
                  apply (simp add: BTL_def)
                  done
                subgoal
                  by (metis BAPPEND_BTL BTL_access)
                subgoal
                  by (metis BAPPEND_BTL BTL_access)
                subgoal
                  apply (subst tested_eq_Suc_gen)
                  subgoal
                    by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                  subgoal
                    by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                  subgoal
                    by (smt (verit) BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty drop_all hd_conv_nth hd_drop_conv_nth le_neq_implies_less)
                  subgoal
                    by (metis BAPPEND_BENQ BENQ_access BHD_def BULK_BENQ_empty append_self_conv2 hd_conv_nth length_tested_0)
                  done
                subgoal
                  by (metis BAPPEND_BENQ BENQ_access BHD_def BULK_BENQ_bulk_benq hd_append2)
                subgoal
                  by (metis BULK_BENQ_empty Suc_leI length_greater_0_conv)
                subgoal
                  by (metis BULK_BENQ_empty Suc_leI length_greater_0_conv)
                done
              subgoal
                apply (drule spec[of _ pd])
                apply (elim conjE exE)
                subgoal for m' n'
                  apply (rule exI[of _ m'])
                  apply (rule exI[of _ n'])
                  apply simp
                  apply (intro conjI)
                  apply (simp_all add: BENQ_diff_access BTL_def BULK_BENQ_def)
                  done
                done
              done
            done
          done
        subgoal for m'
          apply (intro exI conjI)
          apply (rule rtranclp.intros(1))
          apply (rule wbc_base)
          apply (intro exI conjI)
          apply (rule refl)+
          apply (intro allI)
          subgoal for pd
            apply (cases \<open>pb = pd\<close>)
            subgoal
              apply simp
              apply (rule exI[of _ m'])
              apply (rule exI[of _ 0])
              apply (simp add: drop_Suc)
              apply (intro conjI)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                apply (subst (asm) tested_eq_Suc)
                apply simp_all
                apply (metis BHD_def BULK_BENQ_bulk_benq hd_append2)
                unfolding BENQ_def BHD_def BTL_def BULK_BENQ_def
                by (smt (verit) Cons_eq_appendI append_assoc append_eq_append_conv2 fun_upd_same hd_append2 self_append_conv tl_append2)
              subgoal
                by (metis BAPPEND_BTL BTL_access BULK_BENQ_empty Nitpick.size_list_simp(2) not_less_eq_eq)
              subgoal
                by (metis BAPPEND_BTL BTL_access BULK_BENQ_empty Nitpick.size_list_simp(2) not_less_eq_eq)
              done
            subgoal
              apply (drule spec[of _ pd])
              apply (elim conjE exE)
              subgoal for m'' n'
                apply (rule exI[of _ m''])
                apply (rule exI[of _ n'])
                apply simp
                apply (intro conjI)
                apply (simp_all add: BENQ_diff_access BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some (BTL pc BD1) (aeq_op (case_sum B5 D5)) (id_op (BENQ pc (BHD pc BD1) BD2)))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "BD1 pc \<noteq> []"
        and "pc \<notin> defaults"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and op2' :: "(('a + 'a) + 'a + 'a, 'a + 'a, 'b) op"
        and op2'a :: "('a + 'a, 'a, 'b) op"
        and io'a :: "(('a + 'a) + 'a, 'a + 'a, 'b) IO"
        and op''a :: "(('a + 'a) + 'a, 'a + 'a, 'b) op"
        and pb :: 'a
        and xb :: 'b
        and op2'b :: "('a, 'a, 'b) op"
        and pc :: 'a
      using that
      apply -
      apply (intro exI conjI)
      apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
      apply (rule refl)+
      apply (intro allI)
      subgoal for p
        apply (drule spec[of _ p])
        apply (elim conjE exE)
        subgoal for m n
          apply (rule exI[of _ m])
          apply (rule exI[of _ n])
          apply (auto simp add: BENQ_diff_access simp flip: BAPPEND_BENQ)
          done
        done
      done
    have [A10_prems]: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W)))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 AC1 AC2 BD1 BD2 X Y Z W V. op1 = map_op projl projr (comp_op Some Z (aeq_op (case_sum X Y)) (acopy_op (case_sum V W))) \<and> op2 = map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum B5 D5)) (id_op BD2))))) \<and> (\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p))) op2' (map_op projl projr (comp_op Some (case_sum (case_sum A4 C4) (case_sum B4 D4)) (map_op projl projr (comp_op Some (case_sum (case_sum A2 B2) (case_sum C2 D2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum A1 B1)) (acopy_op (case_sum C1 D1))) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A3) (transp_op (case_sum B3 C3)))) (id_op D3))))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some AC1 (aeq_op (case_sum A5 C5)) (id_op AC2))) (map_op projl projr (comp_op Some BD1 (aeq_op (case_sum (BTL pc B5) (BTL pc D5))) (id_op BD2))))))"
      if "\<forall>p. \<exists>m n. (m = 0 \<or> n = 0) \<and> drop n (((((A1 >> A2) >> A3) >> A4) >> A5) p) = X p \<and> drop n (((((C1 >> C2) >> C3) >> C4) >> C5) p) = Y p \<and> drop m (((((B1 >> B2) >> B3) >> B4) >> B5) p) = X p \<and> drop m (((((D1 >> D2) >> D3) >> D4) >> D5) p) = Y p \<and> bulk_benq (tested n (((((A1 >> A2) >> A3) >> A4) >> A5) p) (((((C1 >> C2) >> C3) >> C4) >> C5) p)) ((AC1 >> AC2) p) = (Z >> V) p \<and> bulk_benq (tested m (((((B1 >> B2) >> B3) >> B4) >> B5) p) (((((D1 >> D2) >> D3) >> D4) >> D5) p)) ((BD1 >> BD2) p) = (Z >> W) p \<and> n \<le> length (((((A1 >> A2) >> A3) >> A4) >> A5) p) \<and> n \<le> length (((((C1 >> C2) >> C3) >> C4) >> C5) p) \<and> m \<le> length (((((B1 >> B2) >> B3) >> B4) >> B5) p) \<and> m \<le> length (((((D1 >> D2) >> D3) >> D4) >> D5) p)"
        and "B5 pc \<noteq> []"
        and "D5 pc \<noteq> []"
        and "BHD pc B5 \<noteq> BHD pc D5"
        and "(pc::'a) \<notin> defaults"
      for io' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                 (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) IO"
        and op'' :: "(('a + 'a) + ('a + 'a) + 'a + 'a,
                    (('a + 'a) + 'a + 'a) + 'a + 'a, 'b) op"
        and op2' :: "(('a + 'a) + 'a + 'a, 'a + 'a, 'b) op"
        and op2'a :: "('a + 'a, 'a, 'b) op"
        and io'a :: "(('a + 'a) + 'a, 'a + 'a, 'b) IO"
        and op''a :: "(('a + 'a) + 'a, 'a + 'a, 'b) op"
        and op1' :: "('a + 'a, 'a, 'b) op"
        and pc :: 'a
      using that
      apply -
      apply (frule spec[of _ pc])
      apply (elim exE disjE conjE)
      subgoal for m n
        apply hypsubst_thin
        apply simp
        apply (intro exI conjI)
        apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
        apply (rule step_comp_op_L_Tau)
        apply (rule step_aeq_op_Silent)
        apply assumption
        apply simp_all
        subgoal
          by (metis BULK_BENQ_empty)
        subgoal
          by (metis BULK_BENQ_empty)
        subgoal
          by (metis (no_types, lifting) BHD_BAPPEND_2_cases BHD_def BULK_BENQ_empty self_append_conv2 suffix_take take0)
        subgoal
          apply (rule wbc_base)
          apply (intro exI conjI)
          apply (rule refl)+
          apply (intro allI)
          subgoal for pd
            apply (cases "pc = pd")
            subgoal
              apply simp
              apply (rule exI[of _ 0])
              apply (rule exI[of _ "Suc n"])
              apply (simp add: drop_Suc flip: tl_drop)
              apply (intro conjI)
              subgoal
                apply (simp add: BTL_def)
                done
              subgoal
                apply (simp add: BTL_def)
                done
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                apply (subst tested_diff_Suc_gen)
                subgoal
                  by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                subgoal
                  by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                subgoal
                  by (smt (verit) BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty drop_all hd_drop_conv_nth le_neq_implies_less)
                apply assumption
                done
              subgoal
                by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq Suc_le_eq)
              subgoal
                by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq Suc_le_eq)
              done
            subgoal
              apply (drule spec[of _ pd])
              apply (elim conjE exE)
              subgoal for m' n'
                apply (rule exI[of _ m'])
                apply (rule exI[of _ n'])
                apply simp
                apply (intro conjI)
                apply (simp_all add: BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        done
      subgoal for m n
        apply hypsubst_thin
        apply simp
        apply (cases "m")
        subgoal
          apply (intro exI conjI)
          apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
          apply (rule step_comp_op_L_Tau)
          apply (rule step_aeq_op_Silent)
          apply assumption
          apply simp_all
          subgoal
            by (metis BULK_BENQ_empty)
          subgoal
            by (metis BULK_BENQ_empty)
          subgoal
            by (metis (no_types, lifting) BHD_BAPPEND_2_cases BHD_def BULK_BENQ_empty self_append_conv2 suffix_take take0)
          subgoal
            apply (rule wbc_base)
            apply (intro exI conjI)
            apply (rule refl)+
            apply (intro allI)
            subgoal for pd
              apply (cases "pc = pd")
              subgoal
                apply simp
                apply (rule exI[of _ 0])
                apply (rule exI[of _ 1])
                apply (simp add: drop_Suc flip: tl_drop)
                apply (intro conjI)
                subgoal
                  apply (simp add: BTL_def)
                  done
                subgoal
                  apply (simp add: BTL_def)
                  done
                subgoal
                  by (metis BAPPEND_BTL BTL_access)
                subgoal
                  by (metis BAPPEND_BTL BTL_access)
                subgoal
                  apply (subst tested_diff_Suc_gen)
                  subgoal
                    by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                  subgoal
                    by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq)
                  subgoal
                    by (smt (verit) BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty drop_all hd_conv_nth hd_drop_conv_nth le_neq_implies_less)
                  apply simp
                  done
                subgoal
                  by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq Suc_le_eq)
                subgoal
                  by (metis BULK_BENQ_empty drop_eq_Nil order_le_imp_less_or_eq Suc_le_eq)
                done
              subgoal
                apply (drule spec[of _ pd])
                apply (elim conjE exE)
                subgoal for m' n'
                  apply (rule exI[of _ m'])
                  apply (rule exI[of _ n'])
                  apply simp
                  apply (intro conjI)
                  apply (simp_all add: BTL_def BULK_BENQ_def)
                  done
                done
              done
            done
          done
        subgoal for m'
          apply (intro exI conjI)
          apply (rule rtranclp.intros(1))
          apply (rule wbc_base)
          apply (intro exI conjI)
          apply (rule refl)+
          apply (intro allI)
          subgoal for pd
            apply (cases "pc = pd")
            subgoal
              apply simp
              apply (rule exI[of _ "m'"])
              apply (rule exI[of _ 0])
              apply (simp add: drop_Suc)
              apply (intro conjI)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                by (metis BAPPEND_BTL BTL_access)
              subgoal
                apply (subst (asm) tested_diff_Suc)
                apply simp_all
                apply (metis BHD_def BULK_BENQ_bulk_benq hd_append2)
                apply (metis BAPPEND_BTL BTL_access)
                done
              subgoal
                by (metis BAPPEND_BTL BTL_access BULK_BENQ_empty Nitpick.size_list_simp(2) not_less_eq_eq)
              subgoal
                by (metis BAPPEND_BTL BTL_access BULK_BENQ_empty Nitpick.size_list_simp(2) not_less_eq_eq)
              done
            subgoal
              apply (drule spec[of _ pd])
              apply (elim conjE exE)
              subgoal for m'' n'
                apply (rule exI[of _ m''])
                apply (rule exI[of _ n'])
                apply simp
                apply (intro conjI)
                apply (simp_all add: BTL_def BULK_BENQ_def)
                done
              done
            done
          done
        done
      done
    show ?thesis
        using SIM2 apply -
        apply (elim exE conjE step_acopy_op_elim step_aeq_op_elim step_comp_op_elim step_map_op_elim step_transp_op_cases step_id_op_cases ; simp only: IO.simps ; simp split: sum.splits if_splits; hypsubst_thin?)
        apply (rule A10_prems; assumption)+
        done
  qed
qed

lemma A10:
  "\<Q> \<bullet> \<C> \<approx> (\<C> \<parallel> \<C>) \<bullet> (map_op reassoc reassoc (map_op assoc assoc (\<I> \<parallel> \<X>) \<parallel> \<I>)) \<bullet> (\<Q>\<turnstile> \<parallel> \<Q>\<turnstile>)"
  unfolding scomp_op_def pcomp_op_def
  apply (rule A10_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []", simplified])
  done


end