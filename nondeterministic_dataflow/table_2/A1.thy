theory A1

imports
  "../BNA_Operators"
  "HOL-ex.Sketch_and_Explore"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A1: Equality test commutes with identity\<close>

lemma test_all_buffers_B1:
  assumes \<open>p \<notin> defaults\<close>
    and \<open>n = min (length (B1' p)) (length (B1 p))\<close>
  shows  \<open>(step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2)
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1)))
    (aeq_op (case_sum B3'' B3)))))
   (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' (B2(p := B2 p @ tested n (B1' p) (B1 p))))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum (B1'(p := drop n (B1' p))) (B1(p := drop n (B1 p))))))
    (aeq_op (case_sum B3'' B3)))))\<close>
  using assms proof (induct n arbitrary: B1' B1 B2 rule: less_induct)
  case (less n)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis   using rtranclp.rtrancl_refl by force
  next
    case (Suc n')
    from this less show ?thesis 
      apply -
      apply simp
      apply (cases "BHD p B1' = None")
      subgoal
        apply (rule converse_rtranclp_into_rtranclp)
         apply (rule step_map_op[of Tau])
          apply (rule step_map_op[of Tau])
           apply simp_all
         apply (rule step_Tau_comp_op_L)
            apply (rule step_comp_op_R_Out)
              apply (rule step_aeq_op_Write[where  x="BHD p B1'"])
                  apply (rule assms(1))
                 apply simp_all
          apply force
         apply force
        apply (drule meta_spec[of _ n'])
        apply (drule meta_spec[of _ "BTL p B1'"])
        apply (drule meta_spec[of _ "BTL p B1"])
        apply simp
        apply (drule meta_spec[of _ "BENQ p None B2"])
        apply (drule meta_mp)
         apply (simp add: BTL_access min_diff)
        apply simp
        apply (smt (verit) BENQ_def BHD_def BTL_access BTL_def One_nat_def diff_Suc_1' drop_Suc drop_eq_Nil fun_upd_upd length_0_conv length_greater_0_conv length_tl min.absorb2 min.absorb3 min.cobounded1 min_def nat.discI tested_diff_Suc tested_eq_Suc)
        done
      subgoal
        apply (cases "BHD p B1' = BHD p B1")
        subgoal
          apply (rule converse_rtranclp_into_rtranclp)
           apply (rule step_map_op[of Tau])
            apply (rule step_map_op[of Tau])
             apply simp_all
           apply (rule step_Tau_comp_op_L)
              apply (rule step_comp_op_R_Out)
                apply (rule step_aeq_op_Write[where  x="BHD p B1'"])
                    apply (rule assms(1))
                   apply simp_all
            apply force
           apply force
          apply (drule meta_spec[of _ n'])
          apply (drule meta_spec[of _ "BTL p B1'"])
          apply (drule meta_spec[of _ "BTL p B1"])
          apply simp
          apply (drule meta_spec[of _ "BENQ p (BHD p B1) B2"])
          apply (drule meta_mp)
           apply (simp add: BTL_access min_diff)
          apply simp
          apply (smt (verit) BENQ_def BHD_def BTL_access BTL_def One_nat_def diff_Suc_1' drop_Suc drop_eq_Nil fun_upd_upd length_0_conv length_greater_0_conv length_tl min.absorb2 min.absorb3 min.cobounded1 min_def nat.discI tested_eq_Suc)
          done
        subgoal
          apply simp
          apply (elim exE)
          subgoal for y
            apply (rule converse_rtranclp_into_rtranclp)
             apply (rule step_map_op[of Tau])
              apply (rule step_map_op[of Tau])
               apply simp_all
             apply (rule step_Tau_comp_op_L)
                apply (rule step_comp_op_R_Out)
                  apply (rule step_aeq_op_Write[where  x=None])
                      apply (rule assms(1))
                     apply simp_all
              apply force
             apply force
            apply (drule meta_spec[of _ n'])
            apply (drule meta_spec[of _ "BTL p B1'"])
            apply (drule meta_spec[of _ "BTL p B1"])
            apply simp
            apply (drule meta_spec[of _ "BENQ p None B2"])
            apply (drule meta_mp)
             apply (simp add: BTL_access min_diff)
            apply simp
            apply (smt (z3) BENQ_def BHD_def BTL_access BTL_def One_nat_def diff_Suc_1' drop_Suc drop_eq_Nil fun_upd_upd length_0_conv length_tl min.absorb2 min.cobounded1 min_0R min_def nat.discI tested_diff_Suc)
            done
          done
        done
      done
  qed
qed

lemma progress_buffers1_non_testing:
  assumes \<open>p \<notin> defaults\<close>
    and \<open>n = min (length (B1' p)) (length (B1 p))\<close>
  shows \<open>(step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2)
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1)))
    (aeq_op (case_sum B3'' B3)))))
   (map_op assoc id (map_op projl projr (comp_op Some (case_sum (B2''(p := [])) (B2(p := [])))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (B1''(p := []))) (aeq_op (case_sum B1' B1)))
    (aeq_op (case_sum (B3''(p := (B1'' >> B2'' >> B3'') p)) (B3(p := ((B2 >> B3) p))))))))\<close>
proof -
  have \<open>(step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2)
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1)))
    (aeq_op (case_sum B3'' B3)))))
   (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' (B2(p := [])))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1)))
    (aeq_op (case_sum B3'' (B3(p := ((B2 >> B3) p))))))))\<close>
    using assms proof (induct "B2 p" arbitrary: B3 B2)
    case Nil
    then show ?case 
      using rtranclp.rtrancl_refl by (simp add: fun_upd_idem)
  next
    case (Cons a x)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)+
         apply (rule step_Tau_comp_op_R)
              apply (rule step_aeq_op_Read_R)
               apply assumption
              apply simp_all
       apply force
      apply (smt (verit) BAPPEND_BENQ_BHD BENQ_def BTL_access BTL_def fun_upd_upd list.discI list.sel(3))
      done
  qed
  also have \<open>(step Tau)\<^sup>*\<^sup>* \<dots>
   (map_op assoc id (map_op projl projr (comp_op Some (case_sum (B2''(p := ((B1'' >> B2'') p))) (B2(p := [])))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (B1''(p := []))) (aeq_op (case_sum B1' B1)))
    (aeq_op (case_sum B3'' (B3(p := ((B2 >> B3) p))))))))\<close>
    using assms proof (induct "B1'' p" arbitrary: B2'' B1'')
    case Nil
    then show ?case 
      using rtranclp.rtrancl_refl by (simp add: fun_upd_idem)
  next
    case (Cons a x)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)+
         apply simp_all
       apply (rule step_Tau_comp_op_L)
          apply (rule step_comp_op_L_Out)
             apply force
            apply force
           apply simp_all
      apply (smt (verit, ccfv_threshold) BAPPEND_BENQ_BHD BENQ_def BTL_access BTL_def case_sum_BENQ_L fun_upd_upd length_0_conv length_Cons list.sel(3) nat.discI)
      done
  qed
  also (rtranclp_trans) have \<open>(step Tau)\<^sup>*\<^sup>* \<dots>
   (map_op assoc id (map_op projl projr (comp_op Some (case_sum (B2''(p := [])) (B2(p := [])))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (B1''(p := []))) (aeq_op (case_sum B1' B1)))
    (aeq_op (case_sum (B3''(p := ((B1'' >> B2'' >> B3'') p))) (B3(p := ((B2 >> B3) p))))))))\<close>
    using assms proof (induct "(B1'' >> B2'') p" arbitrary: B3'' B2'' B1'')
    case Nil
    then show ?case 
      using rtranclp.rtrancl_refl by (simp add: fun_upd_idem)
  next
    case (Cons a x)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)+
         apply simp_all
       apply (rule step_Tau_comp_op_R)
            apply (rule step_aeq_op_Read_L)
             apply simp_all
       apply force
      apply (cases "B2'' p")
      subgoal
        apply simp
        apply (smt (verit) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def Cons.hyps(2) fun_upd_same fun_upd_upd list.discI list.sel(3))
        done
      subgoal
        by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def BULK_BENQ_empty \<open>\<lbrakk>\<And>B1'' B2'' B3''. x = (B1'' >> B2'') p \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum (B2''(p := (B1'' >> B2'') p)) (B2(p := []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (B1''(p := []))) (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' (B3(p := (B2 >> B3) p))))))) (map_op assoc id (map_op projl projr (comp_op Some (case_sum (B2''(p := [])) (B2(p := []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (B1''(p := []))) (aeq_op (case_sum B1' B1))) (aeq_op (case_sum (B3''(p := ((B1'' >> B2'') >> B3'') p)) (B3(p := (B2 >> B3) p))))))); a # x = (B1'' >> B2'') p; p \<notin> defaults; n = min (length (B1' p)) (length (B1 p)); B2'' p = []\<rbrakk> \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum (BTL p (B2''(p := (B1'' >> B2'') p))) (B2(p := []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (B1''(p := []))) (aeq_op (case_sum B1' B1))) (aeq_op (case_sum (BENQ p (BHD p (B2''(p := (B1'' >> B2'') p))) B3'') (B3(p := (B2 >> B3) p))))))) (map_op assoc id (map_op projl projr (comp_op Some (case_sum (B2''(p := [])) (B2(p := []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (B1''(p := []))) (aeq_op (case_sum B1' B1))) (aeq_op (case_sum (B3''(p := ((B1'' >> B2'') >> B3'') p)) (B3(p := (B2 >> B3) p)))))))\<close> fun_upd_same fun_upd_upd list.sel(3))
      done
  qed
  ultimately show ?thesis
    by auto
qed

lemma progress_buffers1:
  assumes \<open>p \<notin> defaults\<close>
    and \<open>n = min (length (B1' p)) (length (B1 p))\<close>
  shows \<open>(step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2)
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1)))
    (aeq_op (case_sum B3'' B3)))))
   (map_op assoc id (map_op projl projr (comp_op Some (case_sum (B2''(p := [])) (B2(p := [])))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (B1''(p := []))) (aeq_op (case_sum (B1'(p := drop n (B1' p))) (B1(p := drop n (B1 p))))))
    (aeq_op (case_sum (B3''(p := (B1'' >> B2'' >> B3'') p)) (B3(p := ((B2 >> B3) p) @ tested n (B1' p) (B1 p))))))))\<close>
  using assms apply -
  apply (rule rtranclp_trans)
   apply (rule test_all_buffers_B1)
    apply assumption+
  apply (rule rtranclp_trans)
   apply (rule progress_buffers1_non_testing)
    apply assumption+
   apply auto[1]
  apply simp
  apply (simp add: BULK_BENQ_def)
  done

lemma test_all_buffers_A1:
  assumes \<open>p \<notin> defaults\<close>
    and \<open>n = min (length (A1'' p)) (length (A1' p))\<close>
  shows \<open>(step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum A2' A2)
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1))
    (aeq_op (case_sum A3' A3))))
  (map_op projl projr (comp_op Some (case_sum (A2'(p := (A2' p) @ tested n (A1'' p) (A1' p))) A2)
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (A1''(p := drop n (A1'' p))) (A1'(p := drop n (A1' p))))) (id_op A1))
    (aeq_op (case_sum A3' A3))))\<close>
  using assms proof (induct n arbitrary: A1'' A1' A2' rule: less_induct)
  case (less n)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis   using rtranclp.rtrancl_refl by force
  next
    case (Suc n')
    from this less show ?thesis 
      apply -
      apply simp
      apply (cases "BHD p A1'' = None")
      subgoal
        apply (rule converse_rtranclp_into_rtranclp)
         apply (rule step_map_op[of Tau])
          apply simp_all
         apply (rule step_Tau_comp_op_L)
            apply (rule step_comp_op_L_Out)
               apply (rule step_aeq_op_Write[where  x="BHD p A1''"])
                   apply (rule assms(1))
                  apply simp_all
          apply force
         apply force
        apply (drule meta_spec[of _ n'])
        apply (drule meta_spec[of _ "BTL p A1''"])
        apply (drule meta_spec[of _ "BTL p A1'"])
        apply simp
        apply (drule meta_spec[of _ "BENQ p None A2'"])
        apply (drule meta_mp)
         apply (simp add: BTL_access min_diff)
        apply simp
        apply (smt (verit) BENQ_def BHD_def BTL_access BTL_def One_nat_def diff_Suc_1' drop_Suc drop_eq_Nil fun_upd_upd length_0_conv length_greater_0_conv length_tl min.absorb2 min.absorb3 min.cobounded1 min_def nat.discI tested_diff_Suc tested_eq_Suc)
        done
      subgoal
        apply (cases "BHD p A1'' = BHD p A1'")
        subgoal
          apply (rule converse_rtranclp_into_rtranclp)
           apply (rule step_map_op[of Tau])
            apply simp_all
           apply (rule step_Tau_comp_op_L)
              apply (rule step_comp_op_L_Out)
                 apply (rule step_aeq_op_Write[where  x="BHD p A1''"])
                     apply (rule assms(1))
                    apply simp_all
            apply force
           apply force
          apply (drule meta_spec[of _ n'])
          apply (drule meta_spec[of _ "BTL p A1''"])
          apply (drule meta_spec[of _ "BTL p A1'"])
          apply simp
          apply (drule meta_spec[of _ "BENQ p (BHD p A1'') A2'"])
          apply (drule meta_mp)
           apply (simp add: BTL_access min_diff)
          apply (smt (verit) BENQ_access BENQ_def BHD_def BTL_access BTL_def One_nat_def append.assoc append.simps(2) diff_Suc_1' drop_Suc drop_eq_Nil fun_upd_upd length_greater_0_conv length_tl list.size(3) min.absorb2 min.absorb3 min.cobounded1 min_def nat.discI self_append_conv2 tested_eq_Suc)
          done
        subgoal
          apply simp
          apply (elim exE)
          subgoal for y
            apply (rule converse_rtranclp_into_rtranclp)
             apply (rule step_map_op[of Tau])
              apply (rule step_Tau_comp_op_L)
                 apply (rule step_comp_op_L_Out)
                    apply (rule step_aeq_op_Write[where  x=None])
                        apply (rule assms(1))
                       apply simp_all
              apply force
             apply force
            apply (drule meta_spec[of _ n'])
            apply (drule meta_spec[of _ "BTL p A1''"])
            apply (drule meta_spec[of _ "BTL p A1'"])
            apply simp
            apply (drule meta_spec[of _ "BENQ p None A2'"])
            apply (drule meta_mp)
             apply (simp add: BTL_access min_diff)
            apply simp
            apply (smt (z3) BENQ_def BHD_def BTL_access BTL_def One_nat_def diff_Suc_1' drop_Suc drop_eq_Nil fun_upd_upd length_0_conv length_tl min.absorb2 min.cobounded1 min_0R min_def nat.discI tested_diff_Suc)
            done
          done
        done
      done
  qed
qed

lemma progress_buffers2_non_testing:
  assumes \<open>p \<notin> defaults\<close>
  shows \<open>(step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum A2' A2)
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1))
    (aeq_op (case_sum A3' A3))))
  (map_op projl projr (comp_op Some (case_sum (A2'(p := [])) (A2(p := [])))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op (A1(p := []))))
    (aeq_op (case_sum (A3'(p := ((A2' >> A3') p))) (A3(p := (A1 >> A2 >> A3) p))))))\<close>
proof -
  have \<open>(step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum A2' A2)
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1))
    (aeq_op (case_sum A3' A3))))
  (map_op projl projr (comp_op Some (case_sum (A2'(p := [])) A2)
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1))
    (aeq_op (case_sum (A3'(p := ((A2' >> A3') p))) A3))))\<close>
    using assms proof (induct "A2' p" arbitrary: A3' A2')
    case Nil
    then show ?case 
      using rtranclp.rtrancl_refl by (simp add: fun_upd_idem)
  next
    case (Cons a x)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)+
        apply (rule step_Tau_comp_op_R)
             apply (rule step_aeq_op_Read_L)
              apply assumption
             apply simp_all
       apply force
      apply (smt (verit) BAPPEND_BENQ_BHD BENQ_def BTL_access BTL_def fun_upd_upd list.discI list.sel(3))
      done
  qed
  also have \<open>(step Tau)\<^sup>*\<^sup>* \<dots>
  (map_op projl projr (comp_op Some (case_sum (A2'(p := [])) (A2(p := ((A1 >> A2) p))))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op (A1(p := []))))
    (aeq_op (case_sum (A3'(p := ((A2' >> A3') p))) A3))))\<close>
    using assms proof (induct "A1 p" arbitrary: A1 A2)
    case Nil
    then show ?case 
      using rtranclp.rtrancl_refl by (simp add: fun_upd_idem)
  next
    case (Cons a x)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)+
        apply simp_all
       apply (rule step_Tau_comp_op_L)
          apply (rule step_comp_op_R_Out)
            apply force
           apply force
          apply simp_all
      apply (smt (verit, del_insts) BAPPEND_BENQ_BHD BENQ_def BTL_access BTL_def case_sum_BENQ_R fun_upd_upd list.discI list.sel(3))
      done
  qed
  also (rtranclp_trans) have \<open>(step Tau)\<^sup>*\<^sup>* \<dots>
  (map_op projl projr (comp_op Some (case_sum (A2'(p := [])) (A2(p := [])))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op (A1(p := []))))
    (aeq_op (case_sum (A3'(p := ((A2' >> A3') p))) (A3(p := ((A1 >> A2 >> A3) p)))))))\<close>
    using assms proof (induct "(A1 >> A2) p" arbitrary: A1 A2 A3)
    case Nil
    then show ?case 
      using rtranclp.rtrancl_refl by (simp add: fun_upd_idem)
  next
    case (Cons a x)
    then show ?case 
      apply -
      apply (rule rtranclp_trans)
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)+
        apply simp_all
       apply (rule step_Tau_comp_op_R)
            apply (rule step_aeq_op_Read_R)
             apply simp_all
       apply force
      apply (cases "A2 p")
      subgoal
        apply simp
        apply (smt (verit) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def Cons.hyps(2) fun_upd_same fun_upd_upd list.discI list.sel(3))
        done
      subgoal
        by (smt (z3) BAPPEND_BENQ_BHD BAPPEND_BTL BENQ_def BHD_def BTL_def BULK_BENQ_assoc BULK_BENQ_def \<open>\<lbrakk>\<And>A1 A2 A3. x = (A1 >> A2) p \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (A2'(p := [])) (A2(p := (A1 >> A2) p))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op (A1(p := [])))) (aeq_op (case_sum (A3'(p := (A2' >> A3') p)) A3)))) (map_op projl projr (comp_op Some (case_sum (A2'(p := [])) (A2(p := []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op (A1(p := [])))) (aeq_op (case_sum (A3'(p := (A2' >> A3') p)) (A3(p := ((A1 >> A2) >> A3) p)))))); a # x = (A1 >> A2) p; p \<notin> defaults; A2 p = []\<rbrakk> \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum (A2'(p := [])) (BTL p (A2(p := (A1 >> A2) p)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op (A1(p := [])))) (aeq_op (case_sum (A3'(p := (A2' >> A3') p)) (BENQ p (BHD p (A2(p := (A1 >> A2) p))) A3))))) (map_op projl projr (comp_op Some (case_sum (A2'(p := [])) (A2(p := []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op (A1(p := [])))) (aeq_op (case_sum (A3'(p := (A2' >> A3') p)) (A3(p := ((A1 >> A2) >> A3) p))))))\<close> fun_upd_same fun_upd_upd hd_append2 list.sel(3))
      done
  qed
  ultimately show ?thesis
    by auto
qed

lemma progress_buffers2:
  assumes \<open>p \<notin> defaults\<close>
    and \<open>n = min (length (A1'' p)) (length (A1' p))\<close>
  shows \<open>(step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (case_sum A2' A2)
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1))
    (aeq_op (case_sum A3' A3))))
  (map_op projl projr (comp_op Some (case_sum (A2'(p := [])) (A2(p := [])))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (A1''(p := drop n (A1'' p))) (A1'(p := drop n (A1' p))))) (id_op (A1(p := []))))
    (aeq_op (case_sum (A3'(p := ((A2' >> A3') p) @ tested n (A1'' p) (A1' p))) (A3(p := (A1 >> A2 >> A3) p))))))\<close>
  using assms apply -
  apply (rule rtranclp_trans)
   apply (rule test_all_buffers_A1)
    apply assumption+
  apply (rule rtranclp_trans)
   apply (rule progress_buffers2_non_testing)
   apply assumption+
  apply auto[1]
  apply (simp add: BULK_BENQ_def)
  done

lemma tested_Cons_cases:
  "tested n xs ys = z # zs \<Longrightarrow>
  n > 0 \<and> xs \<noteq> [] \<and> ys \<noteq> [] \<and> tested (n - 1) (tl xs) (tl ys) = zs \<and> (hd xs = hd ys \<and> hd xs = z \<or> (hd xs \<noteq> hd ys \<and> z = None))"
  apply (induct n arbitrary: xs ys)
   apply (simp add: tested_def)
  subgoal for n xs ys
    apply (cases xs; cases ys; simp)
      apply (simp add: tested_def)
      apply (simp add: tested_def)
    apply (simp add: tested_def)
    subgoal for x xs y ys
      apply hypsubst_thin
      apply (cases "x = y"; simp)
       apply (simp_all add: tested_eq_Suc tested_diff_Suc)
      done
    done
  done

lemma tested_Suc:
  \<open>xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> z = (if hd xs = hd ys then hd xs else None) \<Longrightarrow> k = Suc n \<Longrightarrow> tested k xs ys = z # tested n (tl xs) (tl ys)\<close>
  unfolding tested_def by (simp add: take_Suc)

lemma A1_gen:
  assumes \<open>A = A1 >> A2 >> A3\<close>
    and \<open>B'' = B1'' >> B2'' >> B3''\<close>
    and \<open>\<forall>p. \<exists>m n C. A1'' p = drop n (B'' p) \<and> A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (A p)
  \<and> (A2' >> A3') p = tested n (C p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C p)
  \<and> n \<le> length (C p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C p) \<and> m \<le> length (A p)\<close>
  shows \<open>map_op projl projr (comp_op Some (case_sum A2' A2)
  (aeq_op (case_sum A1'' A1') \<parallel> id_op A1)
  (aeq_op (case_sum A3' A3)))
  \<approx> map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2)
    (id_op B1'' \<parallel> aeq_op (case_sum B1' B1))
    (aeq_op (case_sum B3'' B3))))\<close>
  unfolding pcomp_op_def
using assms proof (coinduction arbitrary: A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3' B3 B3'' rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp (Inl (Inl pb)) y) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ pb y A1'') A1')) (id_op A1)) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "pb \<notin> defaults"
      for pb :: 'a
        and y :: "'b option"
      using that
      apply -
      apply (drule spec[of _ pb])
      apply (elim conjE exE)
      subgoal for m n C
        apply (intro exI conjI)
         apply fastforce
        apply (rule wbc_base)
        apply (intro exI conjI)
            apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases \<open>p = pb\<close>)
          subgoal
            apply hypsubst_thin
            apply (rule exI[of _ m])
            apply (rule exI[of _ n])
            apply (intro conjI)
             apply (simp add: BULK_BENQ_bulk_benq)
            apply (rule exI[of _ C])
            apply (intro conjI)
                    apply (simp_all add: BULK_BENQ_bulk_benq tested_def)
            done
          subgoal
            using that(1) apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n' C'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply simp
              apply (intro conjI)
               apply (simp add: BENQ_def BULK_BENQ_bulk_benq)
              apply (rule exI[of _ C'])
              apply (intro conjI)
                    apply (simp_all add: BENQ_def BULK_BENQ_bulk_benq)
              done
            done
          done
        done
      done
    moreover have "\<exists>op2'. wstep (Inp (Inl (Inr pb)) y) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' (BENQ pb y A1'))) (id_op A1)) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "pb \<notin> defaults"
      for pb :: 'a
        and y :: "'b option"
      using that
      apply -
      apply (drule spec[of _ pb])
      apply (elim conjE exE)
      subgoal for m n C
        apply (intro exI conjI)
         apply (rule step_wstep)
         apply (rule step_map_op[of \<open>Inp (Inr (Inl pb)) y\<close>])
          apply (rule step_map_op[of \<open>Inp (Inl (Inr (Inl pb))) y\<close>])
           apply fastforce
          apply simp+
        apply (rule wbc_base)
        apply (intro exI conjI)
            apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases \<open>p = pb\<close>)
          subgoal
            apply hypsubst_thin
            apply (rule exI[of _ m])
            apply (rule exI[of _ n])
            apply (intro conjI)
             apply (simp add: BULK_BENQ_bulk_benq)
            apply (rule exI[of _ \<open>BENQ pb y C\<close>])
            apply (intro conjI)
                    apply (simp_all add: tested_def)
            done
          subgoal
            using that(1) apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n' C'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply simp
              apply (rule exI[of _ C'])
              apply (intro conjI)
                    apply (simp_all add: BENQ_def BULK_BENQ_bulk_benq)
              done
            done
          done
        done
      done
    moreover have "\<exists>op2'. wstep (Inp (Inr pb) xb) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op (BENQ pb xb A1))) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "pb \<notin> defaults"
      for pb :: 'a
        and xb :: "'b option"
      using that
      apply -
      apply (drule spec[of _ pb])
      apply (elim conjE exE)
      subgoal for m n C
        apply (intro exI conjI)
         apply (rule step_wstep)
         apply (rule step_map_op[of \<open>Inp (Inr (Inr pb)) xb\<close>])
          apply (rule step_map_op[of \<open>Inp (Inl (Inr (Inr pb))) xb\<close>])
           apply fastforce
          apply simp+
        apply (rule wbc_base)
        apply (intro exI conjI)
            apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases \<open>p = pb\<close>)
          subgoal
            apply hypsubst_thin
            apply (rule exI[of _ m])
            apply (rule exI[of _ n])
            apply (intro conjI)
             apply (simp add: BULK_BENQ_bulk_benq)
            apply (rule exI[of _ C])
            apply (intro conjI)
                    apply (simp_all add: BULK_BENQ_bulk_benq tested_def)
            done
          subgoal
            using that(1) apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n' C'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply simp
               apply (simp add: BENQ_def BULK_BENQ_bulk_benq)
              apply (rule exI[of _ C'])
              apply (intro conjI)
                    apply (simp_all add: BENQ_def BULK_BENQ_bulk_benq)
              done
            done
          done
        done
      done
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa A3)) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum (BTL pa A3') (BTL pa A3))))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A3' pa \<noteq> []"
        and "A3 pa \<noteq> []"
        and "pa \<notin> defaults"
        and "BHD pa A3' = BHD pa A3"
      for pa :: 'a
      using that
      apply -
      apply (drule spec[of _ pa])
      apply (elim conjE exE)
      subgoal for m n C
        apply (intro exI conjI)
         apply (rule wstep_trans(1))
          apply (rule progress_buffers1)
           apply assumption
          apply blast
         apply (rule step_map_op[of \<open>Out pa (BHD pa A3)\<close>])
          apply (rule step_map_op[of \<open>Out (Inr pa) (BHD pa A3)\<close>])
           apply (rule step_comp_op_R_Out)
             apply (rule step_aeq_op_Write)
                 apply simp_all
           apply fastforce
          apply (rule impI)
          apply (drule tested_empty)
            apply simp_all
          apply (metis BULK_BENQ_empty length_0_conv length_tested_0 min_0R min_def nat_le_linear tested_empty)
         apply auto[1]
        apply (smt (verit, ccfv_threshold) BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty fun_upd_same le_SucE le_zero_eq length_tested_0 list.sel(1) list.size(3) option.simps(3) tested_Suc zero_induct)
        subgoal
    using tested_Cons_cases[where n=n and xs="C pa" and ys="((B1'' >> B2'') >> B3'') pa" and z="BHD pa A3'" and zs="tl ((A2' >> A3') pa)"] apply -
          apply (drule meta_mp)
           apply (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty list.collapse)
          apply (elim disjE conjE)
    subgoal
      apply (simp flip: length_drop)
      apply (subst tested_min_drop[symmetric])
         apply (rule refl)+
      apply (rule tested_comm)
            apply (subst tested_Suc[where n="min (length (C pa)) (length (((A1 >> A2) >> A3) pa)) - 1"])
                apply simp_all
            apply (simp split: if_splits)
            apply (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty fun_upd_same list.sel(1))
      done
    apply simp
    done
        subgoal
          unfolding BHD_def
          apply (simp add: fun_upd_same flip: length_drop)
          apply (subst (2) tested_comm)
          apply (subst min.commute)
          using tested_min_drop[of \<open>drop m ((A1 >> A2 >> A3) pa)\<close> m \<open>(A1 >> A2 >> A3) pa\<close> \<open>drop m (C pa)\<close> \<open>C pa\<close> \<open>tested m ((A1 >> A2 >> A3) pa) (C pa)\<close>, symmetric]
          apply simp
          apply (subst tested_all)
          apply (smt (verit, ccfv_threshold) BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty list.collapse list.map_disc_iff tested_Cons_cases tested_all zip_eq_Nil_iff)
          done
        subgoal
          apply (rule wbc_base)
          apply (intro exI conjI)
              apply (rule refl)+
          apply (intro allI)
          subgoal for p
            apply (cases \<open>p = pa\<close>)
            subgoal
              apply hypsubst_thin
              apply (cases n)
              subgoal
                by (rule FalseE, force)
              subgoal for n'
                apply (rule exI[of _ \<open>min (length (btl (C pa))) (length (btl ((A1 >> A2 >> A3) pa)))\<close>])
                apply (rule exI[of _ n'])
                apply (intro conjI)
                 apply (metis BTL_access BULK_BENQ_left_empty drop_Suc fun_upd_same)
                apply (rule exI[of _ \<open>BTL pa C\<close>])
                apply (intro conjI)
                        apply (simp_all add: BTL_def drop_Suc)
                    apply (smt (verit, del_insts) BULK_BENQ_empty One_nat_def Suc_pred add.commute add_leD1 drop_Suc le_add_diff_inverse2 length_greater_0_conv min_add_distrib_left plus_1_eq_Suc)
                   apply (smt (verit) BULK_BENQ_bulk_benq BULK_BENQ_empty One_nat_def Suc_pred add_leD1 drop_Suc fun_upd_same le_add_diff_inverse le_add_diff_inverse2 length_greater_0_conv min_add_distrib_left min_add_distrib_right plus_1_eq_Suc tl_append2)
                  apply (smt (verit, ccfv_threshold) BULK_BENQ_bulk_benq fun_upd_same leD length_0_conv less_Suc_eq_0_disj list.sel(3) tested_diff_Suc tested_eq_Suc tl_append2)
                subgoal
                  apply (simp flip: length_drop)
                  apply (subst drop_Suc)+
                  apply (subst drop_0)+
                  apply (subst (1) tested_comm)
                  apply (subst (3) tested_comm)
                  apply (subgoal_tac \<open>btl (bulk_benq
   (tested (min (length (drop m (C pa))) (length (drop m ((A1 >> A2 >> A3) pa)))) (drop m (C pa))
     (drop m ((A1 >> A2 >> A3) pa)))
   (tested m (C pa) ((A1 >> A2 >> A3) pa))) =
  btl (tested (min (length (C pa)) (length ((A1 >> A2 >> A3) pa))) (C pa) ((A1 >> A2 >> A3) pa))\<close>)
                  subgoal
                    apply (subgoal_tac \<open>((A1 >> A2) >> A3(pa := btl (A3 pa))) pa = btl ((((A1 >> A2) >> A3) pa))\<close>)
                    subgoal
                      using tested_all_tl
                      by (metis BULK_BENQ_assoc)
                    by (metis BULK_BENQ_bulk_benq fun_upd_same tl_append2)
                  using tested_min_drop[of \<open>drop m (C pa)\<close> m \<open>C pa\<close> \<open>drop m ((A1 >> A2 >> A3) pa)\<close> \<open>(A1 >> A2 >> A3) pa\<close> \<open>tested m (C pa) ((A1 >> A2 >> A3) pa)\<close>, symmetric]
                  by simp
                by (simp add: BULK_BENQ_bulk_benq)
              done
            subgoal
              using that(1) apply -
              apply (drule spec[of _ p])
              apply (elim conjE exE)
              subgoal for m' n' C'
                apply (rule exI[of _ m'])
                apply (rule exI[of _ n'])
                apply (intro conjI)
                 apply (simp add: BTL_def BULK_BENQ_bulk_benq)
                apply (rule exI[of _ C'])
                apply (intro conjI)
                      apply (simp_all add: BTL_def BULK_BENQ_bulk_benq)
                done
              done
            done
          done
        done
      done
    moreover have "\<exists>op2'. wstep (Out pa None) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum (BTL pa A3') (BTL pa A3))))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A3' pa \<noteq> []"
        and "A3 pa \<noteq> []"
        and "pa \<notin> defaults"
        and "BHD pa A3' \<noteq> BHD pa A3"
      for pa :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' (BENQ pb (BHD pb A1) A2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op (BTL pb A1))) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "pb \<notin> defaults"
        and "A1 pb \<noteq> []"
      for pb :: 'a
      using that
      apply -
      apply (drule spec[of _ pb])
      apply (elim conjE exE)
      subgoal for m n C
        apply (intro exI conjI)
         apply fast
        apply (rule wbc_base)
        apply (intro exI conjI)
            apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases \<open>p = pb\<close>)
          subgoal
            apply hypsubst_thin
            apply (rule exI[of _ m])
            apply (rule exI[of _ n])
            apply (intro conjI)
             apply assumption
            apply (rule exI[of _ C])
              apply (intro conjI)
                    apply simp_all
            done
          subgoal
            using that(1) apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n' C'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply simp
              apply (rule exI[of _ C'])
              apply (intro conjI)
                     apply simp_all
              done
            done
          done
        done
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum (BENQ pb (BHD pb A1') A2') A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL pb A1'') (BTL pb A1'))) (id_op A1)) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A1'' pb \<noteq> []"
        and "A1' pb \<noteq> []"
        and "pb \<notin> defaults"
        and "BHD pb A1'' = BHD pb A1'"
      for pb :: 'a
      using that
      apply -
      apply (drule spec[of _ pb])
      apply (elim conjE exE)
      subgoal for m n C
        apply (intro exI conjI)
         apply fast
        apply (rule wbc_base)
        apply (intro exI conjI)
            apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases \<open>p = pb\<close>)
          subgoal
            apply hypsubst_thin
            apply (rule exI[of _ m])
            apply (rule exI[of _ \<open>Suc n\<close>])
            apply (intro conjI)
            subgoal
              by (metis BTL_access drop_Suc tl_drop)
            subgoal
            apply (rule exI[of _ C])
              apply (intro conjI)
              apply simp_all
               apply (metis BTL_access drop_Suc tl_drop)
              by (metis BAPPEND_BENQ BENQ_access BHD_def hd_drop_conv_nth le_neq_implies_less tested_eq_Suc_gen)
            done
          subgoal
            using that(1) apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n' C'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply simp
              apply (intro conjI)
              subgoal
                by (metis BTL_diff_access)
              apply (rule exI[of _ C'])
              apply (intro conjI)
              apply simp_all
               apply (metis BTL_diff_access)
              by (metis BAPPEND_BENQ BENQ_diff_access)
            done
          done
        done
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum (BENQ pb None A2') A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL pb A1'') (BTL pb A1'))) (id_op A1)) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A1'' pb \<noteq> []"
        and "A1' pb \<noteq> []"
        and "pb \<notin> defaults"
        and "BHD pb A1'' \<noteq> BHD pb A1'"
      for pb :: 'a
      using that
      apply -
      apply (drule spec[of _ pb])
      apply (elim conjE exE)
      subgoal for m n C
        apply (intro exI conjI)
         apply fast
        apply (rule wbc_base)
        apply (intro exI conjI)
            apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases \<open>p = pb\<close>)
          subgoal
            apply hypsubst_thin
            apply (rule exI[of _ m])
            apply (rule exI[of _ \<open>Suc n\<close>])
            apply (intro conjI)
            subgoal
              by (metis BTL_access drop_Suc tl_drop)
            subgoal
            apply (rule exI[of _ C])
              apply (intro conjI)
              apply simp_all
               apply (metis BTL_access drop_Suc tl_drop)
              by (metis BAPPEND_BENQ BENQ_access BHD_def hd_drop_conv_nth le_neq_implies_less tested_diff_Suc_gen)
            done
          subgoal
            using that(1) apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n' C'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply simp
              apply (intro conjI)
              subgoal
                by (metis BTL_diff_access)
              apply (rule exI[of _ C'])
              apply (intro conjI)
              apply simp_all
               apply (metis BTL_diff_access)
              by (metis BAPPEND_BENQ BENQ_diff_access)
            done
          done
        done
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum (BTL pa A2') A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum (BENQ pa (BHD pa A2') A3') A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A2' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that
      apply -
      apply (drule spec[of _ pa])
      apply (elim conjE exE)
      subgoal for m n C
        apply (intro exI conjI)
         apply fast
        apply (rule wbc_base)
        apply (intro exI conjI)
            apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases \<open>p = pa\<close>)
          subgoal
            apply hypsubst_thin
            apply (rule exI[of _ m])
            apply (rule exI[of _ n])
            apply (intro conjI)
             apply assumption
            apply (rule exI[of _ C])
              apply (intro conjI)
                    apply simp_all
            done
          subgoal
            using that(1) apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n' C'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply simp
              apply (rule exI[of _ C'])
              apply (intro conjI)
                     apply simp_all
              done
            done
          done
        done
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' (BTL pa A2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' (BENQ pa (BHD pa A2) A3))))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C. A1' p = drop n (C p) \<and> B1' p = drop m (C p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C p) \<and> n \<le> length (C p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that
      apply -
      apply (drule spec[of _ pa])
      apply (elim conjE exE)
      subgoal for m n C
        apply (intro exI conjI)
         apply fast
        apply (rule wbc_base)
        apply (intro exI conjI)
            apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases \<open>p = pa\<close>)
          subgoal
            apply hypsubst_thin
            apply (rule exI[of _ m])
            apply (rule exI[of _ n])
            apply (intro conjI)
             apply assumption
            apply (rule exI[of _ C])
              apply (intro conjI)
                    apply simp_all
              apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
            done
          subgoal
            using that(1) apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n' C'
              apply (rule exI[of _ m'])
              apply (rule exI[of _ n'])
              apply simp
              apply (rule exI[of _ C'])
              apply (intro conjI)
                     apply simp_all
                apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)+
              done
            done
          done
        done
      done
    ultimately show ?thesis
      apply -
      subgoal premises prems
        using SIM1 by (auto elim !: step_map_op_elim step_comp_op_elim step_aeq_op_elim step_id_op_cases simp add: prems)
      done
  qed
next
  case SIM2
  then show ?case sorry
qed

lemma A1:
  \<open>(\<Q> \<parallel> \<I>) \<bullet> \<Q> \<approx> map_op assoc id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>)\<close>
  unfolding scomp_op_def
  using A1_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by force

end