theory B7

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)


section \<open>Axiom B7: Transpose of transpose is identity\<close>

lemma comp_op_transp_transp_id_bufs:
  \<open>map_op projl projr (comp_op Some buf2 (transp_op buf1) (transp_op buf3))
  \<approx> id_op (buf1 >> (buf2 >> buf3 \<circ> case_sum Inr Inl))\<close>
  apply (coinduction arbitrary: buf1 buf2 buf3 rule: wbisim_coinduct_upto)
  subgoal for buf1 buf2 buf3
    unfolding wsim_def
    apply auto
    subgoal for io
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (erule step_transp_op_Inp)
         apply simp
        apply (rule exI[of _ \<open>id_op ((BENQ p x buf1) >> (buf2 >> buf3 \<circ> case_sum Inr Inl))\<close>])
        apply auto
        done
      subgoal for p x
        apply (erule step_transp_op_Out)
          apply simp_all
        apply (intro exI conjI[rotated])
         apply (rule wbc_base)
         apply fast
        apply (cases p)
        subgoal for lp
          apply (rule step_wstep)
          apply auto
           apply (metis BHD_BULK_BENQ_cases BULK_BENQ_empty case_sum_BHD_L case_sum_BHD_R case_sum_Inl_Inr_L o_case_sum)
          apply (simp add: BULK_BENQ_BTL_right_not_empty_case_sum)
          done
        subgoal for rp
          apply (rule step_wstep)
          apply auto
           apply (metis BHD_BULK_BENQ_cases BULK_BENQ_empty case_sum_BHD_L case_sum_BHD_R case_sum_expand_Inr_pointfree o_case_sum)
          apply (simp add: BULK_BENQ_BTL_right_not_empty_case_sum)
          done
        done
      subgoal for p x
        apply (erule step_transp_op_Out)
          apply simp_all
        apply (rule exI[of _ \<open>id_op (buf1 >> (buf2 >> buf3 \<circ> case_sum Inr Inl))\<close>])
        apply simp
        apply (rule wbc_base)
        apply (rule exI[of _ \<open>BTL (case_sum Inr Inl p) buf1\<close>])
        apply (rule exI[of _ \<open>BENQ p x buf2\<close>])
        apply (rule exI[of _ buf3])
        apply auto
        using BAPPEND_BENQ_BHD[of _ \<open>case_sum Inr Inl p\<close> \<open>buf2 >> buf3 \<circ> case_sum Inr Inl\<close>]
        apply (simp add: BENQ_case_sum_compose)
        done
      subgoal for p
        apply (erule step_transp_op_Inp)
         apply simp
        apply (rule exI[of _ \<open>id_op (buf1 >> (buf2 >> buf3 \<circ> case_sum Inr Inl))\<close>])
        apply simp
        apply (rule wbc_base)
        apply fastforce
        done
       apply (rule no_step_transp_op_Tau, simp_all)+
      done
    subgoal for io
      apply (erule step_id_op_cases)
      subgoal for p x
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some buf2 (transp_op (BENQ p x buf1)) (transp_op buf3))\<close>])
        apply auto
        apply blast
        done
      subgoal for p x
        apply hypsubst_thin
        apply (drule BHD_BULK_BENQ_cases)
         apply (auto simp del: BULK_BENQ_empty)
        subgoal
          apply (drule BHD_BULK_BENQ_cases)
           apply auto
          subgoal
            apply (rule exI[of _ \<open>map_op projl projr (comp_op Some buf2 (transp_op buf1) (transp_op (BTL (case_sum Inr Inl p) buf3)))\<close>])
            apply (rule conjI[rotated])
            subgoal
              apply (rule wbc_sym)
              apply (rule wbc_base)
              apply (rule exI)
              apply (rule exI)
              apply (rule exI[of _ \<open>BTL (case_sum Inr Inl p) buf3\<close>])
              apply (auto simp: BULK_BENQ_BTL_right_not_empty_case_sum)
              done
            subgoal
              apply (simp split: sum.splits)
              subgoal
                apply (rule step_wstep)
                apply auto
                apply (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty comp_eq_dest_lhs old.sum.simps(5))
                done
              subgoal
                apply (rule step_wstep)
                apply auto
                apply (metis BHD_BULK_BENQ_right_not_empty BHD_def comp_apply old.sum.simps(6))
                done
              done
            done
          subgoal
            apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (BTL (case_sum Inr Inl p) buf2) (transp_op buf1) (transp_op buf3))\<close>])
            apply (rule conjI[rotated])
            subgoal
              apply (rule wbc_sym)
              apply (rule wbc_base)
              apply (rule exI)
              apply (rule exI[of _ \<open>BTL (case_sum Inr Inl p) buf2\<close>])
              apply (rule exI)
              using BTL_case_sum_compose[of \<open>case_sum Inr Inl p\<close> \<open>buf2 >> buf3\<close>]
              apply (simp split: sum.splits)
              done
            subgoal
              apply (cases p)
              subgoal for lp
                apply simp
                apply (rule step_tau_step_io_wstep)
                 apply (rule step_map_op[of Tau])
                  apply (rule step_Tau_comp_op_R[where p="Inr lp"])
                       apply (rule step_transp_op_Read)
                        apply simp_all
                apply (rule step_map_op[of "Out (Inr (Inl lp)) _"])
                 apply (rule step_comp_op_R_Out)
                   apply (rule step_transp_op_Write[where p="Inr lp"])
                       apply simp_all
                apply (simp add: BHD_def)
                done
              subgoal for rp
                apply simp
                apply (rule step_tau_step_io_wstep)
                 apply (rule step_map_op[of Tau])
                  apply (rule step_Tau_comp_op_R[where p="Inl rp"])
                       apply (rule step_transp_op_Read)
                        apply simp_all
                apply (rule step_map_op[of "Out (Inr (Inr rp)) _"])
                 apply (rule step_comp_op_R_Out)
                   apply simp_all
                apply (rule step_transp_op_Write[where p="Inl rp"])
                    apply simp_all
                apply (simp add: BHD_def)
                done
              done
            done
          done
        subgoal
          apply (cases p)
          subgoal for lp
            apply simp
            apply (intro conjI[rotated] exI)
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply (rule exI)
             apply blast
            apply (rule step_tau_step_tau_step_io_wstep)
              apply (rule step_map_op[of Tau])
               apply simp_all
              apply (rule step_Tau_comp_op_L[where p="Inr lp"])
                 apply simp_all
              apply (rule step_transp_op_Write)
                  apply simp_all
              apply simp_all
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_comp_op_R[where p="Inr lp"])
                  apply simp_all
             apply (rule step_transp_op_Read)
              apply simp_all
            apply (rule step_map_op[of "Out (Inr (Inl lp)) _"])
             apply simp_all
            apply (rule step_comp_op_R_Out)
              apply simp_all
            apply auto
            done
          subgoal for rp
            apply simp
            apply (intro conjI[rotated] exI)
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply (rule exI)
             apply blast
            apply (rule step_tau_step_tau_step_io_wstep)
              apply (rule step_map_op[of Tau])
               apply simp_all
              apply (rule step_Tau_comp_op_L)
                 apply force
                apply simp_all
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_comp_op_R[where p="Inl rp"])
                  apply auto
                apply simp_all
            apply auto
            done
          done
        done
      done
    done
  done

lemma B7:
  \<open>\<X> \<bullet> \<X> \<approx> \<I>\<close>
  using comp_op_transp_transp_id_bufs[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  unfolding scomp_op_def
  by (auto simp: o_def)


end