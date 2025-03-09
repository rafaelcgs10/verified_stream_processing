theory B9

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom B9: Transpose decomposes in parallel and sequential composition\<close>
lemma B9_gen:
  "transp_op (case_sum (buf1 >> buf1' >> buf1'') (case_sum (buf2 >> buf2' >> buf2'') (buf3 >> buf3' >> buf3''))) \<approx>
   map_op projl projr (comp_op Some (case_sum buf2' (case_sum buf1' buf3'))
   (map_op BNA_Operators.reassoc BNA_Operators.reassoc (transp_op (case_sum buf1 buf2) \<parallel> id_op buf3))
   (map_op id BNA_Operators.assoc (id_op buf2'' \<parallel> transp_op (case_sum buf1'' buf3''))))"
  apply (coinduction arbitrary: buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf3'' rule: wbisim_coinduct_upto)
  subgoal for buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf3''
    unfolding wsim_def
    apply auto
    subgoal for io op'
      apply (erule step_transp_op_cases)
      subgoal for p x
        apply (auto; hypsubst_thin?)
        apply (cases p)
        subgoal for lp
          apply hypsubst_thin
          apply (intro exI conjI[rotated])        
           apply (rule wbc_base)
           apply force
          unfolding pcomp_op_def
          using step_wstep[OF step_map_op[OF step_comp_op_L_Inp[OF step_map_op[OF step_comp_op_L_Inp]]], simplified]
          apply (metis BNA_Operators.reassoc.simps(1) Inl_in_defaults case_sum_BENQ_L step_transp_op_Read sum.sel(1))
          done
        subgoal for rp
          apply hypsubst_thin
          apply (cases rp)
          subgoal for lp
            apply hypsubst_thin
            apply (intro exI conjI[rotated])        
             apply (rule wbc_base)
             apply force
            apply (rule step_wstep)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Inp)
               apply (rule step_map_op)
            unfolding pcomp_op_def
                apply (rule step_comp_op_L_Inp)
                  apply (rule step_transp_op_Read)
                   apply auto
            done
          subgoal for rp
            apply hypsubst_thin
            apply (intro exI conjI[rotated])        
             apply (rule wbc_base)
             apply force
            apply (rule step_wstep)
            apply (rule step_map_op)
             apply simp_all
             apply (rule step_comp_op_L_Inp)
               apply (rule step_map_op)
            unfolding pcomp_op_def
                apply (rule step_comp_op_R_Inp)
                   apply (rule step_id_op_Read)
                    apply auto
            done
          done
        done
      subgoal for p x p'
        apply (cases p)
        subgoal for lp
          apply (cases lp)
          subgoal for lp
            apply (auto; hypsubst_thin?)
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_tau_step_io_wstep)
               apply (rule step_map_op)
                apply simp_all
               apply (rule step_Tau_comp_op_R)
                    apply (rule step_map_op)
                     apply (rule step_comp_op_L_Inp)
                       apply blast
                      apply simp_all
               apply simp
              apply (rule step_map_op)
               apply simp_all
               apply (rule step_comp_op_R_Out)
                 apply auto
              done
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply force+
              done
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply blast
              unfolding pcomp_op_def
              apply (rule step_tau_step_tau_step_io_wstep)
                apply (rule step_map_op)
                 apply (rule step_Tau_comp_op_L)
                    apply (rule step_map_op)
                     apply (rule step_comp_op_L_Out)
                        apply (rule step_transp_op_Write)
                            apply simp_all
                 prefer 3
                 apply (rule step_map_op)
                  apply (rule step_Tau_comp_op_R)
                       apply (rule step_map_op)
                        apply (rule step_comp_op_L_Inp)
                          apply (rule step_id_op_Read)
                           apply (auto simp add: BHD_def split: sum.splits)
              done
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply blast
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply auto
              done
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply blast
              unfolding pcomp_op_def
              apply (rule step_tau_step_io_wstep)
               apply (rule step_map_op)
                apply (rule step_Tau_comp_op_R)
                     apply (rule step_map_op)
                      apply (rule step_comp_op_L_Inp)
                        apply (rule step_id_op_Read)
                         apply (auto split: sum.splits)
              done
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply blast
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply auto
              done
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply blast
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply auto
              done
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply blast
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply auto
              done
            done
          subgoal for rp
            apply auto
            subgoal
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_tau_step_io_wstep)
               apply (rule step_map_op)
                apply (rule step_Tau_comp_op_R)
                     apply (rule step_map_op)
                      apply (rule step_comp_op_R_Inp)
                         apply (rule step_transp_op_Read)
                          apply (simp_all split: sum.splits)
                apply auto
               apply auto
              done
            subgoal 
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply (rule step_map_op[of "Out (Inr (Inl (Inr rp))) _"])
               apply simp_all
              apply (rule step_comp_op_R_Out)
                apply (rule step_map_op[of "Out (Inr (Inl _)) _"])
                 apply simp_all
              apply auto  
              done
            subgoal 
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_tau_step_tau_step_io_wstep)
                apply (rule step_map_op[of Tau])
                 apply force
                apply simp
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_comp_op_R)
                    apply (rule step_map_op)
                     apply (rule step_comp_op_R_Inp)
                        apply (rule step_transp_op_Read)
                         apply (auto split: sum.splits)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_transp_op_Write)
                     apply auto
              done
            subgoal 
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply (auto 2 2)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_transp_op_Write)
                     apply auto
              done
            subgoal 
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_tau_step_io_wstep)
               apply (rule step_map_op)
                apply (rule step_Tau_comp_op_R)
                     apply (rule step_map_op)
                      apply (rule step_comp_op_R_Inp)
                         apply (rule step_transp_op_Read)
                          apply (auto split: sum.splits)
               apply auto
              done
            subgoal 
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply force
              done
            subgoal
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply force
              done
            subgoal
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply force
              done
            done
          done
        subgoal for lp
          apply simp
          apply (simp split: if_splits; hypsubst_thin?)
          subgoal 
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force
            unfolding pcomp_op_def
            apply auto
            apply (rule wstep_trans_tau_1)
             apply (rule step_Tau_comp_op_L)
                apply (rule step_map_op)
                 apply simp_all
              apply (rule step_comp_op_L_Out)
                 apply (rule step_transp_op_Write)
                     apply (rule refl)+
                    apply auto
            apply (rule wstep_trans_tau_1)
             apply (rule step_Tau_comp_op_R)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Inp)
                      apply (rule step_transp_op_Read)
                       apply auto
            apply (rule step_wstep)
            apply auto+
            done
          subgoal 
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force
            unfolding pcomp_op_def
            apply auto
            apply (rule wstep_trans_tau_1)
             apply (rule step_Tau_comp_op_R)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Inp)
                      apply (rule step_transp_op_Read)
                       apply auto
            apply (rule step_wstep)
            apply auto+
            done
          apply (intro exI conjI[rotated])  
           apply (rule wbc_base)
           apply force
          unfolding pcomp_op_def
          apply auto
          apply force
          done
        done
      done
    subgoal for io op'
      unfolding pcomp_op_def
      apply (drule step_map_op_inv)
      apply (auto; hypsubst_thin?)
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x op''
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        subgoal for io op''
          apply (drule step_comp_op_cases)
          apply (auto; hypsubst_thin?)
          subgoal for p op''
            apply (erule step_transp_op_cases)
             apply (auto; hypsubst_thin?)
            subgoal
              apply (cases p)
              subgoal for lp
                apply (auto; hypsubst_thin?)
                apply (intro exI conjI[rotated])  
                 apply (rule wbc_sym)
                 apply (rule wbc_base)
                 apply force+
                done
              subgoal for rp
                apply (auto; hypsubst_thin?)
                apply (intro exI conjI[rotated])  
                 apply (rule wbc_sym)
                 apply (rule wbc_base)
                 apply force+
                done
              done
            subgoal
              by simp
            done
          subgoal for p op''
            apply (erule step_id_op_cases)
             apply (auto; hypsubst_thin?)
            subgoal
              apply (intro exI conjI[rotated])  
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force+
              done
            subgoal
              by simp
            done
          done
        done
      subgoal for p x op'
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        apply (drule step_comp_op_cases)
        apply (auto; hypsubst_thin?)
        subgoal for p op'
          apply (erule step_transp_op_cases)
           apply (auto; hypsubst_thin?)
          subgoal for p x p'
            apply (cases p)
             apply (auto; hypsubst_thin?)
            subgoal for lp
              apply (intro exI conjI[rotated])  
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force
              apply (rule step_wstep)
              apply auto
              done
            subgoal for rp
              apply (auto; hypsubst_thin?)
              apply (intro exI conjI[rotated])  
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force
              apply (rule step_wstep)
              apply (rule step_transp_op_Write)
                  apply auto
              done
            done
          done
        subgoal for p op
          apply (drule step_id_op_Out)
           apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force
          apply (rule step_wstep)
          apply (rule step_transp_op_Write)
              apply auto
          done
        done
      subgoal for p x op'
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        apply (drule step_comp_op_cases)
        apply (auto; hypsubst_thin?)
        subgoal for p op2
          apply (drule step_id_op_Out)
           apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force+
          done
        subgoal for p op2
          apply (cases p)
          subgoal for lp
            apply (erule step_transp_op_Out)
              apply auto
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply force+
            done
          subgoal for rp
            apply (erule step_transp_op_Out)
              apply auto
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply force+
            done
          done
        done
      subgoal for p op
        apply (cases p)
        subgoal for lp
          apply (drule step_map_op_inv)
          apply (auto; hypsubst_thin?)
          apply (drule step_comp_op_cases)
          apply (auto; hypsubst_thin?)
          apply (drule step_id_op_Inp)
           apply (auto; hypsubst_thin?)
          apply (intro exI conjI[rotated])  
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
          done
        subgoal for rp
          apply (cases rp; auto)
          subgoal for lp
            apply (drule step_map_op_inv)
            apply (auto; hypsubst_thin?)
            apply (drule step_comp_op_cases)
            apply (auto; hypsubst_thin?)
            apply (erule step_transp_op_Inp)
             apply auto
            apply (intro exI conjI[rotated])  
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply force
            apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
            done
          subgoal for rp
            apply (drule step_map_op_inv)
            apply (auto; hypsubst_thin?)
            apply (drule step_comp_op_cases)
            apply (auto; hypsubst_thin?)
            apply (erule step_transp_op_Inp)
             apply auto
            apply (intro exI conjI[rotated])  
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply force
            apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
            done
          done
        done
      subgoal for op1
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        apply (drule step_comp_op_cases)
        apply (auto elim: no_step_transp_op_Tau no_step_id_op_Tau)
        done
      subgoal for op2'
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        apply (drule step_comp_op_cases)
        apply (auto elim: no_step_transp_op_Tau no_step_id_op_Tau)
        done
      done
    done
  done

lemma B9:
  assumes "\<X>klm = (\<X> :: ('k :: {countable,defaults} + 'l :: {countable,defaults} + 'm :: {countable,defaults}, ('l + 'm) + 'k, 'c) op)"
    and "\<X>kl = (\<X> :: ('k + 'l, 'l + 'k, 'c) op)"
    and "\<X>km = (\<X> :: ('k + 'm, 'm + 'k, 'c) op)"
    and "\<I>m = (\<I> :: ('m, 'm, 'c) op)"
    and "\<I>l = (\<I> :: ('l, 'l, 'c) op)"
  shows "\<X>klm \<approx> map_op reassoc reassoc (\<X>kl \<parallel> \<I>m) \<bullet> map_op id assoc (\<I>l \<parallel> \<X>km)"
  using assms unfolding scomp_op_def
  apply hypsubst_thin
  using B9_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] by auto

end