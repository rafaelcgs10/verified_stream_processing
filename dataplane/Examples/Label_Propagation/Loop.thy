theory Loop

imports
  Input1
begin

lemma loop_move_all_data:
  assumes I: "intsum (os 2) = increment_summary (MyPair 0 1)"
    and N: "initia (os 2)"
    and C1: "input_ocaps_inv (os 2)"
  shows  "(step Tau)\<^sup>*\<^sup>*
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
           (logic_map (1 :: 3) (label_propagation_op (os_label_prop :: (nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state)))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ((os 2) :: (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state))))))
       (loop_op loop_wire ((case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))(Inr (2,1) := [], Inr (1,1) := []))
       (comp_map
         (comp_op
           comp_wire
           ((case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))(Inr (2,1) := [], Inr (1,1) := []))
           (logic_map (1 :: 3) (label_propagation_op (fold (\<lambda>(d, t) os. consumes os 1 t d) (map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
                 (fold (\<lambda>(d, t) os. consumes os 1 t d) (outpu (os 2) 1) (fold (\<lambda>(d, t) os. consumes os 1 t d) (cbufs (1, 1)) (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>))))))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (((drop_caps
                 (produces (fold (\<lambda>(d, t) os. consumes os 1 t d) (outpu os_label_prop 1) (fold (\<lambda>(d, t) os. consumes os 1 t d) (cbufs (2, 1)) (os 2)))
                   (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1)) (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
                 (map (\<lambda>t. Cap t 1) (ocaps (os 2) 1 @  (map (\<lambda>(d, t). t -+- MyPair 0 (Suc 0)) (cbufs (2, 1) @ outpu os_label_prop 1)))))\<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>)))))))"
  apply (cases "input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1")
  subgoal premises prems
    apply (cases "cbufs (1, 1) @ outpu (os 2) 1")
    subgoal
      using prems apply -
      apply (cases "ocaps (os 2) 1")
      subgoal
        apply (clarsimp simp add: produces_def drop_caps_def)
        apply (subst comp_op_buf_cong[where buf'="case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := []))"])
        apply (rule refl)+
        subgoal
          apply (clarsimp simp add: prems increment_op_def op.set_map(1) ran_def split: sum.splits option.splits if_splits)
          done
        apply (subst loop_op_buf_cong[where buf'="(case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := [])))"])
        apply (rule refl)+
        subgoal
          by (auto simp add: op.set_map(1) ran_def split: sum.splits option.splits if_splits)
        apply (rule step_Tau_pow_eqI)
        apply (rule arg_cong2[where f="loop_op loop_wire"])
        apply simp
        apply (rule arg_cong[where f=comp_map])
        apply (rule arg_cong3[where f="comp_op comp_wire"])
        apply simp
        subgoal
          using prems apply -
          apply clarsimp
          apply (rule arg_cong[where f="logic_map 1"])
          apply (rule arg_cong[where f="label_propagation_op"])
          apply (auto simp add: fold_consumes produ_consumes_fold inter_consumes_fold consu_consumes_fold intsum_consumes_fold intro!: operator_state_eqI )
          done
        apply (rule arg_cong[where f="logic_map 2"])
        apply (rule arg_cong[where f="increment_op 1 1 (MyPair 0 (Suc 0))"])
        using prems apply -
        apply (auto simp add: produces_def drop_caps_def intro!: operator_state_eqI)
        done
      subgoal
        apply (rule converse_rtranclp_into_rtranclp) 
        apply (rule step_Tau_loop_op)
        apply (rule step_map_op)
        apply (rule step_comp_op_R_Tau)
        apply (rule step_map_op)
        apply (rule step_increment_op_Silent)
        apply simp
        apply (rule refl)+
        using N apply assumption
        apply (rule refl)+
        apply simp
        apply (rule refl)+
        apply simp
        apply (rule refl)+
        apply (subst comp_op_buf_cong[where buf'="case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := []))"])
        apply (rule refl)+
        subgoal
          using prems by (fastforce simp add: prems increment_op_def op.set_map(1) ran_def split: sum.splits option.splits if_splits)
        apply (subst loop_op_buf_cong[where buf'="(case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := [])))"])
        apply (rule refl)+
        subgoal
          by (auto simp add: op.set_map(1) ran_def split: sum.splits option.splits if_splits)
        apply (rule step_Tau_pow_eqI)
        apply (rule arg_cong2[where f="loop_op loop_wire"])
        apply simp
        apply (rule arg_cong[where f=comp_map])
        apply (rule arg_cong3[where f="comp_op comp_wire"])
        apply simp
        subgoal
          using prems apply -
          apply clarsimp
          apply (rule arg_cong[where f="logic_map 1"])
          apply (rule arg_cong[where f="label_propagation_op"])
          apply (auto simp add: fold_consumes produ_consumes_fold inter_consumes_fold consu_consumes_fold intsum_consumes_fold intro!: operator_state_eqI )
          done
        apply (rule arg_cong[where f="logic_map 2"])
        apply (rule arg_cong[where f="increment_op 1 1 (MyPair 0 (Suc 0))"])
        using prems apply -
        apply (auto simp add: produces_def drop_caps_def intro!: operator_state_eqI)
        done
      done
    subgoal premises prems2
      apply (cases "ocaps (os 2) 1")
      subgoal
        apply (rule rtranclp_trans)
        apply (rule relpowp_imp_rtranclp[where n="length (outpu (os 2) 1)"]) 
        apply (rule step_tau_Out_pow_loop_op_steps_intro[where xs="map Inr (outpu (os 2) 1)"])
        apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Inr _) (Inr x)) ( outpu (os 2) 1)"])
        apply (rule refl)+
        apply force
        apply (rule steps_comp_op_R_Out[where xs="map Inr ( outpu (os 2) 1)"])
        apply (rule steps_map_op[where xs="map (\<lambda> x. Out _ (_ x)) ( outpu (os 2) 1)"])
        apply (rule refl)+
        apply force
        apply (rule steps_increment_op_Write_Some[where ys=Nil])
        apply simp
        apply (rule refl)+
        apply simp
        apply blast
        apply simp
        apply simp
        apply (rule refl)+

        apply (rule rtranclp_trans)
        apply (rule relpowp_imp_rtranclp[where n="length (cbufs (1, 1)) + length (outpu (os 2) 1)"]) 
        apply (rule step_tau_Inp_pow_loop_op_steps_intro[where p="Inr (1, 1)" and xs="map Inr (cbufs (1, 1) @ outpu (os 2) 1)"])
        apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Inl _) (Inr x)) (cbufs (1, 1) @ outpu (os 2) 1)"])
        apply (rule refl)+
        apply force
        apply (rule steps_comp_op_L_Inp[where p="Inr (1, 1)" and xs="map Inr (cbufs (1, 1) @ outpu (os 2) 1)"])
        apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Some 1) (Inr x)) (cbufs (1, 1) @ outpu (os 2) 1)"])
        apply (rule refl)+
        apply simp
        apply blast
        apply (rule refl)+
        apply (simp add: prems2)
        apply simp
        subgoal
          by (auto simp add: ran_def split: sum.splits)
        apply (simp add: BULK_BENQ_def)
        apply (simp add: BULK_BENQ_def)
        apply (rule refl)+

        apply (simp add: BULK_BENQ_def)
        apply (subst loop_op_buf_cong[where buf'="(case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := [])))"])
        apply (rule refl)+
        subgoal
          by (auto simp add: op.set_map(1) ran_def split: sum.splits option.splits if_splits)
        apply (rule step_Tau_pow_eqI)
        apply (rule arg_cong2[where f="loop_op loop_wire"])
        apply simp
        apply (rule arg_cong[where f=comp_map])
        apply (subst comp_op_buf_cong[where buf'="case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := []))"])
        apply (rule refl)+
        subgoal
          apply (clarsimp simp add: prems2 prems increment_op_def op.set_map(1) ran_def split: sum.splits option.splits if_splits)
          using prems apply blast
          done
        apply (rule arg_cong3[where f="comp_op comp_wire"])
        apply simp
        subgoal
          using prems apply -
          apply clarsimp
          apply (rule arg_cong[where f="logic_map 1"])
          apply (rule arg_cong[where f="label_propagation_op"])
          apply (auto simp add: fold_consumes produ_consumes_fold inter_consumes_fold consu_consumes_fold intsum_consumes_fold intro!: operator_state_eqI )
          done
        subgoal
          apply (rule arg_cong[where f="logic_map 2"])
          apply (rule arg_cong[where f="increment_op 1 1 (MyPair 0 (Suc 0))"])
          using prems apply -
          apply (auto simp add: produces_def drop_caps_def C1 intro!: operator_state_eqI)
          done
        done
      subgoal premises prems3
        apply (rule rtranclp_trans)
        apply (rule converse_rtranclp_into_rtranclp) 
        apply (rule step_Tau_loop_op)
        apply (rule step_map_op)
        apply (rule step_comp_op_R_Tau)
        apply (rule step_map_op)
        apply (rule step_increment_op_Silent)
        using prems3    apply simp
        apply (rule refl)+
        using N apply assumption
        apply (rule refl)+
        apply simp
        apply (rule refl)+
        apply simp
        apply (rule refl)+

        apply (rule rtranclp_trans)
        apply (rule relpowp_imp_rtranclp[where n="length (outpu (os 2) 1)"]) 
        apply (rule step_tau_Out_pow_loop_op_steps_intro[where xs="map Inr (outpu (os 2) 1)"])
        apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Inr _) (Inr x)) ( outpu (os 2) 1)"])
        apply (rule refl)+
        apply force
        apply (rule steps_comp_op_R_Out[where xs="map Inr ( outpu (os 2) 1)"])
        apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Some 1) (_ x)) ( outpu (os 2) 1)"])
        apply (rule refl)+
        apply force
        apply (rule steps_increment_op_Write_Some[where ys=Nil])
        apply simp
        apply (rule refl)+
        using prems apply (fastforce simp add: prems2 prems prems3 comp_def split_beta filter_empty_conv)[1]
        apply (rule refl)+
        apply simp
        apply blast
        apply simp
        apply simp
        apply (rule refl)+

        apply (rule relpowp_imp_rtranclp[where n="length (cbufs (1, 1)) + length (outpu (os 2) 1)"]) 
        apply (rule step_tau_Inp_pow_loop_op_steps_intro[where p="Inr (1, 1)" and xs="map Inr (cbufs (1, 1) @ outpu (os 2) 1)"])
        apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Inl _) (Inr x)) (cbufs (1, 1) @ outpu (os 2) 1)"])
        apply (rule refl)+
        apply force
        apply (rule steps_comp_op_L_Inp[where p="Inr (1, 1)" and xs="map Inr (cbufs (1, 1) @ outpu (os 2) 1)"])
        apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Some 1) (Inr x)) (cbufs (1, 1) @ outpu (os 2) 1)"])
        apply (rule refl)+
        apply simp
        apply blast
        apply (rule refl)+
        apply (simp add: prems2)
        apply simp
        subgoal
          by (auto simp add: ran_def split: sum.splits)
        apply (simp add: BULK_BENQ_def)
        apply (simp add: BULK_BENQ_def)
        apply (rule refl)+

        apply (simp add: BULK_BENQ_def)
        apply (subst loop_op_buf_cong[where buf'="(case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := [])))"])
        apply (rule refl)+
        subgoal
          by (auto simp add: op.set_map(1) ran_def split: sum.splits option.splits if_splits)
        apply (rule step_Tau_pow_eqI)
        apply (rule arg_cong2[where f="loop_op loop_wire"])
        apply simp
        apply (rule arg_cong[where f=comp_map])
        apply (subst comp_op_buf_cong[where buf'="case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := []))"])
        apply (rule refl)+
        subgoal
          apply (clarsimp simp add: prems2 prems increment_op_def op.set_map(1) ran_def split: sum.splits option.splits if_splits)
          using prems apply blast
          done
        apply (rule arg_cong3[where f="comp_op comp_wire"])
        apply simp
        subgoal
          using prems apply -
          apply clarsimp
          apply (rule arg_cong[where f="logic_map 1"])
          apply (rule arg_cong[where f="label_propagation_op"])
          apply (auto simp add: fold_consumes produ_consumes_fold inter_consumes_fold consu_consumes_fold intsum_consumes_fold intro!: operator_state_eqI )
          done
        subgoal
          apply (rule arg_cong[where f="logic_map 2"])
          apply (rule arg_cong[where f="increment_op 1 1 (MyPair 0 (Suc 0))"])
          using prems apply -
          apply (auto simp add: produces_def drop_caps_def C1 intro!: operator_state_eqI)
          done
        done
      done
    done
  subgoal premises prems for x xs
    apply (rule rtranclp_trans)
    apply (rule relpowp_imp_rtranclp[where n="length (outpu (os_label_prop) 1)"]) 
    apply (rule step_taus_loop_op_steps_intro)
    apply (rule step_tau_pow_map_op)
    apply (rule step_tau_Out_pow_comp_op_steps_intro[where xs="map Inr (outpu (os_label_prop) 1)" and p="Inr (1, 1)"])
    apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Some 1) (Inr x)) (outpu (os_label_prop) 1)"])
    apply (rule refl)+
    apply simp
    apply (rule steps_label_propagation_op_Write_Some[where ys=Nil])
    apply simp
    apply (rule refl)+
    apply simp
    apply simp
    apply (rule refl)+

    apply (rule rtranclp_trans)
    apply (rule relpowp_imp_rtranclp[where n="length (cbufs (2, 1)) + length (outpu (os_label_prop) 1)"]) 
    apply (rule step_taus_loop_op_steps_intro)
    apply (rule step_tau_pow_map_op)
    apply (rule step_tau_Inp_pow_comp_op_steps_intro[where xs="map Inr (cbufs (2, 1) @ outpu (os_label_prop) 1)" and p="Inr (2, 1)"])
    apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Some 1) (Inr x)) (cbufs (2, 1) @ outpu (os_label_prop) 1)"])
    apply (rule refl)+
    apply simp
    apply (rule steps_increment_op_Read_Some)
    apply (rule refl)+
    apply simp
    apply simp
    apply (simp add: BULK_BENQ_def)
    apply (simp add: BULK_BENQ_def)
    apply (rule refl)+

    apply (rule converse_rtranclp_into_rtranclp) 
    apply (rule step_Tau_loop_op)
    apply (rule step_map_op)
    apply (rule step_comp_op_R_Tau)
    apply (rule step_map_op)
    apply (rule step_increment_op_Silent)
    subgoal    
      apply (cases "input (os 2) 1")
      subgoal
        using prems apply -
        apply (clarsimp simp add:  I intsum_consumes_fold split: prod.splits)
        done
      subgoal for x xs
        apply (cases x)
        subgoal for d t
          using prems apply -
          apply (clarsimp simp add:  I intsum_consumes_fold split: prod.splits)
          apply hypsubst_thin
          using C1[unfolded input_ocaps_inv_def, rule_format, rotated, of "MyPair 0 1" 1 1, unfolded I, of t] apply -
          apply simp
          done
        done
      done
    apply (rule refl)+
    apply (simp add: N)
    apply (rule refl)+
    apply simp
    apply (rule refl)+
    apply simp
    apply (rule refl)+
    apply (simp flip: map_append)

    apply (rule rtranclp_trans)
    apply (rule rtranclp_trans)
    apply (rule relpowp_imp_rtranclp[where n="length (input (os 2) 1) + length (outpu (os 2) 1) + length (cbufs (2, 1)) + length (outpu (os_label_prop) 1)"]) 
    apply (rule step_tau_Out_pow_loop_op_steps_intro[where xs="map Inr (outpu (os 2) 1) @ map (\<lambda>(d, t). Inr (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1)"])
    apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Inr _) (Inr x)) (outpu (os 2) 1) @ map (\<lambda>(d, t). Out (Inr _) (Inr (d, t -+- MyPair 0 (Suc 0)))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1) "])
    apply (rule refl)+
    apply force
    apply (rule steps_comp_op_R_Out[where xs="map Inr (outpu (os 2) 1) @ map (\<lambda>(d, t). Inr (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1)"])
    apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Some 1) (Inr x)) ( outpu (os 2) 1) @ map (\<lambda>(d, t). Out (Some 1) (Inr (d, t -+- MyPair 0 (Suc 0)))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1)"])
    apply (rule refl)+
    apply force
    apply (rule steps_increment_op_Write_Some[where ys=Nil])
    apply simp
    apply (rule refl)+
    apply simp
    apply (simp add: comp_def split_beta filter_True input_fold_consumes)
    apply (rule refl)+
    apply force
    apply simp
    apply simp
    apply (rule refl)+
    apply (simp flip: map_append)

    apply (rule relpowp_imp_rtranclp[where n="length (cbufs (1, 1)) + length (outpu (os 2) 1) + length (input (os 2) 1) + length (cbufs (2, 1)) + length (outpu (os_label_prop) 1)"]) 
    apply (rule step_tau_Inp_pow_loop_op_steps_intro[where p="Inr (1, 1)" and xs="map Inr (cbufs (1, 1) @ outpu (os 2) 1 @ map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1))"])
    apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Inl _) (Inr x)) (cbufs (1, 1) @ outpu (os 2) 1) @ map (\<lambda>(d, t). Inp (Inl _) (Inr (d, t -+- MyPair 0 (Suc 0)))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1)"])
    apply (rule refl)+
    apply force
    apply (rule steps_comp_op_L_Inp[where p="Inr (1, 1)" and xs="map Inr (cbufs (1, 1) @ outpu (os 2) 1 @ map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1))"])
    apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Some 1) (Inr x)) (cbufs (1, 1) @ outpu (os 2) 1 @ map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu (os_label_prop) 1))"])
    apply (rule refl)+
    apply simp
    apply blast
    apply (rule refl)+
    apply simp
    subgoal
      by (simp add: prems split: prod.splits)
    apply simp
    subgoal
      by (auto simp add: ran_def split: sum.splits)
    subgoal
      by (simp add: BULK_BENQ_def)
    subgoal
      by (auto simp add: ran_def BULK_BENQ_def)
    apply (rule refl)+
    apply (simp flip: map_append concat_append filter_append add: I intsum_consumes_fold comp_def split_beta filter_True filter_False input_fold_consumes)
    apply (rule step_Tau_pow_eqI)
    apply (subst loop_op_buf_cong[where buf'="(case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := [])))"])
    apply (rule refl)+
    subgoal
      apply (clarsimp simp add: op.set_map(1) ran_def split: sum.splits option.splits if_splits)
      using prems apply (force simp add: prems BULK_BENQ_def op.set_map(1) ran_def split: sum.splits option.splits if_splits)+
      done
    apply (subst comp_op_buf_cong[where buf'="case_sum (\<lambda>x. []) ((\<lambda>x. map Inr (cbufs x))((2, 1) := [], (1, 1) := []))"])
    apply (rule refl)+
    subgoal
      apply (clarsimp simp add: op.set_map(1) ran_def split: sum.splits option.splits if_splits)
      using prems apply (force simp add: prems BULK_BENQ_def op.set_map(1) ran_def split: sum.splits option.splits if_splits)+
      done
    apply (rule arg_cong2[where f="loop_op loop_wire"])
    apply simp
    apply (rule arg_cong[where f=comp_map])
    apply (rule arg_cong3[where f="comp_op comp_wire"])
    apply simp
    apply simp
    apply (rule arg_cong[where f="logic_map 2"])
    apply (rule arg_cong[where f="increment_op 1 1 (MyPair 0 (Suc 0))"])
    using prems apply -
    apply (auto simp add: prems  produces_def drop_caps_def C1 intro!: operator_state_eqI split: if_splits)
    apply (auto simp add: filter_empty_conv comp_def split_beta map_concat)
    done
  done


lemma loop_label_prop_input1:
  assumes N: "initia os_label_prop"
  shows  "(step Tau)\<^sup>*\<^sup>*
         (loop_op loop_wire cbufs
           (comp_map
             (comp_op
               comp_wire
               cbufs
               (logic_map (1 :: 3) (label_propagation_op (os_label_prop :: (nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state)))
               (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ((os 2) :: (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state))))))
         (loop_op loop_wire cbufs
           (comp_map
             (comp_op
               comp_wire
               cbufs
               (logic_map (1 :: 3) (label_propagation_op (fst (label_prop_input1_batched os_label_prop (input os_label_prop 1)))))
               (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os 2))))))"
  apply (rule relpowp_imp_rtranclp[where n="length (input os_label_prop 1)"]) 
  apply (rule step_taus_loop_op_steps_intro)
  apply (rule step_tau_pow_map_op)
  apply (rule step_taus_L_pow_comp_op_steps_intro)
  apply (rule step_tau_pow_map_op)
  apply (rule step_compower_label_propagation_op_input1_eq_alt[where ys=Nil])
  apply simp
  apply simp
  using N apply assumption
  apply (rule refl)+
  done

section \<open>label_prop_input1_loop_updates\<close>

subsection \<open>Folded consumption\<close>





subsection \<open>One-step input-1 loop update\<close>


lemma loop_move_all_data_label_prop_input1:
  assumes NO: "initia os_label_prop"
    and I: "intsum (os 2) = increment_summary (MyPair 0 1)"
    and N: "initia (os 2)"
    and C1: "input_ocaps_inv (os 2)"
  shows  "(step Tau)\<^sup>*\<^sup>*
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
           (logic_map (1 :: 3) (label_propagation_op (os_label_prop :: (nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state)))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ((os 2) :: (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state))))))
     (loop_op loop_wire ((case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))(Inr (2, 1) := [], Inr (1, 1) := []))
       (comp_map
         (comp_op
           comp_wire
           ((case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))(Inr (2, 1) := [], Inr (1, 1) := []))
           (logic_map (1 :: 3) (label_propagation_op (fst (label_prop_input1_batched
                      (CONSUMES 1 (cbufs (1, 1) @ outpu (os 2) 1 @ map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
                        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>))
                      (input
                        (CONSUMES 1 (cbufs (1, 1) @ outpu (os 2) 1 @ map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
                          (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>))
                        1)))))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (drop_caps (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2)) (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1)) (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
                 (map (\<lambda>t. Cap t 1) (ocaps (os 2) 1 @ map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0)) (cbufs (2, 1) @ outpu os_label_prop 1)))
                \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>))))))"
  apply (rule rtranclp_trans)
  apply (rule loop_move_all_data)
  using I apply assumption
  using N apply assumption
  using C1 apply assumption
  apply (rule rtranclp_trans)
  apply (rule loop_label_prop_input1)
  apply (simp add: NO)
  apply (simp flip: map_append fold_append only: CONSUMES_CONSUMES)
  apply (rule step_Tau_pow_eqI)
  apply (simp only: append_assoc)
  done


lemma loop_move_all_data_label_prop_input1_updates:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes UPDATES:
    \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and NO: \<open>initia os_label_prop\<close>
    and I: \<open>intsum (os 2) = increment_summary (MyPair 0 1)\<close>
    and N: \<open>initia (os 2)\<close>
    and C1: "input_ocaps_inv (os 2)"
  shows  \<open>(step Tau)\<^sup>*\<^sup>*
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
           (logic_map (1 :: 3) (label_propagation_op os_label_prop))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os 2))))))
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs' x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs' x)))
           (logic_map (1 :: 3) (label_propagation_op os_label_prop'))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os' 2))))))\<close>
proof -
  let ?buf = \<open>case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x))\<close>
  let ?buf' = \<open>?buf(Inr (2, 1) := [], Inr (1, 1) := [])\<close>
  let ?os_label_prop_consumed =
    \<open>CONSUMES 1
      (cbufs (1, 1) @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
      (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  let ?os_label_prop_new =
    \<open>fst (label_prop_input1_batched ?os_label_prop_consumed (input ?os_label_prop_consumed 1))\<close>
  let ?os2_new =
    \<open>drop_caps
      (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2))
        (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
      (map (\<lambda>t. Cap t 1)
        (ocaps (os 2) 1 @
          map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
            (cbufs (2, 1) @ outpu os_label_prop 1)))
      \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>\<close>
  have old_step: \<open>(step Tau)\<^sup>*\<^sup>*
      (loop_op loop_wire ?buf
        (comp_map
          (comp_op comp_wire ?buf
            (logic_map (1 :: 3) (label_propagation_op os_label_prop))
            (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os 2))))))
      (loop_op loop_wire ?buf'
        (comp_map
          (comp_op comp_wire ?buf'
            (logic_map (1 :: 3) (label_propagation_op ?os_label_prop_new))
            (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ?os2_new)))))\<close>
    using loop_move_all_data_label_prop_input1[where os=os and os_label_prop=os_label_prop and cbufs=cbufs]
      NO I N C1 by blast
  have buf_eq:
    \<open>case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs' x)) = ?buf'\<close>
    using UPDATES unfolding label_prop_input1_loop_updates_def Let_def
    by (auto simp add: fun_eq_iff split: sum.splits prod.splits)
  have states_eq:
    \<open>os_label_prop' = ?os_label_prop_new \<and> os' 2 = ?os2_new\<close>
    using UPDATES unfolding label_prop_input1_loop_updates_def Let_def by simp
  have target_eq:
    \<open>loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs' x)))
      (comp_map
        (comp_op comp_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs' x)))
          (logic_map (1 :: 3) (label_propagation_op os_label_prop'))
          (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os' 2))))) =
     loop_op loop_wire ?buf'
      (comp_map
        (comp_op comp_wire ?buf'
          (logic_map (1 :: 3) (label_propagation_op ?os_label_prop_new))
          (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ?os2_new))))\<close>
    using buf_eq states_eq by metis

  show ?thesis
    using old_step target_eq by metis

qed


function loop_updates where
  "loop_updates (cbufs :: 3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf) os_label_prop (os :: 3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state) = (
   if label_prop_upd_inv os_label_prop \<and> (\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
      wf_label_prop_updates os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
   then
     let (cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os in
     if outpu os_label_prop' 1 = []
     then (cbufs', os_label_prop', os')
     else loop_updates cbufs' os_label_prop' os'
   else (cbufs((2, 1) := [], (1, 1) := []), os_label_prop, os)
   )"

  by auto

termination
  apply (relation "measure (\<lambda>(cbufs, os_label_prop, os). sum_list (map (\<lambda> t. labels_measure (all_edges os_label_prop t) (min_label os_label_prop t)) (timestamps os_label_prop))) ")
  apply simp
  subgoal for cbufs os_label_prop os x cbufs' y os_label_prop' os'
    apply (clarsimp del: disjCI split: prod.splits)
    apply (rule label_prop_input1_loop_updates_sum_measure_decrease_if_label_output_nonempty[rotated, where cbufs'=cbufs' and cbufs=cbufs and os=os])
    subgoal
      apply (rule ccontr)
      apply blast
      done
    apply simp_all
    done
  done



declare loop_updates.simps[simp del]


lemma loop_updates_intsum_corrected:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
  shows \<open>\<forall>m. intsum ((os'(1 := op_state_base os_label_prop')) m) =
    intsum ((os(1 := op_state_base os_label_prop)) m)\<close>
  using step
proof (induct cbufs os_label_prop os arbitrary: cbufs' os_label_prop' os' rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  show ?case
  proof (cases ?good)
    case False
    have loop_eq:
      \<open>loop_updates cbufs os_label_prop os =
        (cbufs((2, 1) := [], (1, 1) := []), os_label_prop, os)\<close>
      by (subst loop_updates.simps) (simp only: False if_False)
    show ?thesis
      using "1.prems" loop_eq by simp
  next
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have intsum1:
      \<open>\<forall>m. intsum ((os1(1 := op_state_base os_label_prop1)) m) =
        intsum ((os(1 := op_state_base os_label_prop)) m)\<close>
      using label_prop_input1_loop_updates_intsum_corrected[OF step1[symmetric]]
      by simp
    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      have loop_eq:
        \<open>loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 True in simp)
      show ?thesis
        using "1.prems" loop_eq intsum1 by simp
    next
      case False
      have loop_eq:
        \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs1 os_label_prop1 os1\<close>
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 False in simp)
      have step_rec:
        \<open>(cbufs', os_label_prop', os') = loop_updates cbufs1 os_label_prop1 os1\<close>
        using "1.prems" loop_eq by simp
      have rec:
        \<open>\<forall>m. intsum ((os'(1 := op_state_base os_label_prop')) m) =
          intsum ((os1(1 := op_state_base os_label_prop1)) m)\<close>
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False step_rec])
      show ?thesis
        using rec intsum1 by simp
    qed
  qed
qed



lemma loop_updates_cbufs_cleared:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
    and k: \<open>k = ((1 :: 3), (1 :: 2)) \<or> k = ((2 :: 3), (1 :: 2))\<close>
  shows \<open>cbufs' k = []\<close>
  using step k
proof (induct cbufs os_label_prop os arbitrary: cbufs' os_label_prop' os' k rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  show ?case
  proof (cases ?good)
    case False
    have loop_eq:
      \<open>loop_updates cbufs os_label_prop os =
        (cbufs((2, 1) := [], (1, 1) := []), os_label_prop, os)\<close>
      by (subst loop_updates.simps) (simp only: False if_False)
    show ?thesis
      using "1.prems" loop_eq by auto
  next
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have cbufs1_k: \<open>cbufs1 k = []\<close>
      using "1.prems"(2)
        label_prop_input1_loop_updates_cbufs_11[OF step1[symmetric]]
        label_prop_input1_loop_updates_cbufs_21[OF step1[symmetric]]
      by auto
    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      have loop_eq:
        \<open>loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 True in simp)
      show ?thesis
        using "1.prems"(1) loop_eq cbufs1_k by simp
    next
      case False
      have loop_eq:
        \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs1 os_label_prop1 os1\<close>
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 False in simp)
      have step_rec:
        \<open>(cbufs', os_label_prop', os') = loop_updates cbufs1 os_label_prop1 os1\<close>
        using "1.prems"(1) loop_eq by simp
      show ?thesis
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False step_rec "1.prems"(2)])
    qed
  qed
qed



lemma loop_updates_msgs_invI:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and wf_upd: \<open>wf_label_prop_updates os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  shows \<open>wf_label_prop_updates os_label_prop'
      (set (input os_label_prop' 1) \<union>
       set (cbufs' (1, 1) @ outpu (os' 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os' 2) 1 @ cbufs' (2, 1) @ outpu os_label_prop' 1)))\<close>
  using step INV LABELS wf_upd EN1 DE1
proof (induct cbufs os_label_prop os arbitrary: cbufs' os_label_prop' os' rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  have good: ?good
    using "1.prems" by simp
  obtain cbufs1 os_label_prop1 os1 where step1:
    \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
  have input1_empty: \<open>input os_label_prop1 1 = []\<close>
    by (rule label_prop_input1_loop_updates_input_label_1[OF step1[symmetric]])
  have wf1_msgs:
    \<open>wf_label_prop_updates os_label_prop1
      (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    by (rule label_prop_input1_loop_updates_msgs_invI
        [OF step1[symmetric] "1.prems"(5) "1.prems"(6) "1.prems"(2) "1.prems"(3) "1.prems"(4)])
  have wf1:
    \<open>wf_label_prop_updates os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    using input1_empty wf1_msgs by simp
  show ?case
  proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
    case True
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (subst loop_updates.simps) (use good step1 True in simp)
    show ?thesis
      using "1.prems"(1) loop_eq wf1 by simp
  next
    case False
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs1 os_label_prop1 os1\<close>
      by (subst loop_updates.simps) (use good step1 False in simp)
    have step_rec: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs1 os_label_prop1 os1\<close>
      using "1.prems"(1) loop_eq by simp
    have INV1: \<open>label_prop_upd_inv os_label_prop1\<close>
      by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] "1.prems"(2) "1.prems"(4)])
    have LABELS1: \<open>\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)\<close>
      by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] "1.prems"(2) "1.prems"(4) "1.prems"(3)])
    have EN1_1: \<open>en1 os_label_prop1 = Inl\<close>
      using label_prop_input1_loop_updates_en1_label[OF step1[symmetric]] "1.prems"(5) by simp
    have DE1_1: \<open>de1 os_label_prop1 = projl\<close>
      using label_prop_input1_loop_updates_de1_label[OF step1[symmetric]] "1.prems"(6) by simp
    show ?thesis
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False step_rec INV1 LABELS1 wf1 EN1_1 DE1_1])
  qed
qed


subsection \<open>Operational simulation for loop_updates\<close>


lemma step_tau_pow_loop_updates:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes UPDATES:
    \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
    and NO: \<open>initia os_label_prop\<close>
    and Intsum: \<open>\<forall>n. intsum ((os(1 := op_state_base os_label_prop)) n) =
      (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    and N: \<open>initia (os 2)\<close>
    and C1: "input_ocaps_inv (os 2)"
    and L: \<open>label_prop_upd_inv os_label_prop\<close>
    and M: \<open>\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and wf_upd: \<open>wf_label_prop_updates os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
  shows  \<open>(step Tau)\<^sup>*\<^sup>*
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
           (logic_map (1 :: 3) (label_propagation_op os_label_prop))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os 2))))))
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs' x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs' x)))
           (logic_map (1 :: 3) (label_propagation_op os_label_prop'))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os' 2))))))\<close>
  using assms apply -
  apply (induct cbufs os_label_prop os rule: loop_updates.induct)
  apply simp
  subgoal premises prems for cbufs os_label_prop os
    using prems(2-) apply -
    apply (subst (asm) loop_updates.simps)
    apply (clarsimp split: prod.splits if_splits)
    subgoal
      apply (rule loop_move_all_data_label_prop_input1_updates)
      apply (rule sym)
      apply assumption+
      apply simp_all
      unfolding op_state_base_def
      apply simp
      apply (drule spec[of _ 2])
      apply simp
      apply (rule ext)+
      unfolding raw_summary_def 
      apply (auto 0 0)
      using num2_neq(2) apply blast
      done
    subgoal for cbufs' os_label_prop' os'
      apply (rule rtranclp_trans)
      apply (rule loop_move_all_data_label_prop_input1_updates)
      apply (rule sym)
      apply assumption+
      apply simp_all
      subgoal
        apply (drule spec[of _ 2])
        apply simp
        apply (rule ext)+
        unfolding raw_summary_def 
        apply (auto 0 0)
        using num2_neq(2) apply blast
        done
      apply (rule prems(1)[simplified, OF refl])
      apply simp_all
      apply (subst loop_updates.simps)
      apply simp_all
      apply (metis (no_types, opaque_lifting) label_prop_input1_loop_updates_initia_label)
      subgoal
        unfolding op_state_base_def
        apply simp
        apply (metis (no_types, lifting) array_rules(4) label_prop_input1_loop_updates_intsum_label
            label_prop_input1_loop_updates_intsum_corrected)
        done
      subgoal
        by (metis label_prop_input1_loop_updates_initia_os2)
      subgoal
        by (metis (no_types, lifting) array_rules(2) input_ocaps_inv_label_prop_input1_loop_updates_os2)
      subgoal
        apply (rule label_prop_upd_inv_label_prop_input1_loop_updatesI)
        apply (rule sym, assumption)
        apply assumption
        apply simp
        done
      subgoal
        apply (rule labels_inv_label_prop_input1_loop_updates_allI)
        apply (rule sym, assumption)
        apply assumption
        apply simp
        apply simp
        done
      subgoal
        apply (subgoal_tac \<open>input os_label_prop' 1 = []\<close>)
        apply simp
        apply (rule label_prop_input1_loop_updates_msgs_invI[simplified])
        apply (rule sym, assumption)
        apply assumption+
        apply (rule label_prop_input1_loop_updates_input_label_1)
        apply (rule sym, assumption)
        done
      subgoal
        by (metis label_prop_input1_loop_updates_en1_label)
      subgoal
        by (metis label_prop_input1_loop_updates_de1_label)
      done
    done
  done


lemma step_tau_pow_loop_updates_alt:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes NO: \<open>initia os_label_prop\<close>
    and Intsum: \<open>\<forall>n. intsum ((os(1 := op_state_base os_label_prop)) n) =
      (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    and N: \<open>initia (os 2)\<close>
    and C1: "input_ocaps_inv (os 2)"
    and L: \<open>label_prop_upd_inv os_label_prop\<close>
    and M: \<open>\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and wf_upd: \<open>wf_label_prop_updates os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
  shows  \<open>(step Tau)\<^sup>*\<^sup>*
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
           (logic_map (1 :: 3) (label_propagation_op os_label_prop))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) (os 2))))))
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (fst (loop_updates cbufs os_label_prop os) x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (fst (loop_updates cbufs os_label_prop os) x)))
           (logic_map (1 :: 3) (label_propagation_op (fst (snd (loop_updates cbufs os_label_prop os)))))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ((snd (snd (loop_updates cbufs os_label_prop os))) 2))))))\<close>
proof -
  let ?res = \<open>loop_updates cbufs os_label_prop os\<close>
  have updates: \<open>(fst ?res, fst (snd ?res), snd (snd ?res)) = ?res\<close>
    by (cases ?res) simp
  show ?thesis
    using assms step_tau_pow_loop_updates by simp
qed
  (*

lemma loop_op_label_propagation_op_increment_op:
  fixes  os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and sg :: \<open>(3, 2, (nat, nat) myprod) subgraph\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  defines
    \<open>INV \<equiv> \<lambda> os_label_prop os L.
    os_label_prop = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr> \<and>
    label_prob_ty2_check os_label_prop (curry cbufs 1) \<and>
    (\<forall>n. intsum (os n) = (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))) \<and>
    dataplane_tracker_inv os cbufs sg \<and>
    (\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    (\<forall> t \<in> set (timestamps os_label_prop). \<not> frontier_less_equal (exit_scope myfst (front (os 1) 0 + front (os 1) 1)) t \<longrightarrow> labels_stable (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    (\<forall> t \<in> myfst ` snd ` set (input (os 1) 0) \<union> myfst ` snd ` set (input (os 1) 1). frontier_less_equal (exit_scope myfst (front (os 1) 1)) t) \<and>
    label_prop_upd_inv os_label_prop \<and> input_ocaps_inv (os 1)\<close>
    (* Might be needed: \<open>input_ocaps_inv (os 2)
  \<and> wf_label_prop_updates os_label_prop (set (outpu (os 2) 1 @ cbufs (1, 1) @ input os_label_prop 1)
    \<union> set (map (\<lambda>(d, t). (d, t + MyPair 0 1)) (outpu os_label_prop 1 @ cbufs (2, 1) @ input (os 2) 1)))\<close> *)
  assumes \<open>summ sg = antichain_from_list \<circ>\<circ> raw_summary \<and> nxt sg = graph_to_nxt (summ sg)\<close>
    \<open>INV os_label_prop os L\<close>
    \<open>T \<noteq> []\<close>
  shows  "\<exists> os_label_prop' os' L'. (step Tau)\<^sup>*\<^sup>*
     (loop_op loop_wire (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
       (comp_map
         (comp_op
           comp_wire
           (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
           (logic_map (1 :: 3) (label_propagation_op (os_label_prop :: (nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state)))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ((os 2) :: (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state))))))
       (loop_op loop_wire ((case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))(Inr (2,1) := [], Inr (1,1) := []))
       (comp_map
         (comp_op
           comp_wire
           ((case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))(Inr (2,1) := [], Inr (1,1) := []))
           (logic_map (1 :: 3) (label_propagation_op (os_label_prop')))
           (logic_map (2 :: 3) (increment_op 1 1 (MyPair 0 (Suc 0)) ((os' 2))))))) \<and>
       INV os_label_prop' os' L'"
  using assms(3) apply -
  apply (induct "labels_measure (all_edges os_label_prop (Max (set T))) (min_label os_label_prop (Max (set T)))" arbitrary: os_label_prop os L rule: less_induct)
  subgoal premises prems for os_label_prop os L
    apply (intro exI conjI)
     apply (rule rtranclp_trans)
    using prems
    oops *)


subsection \<open>Frame and produced-progress facts for loop_updates\<close>




lemma fst_snd_loop_updates_cbufs_irrelevant[simp]:
  fixes k :: \<open>3 \<times> 2\<close>
  assumes k11: \<open>k \<noteq> ((1 :: 3), (1 :: 2))\<close>
    and k21: \<open>k \<noteq> ((2 :: 3), (1 :: 2))\<close>
  shows \<open>fst (snd (loop_updates (cbufs(k := X)) os_label_prop os)) =
    fst (snd (loop_updates cbufs os_label_prop os))\<close>
proof (induct cbufs os_label_prop os arbitrary: X rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  let ?cbufs_update = \<open>cbufs(k := X)\<close>
  show ?case
  proof (cases ?good)
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have step1_update:
      \<open>label_prop_input1_loop_updates ?cbufs_update os_label_prop os =
        (cbufs1(k := X), os_label_prop1, os1)\<close>
      using step1 k11 k21
      unfolding label_prop_input1_loop_updates_def Let_def
      by (auto simp add: fun_upd_twist split: prod.splits)
    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      show ?thesis
        by (subst loop_updates.simps, subst (2) loop_updates.simps)
          (use \<open>?good\<close> step1 step1_update True k11 k21 in simp)
    next
      case False
      have rec:
        \<open>fst (snd (loop_updates (cbufs1(k := X)) os_label_prop1 os1)) =
          fst (snd (loop_updates cbufs1 os_label_prop1 os1))\<close>
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False])
      show ?thesis
        by (subst loop_updates.simps, subst (2) loop_updates.simps)
          (use \<open>?good\<close> step1 step1_update False rec k11 k21 in simp)

    qed
  next
    case False
    have not_good_update:
      \<open>\<not> (label_prop_upd_inv os_label_prop \<and>
        (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
        wf_label_prop_updates os_label_prop
          (set (input os_label_prop 1) \<union>
           set (?cbufs_update (1, 1) @ outpu (os 2) 1 @
                map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                  (input (os 2) 1 @ ?cbufs_update (2, 1) @ outpu os_label_prop 1))))\<close>
      using False k11 k21 by simp
    show ?thesis
      by (subst loop_updates.simps, subst (2) loop_updates.simps)
        (simp only: not_good_update False if_False fst_conv snd_conv)
  qed
qed



lemma snd_snd_loop_updates_unchanged[simp]:
  assumes n2: \<open>n \<noteq> (2 :: 3)\<close>
  shows \<open>snd (snd (loop_updates cbufs os_label_prop os)) n = os n\<close>
  using n2
  apply (induct cbufs os_label_prop os rule: loop_updates.induct)
  apply (subst loop_updates.simps)
  apply (clarsimp split: prod.splits)
  apply (metis prod.sel(2) snd_snd_label_prop_input1_loop_updates_unchanged)
  done


lemma fst_snd_loop_updates_update[simp]:
  assumes n2: \<open>n \<noteq> (2 :: 3)\<close>
  shows \<open>fst (snd (loop_updates cbufs os_label_prop (os(n := X)))) =
    fst (snd (loop_updates cbufs os_label_prop os))\<close>
proof (induct cbufs os_label_prop os arbitrary: X rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  show ?case
  proof (cases ?good)
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have step1_update:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop (os(n := X)) =
        (cbufs1, os_label_prop1, os1(n := X))\<close>
      using step1 n2
      unfolding label_prop_input1_loop_updates_def Let_def
      by (auto simp add: fun_upd_twist split: prod.splits)
    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      show ?thesis
        by (subst loop_updates.simps, subst (2) loop_updates.simps)
          (use \<open>?good\<close> step1 step1_update True n2 in simp)
    next
      case False
      have rec:
        \<open>fst (snd (loop_updates cbufs1 os_label_prop1 (os1(n := X)))) =
          fst (snd (loop_updates cbufs1 os_label_prop1 os1))\<close>
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False])
      show ?thesis
        by (subst loop_updates.simps, subst (2) loop_updates.simps)
          (use \<open>?good\<close> step1 step1_update False rec n2 in simp)
    qed
  next
    case False
    have not_good_update:
      \<open>\<not> (label_prop_upd_inv os_label_prop \<and>
        (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
        wf_label_prop_updates os_label_prop
          (set (input os_label_prop 1) \<union>
           set (cbufs (1, 1) @ outpu ((os(n := X)) 2) 1 @
                map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                  (input ((os(n := X)) 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))))\<close>
      using False n2 by simp
    show ?thesis
      by (subst loop_updates.simps, subst (2) loop_updates.simps)
        (simp only: not_good_update False if_False fst_conv snd_conv)
  qed
qed




lemma snd_snd_loop_updates_update2:
  assumes n2: \<open>n \<noteq> (2 :: 3)\<close>
  shows \<open>snd (snd (loop_updates cbufs os_label_prop (os(n := X)))) 2 =
    snd (snd (loop_updates cbufs os_label_prop os)) 2\<close>
proof (induct cbufs os_label_prop os arbitrary: X rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  show ?case
  proof (cases ?good)
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have step1_update:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop (os(n := X)) =
        (cbufs1, os_label_prop1, os1(n := X))\<close>
      using step1 n2
      unfolding label_prop_input1_loop_updates_def Let_def
      by (auto simp add: fun_upd_twist split: prod.splits)
    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      show ?thesis
        by (subst loop_updates.simps, subst (2) loop_updates.simps)
          (use \<open>?good\<close> step1 step1_update True n2 in simp)
    next
      case False
      have rec:
        \<open>snd (snd (loop_updates cbufs1 os_label_prop1 (os1(n := X)))) 2 =
          snd (snd (loop_updates cbufs1 os_label_prop1 os1)) 2\<close>
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False])
      show ?thesis
        by (subst loop_updates.simps, subst (2) loop_updates.simps)
          (use \<open>?good\<close> step1 step1_update False rec n2 in simp)
    qed
  next
    case False
    have not_good_update:
      \<open>\<not> (label_prop_upd_inv os_label_prop \<and>
        (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
        wf_label_prop_updates os_label_prop
          (set (input os_label_prop 1) \<union>
           set (cbufs (1, 1) @ outpu ((os(n := X)) 2) 1 @
                map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                  (input ((os(n := X)) 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))))\<close>
      using False n2 by simp
    have os2_update: \<open>(os(n := X)) 2 = os 2\<close>
      using n2 by simp
    show ?thesis
      by (subst loop_updates.simps, subst (2) loop_updates.simps)
        (simp only: not_good_update False if_False fst_conv snd_conv os2_update)


  qed
qed


lemma snd_snd_loop_updates_update[simp]:
  assumes nm: \<open>n \<noteq> m\<close>
  shows \<open>snd (snd (loop_updates cbufs os_label_prop (os(n := X)))) m =
    snd (snd (loop_updates cbufs os_label_prop os)) m\<close>
proof (cases \<open>m = (2 :: 3)\<close>)
  case True
  then show ?thesis
    using nm snd_snd_loop_updates_update2 by simp
next
  case False
  then show ?thesis
    using nm by simp
qed



lemma snd_snd_loop_updates_cbufs_irrelevant2:
  fixes k :: \<open>3 \<times> 2\<close>
  assumes k11: \<open>k \<noteq> ((1 :: 3), (1 :: 2))\<close>
    and k21: \<open>k \<noteq> ((2 :: 3), (1 :: 2))\<close>
  shows \<open>snd (snd (loop_updates (cbufs(k := X)) os_label_prop os)) 2 =
    snd (snd (loop_updates cbufs os_label_prop os)) 2\<close>
proof (induct cbufs os_label_prop os arbitrary: X rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  let ?cbufs_update = \<open>cbufs(k := X)\<close>
  show ?case
  proof (cases ?good)
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have step1_update:
      \<open>label_prop_input1_loop_updates ?cbufs_update os_label_prop os =
        (cbufs1(k := X), os_label_prop1, os1)\<close>
      using step1 k11 k21
      unfolding label_prop_input1_loop_updates_def Let_def
      by (auto simp add: fun_upd_twist split: prod.splits)
    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      show ?thesis
        by (subst loop_updates.simps, subst (2) loop_updates.simps)
          (use \<open>?good\<close> step1 step1_update True k11 k21 in simp)
    next
      case False
      have rec:
        \<open>snd (snd (loop_updates (cbufs1(k := X)) os_label_prop1 os1)) 2 =
          snd (snd (loop_updates cbufs1 os_label_prop1 os1)) 2\<close>
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False])
      show ?thesis
        by (subst loop_updates.simps, subst (2) loop_updates.simps)
          (use \<open>?good\<close> step1 step1_update False rec k11 k21 in simp)
    qed
  next
    case False
    have not_good_update:
      \<open>\<not> (label_prop_upd_inv os_label_prop \<and>
        (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
        wf_label_prop_updates os_label_prop
          (set (input os_label_prop 1) \<union>
           set (?cbufs_update (1, 1) @ outpu (os 2) 1 @
                map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                  (input (os 2) 1 @ ?cbufs_update (2, 1) @ outpu os_label_prop 1))))\<close>
      using False k11 k21 by simp
    show ?thesis
      by (subst loop_updates.simps, subst (2) loop_updates.simps)
        (simp only: not_good_update False if_False fst_conv snd_conv)
  qed
qed


lemma snd_snd_loop_updates_cbufs_irrelevant[simp]:
  fixes k :: \<open>3 \<times> 2\<close>
  assumes k11: \<open>k \<noteq> ((1 :: 3), (1 :: 2))\<close>
    and k21: \<open>k \<noteq> ((2 :: 3), (1 :: 2))\<close>
  shows \<open>snd (snd (loop_updates (cbufs(k := X)) os_label_prop os)) =
    snd (snd (loop_updates cbufs os_label_prop os))\<close>
proof (rule ext)
  fix n :: 3
  show \<open>snd (snd (loop_updates (cbufs(k := X)) os_label_prop os)) n =
    snd (snd (loop_updates cbufs os_label_prop os)) n\<close>
  proof (cases \<open>n = (2 :: 3)\<close>)
    case True
    then show ?thesis
      using k11 k21 snd_snd_loop_updates_cbufs_irrelevant2 by simp
  next
    case False
    then show ?thesis
      by simp
  qed
qed

lemma snd_snd_loop_updates_cbufs11:
  \<open>snd (snd (loop_updates (cbufs(((1 :: 3), (1 :: 2)) := X)) os_label_prop os)) =
    snd (snd (loop_updates cbufs os_label_prop os))\<close>
  oops







lemma fst_loop_updates[simp]:
  \<open>fst (loop_updates cbufs os_label_prop os) = cbufs((2, 1) := [], (1, 1) := [])\<close>
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>

  show ?case
  proof (cases ?good)
    case False
    show ?thesis
      by (subst loop_updates.simps) (simp only: False if_False fst_conv)


  next
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have cbufs1_eq: \<open>cbufs1 = cbufs((2, 1) := [], (1, 1) := [])\<close>
      using step1
      unfolding label_prop_input1_loop_updates_def Let_def
      by (auto split: prod.splits)
    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 True cbufs1_eq in simp)
    next
      case False
      have rec:
        \<open>fst (loop_updates cbufs1 os_label_prop1 os1) =
          cbufs1((2, 1) := [], (1, 1) := [])\<close>
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False])
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 False rec cbufs1_eq in simp)
    qed
  qed
qed


lemma ocaps_0_fst_snd_loop_updates:
  assumes H: \<open>intsum os_label_prop (1 :: 2) (0 :: 2) = []\<close>
  shows \<open>ocaps (fst (snd (loop_updates cbufs os_label_prop os))) 0 = ocaps os_label_prop 0\<close>
  using H
proof (induct cbufs os_label_prop os rule: loop_updates.induct)

  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>

  show ?case
  proof (cases ?good)
    case False
    show ?thesis
      by (subst loop_updates.simps) (simp only: False if_False fst_conv snd_conv)
  next
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have os_label_prop1_eq:
      \<open>os_label_prop1 = fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))\<close>
      using step1 by simp
    have no_loop1: \<open>intsum os_label_prop1 (1 :: 2) (0 :: 2) = []\<close>
      using "1.prems" os_label_prop1_eq by simp
    have ocaps1: \<open>ocaps os_label_prop1 0 = ocaps os_label_prop 0\<close>
      using "1.prems" os_label_prop1_eq by simp

    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 True ocaps1 in simp)
    next
      case False
      have rec:
        \<open>ocaps (fst (snd (loop_updates cbufs1 os_label_prop1 os1))) 0 = ocaps os_label_prop1 0\<close>
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False no_loop1])
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 False rec ocaps1 in simp)
    qed
  qed
qed


lemma ocaps_1_fst_snd_loop_updates_empty:
  assumes INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
    and input0_empty: \<open>input os_label_prop (0 :: 2) = []\<close>
    and no_stale: \<open>input os_label_prop (1 :: 2) @
        cbufs (1, 1) @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1) = [] \<Longrightarrow>
        ocaps os_label_prop (1 :: 2) = []\<close>
  shows \<open>ocaps (fst (snd (loop_updates cbufs os_label_prop os))) (1 :: 2) = []\<close>
  using INV LABELS WF EN1 DE1 input0_empty no_stale
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop (set (input os_label_prop 1) \<union> set ?msgs)\<close>
  have good: ?good
    using "1.prems" by simp
  obtain cbufs1 os_label_prop1 os1 where step1:
    \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
  have one_step_ocaps:
    \<open>ocaps (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) (1 :: 2) = []\<close>
    by (rule ocaps_1_fst_snd_label_prop_input1_loop_updates_empty[OF "1.prems"(6) "1.prems"(7)])
  have ocaps1_empty: \<open>ocaps os_label_prop1 (1 :: 2) = []\<close>
    using one_step_ocaps step1 by simp
  have INV1: \<open>label_prop_upd_inv os_label_prop1\<close>
    by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] "1.prems"(1) "1.prems"(3)])
  have LABELS1:
    \<open>\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)\<close>
    by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] "1.prems"(1) "1.prems"(3) "1.prems"(2)])
  have EN1_1: \<open>en1 os_label_prop1 = Inl\<close>
    using label_prop_input1_loop_updates_en1_label[OF step1[symmetric]] "1.prems"(4)
    by simp
  have DE1_1: \<open>de1 os_label_prop1 = projl\<close>
    using label_prop_input1_loop_updates_de1_label[OF step1[symmetric]] "1.prems"(5)
    by simp
  have input0_1: \<open>input os_label_prop1 (0 :: 2) = []\<close>
    using label_prop_input1_loop_updates_input_label_0[OF step1[symmetric]] "1.prems"(6)
    by simp
  have input1_empty: \<open>input os_label_prop1 (1 :: 2) = []\<close>
    by (rule label_prop_input1_loop_updates_input_label_1[OF step1[symmetric]])
  have WF1_msgs:
    \<open>wf_label_prop_updates os_label_prop1
      (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    by (rule label_prop_input1_loop_updates_msgs_invI
        [OF step1[symmetric] "1.prems"(4) "1.prems"(5) "1.prems"(1) "1.prems"(2) "1.prems"(3)])
  have WF1:
    \<open>wf_label_prop_updates os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    using WF1_msgs input1_empty by simp
  have no_stale1:
    \<open>input os_label_prop1 (1 :: 2) @
        cbufs1 (1, 1) @ outpu (os1 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1) = [] \<Longrightarrow>
        ocaps os_label_prop1 (1 :: 2) = []\<close>
    using ocaps1_empty by simp
  show ?case
  proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
    case True
    show ?thesis
      by (subst loop_updates.simps) (use good step1 True ocaps1_empty in simp)
  next
    case False
    have rec:
      \<open>ocaps (fst (snd (loop_updates cbufs1 os_label_prop1 os1))) (1 :: 2) = []\<close>
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False
            INV1 LABELS1 WF1 EN1_1 DE1_1 input0_1 no_stale1])
    show ?thesis
      by (subst loop_updates.simps) (use good step1 False rec in simp)
  qed
qed


lemma ocaps_1_snd_snd_loop_updates_empty:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes INTSUM: \<open>\<forall>m. intsum ((os(1 := op_state_base os_label_prop)) m) =
      (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
  shows \<open>ocaps ((snd (snd (loop_updates cbufs os_label_prop os))) 2) (1 :: 2) = []\<close>
  using INTSUM INV LABELS WF EN1 DE1
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop (set (input os_label_prop 1) \<union> set ?msgs)\<close>
  have good: ?good
    using "1.prems" by simp
  obtain cbufs1 os_label_prop1 os1 where step1:
    \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
  have intsum_os2_11:
    \<open>intsum (os (2 :: 3)) (1 :: 2) (1 :: 2) = [MyPair 0 (Suc 0)]\<close>
    using "1.prems"(1)[rule_format, of \<open>2 :: 3\<close>]
    by (simp add: raw_summary_def op_state_base_def)
  have one_step_ocaps:
    \<open>ocaps ((snd (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) 2) (1 :: 2) = []\<close>
    by (rule ocaps_1_snd_snd_label_prop_input1_loop_updates_empty
        [where os=os and os_label_prop=os_label_prop and cbufs=cbufs, OF intsum_os2_11])
  have ocaps1_empty: \<open>ocaps (os1 2) (1 :: 2) = []\<close>
    using one_step_ocaps step1 by simp

  have INTSUM1:
    \<open>\<forall>m. intsum ((os1(1 := op_state_base os_label_prop1)) m) =
      (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
    using label_prop_input1_loop_updates_intsum_corrected[OF step1[symmetric]] "1.prems"(1)
    by simp
  have INV1: \<open>label_prop_upd_inv os_label_prop1\<close>
    by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] "1.prems"(2) "1.prems"(4)])
  have LABELS1:
    \<open>\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)\<close>
    by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] "1.prems"(2) "1.prems"(4) "1.prems"(3)])
  have EN1_1: \<open>en1 os_label_prop1 = Inl\<close>
    using label_prop_input1_loop_updates_en1_label[OF step1[symmetric]] "1.prems"(5)
    by simp
  have DE1_1: \<open>de1 os_label_prop1 = projl\<close>
    using label_prop_input1_loop_updates_de1_label[OF step1[symmetric]] "1.prems"(6)
    by simp
  have input1_empty: \<open>input os_label_prop1 (1 :: 2) = []\<close>
    by (rule label_prop_input1_loop_updates_input_label_1[OF step1[symmetric]])
  have WF1_msgs:
    \<open>wf_label_prop_updates os_label_prop1
      (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    by (rule label_prop_input1_loop_updates_msgs_invI
        [OF step1[symmetric] "1.prems"(5) "1.prems"(6) "1.prems"(2) "1.prems"(3) "1.prems"(4)])
  have WF1:
    \<open>wf_label_prop_updates os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    using WF1_msgs input1_empty by simp
  show ?case
  proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
    case True
    show ?thesis
      by (subst loop_updates.simps) (use good step1 True ocaps1_empty in simp)
  next
    case False
    have rec:
      \<open>ocaps ((snd (snd (loop_updates cbufs1 os_label_prop1 os1))) 2) (1 :: 2) = []\<close>
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False
            INTSUM1 INV1 LABELS1 WF1 EN1_1 DE1_1])
    show ?thesis
      by (subst loop_updates.simps) (use good step1 False rec in simp)
  qed
qed


lemma outpu_0_fst_snd_loop_updates[simp]:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  shows \<open>outpu (fst (snd (loop_updates cbufs os_label_prop os))) (0 :: 2) =
    outpu os_label_prop 0\<close>
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  show ?case
  proof (cases ?good)
    case False
    have loop_eq:
      \<open>loop_updates cbufs os_label_prop os =
        (cbufs((2, 1) := [], (1, 1) := []), os_label_prop, os)\<close>
      by (subst loop_updates.simps) (simp only: False if_False)
    show ?thesis
      using loop_eq by simp
  next
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have step0':
      \<open>outpu (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) (0 :: 2) =
        outpu os_label_prop1 0\<close>
      using step1 by simp
    have step0: \<open>outpu os_label_prop1 (0 :: 2) = outpu os_label_prop 0\<close>
      using step0'[symmetric] by simp

    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 True step0 in simp)
    next
      case False
      have rec:
        \<open>outpu (fst (snd (loop_updates cbufs1 os_label_prop1 os1))) (0 :: 2) =
          outpu os_label_prop1 0\<close>
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False])
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 False rec step0 in simp)
    qed
  qed
qed


lemma outpu_1_fst_snd_loop_updates_empty:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
  shows \<open>outpu (fst (snd (loop_updates cbufs os_label_prop os))) (1 :: 2) = []\<close>
  using INV LABELS WF EN1 DE1
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop (set (input os_label_prop 1) \<union> set ?msgs)\<close>
  have good: ?good
    using "1.prems" by simp
  obtain cbufs1 os_label_prop1 os1 where step1:
    \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
  have INV1: \<open>label_prop_upd_inv os_label_prop1\<close>
    by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] "1.prems"(1) "1.prems"(3)])
  have LABELS1:
    \<open>\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)\<close>
    by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] "1.prems"(1) "1.prems"(3) "1.prems"(2)])
  have EN1_1: \<open>en1 os_label_prop1 = Inl\<close>
    using label_prop_input1_loop_updates_en1_label[OF step1[symmetric]] "1.prems"(4)
    by simp
  have DE1_1: \<open>de1 os_label_prop1 = projl\<close>
    using label_prop_input1_loop_updates_de1_label[OF step1[symmetric]] "1.prems"(5)
    by simp
  have input1_empty: \<open>input os_label_prop1 (1 :: 2) = []\<close>
    by (rule label_prop_input1_loop_updates_input_label_1[OF step1[symmetric]])
  have WF1_msgs:
    \<open>wf_label_prop_updates os_label_prop1
      (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    by (rule label_prop_input1_loop_updates_msgs_invI
        [OF step1[symmetric] "1.prems"(4) "1.prems"(5) "1.prems"(1) "1.prems"(2) "1.prems"(3)])
  have WF1:
    \<open>wf_label_prop_updates os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    using WF1_msgs input1_empty by simp
  show ?case
  proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
    case True
    show ?thesis
      by (subst loop_updates.simps) (use good step1 True in simp)
  next
    case False
    have rec:
      \<open>outpu (fst (snd (loop_updates cbufs1 os_label_prop1 os1))) (1 :: 2) = []\<close>
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False
            INV1 LABELS1 WF1 EN1_1 DE1_1])
    show ?thesis
      by (subst loop_updates.simps) (use good step1 False rec in simp)
  qed
qed


lemma outpu_1_snd_snd_loop_updates_empty:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
  shows \<open>outpu ((snd (snd (loop_updates cbufs os_label_prop os))) 2) (1 :: 2) = []\<close>
  using INV LABELS WF EN1 DE1
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop (set (input os_label_prop 1) \<union> set ?msgs)\<close>
  have good: ?good
    using "1.prems" by simp
  obtain cbufs1 os_label_prop1 os1 where step1:
    \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
  have outpu2_empty: \<open>outpu (os1 2) (1 :: 2) = []\<close>
    by (rule label_prop_input1_loop_updates_outpu_os2_1[OF step1[symmetric]])
  have INV1: \<open>label_prop_upd_inv os_label_prop1\<close>
    by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] "1.prems"(1) "1.prems"(3)])
  have LABELS1:
    \<open>\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)\<close>
    by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] "1.prems"(1) "1.prems"(3) "1.prems"(2)])
  have EN1_1: \<open>en1 os_label_prop1 = Inl\<close>
    using label_prop_input1_loop_updates_en1_label[OF step1[symmetric]] "1.prems"(4)
    by simp
  have DE1_1: \<open>de1 os_label_prop1 = projl\<close>
    using label_prop_input1_loop_updates_de1_label[OF step1[symmetric]] "1.prems"(5)
    by simp
  have input1_empty: \<open>input os_label_prop1 (1 :: 2) = []\<close>
    by (rule label_prop_input1_loop_updates_input_label_1[OF step1[symmetric]])
  have WF1_msgs:
    \<open>wf_label_prop_updates os_label_prop1
      (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    by (rule label_prop_input1_loop_updates_msgs_invI
        [OF step1[symmetric] "1.prems"(4) "1.prems"(5) "1.prems"(1) "1.prems"(2) "1.prems"(3)])
  have WF1:
    \<open>wf_label_prop_updates os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    using WF1_msgs input1_empty by simp
  show ?case
  proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
    case True
    show ?thesis
      by (subst loop_updates.simps) (use good step1 True outpu2_empty in simp)
  next
    case False
    have rec:
      \<open>outpu ((snd (snd (loop_updates cbufs1 os_label_prop1 os1))) 2) (1 :: 2) = []\<close>
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False
            INV1 LABELS1 WF1 EN1_1 DE1_1])
    show ?thesis
      by (subst loop_updates.simps) (use good step1 False rec in simp)
  qed
qed


lemma input_1_snd_snd_loop_updates_empty:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
  shows \<open>input ((snd (snd (loop_updates cbufs os_label_prop os))) 2) (1 :: 2) = []\<close>
  using INV LABELS WF EN1 DE1
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop (set (input os_label_prop 1) \<union> set ?msgs)\<close>
  have good: ?good
    using "1.prems" by simp
  obtain cbufs1 os_label_prop1 os1 where step1:
    \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
  have input2_empty: \<open>input (os1 2) (1 :: 2) = []\<close>
    by (rule label_prop_input1_loop_updates_input_os2_1[OF step1[symmetric]])
  have INV1: \<open>label_prop_upd_inv os_label_prop1\<close>
    by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] "1.prems"(1) "1.prems"(3)])
  have LABELS1:
    \<open>\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)\<close>
    by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] "1.prems"(1) "1.prems"(3) "1.prems"(2)])
  have EN1_1: \<open>en1 os_label_prop1 = Inl\<close>
    using label_prop_input1_loop_updates_en1_label[OF step1[symmetric]] "1.prems"(4)
    by simp
  have DE1_1: \<open>de1 os_label_prop1 = projl\<close>
    using label_prop_input1_loop_updates_de1_label[OF step1[symmetric]] "1.prems"(5)
    by simp
  have input1_empty: \<open>input os_label_prop1 (1 :: 2) = []\<close>
    by (rule label_prop_input1_loop_updates_input_label_1[OF step1[symmetric]])
  have WF1_msgs:
    \<open>wf_label_prop_updates os_label_prop1
      (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    by (rule label_prop_input1_loop_updates_msgs_invI
        [OF step1[symmetric] "1.prems"(4) "1.prems"(5) "1.prems"(1) "1.prems"(2) "1.prems"(3)])
  have WF1:
    \<open>wf_label_prop_updates os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    using WF1_msgs input1_empty by simp
  show ?case
  proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
    case True
    show ?thesis
      by (subst loop_updates.simps) (use good step1 True input2_empty in simp)
  next
    case False
    have rec:
      \<open>input ((snd (snd (loop_updates cbufs1 os_label_prop1 os1))) 2) (1 :: 2) = []\<close>
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False
            INV1 LABELS1 WF1 EN1_1 DE1_1])
    show ?thesis
      by (subst loop_updates.simps) (use good step1 False rec in simp)
  qed
qed


lemma input_0_fst_snd_loop_updates:
  \<open>input (fst (snd (loop_updates cbufs os_label_prop os))) (0 :: 2) =
    input os_label_prop (0 :: 2)\<close>
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  show ?case
  proof (cases ?good)
    case False
    show ?thesis
      by (subst loop_updates.simps) (simp only: False if_False fst_conv snd_conv)
  next
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have input0_1: \<open>input os_label_prop1 (0 :: 2) = input os_label_prop (0 :: 2)\<close>
      using label_prop_input1_loop_updates_input_label_0[OF step1[symmetric]]
      by simp
    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 True input0_1 in simp)
    next
      case False
      have rec:
        \<open>input (fst (snd (loop_updates cbufs1 os_label_prop1 os1))) (0 :: 2) =
          input os_label_prop1 (0 :: 2)\<close>
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False])
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 False rec input0_1 in simp)
    qed
  qed
qed


lemma input_1_fst_snd_loop_updates_empty:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
  shows \<open>input (fst (snd (loop_updates cbufs os_label_prop os))) (1 :: 2) = []\<close>
  using INV LABELS WF EN1 DE1
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop (set (input os_label_prop 1) \<union> set ?msgs)\<close>
  have good: ?good
    using "1.prems" by simp
  obtain cbufs1 os_label_prop1 os1 where step1:
    \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
  have input1_empty: \<open>input os_label_prop1 (1 :: 2) = []\<close>
    by (rule label_prop_input1_loop_updates_input_label_1[OF step1[symmetric]])
  have INV1: \<open>label_prop_upd_inv os_label_prop1\<close>
    by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] "1.prems"(1) "1.prems"(3)])
  have LABELS1:
    \<open>\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)\<close>
    by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] "1.prems"(1) "1.prems"(3) "1.prems"(2)])
  have EN1_1: \<open>en1 os_label_prop1 = Inl\<close>
    using label_prop_input1_loop_updates_en1_label[OF step1[symmetric]] "1.prems"(4)
    by simp
  have DE1_1: \<open>de1 os_label_prop1 = projl\<close>
    using label_prop_input1_loop_updates_de1_label[OF step1[symmetric]] "1.prems"(5)
    by simp
  have WF1_msgs:
    \<open>wf_label_prop_updates os_label_prop1
      (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    by (rule label_prop_input1_loop_updates_msgs_invI
        [OF step1[symmetric] "1.prems"(4) "1.prems"(5) "1.prems"(1) "1.prems"(2) "1.prems"(3)])
  have WF1:
    \<open>wf_label_prop_updates os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
    using WF1_msgs input1_empty by simp
  show ?case
  proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
    case True
    show ?thesis
      by (subst loop_updates.simps) (use good step1 True input1_empty in simp)
  next
    case False
    have rec:
      \<open>input (fst (snd (loop_updates cbufs1 os_label_prop1 os1))) (1 :: 2) = []\<close>
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False
            INV1 LABELS1 WF1 EN1_1 DE1_1])
    show ?thesis
      by (subst loop_updates.simps) (use good step1 False rec in simp)
  qed
qed


lemma label_prop_collected_edge_payloads_image_eq:
  assumes chan_zero:
    \<open>\<And>x. x \<in> set xs \<union> set ys \<union> set zs \<Longrightarrow> mysnd (snd x) = 0\<close>
    and stream_zero:
    \<open>\<And>t' d. Data t' d \<in> set evs \<Longrightarrow> mysnd t' = 0\<close>
    and t_zero: \<open>mysnd t = 0\<close>
  shows
    \<open>({d. \<exists>t'. (Data t' d \<in> (\<lambda>(x, t'). Data t' (projl x)) ` set xs \<or>
                 Data t' d \<in> (\<lambda>(x, t'). Data t' (projl x)) ` set ys \<or>
                 Data t' d \<in> (\<lambda>(x, t'). Data t' (projl x)) ` set zs) \<and> t' \<le> t} \<union>
       {d. \<exists>t'. Data t' d \<in> set evs \<and> t' \<le> t}) =
      (\<lambda>x. projl (fst x)) `
        ((set xs \<union> (set ys \<union> (set zs \<union>
          (\<lambda>x. case x of Data t d \<Rightarrow> (Inl d, t)) ` {x \<in> set evs. is_Data x}))) \<inter>
          {x. myfst (snd x) \<le> myfst t})\<close>
  using chan_zero stream_zero t_zero
  apply (auto split: event.splits)
  subgoal for a b
    apply (rule image_eqI[where x=\<open>(a, b)\<close>])
    apply simp
    apply (force intro: myfst_le_if_myprod_le_mysnd_zero)
    done
  subgoal for a b
    apply (rule image_eqI[where x=\<open>(a, b)\<close>])
    apply simp
    apply (force intro: myfst_le_if_myprod_le_mysnd_zero)
    done
  subgoal for a b
    apply (rule image_eqI[where x=\<open>(a, b)\<close>])
    apply simp
    apply (force intro: myfst_le_if_myprod_le_mysnd_zero)
    done
  subgoal for x t'
    apply (rule image_eqI[where x=\<open>(Inl x, t')\<close>])
    apply simp
    apply (force intro: myfst_le_if_myprod_le_mysnd_zero)
    done
  subgoal for a b
    apply (rule exI[of _ b])
    apply (intro conjI)
    apply (rule disjI1)
    apply (rule image_eqI[where x=\<open>(a, b)\<close>])
    apply simp
    apply simp
    apply (force intro: myprod_le_if_myfst_le_mysnd_zero)
    done
  subgoal for a b
    apply (rule exI[of _ b])
    apply (intro conjI)
    apply (rule disjI2)
    apply (rule disjI1)
    apply (rule image_eqI[where x=\<open>(a, b)\<close>])
    apply simp
    apply simp
    apply (force intro: myprod_le_if_myfst_le_mysnd_zero)
    done
  subgoal for a b
    apply (rule exI[of _ b])
    apply (intro conjI)
    apply (rule disjI2)
    apply (rule disjI2)
    apply (rule image_eqI[where x=\<open>(a, b)\<close>])
    apply simp
    apply simp
    apply (force intro: myprod_le_if_myfst_le_mysnd_zero)
    done
  subgoal for b x
    apply (drule spec[of _ b])
    apply (drule mp)
    apply assumption
    apply (erule notE)
    apply (rule myprod_le_if_myfst_le_mysnd_zero)
    apply assumption
    apply blast
    apply assumption
    done

  done


lemma label_prop_collected_edge_payloads_ccs_eq:
  fixes A :: \<open>('a::order \<times> 'a) set\<close>
  assumes chan_zero:
    \<open>\<And>x. x \<in> set xs \<union> set ys \<union> set zs \<Longrightarrow> mysnd (snd x) = 0\<close>
    and stream_zero:
    \<open>\<And>t' d. Data t' d \<in> set evs \<Longrightarrow> mysnd t' = 0\<close>
    and t_zero: \<open>mysnd t = 0\<close>
  shows
    \<open>ccs (A \<union>
       ({d. \<exists>t'. (Data t' d \<in> (\<lambda>(x, t'). Data t' (projl x)) ` set xs \<or>
                  Data t' d \<in> (\<lambda>(x, t'). Data t' (projl x)) ` set ys \<or>
                  Data t' d \<in> (\<lambda>(x, t'). Data t' (projl x)) ` set zs) \<and> t' \<le> t} \<union>
        {d. \<exists>t'. Data t' d \<in> set evs \<and> t' \<le> t})) =
      ccs (A \<union>
       (\<Union>x\<in>((set xs \<union> (set ys \<union> (set zs \<union>
          (\<lambda>x. case x of Data t d \<Rightarrow> (Inl d, t)) ` {x \<in> set evs. is_Data x}))) \<inter>
          {x. myfst (snd x) \<le> myfst t}).
          {projl (fst x), (snd (projl (fst x)), fst (projl (fst x)))}))\<close>
  apply (subst label_prop_collected_edge_payloads_image_eq[where xs=xs and ys=ys and zs=zs and evs=evs and t=t])
  apply (blast intro: chan_zero)
  apply (blast intro: stream_zero)
  apply (rule t_zero)
  apply (rule ccs_Un_symmetric_edge_image)
  done



lemma label_prop_collected_edge_payloads_ccs_eq_ldropn:
  fixes A B :: \<open>('a::order \<times> 'a) set\<close>
  assumes chan_zero:
    \<open>\<And>x. x \<in> set xs \<union> set ys \<union> set zs \<Longrightarrow> mysnd (snd x) = 0\<close>
    and stream_zero:
    \<open>\<And>t' d. Data t' d \<in> set evs \<Longrightarrow> mysnd t' = 0\<close>
    and t_zero: \<open>mysnd t = 0\<close>
    and DD: \<open>dd = projl\<close>
  shows
    \<open>ccs ({d. \<exists>t'. (Data t' d \<in> (\<lambda>(x, t'). Data t' (projl x)) ` set xs \<or>
                  Data t' d \<in> (\<lambda>(x, t'). Data t' (projl x)) ` set ys \<or>
                  Data t' d \<in> (\<lambda>(x, t'). Data t' (projl x)) ` set zs) \<and> t' \<le> t} \<union>
        ({d. \<exists>t'. Data t' d \<in> set evs \<and> t' \<le> t} \<union> B) \<union> A) =
      ccs (B \<union> (A \<union>
        ((\<Union>(d, t')\<in>set xs. if myfst t' \<le> myfst t
            then {dd d, (snd (dd d), fst (dd d))} else {}) \<union>
         ((\<Union>(d, t')\<in>set ys. if myfst t' \<le> myfst t
             then {dd d, (snd (dd d), fst (dd d))} else {}) \<union>
          ((\<Union>(d, t')\<in>set zs. if myfst t' \<le> myfst t
              then {dd d, (snd (dd d), fst (dd d))} else {}) \<union>
           (\<Union>a\<in>{x \<in> set evs. is_Data x}.
              case case a of Data t' d \<Rightarrow> (Inl d, t') of (d, t') \<Rightarrow>
                if myfst t' \<le> myfst t
                then {dd d, (snd (dd d), fst (dd d))} else {}))))))\<close>
  apply (rule trans[of _ \<open>ccs ((B \<union> A) \<union>
      ({d. \<exists>t'. (Data t' d \<in> (\<lambda>(x, t'). Data t' (projl x)) ` set xs \<or>
                 Data t' d \<in> (\<lambda>(x, t'). Data t' (projl x)) ` set ys \<or>
                 Data t' d \<in> (\<lambda>(x, t'). Data t' (projl x)) ` set zs) \<and> t' \<le> t} \<union>
       {d. \<exists>t'. Data t' d \<in> set evs \<and> t' \<le> t}))\<close>])
  subgoal
    by (rule arg_cong[where f=ccs]) auto
  apply (rule trans[OF label_prop_collected_edge_payloads_ccs_eq])
  apply (blast intro: chan_zero)
  apply (blast intro: stream_zero)
  apply (rule t_zero)
  apply (rule arg_cong[where f=ccs])
  apply (unfold DD)
  apply (simp only: Un_assoc)
  apply (rule arg_cong[where f=\<open>(\<union>) B\<close>])
  apply (rule arg_cong[where f=\<open>(\<union>) A\<close>])
  apply (simp only: Int_Un_distrib2 UN_Un)
  apply (intro arg_cong2[where f=\<open>(\<union>)\<close>])
  subgoal by (auto split: if_splits)
  subgoal by (auto split: if_splits)
  subgoal by (auto split: if_splits)
  subgoal by (auto split: event.splits if_splits)
  done















lemma initia_fst_snd_loop_updates[simp]:
  \<open>initia (fst (snd (loop_updates cbufs os_label_prop os))) = initia os_label_prop\<close>
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>

  show ?case
  proof (cases ?good)
    case False
    show ?thesis
      by (subst loop_updates.simps) (simp only: False if_False fst_conv snd_conv)
  next
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have initia1: \<open>initia os_label_prop1 = initia os_label_prop\<close>
      using label_prop_input1_loop_updates_initia_label[OF step1[symmetric]]
      by simp

    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 True initia1 in simp)
    next
      case False
      have rec:
        \<open>initia (fst (snd (loop_updates cbufs1 os_label_prop1 os1))) = initia os_label_prop1\<close>
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False])
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 False rec initia1 in simp)
    qed
  qed
qed


lemma initia_snd_snd_loop_updates2[simp]:
  \<open>initia ((snd (snd (loop_updates cbufs os_label_prop os))) (2 :: 3)) =
    initia (os (2 :: 3))\<close>
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>

  show ?case
  proof (cases ?good)
    case False
    show ?thesis
      by (subst loop_updates.simps) (simp only: False if_False fst_conv snd_conv)
  next
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have initia1: \<open>initia (os1 (2 :: 3)) = initia (os (2 :: 3))\<close>
      using label_prop_input1_loop_updates_initia_os2[OF step1[symmetric]]
      by simp

    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 True initia1 in simp)
    next
      case False
      have rec:
        \<open>initia ((snd (snd (loop_updates cbufs1 os_label_prop1 os1))) (2 :: 3)) =
          initia (os1 (2 :: 3))\<close>
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False])
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 False rec initia1 in simp)
    qed
  qed
qed


lemma input_ocaps_inv_snd_snd_loop_updates2:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes step:
    \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
    and IOC: \<open>input_ocaps_inv (os 2)\<close>
    and Intsum: \<open>\<forall>n. intsum ((os(1 := op_state_base os_label_prop)) n) =
      (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    and EN: \<open>en1 os_label_prop = Inl\<close>
    and DE: \<open>de1 os_label_prop = projl\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  shows \<open>input_ocaps_inv (os' 2)\<close>
  using step IOC Intsum EN DE INV LABELS WF
proof (induct cbufs os_label_prop os arbitrary: cbufs' os_label_prop' os' rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  note loop_step = "1.prems"(1)
  note IOC0 = "1.prems"(2)
  note Intsum0 = "1.prems"(3)
  note EN0 = "1.prems"(4)
  note DE0 = "1.prems"(5)
  note INV0 = "1.prems"(6)
  note LABELS0 = "1.prems"(7)
  note WF0 = "1.prems"(8)

  have good: \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    using INV0 LABELS0 WF0 by blast

  obtain cbufs1 os_label_prop1 os1 where step1:
    \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto

  have IOC1: \<open>input_ocaps_inv (os1 2)\<close>
    by (rule input_ocaps_inv_label_prop_input1_loop_updates_os2
        [OF step1[symmetric] IOC0 Intsum0])

  show ?case
  proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
    case True
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (subst loop_updates.simps) (use good step1 True in simp)
    show ?thesis
      using loop_step loop_eq IOC1 by simp
  next
    case False
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs1 os_label_prop1 os1\<close>
      by (subst loop_updates.simps) (use good step1 False in simp)
    have step_rec: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs1 os_label_prop1 os1\<close>
      using loop_step loop_eq by simp
    have Intsum1: \<open>\<forall>n. intsum ((os1(1 := op_state_base os_label_prop1)) n) =
      (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
      using label_prop_input1_loop_updates_intsum_corrected[OF step1[symmetric]] Intsum0 by simp
    have EN1: \<open>en1 os_label_prop1 = Inl\<close>
      using label_prop_input1_loop_updates_en1_label[OF step1[symmetric]] EN0 by simp
    have DE1: \<open>de1 os_label_prop1 = projl\<close>
      using label_prop_input1_loop_updates_de1_label[OF step1[symmetric]] DE0 by simp
    have INV1: \<open>label_prop_upd_inv os_label_prop1\<close>
      by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] INV0 WF0])
    have LABELS1: \<open>\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)\<close>
      by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] INV0 WF0 LABELS0])
    have INPUT11: \<open>input os_label_prop1 1 = []\<close>
      by (rule label_prop_input1_loop_updates_input_label_1[OF step1[symmetric]])
    have WF_msgs1: \<open>wf_label_prop_updates os_label_prop1
      (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
      by (rule label_prop_input1_loop_updates_msgs_invI
          [OF step1[symmetric] EN0 DE0 INV0 LABELS0 WF0])
    have WF1: \<open>wf_label_prop_updates os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
      using INPUT11 WF_msgs1 by simp

    show ?thesis
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False
            step_rec IOC1 Intsum1 EN1 DE1 INV1 LABELS1 WF1])
  qed
qed



lemma loop_updates_extension:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
    and ext: \<open>os_label_prop = operator_state.extend (op_state_base os_label_prop)
      \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr,
        timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
  shows \<open>os_label_prop' = operator_state.extend (op_state_base os_label_prop')
      \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr,
        timestamps = T, graph = G, vertices = V, label = label os_label_prop'\<rparr>\<close>
  using step ext
proof (induct cbufs os_label_prop os arbitrary: cbufs' os_label_prop' os' T G V L rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  show ?case
  proof (cases ?good)
    case False
    have loop_eq:
      \<open>loop_updates cbufs os_label_prop os =
        (cbufs((2, 1) := [], (1, 1) := []), os_label_prop, os)\<close>
      by (subst loop_updates.simps) (simp only: False if_False)
    then have os_label_prop'_eq: \<open>os_label_prop' = os_label_prop\<close>
      using "1.prems"(1) by simp
    have label_eq: \<open>label os_label_prop = L\<close>
      using arg_cong[OF "1.prems"(2), where f=label]
      by (simp add: op_state_base_def operator_state.defs)

    show ?thesis
      using "1.prems"(2) os_label_prop'_eq label_eq
      by (simp add: op_state_base_def operator_state.defs)

  next
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have ext1:
      \<open>os_label_prop1 = operator_state.extend (op_state_base os_label_prop1)
        \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
          en2 = Inr, de2 = projr, is_en2 = isr,
          timestamps = T, graph = G, vertices = V, label = label os_label_prop1\<rparr>\<close>
      by (rule label_prop_input1_loop_updates_extension[OF step1[symmetric] "1.prems"(2)])
    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      have loop_eq: \<open>loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 True in simp)
      show ?thesis
        using "1.prems"(1) loop_eq ext1 by simp
    next
      case False
      have loop_eq: \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs1 os_label_prop1 os1\<close>
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 False in simp)
      have step_rec: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs1 os_label_prop1 os1\<close>
        using "1.prems"(1) loop_eq by simp
      show ?thesis
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False
              step_rec ext1])
    qed
  qed
qed

lemma en2_fst_snd_loop_updates[simp]:
  \<open>en2 (fst (snd (loop_updates cbufs os_label_prop os))) = en2 os_label_prop\<close>
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>

  show ?case
  proof (cases ?good)
    case False
    show ?thesis
      by (subst loop_updates.simps) (simp only: False if_False fst_conv snd_conv)
  next
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have en2_1: \<open>en2 os_label_prop1 = en2 os_label_prop\<close>
      using label_prop_input1_loop_updates_en2_label[OF step1[symmetric]]
      by simp

    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 True en2_1 in simp)
    next
      case False
      have rec:
        \<open>en2 (fst (snd (loop_updates cbufs1 os_label_prop1 os1))) = en2 os_label_prop1\<close>
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False])
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 False rec en2_1 in simp)
    qed
  qed
qed


lemma all_edges_fst_snd_loop_updates[simp]:
  \<open>all_edges (fst (snd (loop_updates cbufs os_label_prop os))) = all_edges os_label_prop\<close>
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>

  show ?case
  proof (cases ?good)
    case False
    show ?thesis
      by (subst loop_updates.simps) (simp only: False if_False fst_conv snd_conv)
  next
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have edges1: \<open>all_edges os_label_prop1 = all_edges os_label_prop\<close>
      using step1[symmetric]
      unfolding label_prop_input1_loop_updates_def Let_def
      by simp

    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 True edges1 in simp)
    next
      case False
      have rec:
        \<open>all_edges (fst (snd (loop_updates cbufs1 os_label_prop1 os1))) = all_edges os_label_prop1\<close>
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False])
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 False rec edges1 in simp)
    qed
  qed
qed



lemma timestamps_fst_snd_loop_updates[simp]:
  \<open>timestamps (fst (snd (loop_updates cbufs os_label_prop os))) = timestamps os_label_prop\<close>
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>

  show ?case
  proof (cases ?good)
    case False
    show ?thesis
      by (subst loop_updates.simps) (simp only: False if_False fst_conv snd_conv)
  next
    case True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have os_label_prop1_eq:
      \<open>os_label_prop1 = fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))\<close>
      using step1 by simp
    have ts1: \<open>timestamps os_label_prop1 = timestamps os_label_prop\<close>
      using os_label_prop1_eq by simp

    show ?thesis
    proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
      case True
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 True ts1 in simp)
    next
      case False
      have rec:
        \<open>timestamps (fst (snd (loop_updates cbufs1 os_label_prop1 os1))) = timestamps os_label_prop1\<close>
        by (rule "1.hyps"[OF \<open>?good\<close> step1[symmetric] refl refl False])
      show ?thesis
        by (subst loop_updates.simps) (use \<open>?good\<close> step1 False rec ts1 in simp)
    qed
  qed
qed


subsection \<open>Dataplane invariant preservation for loop_updates\<close>

(* Preservation of dataplane_tracker_inv by the entire loop_updates iteration. *)

end
