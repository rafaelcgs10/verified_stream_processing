theory Label_Propagation_op_Correctness

imports
  Label_Propagation_op
  Ooo_Input_op
  Increment_op
  Set_op
  "../Correctness/Outputs"
  "../Correctness/Produces"
  "../Correctness/Mints"
  "../Correctness/Propagates"
  "../Correctness/OCapsReorder"
  "../Correctness/Consumes"
  "HOL-ex.Sketch_and_Explore"
  Dataplane.Timely_Dataflow_Op
  Dataplane.Bots
  "../Correctness/Timely_Collections"
  Dataplane.Propagation_Properties
  Dataplane.SimulationProofMethods
  Label_Propagation_op_Correctness_Extras
begin



declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del] 
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]
declare if_cong[cong]
declare list_emb_Nil2[simp del] BULK_BENQ_right_empty[simp del] BULK_BENQ_left_empty[simp del]
  filter_True[simp del] filter_False[simp del]
declare cin.rep_eq[simp del]
declare cin.rep_eq[symmetric, simp]

no_notation shiftr (infixl \<open>>>\<close> 55)
no_syntax (ASCII) "_thenM" :: \<open>['a, 'b] \<Rightarrow> 'c\<close>  (infixl \<open>>>\<close> 54)

(* label_prop_label_record_update only modifies the label field; input, intsum,
   and ocaps are untouched, so input_ocaps_inv transfers trivially. *)
lemma input_ocaps_inv_label_prop_label_record_updateI:
  assumes inv: "input_ocaps_inv os"
  shows "input_ocaps_inv (label_prop_label_record_update os event_t vertex assigned_label)"
  using inv unfolding input_ocaps_inv_def label_prop_label_record_update_def by simp


subsection \<open>Moving pending data through the loop\<close>

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

abbreviation "CONSUMES p \<equiv> fold (\<lambda>(d, t) os. consumes os p t d)"

lemma CONSUMES_CONSUMES:
  "CONSUMES p xs (CONSUMES p ys os) =
   CONSUMES p (ys @ xs) os"
  unfolding fold_consumes
  by simp


lemma intsum_CONSUMES[simp]:
  \<open>intsum (CONSUMES p xs os) = intsum os\<close>
  by (induct xs arbitrary: os) (auto split: prod.splits)

lemma vertices_CONSUMES[simp]:
  \<open>vertices (CONSUMES p xs os) = vertices os\<close>
  unfolding fold_consumes by simp

lemma label_CONSUMES[simp]:
  \<open>label (CONSUMES p xs os) = label os\<close>
  unfolding fold_consumes by simp

lemma de1_CONSUMES[simp]:
  \<open>de1 (CONSUMES p xs os) = de1 os\<close>
  by simp

lemma input_CONSUMES:
  \<open>input (CONSUMES p xs os) = (input os)(p := input os p @ xs)\<close>
  unfolding fold_consumes by simp


lemma all_vertices_CONSUMES[simp]:
  \<open>all_vertices (CONSUMES p xs os) = all_vertices os\<close>
  unfolding all_vertices_def by simp

lemma all_edges_CONSUMES[simp]:
  \<open>all_edges (CONSUMES p xs os) = all_edges os\<close>
  unfolding all_edges_def all_vertices_def neighbors_def by simp

lemma min_label_CONSUMES[simp]:
  \<open>min_label (CONSUMES p xs os) = min_label os\<close>
  unfolding min_label_def by simp

lemma timestamps_CONSUMES[simp]:
  \<open>timestamps (CONSUMES p xs os) = timestamps os\<close>
  unfolding fold_consumes by simp

lemma graph_CONSUMES[simp]:
  \<open>label_propagation_state.graph (CONSUMES p xs os) = label_propagation_state.graph os\<close>
  unfolding fold_consumes by simp


lemma label_prop_upd_inv_CONSUMES_port1I:
  assumes inv: \<open>label_prop_upd_inv os\<close>
    and xs_inv: \<open>\<And>d t. (d, t) \<in> set xs \<Longrightarrow>
      myfst t \<in> set (timestamps os) \<and>
      fst (de1 os d) \<in> all_vertices os (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow> snd (de1 os d) \<in> cc_of (all_edges os q) (fst (de1 os d)))\<close>
  shows \<open>label_prop_upd_inv (CONSUMES (1 :: 2) xs os)\<close>
proof -
  let ?os' = \<open>CONSUMES (1 :: 2) xs os\<close>
  have input_eq: \<open>set (input ?os' 1) = set (input os 1) \<union> set xs\<close>
    by (simp add: input_CONSUMES)
  show ?thesis
    using inv xs_inv
    unfolding label_prop_upd_inv_def
    apply (auto simp add: input_eq)
    done
qed

subsection \<open>One-step input-1 loop update\<close>

definition label_prop_input1_loop_updates where
  \<open>label_prop_input1_loop_updates cbufs os_label_prop os =
    (let
      cbufs' = cbufs((2, 1) := [], (1, 1) := []);
      os_label_prop_consumed =
        CONSUMES 1
          (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
          (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>);
      os_label_prop' =
        fst (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1));
      os2' =
        drop_caps
          (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2))
            (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
          (map (\<lambda>t. Cap t 1)
            (ocaps (os 2) 1 @
              map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
                (cbufs (2, 1) @ outpu os_label_prop 1)))
          \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>;
      os' = os(2 := os2')
     in (cbufs', os_label_prop', os'))\<close>

lemma label_prop_input1_loop_updates_clears[simp]:
  assumes \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>cbufs' (1, 1) = []\<close>
    and \<open>cbufs' (2, 1) = []\<close>
    and \<open>input os_label_prop' 1 = []\<close>
    and \<open>input (os' 2) 1 = []\<close>
    and \<open>outpu (os' 2) 1 = []\<close>
  using assms
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


section \<open>Label-propagation input-1 batch facts\<close>

subsection \<open>Frame facts for input-1 batches\<close>

lemma timestamps_label_prop_input1_step_state[simp]:
  \<open>timestamps (label_prop_input1_step_state os d t) = timestamps os\<close>
  unfolding label_prop_input1_step_state_def label_prop_label_record_update_def input_tl_def
  by (simp add: Let_def)

lemma all_edges_label_prop_input1_step_state[simp]:
  \<open>all_edges (label_prop_input1_step_state os d t) = all_edges os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)

lemma timestamps_fst_label_prop_input1_batched[simp]:
  \<open>timestamps (fst (label_prop_input1_batched os msgs)) = timestamps os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)

lemma all_edges_fst_label_prop_input1_batched[simp]:
  \<open>all_edges (fst (label_prop_input1_batched os msgs)) = all_edges os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)


subsection \<open>Batch member and non-empty destructors\<close>

lemma min_label_mono_time:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>t \<in> set (timestamps os)\<close>
    and \<open>t \<le> q\<close>
  shows \<open>min_label os q v \<le> min_label os t v\<close>
  using assms
  unfolding min_label_def
  by (intro Min.boundedI) auto


lemma label_prop_neighbor_batch_nonemptyD:
  fixes old_os neighbor_os label_os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_neighbor_batch old_os neighbor_os label_os relevant_times vertex new_label event_time \<noteq> []\<close>
  obtains cur_t v' where
    \<open>cur_t \<in> set relevant_times\<close>
    \<open>v' \<in> set (neighbors neighbor_os cur_t vertex)\<close>
    \<open>new_label < min_label old_os cur_t vertex\<close>
    \<open>new_label < min_label label_os cur_t v'\<close>
proof -
  let ?batch_at = \<open>\<lambda>cur_t.
    if min_label old_os cur_t vertex > new_label
    then map (\<lambda>v'. (en1 old_os (v', new_label), Cap (MyPair cur_t (mysnd event_time)) 1))
      (filter (\<lambda>v'. min_label label_os cur_t v' > new_label)
        (neighbors neighbor_os cur_t vertex))
    else []\<close>
  have \<open>\<exists>cur_t\<in>set relevant_times. ?batch_at cur_t \<noteq> []\<close>
    using assms unfolding label_prop_neighbor_batch_def Let_def
    by (auto simp: concat_eq_Nil_conv)
  then obtain cur_t where cur_t_in: \<open>cur_t \<in> set relevant_times\<close>
    and batch_at_nonempty: \<open>?batch_at cur_t \<noteq> []\<close>
    by auto

  then have old_guard: \<open>new_label < min_label old_os cur_t vertex\<close>
    by (auto split: if_splits)
  have filter_nonempty:
    \<open>filter (\<lambda>v'. new_label < min_label label_os cur_t v')
      (neighbors neighbor_os cur_t vertex) \<noteq> []\<close>
    using batch_at_nonempty old_guard by simp
  then obtain v' where filt_in:
    \<open>v' \<in> set (filter (\<lambda>v'. new_label < min_label label_os cur_t v')
      (neighbors neighbor_os cur_t vertex))\<close>
    by (cases \<open>filter (\<lambda>v'. new_label < min_label label_os cur_t v')
      (neighbors neighbor_os cur_t vertex)\<close>) auto
  then have v'_in: \<open>v' \<in> set (neighbors neighbor_os cur_t vertex)\<close>
    and label_guard: \<open>new_label < min_label label_os cur_t v'\<close>
    by auto
  show ?thesis
    using that[OF cur_t_in v'_in old_guard label_guard] .
qed





lemma label_prop_label_batch_nonemptyD:
  fixes old_os updated_os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_label_batch old_os updated_os event_t vertex new_label event_time \<noteq> []\<close>
  obtains cur_t v' where
    \<open>cur_t \<in> set (timestamps old_os)\<close>
    \<open>event_t \<le> cur_t\<close>
    \<open>v' \<in> set (neighbors old_os cur_t vertex)\<close>
    \<open>new_label < min_label old_os cur_t vertex\<close>
    \<open>new_label < min_label updated_os cur_t v'\<close>
proof -
  obtain cur_t v' where cur_t_in: \<open>cur_t \<in> set (filter ((\<le>) event_t) (timestamps old_os))\<close>
    and v'_in: \<open>v' \<in> set (neighbors old_os cur_t vertex)\<close>
    and old_guard: \<open>new_label < min_label old_os cur_t vertex\<close>
    and updated_guard: \<open>new_label < min_label updated_os cur_t v'\<close>
    using assms unfolding label_prop_label_batch_def
    by (elim label_prop_neighbor_batch_nonemptyD)
  have cur_t_ts: \<open>cur_t \<in> set (timestamps old_os)\<close>
    and event_le: \<open>event_t \<le> cur_t\<close>
    using cur_t_in by auto
  show ?thesis
    using that[OF cur_t_ts event_le v'_in old_guard updated_guard] .
qed

lemma label_prop_neighbor_batch_memberD:
  fixes old_os neighbor_os label_os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(x, cap) \<in> set (label_prop_neighbor_batch old_os neighbor_os label_os
    relevant_times vertex new_label event_time)\<close>
  obtains cur_t where
    \<open>cur_t \<in> set relevant_times\<close>
    \<open>cap = Cap (MyPair cur_t (mysnd event_time)) 1\<close>
  using assms unfolding label_prop_neighbor_batch_def
  by (auto simp: Let_def split: if_splits)

lemma label_prop_label_batch_memberD:
  fixes old_os updated_os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(x, cap) \<in> set (label_prop_label_batch old_os updated_os event_t vertex new_label event_time)\<close>
  obtains cur_t where
    \<open>cur_t \<in> set (timestamps old_os)\<close>
    \<open>event_t \<le> cur_t\<close>
    \<open>cap = Cap (MyPair cur_t (mysnd event_time)) 1\<close>
proof -
  obtain cur_t where cur_t_in: \<open>cur_t \<in> set (filter ((\<le>) event_t) (timestamps old_os))\<close>
    and cap_eq: \<open>cap = Cap (MyPair cur_t (mysnd event_time)) 1\<close>
    using assms unfolding label_prop_label_batch_def
    by (elim label_prop_neighbor_batch_memberD)
  show ?thesis
    using that cur_t_in cap_eq by auto
qed

lemma label_prop_input1_step_batch_memberD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(x, cap) \<in> set (label_prop_input1_step_batch os d t)\<close>
  obtains cur_t where
    \<open>cur_t \<in> set (timestamps os)\<close>
    \<open>myfst t \<le> cur_t\<close>
    \<open>cap = Cap (MyPair cur_t (mysnd t)) 1\<close>
proof -
  obtain cur_t where cur_t_in: \<open>cur_t \<in> set (timestamps os)\<close>
    and time_le: \<open>myfst t \<le> cur_t\<close>
    and cap_eq: \<open>cap = Cap (MyPair cur_t (mysnd t)) 1\<close>
    using assms unfolding label_prop_input1_step_batch_def Let_def
    by (elim label_prop_label_batch_memberD)
  show ?thesis
    using that[OF cur_t_in time_le cap_eq] .
qed

lemma label_prop_input1_step_batch_member_payloadD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os d t)\<close>
  obtains v l cur_t v' where
    \<open>de1 os d = (v, l)\<close>
    \<open>cur_t \<in> set (timestamps os)\<close>
    \<open>myfst t \<le> cur_t\<close>
    \<open>v' \<in> set (neighbors os cur_t v)\<close>
    \<open>x = en1 os (v', l)\<close>
    \<open>cap = Cap (MyPair cur_t (mysnd t)) 1\<close>
proof -
  obtain v l where de1_eq: \<open>de1 os d = (v, l)\<close>
    by (cases \<open>de1 os d\<close>)
  show ?thesis
    using member that[of v l] de1_eq
    unfolding label_prop_input1_step_batch_def label_prop_label_batch_def
      label_prop_neighbor_batch_def Let_def
    by (auto split: if_splits)
qed


lemma label_prop_input1_step_batch_unfold:
  \<open>label_prop_input1_step_batch os d t =
    label_prop_label_batch os
      (label_prop_label_record_update (input_tl os 1) (myfst t) (fst (de1 os d))
        (min (min_label os (myfst t) (fst (de1 os d))) (snd (de1 os d))))
      (myfst t) (fst (de1 os d)) (snd (de1 os d)) t\<close>
  unfolding label_prop_input1_step_batch_def Let_def by simp

lemma label_prop_input1_step_batch_nonempty_unfoldD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_input1_step_batch os d t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
  shows \<open>label_prop_label_batch os
    (label_prop_label_record_update (input_tl os 1) (myfst t) (fst (de1 os d))
      (min (min_label os (myfst t) (fst (de1 os d))) (snd (de1 os d))))
    (myfst t) (fst (de1 os d)) (snd (de1 os d)) t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
  using assms[unfolded label_prop_input1_step_batch_unfold] by assumption

lemma label_prop_input1_step_batch_nonemptyD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_input1_step_batch os d t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
  obtains v l cur_t v' where
    \<open>de1 os d = (v, l)\<close>
    \<open>cur_t \<in> set (timestamps os)\<close>
    \<open>myfst t \<le> cur_t\<close>
    \<open>v' \<in> set (neighbors os cur_t v)\<close>
    \<open>l < min_label os cur_t v\<close>
    \<open>l < min_label
      (label_prop_label_record_update (input_tl os 1) (myfst t) v (min (min_label os (myfst t) v) l))
      cur_t v'\<close>
proof -
  let ?v = \<open>fst (de1 os d)\<close>
  let ?l = \<open>snd (de1 os d)\<close>
  let ?updated = \<open>label_prop_label_record_update (input_tl os 1) (myfst t) ?v
    (min (min_label os (myfst t) ?v) ?l)\<close>
  have de1_eq: \<open>de1 os d = (?v, ?l)\<close>
    by simp
  have batch_nonempty:
    \<open>label_prop_label_batch os ?updated (myfst t) ?v ?l t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
    by (rule label_prop_input1_step_batch_nonempty_unfoldD[OF assms])


  show ?thesis
  proof (rule label_prop_label_batch_nonemptyD[OF batch_nonempty])
    fix cur_t v'
    assume cur_t_in: \<open>cur_t \<in> set (timestamps os)\<close>
      and time_le: \<open>myfst t \<le> cur_t\<close>
      and v'_in: \<open>v' \<in> set (neighbors os cur_t ?v)\<close>
      and old_guard: \<open>?l < min_label os cur_t ?v\<close>
      and updated_guard: \<open>?l < min_label ?updated cur_t v'\<close>
    show thesis
      using that[OF de1_eq cur_t_in time_le v'_in old_guard updated_guard] .
  qed
qed



lemma label_prop_input1_step_batch_nonempty_strict_updateD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_input1_step_batch os d t \<noteq> []\<close>
    and ts_t: \<open>myfst t \<in> set (timestamps os)\<close>
  obtains v l where
    \<open>de1 os d = (v, l)\<close>
    \<open>l < min_label os (myfst t) v\<close>
    \<open>min_label
      (label_prop_label_record_update (input_tl os 1) (myfst t) v l)
      (myfst t) v < min_label os (myfst t) v\<close>
proof -
  obtain v l cur_t v' where de1_eq: \<open>de1 os d = (v, l)\<close>
    and cur_t_in: \<open>cur_t \<in> set (timestamps os)\<close>
    and time_le: \<open>myfst t \<le> cur_t\<close>
    and v'_in: \<open>v' \<in> set (neighbors os cur_t v)\<close>
    and strict_cur: \<open>l < min_label os cur_t v\<close>
    using label_prop_input1_step_batch_nonemptyD[OF assms(1)] by metis
  have mono: \<open>min_label os cur_t v \<le> min_label os (myfst t) v\<close>
    using min_label_mono_time[OF ts_t time_le] .
  have strict_myfst: \<open>l < min_label os (myfst t) v\<close>
    using strict_cur mono by linarith
  let ?updated = \<open>label_prop_label_record_update (input_tl os 1) (myfst t) v l\<close>
  have label_eq: \<open>label ?updated = (label os)(myfst t := (label os (myfst t))(v := l))\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  have ts_eq: \<open>timestamps ?updated = timestamps os\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  have l_in_set: \<open>l \<in> insert (label ?updated (myfst t) v)
      ((\<lambda>t'. label ?updated t' v) ` {t' \<in> set (timestamps ?updated). t' \<le> myfst t})\<close>
    using label_eq by simp
  have min_le_l: \<open>min_label ?updated (myfst t) v \<le> l\<close>
    using l_in_set unfolding min_label_def by (intro Min_le) auto
  have strict_update: \<open>min_label ?updated (myfst t) v < min_label os (myfst t) v\<close>
    using min_le_l strict_myfst by linarith
  show ?thesis
    using that[OF de1_eq strict_myfst strict_update] .
qed


lemma fst_label_prop_input1_batched_Cons_prefix:
  \<open>fst (label_prop_input1_batched os ((d, t) # pre)) =
    fst (label_prop_input1_batched (label_prop_input1_step_state os d t) pre)\<close>
  by (cases \<open>label_prop_input1_batched (label_prop_input1_step_state os d t) pre\<close>) simp

lemma label_prop_input1_batched_batch_memberD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
  obtains pre d t post os_pre where
    \<open>msgs = pre @ (d, t) # post\<close>
    \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre d t)\<close>
  using assms
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  show ?case
  proof (cases \<open>(x, cap) \<in> set (label_prop_input1_step_batch os d t)\<close>)
    case True
    show ?thesis
      by (rule Cons.prems(1)[of Nil d t msgs os]) (simp_all add: msg_eq True)
  next
    case False
    have tail_member:
      \<open>(x, cap) \<in> set (snd (label_prop_input1_batched (label_prop_input1_step_state os d t) msgs))\<close>
      using Cons.prems(2) False unfolding msg_eq
      by (cases \<open>label_prop_input1_batched (label_prop_input1_step_state os d t) msgs\<close>) simp
    show ?thesis
    proof (rule Cons.hyps[OF _ tail_member])
      fix pre da ta post os_pre
      assume msgs_tail: \<open>msgs = pre @ (da, ta) # post\<close>
        and os_pre_eq: \<open>os_pre = fst (label_prop_input1_batched (label_prop_input1_step_state os d t) pre)\<close>
        and member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre da ta)\<close>
      have msgs_eq: \<open>msg # msgs = (d, t) # pre @ (da, ta) # post\<close>
        using msgs_tail msg_eq by simp
      have os_pre_eq': \<open>os_pre = fst (label_prop_input1_batched os ((d, t) # pre))\<close>
        using os_pre_eq fst_label_prop_input1_batched_Cons_prefix[of os d t pre] by simp
      show thesis
      proof (rule Cons.prems(1)[of \<open>(d, t) # pre\<close> da ta post os_pre])
        show \<open>msg # msgs = ((d, t) # pre) @ (da, ta) # post\<close>
          using msgs_tail msg_eq by simp

        show \<open>os_pre = fst (label_prop_input1_batched os ((d, t) # pre))\<close>
          using os_pre_eq' .
        show \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre da ta)\<close>
          using member .
      qed


    qed
  qed
qed


lemma label_prop_input1_batched_produced_memberD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(p, pt, n) \<in> set (map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
    (snd (label_prop_input1_batched os msgs)))\<close>
  obtains
    \<open>p = 1\<close>
    \<open>n = 1\<close>
    \<open>myfst pt \<in> set (timestamps os)\<close>
    \<open>MyPair (myfst pt) 0 \<le> pt\<close>
proof -
  obtain x cap where batch_member: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    and triple_eq: \<open>(p, pt, n) = (case cap of Cap t p \<Rightarrow> (p, t, 1))\<close>
    using assms by auto
  obtain pre d t post os_pre where os_pre_eq:
    \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    and step_member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre d t)\<close>
    using batch_member by (elim label_prop_input1_batched_batch_memberD)
  obtain cur_t where cur_t_pre: \<open>cur_t \<in> set (timestamps os_pre)\<close>
    and cap_eq: \<open>cap = Cap (MyPair cur_t (mysnd t)) 1\<close>
    using step_member by (elim label_prop_input1_step_batch_memberD)
  have cur_t: \<open>cur_t \<in> set (timestamps os)\<close>
    using cur_t_pre os_pre_eq by simp
  have fields: \<open>p = 1\<close> \<open>n = 1\<close> \<open>pt = MyPair cur_t (mysnd t)\<close>
    using triple_eq cap_eq by simp_all
  have pt_ts: \<open>myfst pt \<in> set (timestamps os)\<close>
    using fields cur_t by simp
  have pt_ge: \<open>MyPair (myfst pt) 0 \<le> pt\<close>
    using fields by simp
  show ?thesis
    using that[OF fields(1) fields(2) pt_ts pt_ge] .
qed



lemma outpu_fst_label_prop_input1_batched_eq:
  \<open>outpu (fst (label_prop_input1_batched os msgs)) p =
    outpu os p @ map (\<lambda>(x, cap). (x, capability.time cap))
      (filter (\<lambda>(x, cap). out cap = p) (snd (label_prop_input1_batched os msgs)))\<close>
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  let ?step = \<open>label_prop_input1_step_state os d t\<close>
  have step_out: \<open>outpu ?step p = outpu os p @
      map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = p) (label_prop_input1_step_batch os d t))\<close>
    unfolding label_prop_input1_step_state_def label_prop_input1_step_batch_def
    by (simp add: Let_def split: capability.splits)
  obtain os_final batches where tail:
    \<open>label_prop_input1_batched ?step msgs = (os_final, batches)\<close>
    by (cases \<open>label_prop_input1_batched ?step msgs\<close>) auto
  have tail_out: \<open>outpu os_final p = outpu ?step p @
      map (\<lambda>(x, cap). (x, capability.time cap)) (filter (\<lambda>(x, cap). out cap = p) batches)\<close>
    using Cons.hyps[of ?step] tail by simp
  show ?case
    using msg_eq tail step_out tail_out
    by (simp add: append_assoc)
qed
lemma outpu_fst_label_prop_input1_batched_nonemptyD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>outpu os 1 = []\<close>
    and \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
  obtains x cap where
    \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    \<open>out cap = (1 :: 2)\<close>
proof -
  have filter_nonempty:
    \<open>filter (\<lambda>(x, cap). out cap = (1 :: 2)) (snd (label_prop_input1_batched os msgs)) \<noteq> []\<close>
    using assms by auto
  then obtain pair where pair_in:
    \<open>pair \<in> set (filter (\<lambda>(x, cap). out cap = (1 :: 2))
      (snd (label_prop_input1_batched os msgs)))\<close>
    by (cases \<open>filter (\<lambda>(x, cap). out cap = (1 :: 2))
      (snd (label_prop_input1_batched os msgs))\<close>) auto
  obtain x cap where pair: \<open>pair = (x, cap)\<close>
    by (cases pair)
  have batch_in: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    and cap_out: \<open>out cap = (1 :: 2)\<close>
    using pair_in unfolding pair by auto
  show ?thesis
    using that[OF batch_in cap_out] .
qed


lemma label_prop_input1_batched_snd_member_strict_updateD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes member: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
  obtains pre d t post os_pre v l where
    \<open>msgs = pre @ (d, t) # post\<close>
    \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    \<open>de1 os_pre d = (v, l)\<close>
    \<open>myfst t \<in> set (timestamps os)\<close>
    \<open>l < min_label os_pre (myfst t) v\<close>
    \<open>min_label
      (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l)
      (myfst t) v < min_label os_pre (myfst t) v\<close>
proof -
  obtain pre d t post os_pre where msgs_eq: \<open>msgs = pre @ (d, t) # post\<close>
    and os_pre_eq: \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    and step_batch_member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre d t)\<close>
    using member by (elim label_prop_input1_batched_batch_memberD)
  have step_batch_nonempty: \<open>label_prop_input1_step_batch os_pre d t \<noteq> []\<close>
    using step_batch_member by auto
  have dt_in_msgs: \<open>(d, t) \<in> set msgs\<close>
    using msgs_eq by simp
  have dt_in_input: \<open>(d, t) \<in> set (input os 1)\<close>
    using dt_in_msgs msgs_input by auto
  have ts_t_os: \<open>myfst t \<in> set (timestamps os)\<close>
    using dt_in_input INV unfolding label_prop_upd_inv_def by metis
  have ts_t_pre: \<open>myfst t \<in> set (timestamps os_pre)\<close>
    using ts_t_os os_pre_eq by simp
  obtain v l where de1_eq: \<open>de1 os_pre d = (v, l)\<close>
    and strict: \<open>l < min_label os_pre (myfst t) v\<close>
    and update_strict:
    \<open>min_label (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l)
        (myfst t) v < min_label os_pre (myfst t) v\<close>
    using step_batch_nonempty ts_t_pre
    by (elim label_prop_input1_step_batch_nonempty_strict_updateD)
  show ?thesis
    using that[OF msgs_eq os_pre_eq de1_eq ts_t_os strict update_strict] .
qed

lemma min_label_fst_label_prop_input1_batched_strict_timestamped_if_snd_member:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes member: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
  obtains q v where
    \<open>q \<in> set (timestamps os)\<close>
    \<open>v \<in> edge_vertices (all_edges os q)\<close>
    \<open>min_label (fst (label_prop_input1_batched os msgs)) q v < min_label os q v\<close>
  oops



lemma label_prop_input1_batched_outpu_nonempty_strict_updateD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>outpu os 1 = []\<close>
    and \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
  obtains pre d t post os_pre v l where
    \<open>msgs = pre @ (d, t) # post\<close>
    \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    \<open>de1 os_pre d = (v, l)\<close>
    \<open>myfst t \<in> set (timestamps os)\<close>
    \<open>l < min_label os_pre (myfst t) v\<close>
    \<open>min_label
      (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l)
      (myfst t) v < min_label os_pre (myfst t) v\<close>
proof -
  obtain x cap where batch_member: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    and cap_out: \<open>out cap = (1 :: 2)\<close>
    using assms(1,2) by (elim outpu_fst_label_prop_input1_batched_nonemptyD)
  obtain pre d t post os_pre where msgs_eq: \<open>msgs = pre @ (d, t) # post\<close>
    and os_pre_eq: \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    and step_batch_member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre d t)\<close>
    using batch_member by (elim label_prop_input1_batched_batch_memberD)
  have step_batch_nonempty: \<open>label_prop_input1_step_batch os_pre d t \<noteq> []\<close>
    using step_batch_member by auto
  have dt_in_msgs: \<open>(d, t) \<in> set msgs\<close>
    using msgs_eq by simp
  have dt_in_input: \<open>(d, t) \<in> set (input os 1)\<close>
    using dt_in_msgs msgs_input by auto
  have ts_t_os: \<open>myfst t \<in> set (timestamps os)\<close>
    using dt_in_input INV unfolding label_prop_upd_inv_def by metis
  have ts_t_pre: \<open>myfst t \<in> set (timestamps os_pre)\<close>
    using ts_t_os os_pre_eq by simp
  obtain v l where de1_eq: \<open>de1 os_pre d = (v, l)\<close>
    and strict: \<open>l < min_label os_pre (myfst t) v\<close>
    and update_strict:
    \<open>min_label (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l)
        (myfst t) v < min_label os_pre (myfst t) v\<close>
    using step_batch_nonempty ts_t_pre
    by (elim label_prop_input1_step_batch_nonempty_strict_updateD)
  show ?thesis
    using that[OF msgs_eq os_pre_eq de1_eq ts_t_os strict update_strict] .
qed


subsection \<open>Label minima and invariant preservation\<close>

lemma min_label_label_prop_label_record_update_le:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes l_le: \<open>l \<le> min_label os t v\<close>
  shows \<open>min_label (label_prop_label_record_update (input_tl os 1) t v l) q x \<le> min_label os q x\<close>
proof -
  let ?os' = \<open>label_prop_label_record_update (input_tl os 1) t v l\<close>
  have ts_eq: \<open>timestamps ?os' = timestamps os\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  have label_eq: \<open>label ?os' = (label os)(t := (label os t)(v := l))\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  show ?thesis
  proof (cases \<open>x = v\<close>)
    case False
    have \<open>\<And>t'. label ?os' t' x = label os t' x\<close>
      using False label_eq by (auto simp: fun_upd_def)
    then show ?thesis
      unfolding min_label_def using ts_eq by simp
  next
    case True
    have l_le_label_t: \<open>l \<le> label os t v\<close>
    proof -
      have \<open>min_label os t v \<le> label os t v\<close>
        unfolding min_label_def by (intro Min_le) auto
      then show ?thesis using l_le by simp
    qed
    let ?S = \<open>insert (label os q v) ((\<lambda>t'. label os t' v) ` {t' \<in> set (timestamps os). t' \<le> q})\<close>
    let ?S' = \<open>insert (label ?os' q v) ((\<lambda>t'. label ?os' t' v) ` {t' \<in> set (timestamps ?os'). t' \<le> q})\<close>
    have S'_eq: \<open>?S' = insert (label ?os' q v) ((\<lambda>t'. label ?os' t' v) ` {t' \<in> set (timestamps os). t' \<le> q})\<close>
      using ts_eq by simp
    have fin_S: \<open>finite ?S\<close> by auto
    have fin_S': \<open>finite ?S'\<close> by auto
    have ne_S: \<open>?S \<noteq> {}\<close> by auto
    have bound: \<open>Min ?S' \<le> Min ?S\<close>
    proof (rule Min.boundedI[OF fin_S ne_S])
      fix y assume y_in: \<open>y \<in> ?S\<close>
      then consider (q_lbl) \<open>y = label os q v\<close>
        | (t_lbl) t' where \<open>t' \<in> set (timestamps os)\<close> \<open>t' \<le> q\<close> \<open>y = label os t' v\<close>
        by blast
      then show \<open>Min ?S' \<le> y\<close>
      proof cases
        case q_lbl
        show ?thesis
        proof (cases \<open>q = t\<close>)
          case True
          have \<open>label ?os' q v = l\<close> using True label_eq by simp
          then have \<open>l \<in> ?S'\<close> by auto
          then have \<open>Min ?S' \<le> l\<close> using fin_S' by (intro Min_le) auto
          also have \<open>l \<le> y\<close> using l_le_label_t q_lbl True by simp
          finally show ?thesis .
        next
          case False
          have \<open>label ?os' q v = label os q v\<close>
            using False label_eq by simp
          then have \<open>y \<in> ?S'\<close> using q_lbl by auto
          then show ?thesis using fin_S' by (intro Min_le) auto
        qed
      next
        case (t_lbl t')
        show ?thesis
        proof (cases \<open>t' = t\<close>)
          case True
          have lbl_t: \<open>label ?os' t v = l\<close> using label_eq by simp
          have t_mem: \<open>t \<in> {t'' \<in> set (timestamps ?os'). t'' \<le> q}\<close>
            using ts_eq t_lbl(1,2) True by simp
          have \<open>l \<in> ?S'\<close>
            using lbl_t t_mem image_eqI[where x=t and f=\<open>\<lambda>t'. label ?os' t' v\<close>] by auto
          then have \<open>Min ?S' \<le> l\<close> using fin_S' by (intro Min_le) auto
          also have \<open>l \<le> y\<close> using l_le_label_t t_lbl(3) True by simp
          finally show ?thesis .
        next
          case False
          have lbl_eq: \<open>label ?os' t' v = label os t' v\<close>
            using False label_eq by (simp add: fun_upd_def)
          have t'_mem: \<open>t' \<in> {t'' \<in> set (timestamps ?os'). t'' \<le> q}\<close>
            using ts_eq t_lbl(1,2) by simp
          have \<open>y \<in> ?S'\<close>
            using lbl_eq t'_mem t_lbl(3) image_eqI[where x=t' and f=\<open>\<lambda>t''. label ?os' t'' v\<close>] by auto
          then show ?thesis using fin_S' by (intro Min_le) auto
        qed
      qed
    qed
    have \<open>min_label ?os' q v = Min ?S'\<close>
      unfolding min_label_def by simp
    moreover have \<open>min_label os q v = Min ?S\<close>
      unfolding min_label_def by simp
    ultimately show ?thesis using bound True by simp
  qed
qed

lemma min_label_label_prop_input1_step_state_le:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  shows \<open>min_label (label_prop_input1_step_state os d t) q x \<le> min_label os q x\<close>
proof -
  let ?v = \<open>fst (de1 os d)\<close>
  let ?l = \<open>snd (de1 os d)\<close>
  let ?t1 = \<open>myfst t\<close>
  let ?new = \<open>min (min_label os ?t1 ?v) ?l\<close>
  let ?os'' = \<open>label_prop_label_record_update (input_tl os 1) ?t1 ?v ?new\<close>
  let ?batch = \<open>label_prop_label_batch os ?os'' ?t1 ?v ?l t\<close>
  have step_eq:
    \<open>label_prop_input1_step_state os d t =
       release_caps (drop_caps (produces (add_caps ?os'' (map snd ?batch)) ?batch) (map snd ?batch)) 1\<close>
    unfolding label_prop_input1_step_state_def Let_def by simp
  have new_le: \<open>?new \<le> min_label os ?t1 ?v\<close>
    by simp
  have \<open>min_label (label_prop_input1_step_state os d t) q x = min_label ?os'' q x\<close>
    unfolding step_eq by simp
  also have \<open>\<dots> \<le> min_label os q x\<close>
    using min_label_label_prop_label_record_update_le[OF new_le] .
  finally show ?thesis .
qed

lemma min_label_fst_label_prop_input1_batched_le:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  shows \<open>min_label (fst (label_prop_input1_batched os msgs)) q x \<le> min_label os q x\<close>
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons a ms)
  obtain d t where a_eq: \<open>a = (d, t)\<close> by (cases a) auto
  have unfold:
    \<open>fst (label_prop_input1_batched os (a # ms)) =
       fst (label_prop_input1_batched (label_prop_input1_step_state os d t) ms)\<close>
    using a_eq fst_label_prop_input1_batched_Cons_prefix[of os d t ms] by simp
  have ih: \<open>min_label (fst (label_prop_input1_batched (label_prop_input1_step_state os d t) ms)) q x
             \<le> min_label (label_prop_input1_step_state os d t) q x\<close>
    using Cons.hyps[of \<open>label_prop_input1_step_state os d t\<close>] by simp
  also have \<open>\<dots> \<le> min_label os q x\<close>
    using min_label_label_prop_input1_step_state_le[of os d t q x] .
  finally show ?case using unfold by simp
qed


lemma labels_inv_label_prop_input1_step_stateI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes labels: \<open>\<And>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and input1: \<open>input os 1 = (d, t) # xs\<close>
  shows \<open>labels_inv (all_edges (label_prop_input1_step_state os d t) q)
    (min_label (label_prop_input1_step_state os d t) q)\<close>
proof -
  obtain v l where de1_eq: \<open>de1 os d = (v, l)\<close>
    by (cases \<open>de1 os d\<close>)
  let ?t1 = \<open>myfst t\<close>
  let ?os'' = \<open>label_prop_label_record_update (input_tl os 1) ?t1 v
    (min (min_label os ?t1 v) l)\<close>
  have step_eq: \<open>label_prop_input1_step_state os d t =
    release_caps (drop_caps (produces (add_caps ?os''
      (map snd (label_prop_label_batch os ?os'' ?t1 v l t)))
      (label_prop_label_batch os ?os'' ?t1 v l t))
      (map snd (label_prop_label_batch os ?os'' ?t1 v l t))) 1\<close>
    using de1_eq unfolding label_prop_input1_step_state_def Let_def by simp
  have \<open>labels_inv (all_edges ?os'' q) (min_label ?os'' q)\<close>
    by (rule labels_inv_input1_preserved_record_update_tl[OF labels inv _ de1_eq refl refl])
      (use input1 in simp)
  then show ?thesis
    unfolding step_eq by simp
qed

lemma label_prop_upd_inv_label_prop_input1_step_stateI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes inv: \<open>label_prop_upd_inv os\<close>
    and input1: \<open>input os 1 = (d, t) # xs\<close>
  shows \<open>label_prop_upd_inv (label_prop_input1_step_state os d t)\<close>
proof -
  obtain v l where de1_eq: \<open>de1 os d = (v, l)\<close>
    by (cases \<open>de1 os d\<close>)
  let ?t1 = \<open>myfst t\<close>
  let ?os'' = \<open>label_prop_label_record_update (input_tl os 1) ?t1 v
    (min (min_label os ?t1 v) l)\<close>
  have step_eq: \<open>label_prop_input1_step_state os d t =
    release_caps (drop_caps (produces (add_caps ?os''
      (map snd (label_prop_label_batch os ?os'' ?t1 v l t)))
      (label_prop_label_batch os ?os'' ?t1 v l t))
      (map snd (label_prop_label_batch os ?os'' ?t1 v l t))) 1\<close>
    using de1_eq unfolding label_prop_input1_step_state_def Let_def by simp
  have os''_inv: \<open>label_prop_upd_inv ?os''\<close>
    by (rule label_prop_upd_inv_input1_preserved[OF inv input1 _ de1_eq refl])
      (use input1 in \<open>simp_all add: label_prop_label_record_update_def input_tl_def\<close>)

  then show ?thesis
    unfolding step_eq by simp
qed

lemma label_prop_upd_inv_fst_label_prop_input1_batched_prefixI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes input_eq: \<open>input os 1 = msgs @ rest\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
  shows \<open>label_prop_upd_inv (fst (label_prop_input1_batched os msgs))\<close>
  using input_eq inv
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close> by (cases msg)
  have input1: \<open>input os 1 = (d, t) # (msgs @ rest)\<close>
    using Cons.prems(1) msg_eq by simp
  let ?step = \<open>label_prop_input1_step_state os d t\<close>
  have inv_step: \<open>label_prop_upd_inv ?step\<close>
    by (rule label_prop_upd_inv_label_prop_input1_step_stateI[OF Cons.prems(2) input1])
  have input_step: \<open>input ?step 1 = msgs @ rest\<close>
    using input1 by simp
  have ih: \<open>label_prop_upd_inv (fst (label_prop_input1_batched ?step msgs))\<close>
    by (rule Cons.hyps[OF input_step inv_step])
  then show ?case
    using msg_eq by (cases \<open>label_prop_input1_batched ?step msgs\<close>) simp
qed

lemma labels_inv_fst_label_prop_input1_batched_prefixI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes input_eq: \<open>input os 1 = msgs @ rest\<close>
    and labels: \<open>\<And>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
  shows \<open>labels_inv (all_edges (fst (label_prop_input1_batched os msgs)) q)
    (min_label (fst (label_prop_input1_batched os msgs)) q)\<close>
  using input_eq labels inv
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  have input1: \<open>input os 1 = (d, t) # (msgs @ rest)\<close>
    using Cons.prems(1) msg_eq by simp
  let ?step = \<open>label_prop_input1_step_state os d t\<close>
  have labels_step: \<open>\<And>q. labels_inv (all_edges ?step q) (min_label ?step q)\<close>
    by (rule labels_inv_label_prop_input1_step_stateI[OF Cons.prems(2) Cons.prems(3) input1])
  have inv_step: \<open>label_prop_upd_inv ?step\<close>
    by (rule label_prop_upd_inv_label_prop_input1_step_stateI[OF Cons.prems(3) input1])
  have input_step: \<open>input ?step 1 = msgs @ rest\<close>
    using input1 by simp
  have ih: \<open>labels_inv (all_edges (fst (label_prop_input1_batched ?step msgs)) q)
    (min_label (fst (label_prop_input1_batched ?step msgs)) q)\<close>
    by (rule Cons.hyps[OF input_step labels_step inv_step])
  then show ?case
    using msg_eq
    by (cases \<open>label_prop_input1_batched ?step msgs\<close>) simp

qed

lemma labels_inv_fst_label_prop_input1_batched_inputI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes labels: \<open>\<And>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
  shows \<open>labels_inv (all_edges (fst (label_prop_input1_batched os (input os 1))) q)
    (min_label (fst (label_prop_input1_batched os (input os 1))) q)\<close>
  by (rule labels_inv_fst_label_prop_input1_batched_prefixI[where rest=Nil])
    (use assms in simp_all)

lemma fst_label_prop_input1_batched_append:
  \<open>fst (label_prop_input1_batched os (xs @ ys)) =
   fst (label_prop_input1_batched (fst (label_prop_input1_batched os xs)) ys)\<close>
proof (induct xs arbitrary: os)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  obtain d t where a_eq: \<open>a = (d, t)\<close> by (cases a)
  have step_eq:
    \<open>fst (label_prop_input1_batched os ((d, t) # (xs @ ys))) =
     fst (label_prop_input1_batched (label_prop_input1_step_state os d t) (xs @ ys))\<close>
    using fst_label_prop_input1_batched_Cons_prefix[of os d t \<open>xs @ ys\<close>] by simp
  have step_eq2:
    \<open>fst (label_prop_input1_batched os ((d, t) # xs)) =
     fst (label_prop_input1_batched (label_prop_input1_step_state os d t) xs)\<close>
    using fst_label_prop_input1_batched_Cons_prefix[of os d t xs] by simp
  show ?case
    using a_eq step_eq step_eq2
      Cons.hyps[of \<open>label_prop_input1_step_state os d t\<close>]
    by simp
qed

(* preservation lemma for label_prop_upd_inv through batched *)
lemma label_prop_upd_inv_fst_label_prop_input1_batched_preserved:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_upd_inv os\<close>
  shows \<open>label_prop_upd_inv (fst (label_prop_input1_batched os msgs))\<close>
  oops

lemma min_label_fst_label_prop_input1_batched_strict_if_output_nonempty:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>outpu os 1 = []\<close>
    and \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
  obtains q v where
    \<open>v \<in> edge_vertices (all_edges os q)\<close>
    \<open>min_label (fst (label_prop_input1_batched os msgs)) q v < min_label os q v\<close>
  oops


lemma min_label_fst_label_prop_input1_batched_strict_timestamped_if_output_nonempty:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes out_empty: \<open>outpu os 1 = []\<close>
    and out_nonempty: \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
  obtains q v where
    \<open>q \<in> set (timestamps os)\<close>
    \<open>v \<in> edge_vertices (all_edges os q)\<close>
    \<open>min_label (fst (label_prop_input1_batched os msgs)) q v < min_label os q v\<close>
proof -
  obtain pre d t post os_pre v l where
    msgs_eq: \<open>msgs = pre @ (d, t) # post\<close>
    and os_pre_eq: \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    and de1_pre_eq: \<open>de1 os_pre d = (v, l)\<close>
    and strict_pre: \<open>l < min_label os_pre (myfst t) v\<close>
    and update_strict:
    \<open>min_label (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l) (myfst t) v
        < min_label os_pre (myfst t) v\<close>
    apply (rule label_prop_input1_batched_outpu_nonempty_strict_updateD[OF out_empty out_nonempty, OF INV msgs_input])
    apply simp
    done   
  have de1_os_eq: \<open>de1 os d = (v, l)\<close>
    using de1_pre_eq os_pre_eq by simp
  have dt_in_msgs: \<open>(d, t) \<in> set msgs\<close>
    using msgs_eq by simp
  have dt_in_input: \<open>(d, t) \<in> set (input os 1)\<close>
    using dt_in_msgs msgs_input by auto
  have ts_t: \<open>myfst t \<in> set (timestamps os)\<close>
    and v_vertex_raw: \<open>fst (de1 os d) \<in> all_vertices os (myfst t)\<close>
    using dt_in_input INV unfolding label_prop_upd_inv_def by metis+
  have v_in_all: \<open>v \<in> all_vertices os (myfst t)\<close>
    using v_vertex_raw de1_os_eq by simp
  have v_in_edge: \<open>v \<in> edge_vertices (all_edges os (myfst t))\<close>
    using v_in_all edge_vertices_all_edges[OF INV] by simp

  let ?step = \<open>label_prop_input1_step_state os_pre d t\<close>
  let ?new = \<open>min (min_label os_pre (myfst t) v) l\<close>
  have new_eq_l: \<open>?new = l\<close> using strict_pre by simp
  have step_min:
    \<open>min_label ?step (myfst t) v =
       min_label (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v ?new) (myfst t) v\<close>
    unfolding label_prop_input1_step_state_def Let_def
    using de1_pre_eq by simp
  have step_strict_pre:
    \<open>min_label ?step (myfst t) v < min_label os_pre (myfst t) v\<close>
    using step_min new_eq_l update_strict by simp

  have fst_unfold:
    \<open>fst (label_prop_input1_batched os msgs) =
     fst (label_prop_input1_batched ?step post)\<close>
    using msgs_eq os_pre_eq
      fst_label_prop_input1_batched_append[of os pre \<open>(d, t) # post\<close>]
      fst_label_prop_input1_batched_Cons_prefix[of os_pre d t post]
    by simp

  have step_le_os:
    \<open>min_label os_pre (myfst t) v \<le> min_label os (myfst t) v\<close>
    using os_pre_eq min_label_fst_label_prop_input1_batched_le[of os pre \<open>myfst t\<close> v]
    by simp

  have tail_le_step:
    \<open>min_label (fst (label_prop_input1_batched ?step post)) (myfst t) v
       \<le> min_label ?step (myfst t) v\<close>
    using min_label_fst_label_prop_input1_batched_le[of ?step post \<open>myfst t\<close> v] .

  have strict_full:
    \<open>min_label (fst (label_prop_input1_batched os msgs)) (myfst t) v < min_label os (myfst t) v\<close>
  proof -
    have \<open>min_label (fst (label_prop_input1_batched os msgs)) (myfst t) v
            = min_label (fst (label_prop_input1_batched ?step post)) (myfst t) v\<close>
      using fst_unfold by simp
    also have \<open>\<dots> \<le> min_label ?step (myfst t) v\<close>
      using tail_le_step .
    also have \<open>\<dots> < min_label os_pre (myfst t) v\<close>
      using step_strict_pre .
    also have \<open>\<dots> \<le> min_label os (myfst t) v\<close>
      using step_le_os .
    finally show ?thesis .
  qed

  show ?thesis
    using that[OF ts_t v_in_edge strict_full] .
qed

subsection \<open>Measure decrease\<close>

lemma labels_measure_strict_decrease_if_pointwise_le_and_less:
  fixes A :: \<open>(nat \<times> nat) set\<close>
    and l l' :: \<open>nat \<Rightarrow> nat\<close>
  assumes finite_edges: \<open>finite (edge_vertices A)\<close>
    and labels: \<open>labels_inv A l\<close>
    and labels': \<open>labels_inv A l'\<close>
    and le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> l' v \<le> l v\<close>
    and strict: \<open>\<exists>v\<in>edge_vertices A. l' v < l v\<close>
  shows \<open>labels_measure A l' < labels_measure A l\<close>
proof -
  have rank_le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> rank A (l' v) \<le> rank A (l v)\<close>
    using le finite_edges
    unfolding rank_def
    by (intro card_mono; force)

  obtain v where v_in: \<open>v \<in> edge_vertices A\<close> and strict_v: \<open>l' v < l v\<close>
    using strict by auto
  have l'_in: \<open>l' v \<in> edge_vertices A\<close>
    using labels' v_in unfolding labels_inv_def cc_of_def by auto
  have rank_strict: \<open>rank A (l' v) < rank A (l v)\<close>
  proof -
    let ?S' = \<open>{y \<in> edge_vertices A. y < l' v}\<close>
    let ?S = \<open>{y \<in> edge_vertices A. y < l v}\<close>
    have subset: \<open>?S' \<subset> ?S\<close>
      using l'_in strict_v by auto
    moreover have \<open>finite ?S\<close>
      using finite_edges by auto
    ultimately show ?thesis
      unfolding rank_def by (simp add: psubset_card_mono)
  qed
  show ?thesis
    unfolding labels_measure_def
    by (rule sum_strict_mono_ex1[OF finite_edges]) (auto intro: rank_le v_in rank_strict)
qed


lemma labels_measure_strict_decrease_if_pointwise_le_and_less_same_edges:
  fixes A A' :: \<open>(nat \<times> nat) set\<close>
    and l l' :: \<open>nat \<Rightarrow> nat\<close>
  assumes finite_edges: \<open>finite (edge_vertices A)\<close>
    and labels: \<open>labels_inv A l\<close>
    and labels': \<open>labels_inv A l'\<close>
    and edges_eq: \<open>A' = A\<close>
    and le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> l' v \<le> l v\<close>
    and strict: \<open>\<exists>v\<in>edge_vertices A. l' v < l v\<close>
  shows \<open>labels_measure A' l' < labels_measure A l\<close>
  using labels_measure_strict_decrease_if_pointwise_le_and_less
    [OF finite_edges labels labels' le strict]
    edges_eq by simp


lemma finite_all_vertices:
  shows \<open>finite (all_vertices os t)\<close>
  unfolding all_vertices_def by simp

lemma finite_edge_vertices_all_edges:
  shows \<open>finite (edge_vertices (all_edges os t))\<close>
proof -
  have \<open>edge_vertices (all_edges os t) \<subseteq> all_vertices os t\<close>
    by (rule edge_vertices_all_edges_subset_all_vertices)
  then show ?thesis
    using finite_all_vertices[of os t] by (rule finite_subset)
qed

lemma labels_measure_le_if_pointwise_le_same_edges:
  fixes A A' :: \<open>(nat \<times> nat) set\<close>
    and l l' :: \<open>nat \<Rightarrow> nat\<close>
  assumes finite_edges: \<open>finite (edge_vertices A)\<close>
    and edges_eq: \<open>A' = A\<close>
    and le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> l' v \<le> l v\<close>
  shows \<open>labels_measure A' l' \<le> labels_measure A l\<close>
proof -
  have rank_le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> rank A (l' v) \<le> rank A (l v)\<close>
    using le finite_edges
    unfolding rank_def
    by (intro card_mono; force)
  have \<open>(\<Sum>v\<in>edge_vertices A. rank A (l' v)) \<le> (\<Sum>v\<in>edge_vertices A. rank A (l v))\<close>
    by (rule sum_mono) (auto intro: rank_le)
  then show ?thesis
    using edges_eq unfolding labels_measure_def by simp

qed


lemma labels_measure_fst_label_prop_input1_batched_le_at_timestamp:
  fixes os os' :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and msgs :: \<open>('d \<times> (nat, nat) myprod) list\<close>
  assumes os'_def: \<open>os' = fst (label_prop_input1_batched os msgs)\<close>
  shows \<open>labels_measure (all_edges os' t) (min_label os' t)
      \<le> labels_measure (all_edges os t) (min_label os t)\<close>
proof -
  have edges_eq: \<open>all_edges os' t = all_edges os t\<close>
    using os'_def by simp
  have finite_edges: \<open>finite (edge_vertices (all_edges os t))\<close>
    by (rule finite_edge_vertices_all_edges)
  have pointwise:
    \<open>\<And>v. v \<in> edge_vertices (all_edges os t) \<Longrightarrow> min_label os' t v \<le> min_label os t v\<close>
    using os'_def min_label_fst_label_prop_input1_batched_le[of os msgs t]
    by simp
  show ?thesis
    by (rule labels_measure_le_if_pointwise_le_same_edges
        [OF finite_edges edges_eq pointwise])
qed


lemma labels_measure_fst_label_prop_input1_batched_strict_at_some_timestamp_if_output_nonempty:
  fixes os os' :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and msgs :: \<open>('d \<times> (nat, nat) myprod) list\<close>
  assumes os'_def: \<open>os' = fst (label_prop_input1_batched os msgs)\<close>
    and out_empty: \<open>outpu os 1 = []\<close>
    and out_nonempty: \<open>outpu os' 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
    and labels_os: \<open>\<And>t. labels_inv (all_edges os t) (min_label os t)\<close>
    and labels_os': \<open>\<And>t. labels_inv (all_edges os' t) (min_label os' t)\<close>
  obtains q where
    \<open>q \<in> set (timestamps os)\<close>
    \<open>labels_measure (all_edges os' q) (min_label os' q)
      < labels_measure (all_edges os q) (min_label os q)\<close>
proof -
  have out_batch: \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
    using os'_def out_nonempty by simp
  obtain q v where q_in: \<open>q \<in> set (timestamps os)\<close>
    and v_in: \<open>v \<in> edge_vertices (all_edges os q)\<close>
    and strict_v: \<open>min_label (fst (label_prop_input1_batched os msgs)) q v < min_label os q v\<close>
    using min_label_fst_label_prop_input1_batched_strict_timestamped_if_output_nonempty
      [OF out_empty out_batch INV msgs_input]
    by blast
  have pointwise:
    \<open>\<And>v. v \<in> edge_vertices (all_edges os q) \<Longrightarrow> min_label os' q v \<le> min_label os q v\<close>
    using os'_def min_label_fst_label_prop_input1_batched_le[of os msgs q]
    by simp
  have strict_ex:
    \<open>\<exists>v\<in>edge_vertices (all_edges os q). min_label os' q v < min_label os q v\<close>
    using os'_def v_in strict_v by auto
  have edges_eq: \<open>all_edges os' q = all_edges os q\<close>
    using os'_def by simp
  have finite_edges: \<open>finite (edge_vertices (all_edges os q))\<close>
    by (rule finite_edge_vertices_all_edges)
  have labels: \<open>labels_inv (all_edges os q) (min_label os q)\<close>
    using labels_os .
  have labels': \<open>labels_inv (all_edges os q) (min_label os' q)\<close>
    using labels_os'[of q] edges_eq by simp
  have strict_measure:
    \<open>labels_measure (all_edges os' q) (min_label os' q)
      < labels_measure (all_edges os q) (min_label os q)\<close>
    by (rule labels_measure_strict_decrease_if_pointwise_le_and_less_same_edges
        [OF finite_edges labels labels' edges_eq pointwise strict_ex])
  show ?thesis
    using that[OF q_in strict_measure] .
qed


lemma sum_list_strict_mono_ex1:
  fixes xs :: \<open>'a list\<close>
    and f g :: \<open>'a \<Rightarrow> nat\<close>
  assumes le: \<open>\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> g x\<close>
    and strict: \<open>\<exists>x\<in>set xs. f x < g x\<close>
  shows \<open>sum_list (map f xs) < sum_list (map g xs)\<close>
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have le_a: \<open>f a \<le> g a\<close>
    using Cons.prems(1) by simp
  have le_tail: \<open>\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> g x\<close>
    using Cons.prems(1) by simp
  have tail_le: \<open>sum_list (map f xs) \<le> sum_list (map g xs)\<close>
    using le_tail
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons b ys)
    have head_le: \<open>f b \<le> g b\<close>
      using Cons.prems by simp
    have tail_le': \<open>sum_list (map f ys) \<le> sum_list (map g ys)\<close>
      using Cons.hyps Cons.prems by simp
    show ?case
      using head_le tail_le' by simp
  qed

  from Cons.prems(2) consider (head) \<open>f a < g a\<close> | (tail) \<open>\<exists>x\<in>set xs. f x < g x\<close>
    by auto
  then show ?case
  proof cases
    case head
    then show ?thesis
      using tail_le by simp
  next
    case tail
    have tail_strict: \<open>sum_list (map f xs) < sum_list (map g xs)\<close>
      using Cons.hyps[OF le_tail tail] .
    then show ?thesis
      using le_a by simp
  qed
qed


lemma labels_measure_sum_fst_label_prop_input1_batched_decreases_if_output_nonempty:
  fixes os os' :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and msgs :: \<open>('d \<times> (nat, nat) myprod) list\<close>
  assumes os'_def: \<open>os' = fst (label_prop_input1_batched os msgs)\<close>
    and out_empty: \<open>outpu os 1 = []\<close>
    and out_nonempty: \<open>outpu os' 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
    and labels_os: \<open>\<And>t. labels_inv (all_edges os t) (min_label os t)\<close>
    and labels_os': \<open>\<And>t. labels_inv (all_edges os' t) (min_label os' t)\<close>
  shows \<open>sum_list (map (\<lambda>t. labels_measure (all_edges os' t) (min_label os' t))
          (timestamps os'))
      < sum_list (map (\<lambda>t. labels_measure (all_edges os t) (min_label os t))
          (timestamps os))\<close>
proof -
  have ts_eq: \<open>timestamps os' = timestamps os\<close>
    using os'_def by simp
  have pointwise:
    \<open>\<And>t. t \<in> set (timestamps os) \<Longrightarrow>
      labels_measure (all_edges os' t) (min_label os' t)
        \<le> labels_measure (all_edges os t) (min_label os t)\<close>
    using labels_measure_fst_label_prop_input1_batched_le_at_timestamp[OF os'_def]
    by simp
  obtain q where q_in: \<open>q \<in> set (timestamps os)\<close>
    and strict_q: \<open>labels_measure (all_edges os' q) (min_label os' q)
      < labels_measure (all_edges os q) (min_label os q)\<close>
    using labels_measure_fst_label_prop_input1_batched_strict_at_some_timestamp_if_output_nonempty
      [OF os'_def out_empty out_nonempty INV msgs_input labels_os labels_os']
    by blast
  have strict_ex:
    \<open>\<exists>t\<in>set (timestamps os). labels_measure (all_edges os' t) (min_label os' t)
      < labels_measure (all_edges os t) (min_label os t)\<close>
    using q_in strict_q by blast
  have \<open>sum_list (map (\<lambda>t. labels_measure (all_edges os' t) (min_label os' t))
          (timestamps os))
      < sum_list (map (\<lambda>t. labels_measure (all_edges os t) (min_label os t))
          (timestamps os))\<close>
    by (rule sum_list_strict_mono_ex1[OF pointwise strict_ex])
  then show ?thesis
    using ts_eq by simp
qed


subsection \<open>Loop-update termination driver\<close>

lemma labels_inv_label_prop_input1_loop_updatesI:
  fixes os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes UPDATES: \<open>(cbufs', os_label_prop', os') =
      label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and msgs_inv: \<open>\<And>d t. (d, t) \<in> set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)) \<Longrightarrow>
      myfst t \<in> set (timestamps os_label_prop) \<and>
      fst (de1 os_label_prop d) \<in> all_vertices os_label_prop (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow>
        snd (de1 os_label_prop d) \<in> cc_of (all_edges os_label_prop q) (fst (de1 os_label_prop d)))\<close>
    and labels_os: \<open>\<And>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
  shows \<open>labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
proof -
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?base = \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>\<close>
  let ?consumed = \<open>CONSUMES 1 ?msgs ?base\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?consumed (input ?consumed 1))\<close>
    using UPDATES
    unfolding label_prop_input1_loop_updates_def Let_def
    by (auto split: prod.splits)
  have inv_consumed: \<open>label_prop_upd_inv ?consumed\<close>
  proof (rule label_prop_upd_inv_CONSUMES_port1I)
    show \<open>label_prop_upd_inv ?base\<close>
      using INV by simp
  next
    fix d t
    assume m: \<open>(d, t) \<in> set ?msgs\<close>
    show \<open>myfst t \<in> set (timestamps ?base) \<and>
      fst (de1 ?base d) \<in> all_vertices ?base (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow> snd (de1 ?base d) \<in> cc_of (all_edges ?base q) (fst (de1 ?base d)))\<close>
      using msgs_inv[OF m] by simp
  qed
  have labels_consumed: \<open>\<And>t. labels_inv (all_edges ?consumed t) (min_label ?consumed t)\<close>
    using labels_os by simp
  show ?thesis
    using os_label_prop'_eq labels_inv_fst_label_prop_input1_batched_inputI
      [OF labels_consumed inv_consumed, of t]
    by simp
qed

lemma label_prop_input1_loop_updates_sum_measure_decrease_if_label_output_nonempty:
  fixes os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes UPDATES: \<open>(cbufs', os_label_prop', os') =
      label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and out_nonempty: \<open>outpu os_label_prop' 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and msgs_inv: \<open>\<And>d t. (d, t) \<in> set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)) \<Longrightarrow>
      myfst t \<in> set (timestamps os_label_prop) \<and>
      fst (de1 os_label_prop d) \<in> all_vertices os_label_prop (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow>
        snd (de1 os_label_prop d) \<in> cc_of (all_edges os_label_prop q) (fst (de1 os_label_prop d)))\<close>
    and labels_os: \<open>\<And>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
  shows \<open>sum_list (map (\<lambda>t. labels_measure (all_edges os_label_prop' t) (min_label os_label_prop' t))
          (timestamps os_label_prop'))
      < sum_list (map (\<lambda>t. labels_measure (all_edges os_label_prop t) (min_label os_label_prop t))
          (timestamps os_label_prop))\<close>
proof -
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?base = \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>\<close>
  let ?consumed = \<open>CONSUMES 1 ?msgs ?base\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?consumed (input ?consumed 1))\<close>
    using UPDATES
    unfolding label_prop_input1_loop_updates_def Let_def
    by (auto split: prod.splits)
  have consumed_outpu: \<open>outpu ?consumed 1 = []\<close>
    unfolding fold_consumes by simp
  have msgs_input_self: \<open>set (input ?consumed 1) \<subseteq> set (input ?consumed 1)\<close>
    by simp
  have inv_consumed: \<open>label_prop_upd_inv ?consumed\<close>
  proof (rule label_prop_upd_inv_CONSUMES_port1I)
    show \<open>label_prop_upd_inv ?base\<close>
      using INV by simp
  next
    fix d t
    assume m: \<open>(d, t) \<in> set ?msgs\<close>
    show \<open>myfst t \<in> set (timestamps ?base) \<and>
      fst (de1 ?base d) \<in> all_vertices ?base (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow> snd (de1 ?base d) \<in> cc_of (all_edges ?base q) (fst (de1 ?base d)))\<close>
      using msgs_inv[OF m] by simp
  qed
  have labels_consumed: \<open>\<And>t. labels_inv (all_edges ?consumed t) (min_label ?consumed t)\<close>
    using labels_os by simp
  have labels_os': \<open>\<And>t. labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
    by (rule labels_inv_label_prop_input1_loop_updatesI[OF UPDATES INV msgs_inv labels_os])
  have consumed_decrease:
    \<open>sum_list (map (\<lambda>t. labels_measure (all_edges os_label_prop' t) (min_label os_label_prop' t))
        (timestamps os_label_prop'))
      < sum_list (map (\<lambda>t. labels_measure (all_edges ?consumed t) (min_label ?consumed t))
        (timestamps ?consumed))\<close>
    using labels_measure_sum_fst_label_prop_input1_batched_decreases_if_output_nonempty
      [of os_label_prop' ?consumed \<open>input ?consumed 1\<close>]
      os_label_prop'_eq consumed_outpu out_nonempty inv_consumed msgs_input_self labels_consumed labels_os'
    by simp
  have consumed_same:
    \<open>sum_list (map (\<lambda>t. labels_measure (all_edges ?consumed t) (min_label ?consumed t))
        (timestamps ?consumed)) =
      sum_list (map (\<lambda>t. labels_measure (all_edges os_label_prop t) (min_label os_label_prop t))
        (timestamps os_label_prop))\<close>
    unfolding fold_consumes min_label_def all_edges_def all_vertices_def neighbors_def
    by simp
  show ?thesis
    using consumed_decrease consumed_same by simp
qed



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

lemma label_prop_input1_loop_updates_timestmaps:
  "label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os') \<Longrightarrow>
   timestamps os_label_prop' = timestamps os_label_prop"
  unfolding label_prop_input1_loop_updates_def
  by clarsimp

subsection \<open>Frame facts for label_prop_input1_loop_updates\<close>

lemma fst_label_prop_input1_loop_updates[simp]:
  \<open>fst (label_prop_input1_loop_updates cbufs os_label_prop os) =
   cbufs((2, 1) := [], (1, 1) := [])\<close>
  unfolding label_prop_input1_loop_updates_def Let_def by simp

subsection \<open>Produced progress for label_prop_input1_loop_updates\<close>

lemma produ_fst_snd_label_prop_input1_loop_updates:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os_label_prop_consumed :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes os_label_prop_consumed_def:
    \<open>os_label_prop_consumed =
      CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  shows \<open>produ (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) =
    produ os_label_prop @
      map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
        (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1)))\<close>
  using os_label_prop_consumed_def
  unfolding label_prop_input1_loop_updates_def Let_def
  by (simp add: fold_consumes split_beta split: capability.splits)


section \<open>Dataplane invariant transfer lemmas\<close>

lemma dataplane_tracker_inv_outpu_then_fold_consumes:
  fixes os :: \<open>'nid :: {linorder,enum} \<Rightarrow> ('p :: {linorder,enum}, 'd, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) operator_state\<close>
    and cbufs :: \<open>'nid \<times> 'p \<Rightarrow> ('d \<times> 't) buf\<close>
    and sg :: \<open>('nid, 'p, 't) subgraph\<close>
  assumes Inv: \<open>dataplane_tracker_inv os cbufs sg\<close>
    and D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and GR: \<open>graph_summar_nt (summ sg) (nxt sg) os\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and edge: \<open>summ sg (Loc nid_up (Src p_up)) (Loc nid_dn (Trg p_dn)) \<noteq> {}\<^sub>A\<close>
    and nid_neq: \<open>nid_up \<noteq> nid_dn\<close>
  shows
    \<open>dataplane_tracker_inv
       (os(nid_up := (os nid_up)\<lparr>outpu := (outpu (os nid_up))(p_up := [])\<rparr>,
           nid_dn := fold (\<lambda>(d, t) s. consumes s p_dn t d)
                       (cbufs (nid_dn, p_dn) @ outpu (os nid_up) p_up)
                       (os nid_dn)))
       (cbufs((nid_dn, p_dn) := []))
       sg\<close>
proof -
  let ?os1 = "os(nid_up := (os nid_up)\<lparr>outpu := (outpu (os nid_up))(p_up := [])\<rparr>)"
  let ?cb1 = "cbufs((nid_dn, p_dn) := cbufs (nid_dn, p_dn) @ outpu (os nid_up) p_up)"
  have outpu_split: "outpu (os nid_up) p_up = outpu (os nid_up) p_up @ []"
    by simp
  have os1_eq: "?os1 = os(nid_up := (os nid_up)\<lparr>outpu :=
                 (\<lambda>p'. if p' = p_up then [] else outpu (os nid_up) p')\<rparr>)"
    by (auto simp: fun_upd_def)
  have inv1: "dataplane_tracker_inv ?os1 ?cb1 sg"
    apply (rule dataplane_tracker_inv_update_outputs
        [where nid=nid_up and p=p_up and xs="outpu (os nid_up) p_up" and ys="[]"
          and nid'=nid_dn and p'=p_dn])
    apply (rule Inv)
    apply (rule outpu_split)
    apply (simp add: fun_upd_def)
    apply simp
    apply (rule edge)
    apply (rule GR)
    done
  have GR1: "graph_summar_nt (summ sg) (nxt sg) ?os1"
    using GR by (auto simp: graph_summar_nt_def)
  let ?L = "cbufs (nid_dn, p_dn) @ outpu (os nid_up) p_up"
  let ?os2 = "?os1(nid_dn := fold (\<lambda>(d, t) s. consumes s p_dn t d) ?L (?os1 nid_dn))"
  let ?cb2 = "(\<lambda>(nid', p'). if nid' = nid_dn \<and> p' = p_dn then drop (length ?L) (?cb1 (nid_dn, p_dn))
                            else ?cb1 (nid', p'))"
  have len_le: "length ?L \<le> length (?cb1 (nid_dn, p_dn))"
    by simp
  have inv2: "dataplane_tracker_inv ?os2 ?cb2 sg"
    apply (rule dataplane_tracker_inv_fold_consumes
        [where os="?os1" and cbufs="?cb1" and nid=nid_dn and p=p_dn and n="length ?L"])
    apply (rule inv1)
    apply (rule D)
    apply (rule GR1)
    apply (rule len_le)
    apply (rule refl)
    apply simp
    done
  have take_all_eq: "take (length ?L) (?cb1 (nid_dn, p_dn)) = ?L"
    by (simp add: take_all)
  have drop_all_eq: "drop (length ?L) (?cb1 (nid_dn, p_dn)) = []"
    by simp
  have cb2_eq: "?cb2 = cbufs((nid_dn, p_dn) := [])"
    using drop_all_eq nid_neq
    by (auto simp: fun_eq_iff fun_upd_def split: prod.splits)
  have os1_dn: "?os1 nid_dn = os nid_dn"
    using nid_neq by simp
  have os2_eq: "?os2 = os(nid_up := (os nid_up)\<lparr>outpu := (outpu (os nid_up))(p_up := [])\<rparr>,
                          nid_dn := fold (\<lambda>(d, t) s. consumes s p_dn t d) ?L (os nid_dn))"
    using os1_dn by (simp add: fun_upd_def fun_eq_iff)
  show ?thesis
    using inv2 unfolding os2_eq cb2_eq .
qed

lemma dataplane_tracker_inv_produces_drops_dropcaps_shape:
  fixes caps_to_drop :: \<open>('p :: {enum,linorder}, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) capability list\<close>
  assumes D: \<open>dataflow_topology (summ sg) (-+-)\<close>
  shows
    \<open>noutput = (\<lambda>p. outpu (os nid) p @ oputs p) \<Longrightarrow>
     nocaps = (\<lambda>p. list_diff (ocaps (os nid) p)
                              (map capability.time (filter (\<lambda>c. out c = p) caps_to_drop))) \<Longrightarrow>
     ninput = (\<lambda>p. filter (\<lambda>(_, t). t \<notin> set (map capability.time (filter (\<lambda>c. out c = p) caps_to_drop)))
                          (input (os nid) p)) \<Longrightarrow>
     nprodu = produ (os nid) @ produs \<Longrightarrow>
     ninter = operator_state.inter (os nid)
              @ map (\<lambda>cap. (out cap, capability.time cap, - 1)) caps_to_drop \<Longrightarrow>
     (\<forall>p'. mset (map capability.time (filter (\<lambda>c. out c = p') caps_to_drop))
            \<subseteq># mset (ocaps (os nid) p')) \<Longrightarrow>
     (\<forall>(p, t, m) \<in> set produs. m > 0 \<and> t \<in> set (ocaps (os nid) p)) \<Longrightarrow>
     (\<forall>p. snd ` set (oputs p) \<subseteq> set (ocaps (os nid) p)) \<Longrightarrow>
     (\<forall>p. to_zmset (map snd (oputs p)) = zmset (map snd (filter (\<lambda>x. p = fst x) produs))) \<Longrightarrow>
     graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
     nxt sg = graph_to_nxt (summ sg) \<Longrightarrow>
     dataplane_tracker_inv os cbufs sg \<Longrightarrow>
     dataplane_tracker_inv (os(nid := os nid \<lparr>outpu := noutput, ocaps := nocaps,
        input := ninput, produ := nprodu, inter := ninter\<rparr>)) cbufs sg\<close>
proof -
  assume NOut: "noutput = (\<lambda>p. outpu (os nid) p @ oputs p)"
  assume NOcaps: "nocaps = (\<lambda>p. list_diff (ocaps (os nid) p)
                                  (map capability.time (filter (\<lambda>c. out c = p) caps_to_drop)))"
  assume NInput: "ninput = (\<lambda>p. filter (\<lambda>(_, t). t \<notin> set (map capability.time
                                          (filter (\<lambda>c. out c = p) caps_to_drop)))
                                       (input (os nid) p))"
  assume NProdu: "nprodu = produ (os nid) @ produs"
  assume NInter: "ninter = operator_state.inter (os nid)
                          @ map (\<lambda>cap. (out cap, capability.time cap, - 1)) caps_to_drop"
  assume Drops: "\<forall>p'. mset (map capability.time (filter (\<lambda>c. out c = p') caps_to_drop))
                       \<subseteq># mset (ocaps (os nid) p')"
  assume Produs: "\<forall>(p, t, m) \<in> set produs. m > 0 \<and> t \<in> set (ocaps (os nid) p)"
  assume Oputs: "\<forall>p. snd ` set (oputs p) \<subseteq> set (ocaps (os nid) p)"
  assume OPZ: "\<forall>p. to_zmset (map snd (oputs p)) = zmset (map snd (filter (\<lambda>x. p = fst x) produs))"
  assume G: "graph_summar_nt (summ sg) (nxt sg) os"
  assume Nxt: "nxt sg = graph_to_nxt (summ sg)"
  assume Inv: "dataplane_tracker_inv os cbufs sg"

  define drops :: "'p \<Rightarrow> 't list"
    where "drops = (\<lambda>p. map capability.time (filter (\<lambda>c. out c = p) caps_to_drop))"

  let ?ninter_concat = "operator_state.inter (os nid)
                        @ concat (map (\<lambda>p. map (\<lambda>t. (p, t, - 1 :: int)) (drops p)) Enum.enum)"

  let ?osPD = "os(nid := (os nid)\<lparr>outpu := noutput, ocaps := nocaps,
                                   input := ninput, produ := nprodu, inter := ?ninter_concat\<rparr>)"

  have NOcaps': "nocaps = (\<lambda>p. list_diff (ocaps (os nid) p) (drops p))"
    using NOcaps by (simp add: drops_def)
  have NInput': "ninput = (\<lambda>p. filter (\<lambda>(_, t). t \<notin> set (drops p)) (input (os nid) p))"
    using NInput by (simp add: drops_def)
  have Drops': "\<forall>p. mset (drops p) \<subseteq># mset (ocaps (os nid) p)"
    using Drops by (simp add: drops_def)

  have inv_PD: "dataplane_tracker_inv ?osPD cbufs sg"
    by (rule dataplane_tracker_inv_produces_drops[OF D NOut NOcaps' NInput' NProdu refl
            Drops' Produs Oputs OPZ G Nxt Inv])

  have group_caps:
    "mset (concat (map (\<lambda>p. map (\<lambda>t. (p, t, - 1 :: int))
                           (map capability.time (filter (\<lambda>c. out c = p) cs))) Enum.enum)) =
     mset (map (\<lambda>cap. (out cap, capability.time cap, - 1)) cs)" for cs :: "('p, 't) capability list"
  proof (induct cs)
    case Nil
    show ?case by simp
  next
    case (Cons c cs)
    let ?f = "\<lambda>p. map (\<lambda>t. (p, t, - 1 :: int)) (map capability.time (filter (\<lambda>c'. out c' = p) cs))"
    have rewrite:
      "concat (map (\<lambda>p. map (\<lambda>t. (p, t, - 1 :: int))
                            (map capability.time (filter (\<lambda>c'. out c' = p) (c # cs)))) Enum.enum)
       = concat (map (\<lambda>p. (if out c = p then [(p, capability.time c, - 1 :: int)] else []) @ ?f p)
                      Enum.enum)"
      by (rule arg_cong[where f=concat], rule map_cong[OF refl], simp)
    have enum_pick:
      "mset (concat (map (\<lambda>p :: 'p. if out c = p then [(p, capability.time c, - 1 :: int)] else [])
                          Enum.enum))
       = {#(out c, capability.time c, - 1)#}"
    proof -
      have aux: "distinct ps \<Longrightarrow> out c \<in> set ps \<Longrightarrow>
        mset (concat (map (\<lambda>p :: 'p. if out c = p then [(p, capability.time c, - 1 :: int)] else []) ps))
        = {#(out c, capability.time c, - 1)#}" for ps
        by (induct ps) auto
      show ?thesis
        by (rule aux[OF Enum.enum_class.enum_distinct Enum.enum_class.in_enum])
    qed
    show ?case
    proof -
      have split_mset_aux:
        "mset (concat (map (\<lambda>p. A p @ B p) ps)) =
         mset (concat (map A ps)) + mset (concat (map B ps))" for A B and ps :: "'p list"
        by (induct ps) simp_all
      have split_mset:
        "mset (concat (map (\<lambda>p. (if out c = p then [(p, capability.time c, - 1 :: int)] else []) @ ?f p) Enum.enum)) =
         mset (concat (map (\<lambda>p. if out c = p then [(p, capability.time c, - 1 :: int)] else []) Enum.enum)) +
         mset (concat (map ?f Enum.enum))"
        by (rule split_mset_aux)

      have "mset (concat (map (\<lambda>p. map (\<lambda>t. (p, t, - 1 :: int))
                            (map capability.time (filter (\<lambda>c'. out c' = p) (c # cs)))) Enum.enum)) =
        mset (concat (map (\<lambda>p. (if out c = p then [(p, capability.time c, - 1 :: int)] else []) @ ?f p)
                      Enum.enum))"
        using rewrite by simp
      also have "... = {#(out c, capability.time c, - 1)#} +
        mset (map (\<lambda>cap. (out cap, capability.time cap, - 1)) cs)"
        using split_mset enum_pick Cons.hyps by simp
      also have "... = mset (map (\<lambda>cap. (out cap, capability.time cap, - 1)) (c # cs))"
        by simp
      finally show ?thesis .
    qed


  qed

  have inter_mset_eq:
    "mset (operator_state.inter (?osPD nid)) = mset (operator_state.inter (?osPD nid \<lparr>inter := ninter\<rparr>))"
    using group_caps[of caps_to_drop] NInter by (simp add: drops_def)

  let ?osTarget = "os(nid := (os nid)\<lparr>outpu := noutput, ocaps := nocaps,
                                       input := ninput, produ := nprodu, inter := ninter\<rparr>)"

  have all_fields_match:
    "\<forall>nid'. intsum (?osTarget nid') = intsum (?osPD nid') \<and>
            ocaps (?osTarget nid') = ocaps (?osPD nid') \<and>
            consu (?osTarget nid') = consu (?osPD nid') \<and>
            mset (operator_state.inter (?osTarget nid')) = mset (operator_state.inter (?osPD nid')) \<and>
            produ (?osTarget nid') = produ (?osPD nid') \<and>
            outpu (?osTarget nid') = outpu (?osPD nid') \<and>
            front (?osTarget nid') = front (?osPD nid')"
    apply (intro allI conjI)
    subgoal for nid' by simp
    subgoal for nid' by simp
    subgoal for nid' by simp
    subgoal for nid' using group_caps[of caps_to_drop] NInter
      by (cases "nid' = nid") (simp_all add: drops_def)
    subgoal for nid' by simp
    subgoal for nid' by simp
    subgoal for nid' by simp
    done

  show ?thesis
    using inv_PD dataplane_tracker_inv_clean_reorder_inter[OF all_fields_match]
    by blast
qed

lemma dataplane_tracker_inv_produces_drop:
  fixes os :: \<open>'nid :: {linorder,enum} \<Rightarrow> ('p :: {linorder,enum}, 'd, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) operator_state\<close>
    and cbufs :: \<open>'nid \<times> 'p \<Rightarrow> ('d \<times> 't) buf\<close>
    and sg :: \<open>('nid, 'p, 't) subgraph\<close>
  assumes Inv: \<open>dataplane_tracker_inv (os(nid := s1)) cbufs sg\<close>
    and D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and GR: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := s1))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and batch_caps_exact:
      \<open>\<And>x cap. (x, cap) \<in> set batch \<Longrightarrow>
        capability.time cap \<in> set (ocaps s1 (out cap))\<close>
    and drops_subset_per_port:
      \<open>\<And>p'. mset (map capability.time (filter (\<lambda>c. out c = p') caps_to_drop)) \<subseteq>#
            mset (ocaps s1 p')\<close>
    and drops_disjoint_input:
      \<open>\<And>p'. set (map capability.time (filter (\<lambda>c. out c = p') caps_to_drop)) \<inter>
            snd ` set (input s1 p') = {}\<close>
  shows
    \<open>dataplane_tracker_inv
       (os(nid := drop_caps (produces s1 batch) caps_to_drop))
       cbufs sg\<close>
proof -
  let ?os0 = \<open>os(nid := s1)\<close>
  let ?oputs = \<open>\<lambda>p. map (\<lambda>(x, cap). (x, capability.time cap))
    (filter (\<lambda>(x, cap). out cap = p) batch)\<close>
  let ?produs = \<open>map (\<lambda>(x, cap). (out cap, capability.time cap, 1 :: int)) batch\<close>
  let ?drop_times = \<open>\<lambda>p. map capability.time (filter (\<lambda>c. out c = p) caps_to_drop)\<close>

  have input_filter:
    \<open>input s1 = (\<lambda>p. filter (\<lambda>(_, t). t \<notin> set (?drop_times p)) (input s1 p))\<close>
  proof (rule ext)
    fix p
    have all_not: \<open>\<forall>x\<in>set (input s1 p). case x of (_, t) \<Rightarrow> t \<notin> set (?drop_times p)\<close>
      using drops_disjoint_input[of p]
      by auto
    show \<open>input s1 p = filter (\<lambda>(_, t). t \<notin> set (?drop_times p)) (input s1 p)\<close>
      by (rule sym, subst filter_id_conv) (use all_not in auto)
  qed

  have Produs: \<open>\<forall>(p, t, m) \<in> set ?produs. m > 0 \<and> t \<in> set (ocaps (?os0 nid) p)\<close>
    using batch_caps_exact
    by (auto split: prod.splits capability.splits)

  have Oputs: \<open>\<forall>p. snd ` set (?oputs p) \<subseteq> set (ocaps (?os0 nid) p)\<close>
    using batch_caps_exact
    by (auto split: prod.splits capability.splits)

  have OPZ:
    \<open>\<forall>p. to_zmset (map snd (?oputs p)) =
      zmset (map snd (filter (\<lambda>x. p = fst x) ?produs))\<close>
  proof
    fix p
    have rhs:
      \<open>map snd (filter (\<lambda>x. p = fst x) ?produs) =
        map (\<lambda>(x, cap). (capability.time cap, 1 :: int))
          (filter (\<lambda>(x, cap). out cap = p) batch)\<close>
      by (induct batch) (auto simp: split_beta)
    have lhs_to:
      \<open>to_zmset (map snd (?oputs p)) =
        to_zmset (map (\<lambda>(x, cap). capability.time cap)
          (filter (\<lambda>(x, cap). out cap = p) batch))\<close>
      by (induct batch) (auto simp: split_beta)
    have zm:
      \<open>zmset (map (\<lambda>(x, cap). (capability.time cap, 1 :: int))
          (filter (\<lambda>(x, cap). out cap = p) batch)) =
        to_zmset (map (\<lambda>(x, cap). capability.time cap)
          (filter (\<lambda>(x, cap). out cap = p) batch))\<close>
      by (induct \<open>filter (\<lambda>(x, cap). out cap = p) batch\<close>) (auto simp: split_beta)
    show \<open>to_zmset (map snd (?oputs p)) =
      zmset (map snd (filter (\<lambda>x. p = fst x) ?produs))\<close>
      using lhs_to rhs zm by simp
  qed

  have inv_shape:
    \<open>dataplane_tracker_inv
      (?os0(nid := (?os0 nid)\<lparr>
        outpu := (\<lambda>p. outpu (?os0 nid) p @ ?oputs p),
        ocaps := (\<lambda>p. list_diff (ocaps (?os0 nid) p) (?drop_times p)),
        input := input s1,
        produ := produ (?os0 nid) @ ?produs,
        inter := operator_state.inter (?os0 nid) @
          map (\<lambda>cap. (out cap, capability.time cap, - 1)) caps_to_drop\<rparr>))
      cbufs sg\<close>
    apply (rule dataplane_tracker_inv_produces_drops_dropcaps_shape[OF D])
               apply (rule refl)
              apply (rule refl)
             apply (subst fun_upd_same)
             apply (rule input_filter)
            apply (rule refl)
           apply (rule refl)
          apply (rule allI)
          apply (subst fun_upd_same)
          apply (rule drops_subset_per_port)
         apply (rule Produs)
        apply (rule Oputs)
       apply (rule OPZ)
      apply (rule GR)
     apply (rule Nxt)
    apply (rule Inv)
    done

  have target_eq:
    \<open>os(nid := drop_caps (produces s1 batch) caps_to_drop) =
     ?os0(nid := (?os0 nid)\<lparr>
        outpu := (\<lambda>p. outpu (?os0 nid) p @ ?oputs p),
        ocaps := (\<lambda>p. list_diff (ocaps (?os0 nid) p) (?drop_times p)),
        input := input s1,
        produ := produ (?os0 nid) @ ?produs,
        inter := operator_state.inter (?os0 nid) @
          map (\<lambda>cap. (out cap, capability.time cap, - 1)) caps_to_drop\<rparr>)\<close>
    unfolding drop_caps_def produces_def
    by (cases s1) simp

  show ?thesis
    using inv_shape target_eq by simp
qed


section \<open>Base-state projection\<close>

definition op_state_base where
  \<open>op_state_base os = \<lparr>
    intsum = intsum os,
    consu = consu os,
    inter = inter os,
    produ = produ os,
    input = input os,
    outpu = outpu os,
    front = front os,
    ocaps = ocaps os,
    initia = initia os\<rparr>\<close>

lemma op_state_base_add_caps[simp]:
  \<open>op_state_base (add_caps os caps) = add_caps (op_state_base os) caps\<close>
  unfolding op_state_base_def add_caps_def
  by (rule operator_state_eqI) (simp_all add: fun_eq_iff)

lemma op_state_base_produces[simp]:
  \<open>op_state_base (produces os batch) = produces (op_state_base os) batch\<close>
  unfolding op_state_base_def produces_def
  by (rule operator_state_eqI) (simp_all add: fun_eq_iff)

lemma op_state_base_drop_caps[simp]:
  \<open>op_state_base (drop_caps os caps) = drop_caps (op_state_base os) caps\<close>
  unfolding op_state_base_def drop_caps_def
  by (rule operator_state_eqI) (simp_all add: fun_eq_iff)

lemma op_state_base_release_caps[simp]:
  \<open>op_state_base (release_caps os p) = release_caps (op_state_base os) p\<close>
  unfolding op_state_base_def release_caps_def drop_caps_def Let_def
  by (rule operator_state_eqI) (simp_all add: trace_simp fun_eq_iff)

lemma op_state_base_outpu_update[simp]:
  \<open>op_state_base (os\<lparr>outpu := outs\<rparr>) = (op_state_base os)\<lparr>outpu := outs\<rparr>\<close>
  unfolding op_state_base_def
  by (rule operator_state_eqI) simp_all

lemma op_state_base_CONSUMES[simp]:
  \<open>op_state_base (CONSUMES p xs os) = CONSUMES p xs (op_state_base os)\<close>
  unfolding op_state_base_def fold_consumes
  by (rule operator_state_eqI) (simp_all add: fun_eq_iff)

section \<open>Capability bookkeeping for produced batches\<close>

lemma cap_times_filter_single_port_subset:
  assumes "mset xs \<subseteq># mset (ocaps os p)"
  shows "\<forall>p'. mset (map capability.time (filter (\<lambda>c. out c = p') (map (\<lambda>t. Cap t p) xs))) \<subseteq># mset (ocaps os p')"
proof (intro allI)
  fix p'
  have filt_eq:
    "map capability.time (filter (\<lambda>c. out c = p') (map (\<lambda>t. Cap t p) xs)) =
      (if p' = p then xs else [])"
    by (induct xs) auto
  show "mset (map capability.time (filter (\<lambda>c. out c = p') (map (\<lambda>t. Cap t p) xs))) \<subseteq># mset (ocaps os p')"
    using assms filt_eq by auto
qed

lemma produced_oputs_caps_from_produs:
  assumes "\<forall>(p, t, m) \<in> set (map (\<lambda>(x, cap). (out cap, capability.time cap, 1 :: int)) batch).
    m > 0 \<and> t \<in> set (ocaps os p)"
  shows "\<forall>p. snd ` set (map (\<lambda>(x, cap). (x, capability.time cap)) (filter (\<lambda>(x, cap). out cap = p) batch)) \<subseteq> set (ocaps os p)"
  using assms
  by (auto split: prod.splits)

lemma produced_oputs_produs_zmset:
  "\<forall>p. to_zmset (map snd (map (\<lambda>(x, cap). (x, capability.time cap)) (filter (\<lambda>(x, cap). out cap = p) batch))) =
    zmset (map snd (filter (\<lambda>x. p = fst x) (map (\<lambda>(x, cap). (out cap, capability.time cap, 1 :: int)) batch)))"
  by (induct batch) (auto simp add: split_beta zmset_map_one update_zmultiset_one add.commute split: prod.splits capability.splits)


subsection \<open>Input capability preservation for input-1 batches\<close>

lemma label_prop_input1_step_batch_caps:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes IOC: \<open>input_ocaps_inv os\<close>
    and zero: \<open>0 \<in> set (intsum os 1 1)\<close>
    and input: \<open>(d, t) \<in> set (input os 1)\<close>
    and member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os d t)\<close>
  shows \<open>\<exists>t'\<in>set (ocaps os (out cap)). t' \<le> capability.time cap\<close>
  using member input IOC zero
  unfolding label_prop_input1_step_batch_def label_prop_label_batch_def
    label_prop_neighbor_batch_def input_ocaps_inv_def
  apply (auto simp add: zero_myprod_def less_eq_myprod_def split: if_splits)
  subgoal for cur_t v
    apply (rule bexI[where x=t])
     apply (cases t; simp add: less_eq_myprod_def)
    apply force
    done
  done

lemma input_ocaps_inv_label_prop_input1_step_stateI:
  assumes \<open>input_ocaps_inv os\<close>
  shows \<open>input_ocaps_inv (label_prop_input1_step_state os d t)\<close>
  unfolding label_prop_input1_step_state_def Let_def
  apply (rule input_ocaps_inv_release_capsI)
  apply (rule input_ocaps_inv_drop_produces_add_capsI)
  apply (rule input_ocaps_inv_label_prop_label_record_updateI)
  apply (rule input_ocaps_inv_input_tlI)
  apply (rule assms)
  done

lemma input_ocaps_inv_fst_label_prop_input1_batchedI:
  assumes \<open>input_ocaps_inv os\<close>
  shows \<open>input_ocaps_inv (fst (label_prop_input1_batched os msgs))\<close>
  using assms
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  have step_inv: \<open>input_ocaps_inv (label_prop_input1_step_state os d t)\<close>
    by (rule input_ocaps_inv_label_prop_input1_step_stateI[OF Cons.prems])
  obtain os_final batches where rec:
    \<open>label_prop_input1_batched (label_prop_input1_step_state os d t) msgs = (os_final, batches)\<close>
    by (cases \<open>label_prop_input1_batched (label_prop_input1_step_state os d t) msgs\<close>)
  show ?case
    using Cons.hyps[OF step_inv] msg_eq rec
    by simp

qed

lemma input_ocaps_inv_CONSUMES:
  assumes \<open>input_ocaps_inv os\<close>
  shows \<open>input_ocaps_inv (CONSUMES p xs os)\<close>
  using assms
  by (induct xs arbitrary: os) (auto simp add: inputs_ocaps_inv_consumes split: prod.splits)

lemma ocaps_CONSUMES_other_port:
  fixes os :: \<open>('p :: enum, 'd, 't :: plus) operator_state\<close>
  assumes \<open>intsum os p p' = []\<close>
  shows \<open>ocaps (CONSUMES p xs os) p' = ocaps os p'\<close>
  using assms
proof (induct xs arbitrary: os)
  case Nil
  thus ?case unfolding fold_consumes by simp
next
  case (Cons x xs)
  obtain d t where x_eq: \<open>x = (d, t)\<close> by (cases x)
  let ?os' = \<open>consumes os p t d\<close>
  have intsum_step: \<open>intsum ?os' p p' = intsum os p p'\<close>
    unfolding consumes_def add_caps_def by simp
  have empty_filter: \<open>\<And>p''. filter (\<lambda>cap. out cap = p')
        (map (\<lambda>t'. Cap (t + t') p'') (intsum os p p'')) = []\<close>
  proof -
    fix p''
    show \<open>filter (\<lambda>cap. out cap = p')
              (map (\<lambda>t'. Cap (t + t') p'') (intsum os p p'')) = []\<close>
    proof (cases \<open>p'' = p'\<close>)
      case True
      thus ?thesis using Cons.prems by (simp add: filter_map comp_def filter_True)
    next
      case False
      thus ?thesis by (simp add: filter_map comp_def filter_False)
    qed
  qed
  have ocaps_step: \<open>ocaps ?os' p' = ocaps os p'\<close>
    unfolding consumes_def add_caps_def
    using empty_filter
    by (simp add: enum_class.enum_UNIV filter_concat)
  have \<open>ocaps (CONSUMES p (x # xs) os) p' = ocaps (CONSUMES p xs ?os') p'\<close>
    unfolding fold_consumes x_eq by simp
  also have \<open>... = ocaps ?os' p'\<close>
    using Cons.hyps Cons.prems intsum_step by simp
  also have \<open>... = ocaps os p'\<close>
    using ocaps_step .
  finally show ?case .
qed


subsection \<open>Dataplane preservation for input-1 batches\<close>

lemma dataplane_tracker_inv_input_update:
  assumes \<open>dataplane_tracker_inv os cbufs sg\<close>
  shows \<open>dataplane_tracker_inv (os(nid := (os nid)\<lparr>input := inp\<rparr>)) cbufs sg\<close>
proof -
  have fields: \<open>\<forall>nid'. intsum (os nid') = intsum ((os(nid := (os nid)\<lparr>input := inp\<rparr>)) nid') \<and>
    ocaps (os nid') = ocaps ((os(nid := (os nid)\<lparr>input := inp\<rparr>)) nid') \<and>
    consu (os nid') = consu ((os(nid := (os nid)\<lparr>input := inp\<rparr>)) nid') \<and>
    operator_state.inter (os nid') = operator_state.inter ((os(nid := (os nid)\<lparr>input := inp\<rparr>)) nid') \<and>
    produ (os nid') = produ ((os(nid := (os nid)\<lparr>input := inp\<rparr>)) nid') \<and>
    outpu (os nid') = outpu ((os(nid := (os nid)\<lparr>input := inp\<rparr>)) nid') \<and>
    front (os nid') = front ((os(nid := (os nid)\<lparr>input := inp\<rparr>)) nid')\<close>
    by (auto split: if_splits)
  show ?thesis
    using iffD1[OF dataplane_tracker_inv_clean_input[OF fields] assms] .
qed

lemma dataplane_tracker_inv_label_prop_input1_step_state:
  fixes ls :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>'nid :: {enum, linorder} \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
  assumes D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and Inv: \<open>dataplane_tracker_inv (os(nid := op_state_base ls)) cbufs sg\<close>
    and G: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and IOC: \<open>input_ocaps_inv ls\<close>
    and zero: \<open>0 \<in> set (intsum ls 1 1)\<close>
    and input: \<open>input ls 1 = (d, t) # xs\<close>
  shows \<open>dataplane_tracker_inv (os(nid := op_state_base (label_prop_input1_step_state ls d t))) cbufs sg\<close>
proof -
  let ?ls1 = \<open>input_tl ls 1\<close>
  let ?ls2 = \<open>label_prop_label_record_update ?ls1 (myfst t) (fst (de1 ls d))
    (min (min_label ls (myfst t) (fst (de1 ls d))) (snd (de1 ls d)))\<close>
  let ?batch = \<open>label_prop_input1_step_batch ls d t\<close>
  have inv_base2: \<open>dataplane_tracker_inv (os(nid := op_state_base ?ls2)) cbufs sg\<close>
  proof -
    have fields: \<open>\<forall>nid'. intsum ((os(nid := op_state_base ls)) nid') = intsum ((os(nid := op_state_base ?ls2)) nid') \<and>
      ocaps ((os(nid := op_state_base ls)) nid') = ocaps ((os(nid := op_state_base ?ls2)) nid') \<and>
      consu ((os(nid := op_state_base ls)) nid') = consu ((os(nid := op_state_base ?ls2)) nid') \<and>
      inter ((os(nid := op_state_base ls)) nid') = inter ((os(nid := op_state_base ?ls2)) nid') \<and>
      produ ((os(nid := op_state_base ls)) nid') = produ ((os(nid := op_state_base ?ls2)) nid') \<and>
      outpu ((os(nid := op_state_base ls)) nid') = outpu ((os(nid := op_state_base ?ls2)) nid') \<and>
      front ((os(nid := op_state_base ls)) nid') = front ((os(nid := op_state_base ?ls2)) nid')\<close>
      by (auto simp add: op_state_base_def input_tl_def label_prop_label_record_update_def)
    show ?thesis
      using iffD1[OF dataplane_tracker_inv_clean_input[OF fields] Inv] .
  qed
  have G_base2: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls2))\<close>
  proof -
    have geq: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls2)) =
      graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
      by (rule graph_summar_nt_intsum_cong) (simp add: op_state_base_def input_tl_def label_prop_label_record_update_def)
    show ?thesis
      using geq G by simp
  qed
  have input_member: \<open>(d, t) \<in> set (input ls 1)\<close>
    using input by simp
  have batch_caps: \<open>\<And>x cap. (x, cap) \<in> set ?batch \<Longrightarrow>
    \<exists>t'\<in>set (ocaps (op_state_base ?ls2) (out cap)). t' \<le> capability.time cap\<close>
    using label_prop_input1_step_batch_caps[OF IOC zero input_member]
    by (simp add: op_state_base_def input_tl_def label_prop_label_record_update_def)
  have inv_drop:
    \<open>dataplane_tracker_inv
      (os(nid := drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch)))
      cbufs sg\<close>
    by (rule dataplane_tracker_inv_add_caps_produces_drop_caps_update[OF D inv_base2 G_base2 Nxt batch_caps])
  have G_drop:
    \<open>graph_summar_nt (summ sg) (nxt sg)
      (os(nid := drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch)))\<close>
  proof -
    have geq: \<open>graph_summar_nt (summ sg) (nxt sg)
      (os(nid := drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch))) =
      graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls2))\<close>
      by (rule graph_summar_nt_intsum_cong) (simp add: drop_caps_def produces_def add_caps_def)
    show ?thesis
      using geq G_base2 by simp
  qed
  have inv_release:
    \<open>dataplane_tracker_inv
      (os(nid := release_caps (drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch)) 1))
      cbufs sg\<close>
    by (rule dataplane_tracker_inv_release_caps_update[OF D inv_drop G_drop Nxt])
  have step_base:
    \<open>op_state_base (label_prop_input1_step_state ls d t) =
      release_caps (drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch)) 1\<close>
    unfolding label_prop_input1_step_state_def label_prop_input1_step_batch_def Let_def
    by simp
  show ?thesis
    using inv_release by (simp add: step_base)
qed
lemma dataplane_tracker_inv_label_prop_input1_batched:
  fixes ls :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>'nid :: {enum, linorder} \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
  assumes D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and Inv: \<open>dataplane_tracker_inv (os(nid := op_state_base ls)) cbufs sg\<close>
    and G: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and IOC: \<open>input_ocaps_inv ls\<close>
    and zero: \<open>0 \<in> set (intsum ls 1 1)\<close>
  shows \<open>dataplane_tracker_inv
    (os(nid := op_state_base (fst (label_prop_input1_batched ls (input ls 1))))) cbufs sg\<close>
proof -
  have aux:
    \<open>msgs = input ls 1 \<Longrightarrow>
      dataplane_tracker_inv (os(nid := op_state_base ls)) cbufs sg \<Longrightarrow>
      graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls)) \<Longrightarrow>
      input_ocaps_inv ls \<Longrightarrow>
      0 \<in> set (intsum ls 1 1) \<Longrightarrow>
      dataplane_tracker_inv
        (os(nid := op_state_base (fst (label_prop_input1_batched ls (input ls 1))))) cbufs sg\<close>
    for msgs ls
  proof (induct msgs arbitrary: ls)
    case Nil
    then show ?case by simp
  next
    case (Cons msg msgs)
    obtain d t where msg_eq: \<open>msg = (d, t)\<close>
      by (cases msg)
    have input_eq: \<open>input ls 1 = (d, t) # msgs\<close>
      using Cons.prems(1) msg_eq by simp
    let ?ls' = \<open>label_prop_input1_step_state ls d t\<close>
    have inv_step: \<open>dataplane_tracker_inv (os(nid := op_state_base ?ls')) cbufs sg\<close>
      by (rule dataplane_tracker_inv_label_prop_input1_step_state[OF D Cons.prems(2) Cons.prems(3) Nxt Cons.prems(4) Cons.prems(5) input_eq])
    have G_step: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls'))\<close>
    proof -
      have geq: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls')) =
        graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
        by (rule graph_summar_nt_intsum_cong) (simp add: label_prop_input1_step_state_def Let_def op_state_base_def)
      show ?thesis
        using geq Cons.prems(3) by simp
    qed
    have IOC_step: \<open>input_ocaps_inv ?ls'\<close>
      by (rule input_ocaps_inv_label_prop_input1_step_stateI[OF Cons.prems(4)])
    have zero_step: \<open>0 \<in> set (intsum ?ls' 1 1)\<close>
      using Cons.prems(5) by simp
    have input_step: \<open>msgs = input ?ls' 1\<close>
      using input_eq by simp
    have rec: \<open>dataplane_tracker_inv
      (os(nid := op_state_base (fst (label_prop_input1_batched ?ls' (input ?ls' 1))))) cbufs sg\<close>
      by (rule Cons.hyps[OF input_step inv_step G_step IOC_step zero_step])
    obtain ls_final batches where rec_eq:
      \<open>label_prop_input1_batched ?ls' msgs = (ls_final, batches)\<close>
      by (cases \<open>label_prop_input1_batched ?ls' msgs\<close>)
    show ?case
      using rec input_eq msg_eq rec_eq by (simp add: fun_upd_def)
  qed
  show ?thesis
    by (rule aux[OF refl Inv G IOC zero])
qed



subsection \<open>One-step dataplane preservation for input-1 loop update\<close>
lemma label_prop_input1_loop_updates_preserves_dataplane_tracker_inv:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and sg :: \<open>(3, 2, (nat, nat) myprod) subgraph\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  assumes step:
    \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  and D: \<open>dataflow_topology (summ sg) (-+-)\<close>
  and GR: \<open>graph_summar_nt (summ sg) (nxt sg) os\<close>
  and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
  and Inv: \<open>dataplane_tracker_inv os cbufs sg\<close>
  and label_prop_extension:
    \<open>os_label_prop = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
  and Summ: \<open>summ sg = antichain_from_list \<circ>\<circ> raw_summary\<close>
  and Intsum: \<open>\<forall>n. intsum (os n) = (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
  and IOC1: \<open>input_ocaps_inv (os 1)\<close>
  and IOC2: \<open>input_ocaps_inv (os 2)\<close>
  shows \<open>dataplane_tracker_inv (os'(1 := op_state_base os_label_prop')) cbufs' sg\<close>

proof -
  let ?b1 = "cbufs (1, 1)"
  let ?b21 = "cbufs (2, 1)"
  let ?out1 = "outpu os_label_prop 1"
  let ?in21 = "input (os 2) 1"
  let ?inc = "MyPair 0 (Suc 0)"
  let ?ts_caps2_extra = "map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- ?inc) (?b21 @ ?out1)"
  let ?ts_drop = "ocaps (os 2) 1 @ ?ts_caps2_extra"
  let ?batch = "map (\<lambda>x. (fst x, Cap (snd x -+- ?inc) 1)) (?in21 @ ?b21 @ ?out1)"
  let ?os2_consumed = "CONSUMES 1 (?b21 @ ?out1) (os 2)"
  let ?os2_after_prod = "produces ?os2_consumed ?batch"
  let ?os2_after_drop = "drop_caps ?os2_after_prod (map (\<lambda>t. Cap t 1) ?ts_drop)"
  let ?os2' = "?os2_after_drop\<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>"

  have cbufs'_eq: "cbufs' = cbufs((2, 1) := [], (1, 1) := [])"
    and os'_eq: "os' = os(2 := ?os2')"
    using step unfolding label_prop_input1_loop_updates_def Let_def
    by (simp_all split: prod.splits)

  let ?os_label_prop_consumed =
    "CONSUMES 1
      (?b1 @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- ?inc)) (?in21 @ ?b21 @ ?out1))
      (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)"

  have base_label_prop: "op_state_base os_label_prop = os 1"
    using label_prop_extension
    unfolding op_state_base_def
    by (simp add: operator_state.defs)

  have IOC_label_prop: "input_ocaps_inv os_label_prop"
    using IOC1 label_prop_extension
    unfolding input_ocaps_inv_def
    by (simp add: operator_state.defs)

  have zero_label_prop: "0 \<in> set (intsum os_label_prop 1 1)"
    using Intsum label_prop_extension
    by (simp add: raw_summary_def zero_myprod_def operator_state.defs)

  have out1_eq: "?out1 = outpu (os 1) 1"
    using label_prop_extension by (simp add: operator_state.defs)

  have edge12: "summ sg (Loc (1 :: 3) (Src (1 :: 2))) (Loc (2 :: 3) (Trg (1 :: 2))) \<noteq> {}\<^sub>A"
    using Summ
    by (simp add: raw_summary_def antichain_from_list_singleton)

  have edge21: "summ sg (Loc (2 :: 3) (Src (1 :: 2))) (Loc (1 :: 3) (Trg (1 :: 2))) \<noteq> {}\<^sub>A"
    using Summ
    by (simp add: raw_summary_def antichain_from_list_singleton)

  let ?osA = "os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>,
                 2 := ?os2_consumed)"
  let ?cbufsA = "cbufs((2, 1) := [])"

  have invA: "dataplane_tracker_inv ?osA ?cbufsA sg"
  proof -
    have raw: "dataplane_tracker_inv
      (os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>,
          2 := CONSUMES 1 (cbufs (2, 1) @ outpu (os 1) 1) (os 2)))
      (cbufs((2, 1) := [])) sg"
      by (rule dataplane_tracker_inv_outpu_then_fold_consumes
          [where nid_up=1 and p_up=1 and nid_dn=2 and p_dn=1,
            OF Inv D GR Nxt edge12]) simp
    show ?thesis
      using raw out1_eq by simp
  qed

  have GA: "graph_summar_nt (summ sg) (nxt sg) ?osA"
  proof -
    have "graph_summar_nt (summ sg) (nxt sg) ?osA = graph_summar_nt (summ sg) (nxt sg) os"
      by (rule graph_summar_nt_intsum_cong) (simp add: fold_consumes)
    then show ?thesis
      using GR by simp
  qed

  let ?msgsA = "?b1 @ outpu (os 2) 1"
  let ?osB = "?osA(2 := (?osA 2)\<lparr>outpu := (outpu (?osA 2))(1 := [])\<rparr>,
                   1 := CONSUMES 1 ?msgsA (?osA 1))"
  let ?cbufsB = "?cbufsA((1, 1) := [])"

  have invB: "dataplane_tracker_inv ?osB ?cbufsB sg"
  proof -
    have raw: "dataplane_tracker_inv
      (?osA(2 := (?osA 2)\<lparr>outpu := (outpu (?osA 2))(1 := [])\<rparr>,
             1 := CONSUMES 1 (?cbufsA (1, 1) @ outpu (?osA 2) 1) (?osA 1)))
      (?cbufsA((1, 1) := [])) sg"
      by (rule dataplane_tracker_inv_outpu_then_fold_consumes
          [where nid_up=2 and p_up=1 and nid_dn=1 and p_dn=1,
            OF invA D GA Nxt edge21]) simp
    show ?thesis
      using raw by (simp add: fold_consumes)
  qed

  have GB: "graph_summar_nt (summ sg) (nxt sg) ?osB"
  proof -
    have "graph_summar_nt (summ sg) (nxt sg) ?osB = graph_summar_nt (summ sg) (nxt sg) os"
      by (rule graph_summar_nt_intsum_cong) (simp add: fold_consumes)
    then show ?thesis
      using GR by simp
  qed

  let ?caps_drop = "map (\<lambda>t. Cap t 1) ?ts_drop"
  let ?produs = "map (\<lambda>(x, cap). (out cap, capability.time cap, 1 :: int)) ?batch"
  let ?oputs = "\<lambda>p. map (\<lambda>(x, cap). (x, capability.time cap)) (filter (\<lambda>(x, cap). out cap = p) ?batch)"


  have concat_shift:
    "concat (map (\<lambda>(d, t). [t -+- ?inc]) xs) = map (\<lambda>(d, t). t -+- ?inc) xs" for xs
    by (induct xs) auto
  have osB2_ocaps1:
    "ocaps (?osB 2) 1 = ocaps (os 2) 1 @ map (\<lambda>(d, t). t -+- ?inc) (?b21 @ ?out1)"
    using Intsum
    by (simp add: fold_consumes raw_summary_def concat_shift)




  have input_caps2:
    "\<And>d t. (d, t) \<in> set ?in21 \<Longrightarrow> t -+- ?inc \<in> set (ocaps (os 2) 1)"
  proof -
    fix d t
    assume mem: "(d, t) \<in> set ?in21"
    have inc: "?inc \<in> set (intsum (os 2) 1 1)"
      using Intsum by (simp add: raw_summary_def)
    show "t -+- ?inc \<in> set (ocaps (os 2) 1)"
      using IOC2 mem inc unfolding input_ocaps_inv_def by blast
  qed

  have shifted_caps_B:
    "\<And>d t. (d, t) \<in> set (?in21 @ ?b21 @ ?out1) \<Longrightarrow> t -+- ?inc \<in> set (ocaps (?osB 2) 1)"
    using input_caps2 osB2_ocaps1 by auto

  have prod_caps_B: "\<forall>(p, t, m) \<in> set ?produs. m > 0 \<and> t \<in> set (ocaps (?osB 2) p)"
  proof (rule ballI)
    fix y :: "2 \<times> (nat, nat) myprod \<times> int"

    assume y: "y \<in> set ?produs"
    then obtain x where x_mem: "x \<in> set (?in21 @ ?b21 @ ?out1)"
      and y_eq: "y = (1, snd x -+- ?inc, 1)"
      by auto
    obtain d t where x_eq: "x = (d, t)"
      by (cases x)
    show "case y of (p, t, m) \<Rightarrow> 0 < m \<and> t \<in> set (ocaps (?osB 2) p)"
      using shifted_caps_B[of d t] x_mem x_eq y_eq by simp
  qed

  have ts_drop_subset_B: "mset ?ts_drop \<subseteq># mset (ocaps (?osB 2) 1)"
    using osB2_ocaps1 by (simp add: split_beta)

  have drops_subset_B:
    "\<forall>p'. mset (map capability.time (filter (\<lambda>c. out c = p') ?caps_drop)) \<subseteq># mset (ocaps (?osB 2) p')"
    by (rule cap_times_filter_single_port_subset[OF ts_drop_subset_B])

  have oputs_caps_B: "\<forall>p. snd ` set (?oputs p) \<subseteq> set (ocaps (?osB 2) p)"
    by (rule produced_oputs_caps_from_produs[OF prod_caps_B])

  have oputs_produs_B:
    "\<forall>p. to_zmset (map snd (?oputs p)) = zmset (map snd (filter (\<lambda>x. p = fst x) ?produs))"
    by (rule produced_oputs_produs_zmset)

  let ?drop_times = "\<lambda>p. map capability.time (filter (\<lambda>c. out c = p) ?caps_drop)"
  let ?os2C_abs = "(?osB 2)\<lparr>
    outpu := (\<lambda>p. outpu (?osB 2) p @ ?oputs p),
    ocaps := (\<lambda>p. list_diff (ocaps (?osB 2) p) (?drop_times p)),
    input := (\<lambda>p. filter (\<lambda>(_, t). t \<notin> set (?drop_times p)) (input (?osB 2) p)),
    produ := produ (?osB 2) @ ?produs,
    inter := operator_state.inter (?osB 2) @ map (\<lambda>cap. (out cap, capability.time cap, - 1)) ?caps_drop\<rparr>"
  let ?osC_abs = "?osB(2 := ?os2C_abs)"

  have invC_abs: "dataplane_tracker_inv ?osC_abs ?cbufsB sg"
    by (rule dataplane_tracker_inv_produces_drops_dropcaps_shape
        [OF D refl refl refl refl refl drops_subset_B prod_caps_B oputs_caps_B oputs_produs_B GB Nxt invB])

  have GC_abs: "graph_summar_nt (summ sg) (nxt sg) ?osC_abs"
  proof -
    have "graph_summar_nt (summ sg) (nxt sg) ?osC_abs = graph_summar_nt (summ sg) (nxt sg) ?osB"
      by (rule graph_summar_nt_intsum_cong) simp
    then show ?thesis
      using GB by simp
  qed

  let ?osD = "?osC_abs(2 := (?osC_abs 2)\<lparr>outpu := (outpu (?osC_abs 2))(1 := [])\<rparr>,
                       1 := CONSUMES 1 (?cbufsB (1, 1) @ outpu (?osC_abs 2) 1) (?osC_abs 1))"

  have invD: "dataplane_tracker_inv ?osD (?cbufsB((1, 1) := [])) sg"
    by (rule dataplane_tracker_inv_outpu_then_fold_consumes
        [where nid_up=2 and p_up=1 and nid_dn=1 and p_dn=1,
          OF invC_abs D GC_abs Nxt edge21]) simp

  have oputs1_map:
    "map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = 1)
          (map (\<lambda>x. (fst x, Cap (snd x -+- ?inc) 1)) xs)) =
      map (\<lambda>(d, t). (d, t -+- ?inc)) xs" for xs
    by (induct xs) (auto split: prod.splits)

  have oputs1_eq:
    "?oputs 1 = map (\<lambda>(d, t). (d, t -+- ?inc)) (?in21 @ ?b21 @ ?out1)"
    by (simp add: oputs1_map)

  have out_label_prop: "outpu os_label_prop = outpu (os 1)"
    using label_prop_extension by (simp add: operator_state.defs)

  have base_clear:
    "op_state_base (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>) =
      (os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>"
    using base_label_prop out_label_prop by simp

  have osB1:
    "?osB 1 = CONSUMES 1 ?msgsA ((os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>)"
    by simp

  have osC_abs_1: "?osC_abs 1 = ?osB 1"
    by simp

  have osC_abs_out2_1: "outpu (?osC_abs 2) 1 = ?oputs 1"
    by (simp add: oputs1_map)

  have osD_to_B: "?osD 1 = CONSUMES 1 (?oputs 1) (?osB 1)"
  proof -
    have raw: "?osD 1 = CONSUMES 1 (?cbufsB (1, 1) @ outpu (?osC_abs 2) 1) (?osC_abs 1)"
      by simp
    have msgs: "?cbufsB (1, 1) @ outpu (?osC_abs 2) 1 = ?oputs 1"
      using osC_abs_out2_1 by simp
    show ?thesis
      apply (subst raw)
      apply (subst msgs)
      apply (subst osC_abs_1)
      apply (rule refl)
      done
  qed

  have osD_to_base:
    "?osD 1 = CONSUMES 1 (?msgsA @ ?oputs 1) ((os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>)"
    apply (subst osD_to_B)
    apply (subst osB1)
    apply (rule CONSUMES_CONSUMES)
    done

  have msgs_oputs_eq:
    "?msgsA @ ?oputs 1 =
      ?b1 @ outpu (os 2) 1 @ map (\<lambda>(d, t). (d, t -+- ?inc)) (?in21 @ ?b21 @ ?out1)"
    using oputs1_eq by simp

  have label_prop_consumed_base:
    "op_state_base ?os_label_prop_consumed =
      CONSUMES 1 (?msgsA @ ?oputs 1) ((os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>)"
    apply (simp only: op_state_base_CONSUMES)
    apply (subst base_clear)
    apply (subst msgs_oputs_eq)
    apply (rule refl)
    done

  have osD_slot1: "?osD 1 = op_state_base ?os_label_prop_consumed"
    apply (subst osD_to_base)
    apply (subst label_prop_consumed_base)
    apply (rule refl)
    done

  let ?osE = "?osD(2 := (?osD 2)\<lparr>input := (input (os 2))(1 := [])\<rparr>)"

  have invE: "dataplane_tracker_inv ?osE (?cbufsB((1, 1) := [])) sg"
    by (rule dataplane_tracker_inv_input_update
        [where nid=2 and inp="(input (os 2))(1 := [])", OF invD])


  have oputs_other_map:
    "p \<noteq> 1 \<Longrightarrow>
      map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = p)
          (map (\<lambda>x. (fst x, Cap (snd x -+- ?inc) 1)) xs)) = []" for p :: 2 and xs
    by (induct xs) (auto split: prod.splits)

  have oputs_other: "p \<noteq> 1 \<Longrightarrow> ?oputs p = []" for p :: 2
    by (rule oputs_other_map)

  have osB2_eq: "?osB 2 = ?os2_consumed\<lparr>outpu := (outpu (os 2))(1 := [])\<rparr>"
    by simp

  have osE2_outpu: "outpu (?osE 2) = outpu ?os2'"
  proof (rule ext)
    fix p :: 2
    show "outpu (?osE 2) p = outpu ?os2' p"
    proof (cases "p = 1")
      case True
      then show ?thesis
        by (simp add: drop_caps_def produces_def)
    next
      case False
      then show ?thesis
        using oputs_other[OF False]
        by (simp add: osB2_eq drop_caps_def produces_def)
    qed
  qed

  have osE2_eq: "?osE 2 = ?os2'"
  proof (rule operator_state_eqI)
    show "intsum (?osE 2) = intsum ?os2'"
      by (simp add: osB2_eq drop_caps_def produces_def)
    show "consu (?osE 2) = consu ?os2'"
      by (simp add: osB2_eq drop_caps_def produces_def)
    show "operator_state.inter (?osE 2) = operator_state.inter ?os2'"
      by (simp add: osB2_eq drop_caps_def produces_def)
    show "produ (?osE 2) = produ ?os2'"
      by (simp add: osB2_eq drop_caps_def produces_def)
    show "input (?osE 2) = input ?os2'"
      by (simp add: osB2_eq drop_caps_def produces_def)
    show "outpu (?osE 2) = outpu ?os2'"
      by (rule osE2_outpu)
    show "front (?osE 2) = front ?os2'"
      by (simp add: osB2_eq drop_caps_def produces_def)
    show "ocaps (?osE 2) = ocaps ?os2'"
      by (simp add: osB2_eq drop_caps_def produces_def)
    show "initia (?osE 2) = initia ?os2'"
      by (simp add: osB2_eq drop_caps_def produces_def)
    show "operator_state.more (?osE 2) = operator_state.more ?os2'"
      by (simp add: osB2_eq drop_caps_def produces_def)
  qed

  have osE_eq: "?osE = os(2 := ?os2', 1 := op_state_base ?os_label_prop_consumed)"
  proof (rule ext)
    fix nid'
    show "?osE nid' = (os(2 := ?os2', 1 := op_state_base ?os_label_prop_consumed)) nid'"
    proof (cases "nid' = 1")
      case True
      then show ?thesis
        using osD_slot1 by simp
    next
      case False
      then show ?thesis
      proof (cases "nid' = 2")
        case True
        then show ?thesis
          using osE2_eq False by simp
      next
        case False2: False
        then show ?thesis
          using False by simp
      qed
    qed
  qed

  have intsum_os2': "intsum ?os2' = intsum (os 2)"
    by (simp add: drop_caps_def produces_def)

  have intsum_consumed_base:
    "intsum (op_state_base ?os_label_prop_consumed) = intsum (os 1)"
  proof -
    have "intsum (op_state_base ?os_label_prop_consumed) =
      intsum (op_state_base (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>))"
      by simp
    also have "... = intsum ((op_state_base os_label_prop)\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)"
      by simp
    also have "... = intsum (op_state_base os_label_prop)"
      by simp
    also have "... = intsum (os 1)"
      using base_label_prop by simp
    finally show ?thesis .
  qed

  have intsum_label_base: "intsum (op_state_base os_label_prop) = intsum (os 1)"
    using base_label_prop by simp


  have GE: "graph_summar_nt (summ sg) (nxt sg) ?osE"
  proof -
    have geq:
      "graph_summar_nt (summ sg) (nxt sg)
        (os(2 := ?os2', 1 := op_state_base ?os_label_prop_consumed)) =
       graph_summar_nt (summ sg) (nxt sg) os"
      by (rule graph_summar_nt_intsum_cong)
        (simp add: intsum_os2' intsum_consumed_base intsum_label_base)
    have "graph_summar_nt (summ sg) (nxt sg) ?osE = graph_summar_nt (summ sg) (nxt sg) os"
      apply (subst osE_eq)
      apply (rule geq)
      done
    then show ?thesis
      using GR by simp
  qed

  have IOC_consumed: "input_ocaps_inv ?os_label_prop_consumed"
  proof -
    have "input_ocaps_inv (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)"
      using IOC_label_prop unfolding input_ocaps_inv_def by simp
    then show ?thesis
      by (rule input_ocaps_inv_CONSUMES)
  qed

  have zero_consumed: "0 \<in> set (intsum ?os_label_prop_consumed 1 1)"
    using zero_label_prop by simp

  have upd: "?osE(1 := op_state_base ?os_label_prop_consumed) = ?osE"
    apply (subst osE_eq)
    apply (subst osE_eq)
    apply simp
    done

  have invE_base:
    "dataplane_tracker_inv (?osE(1 := op_state_base ?os_label_prop_consumed))
      (?cbufsB((1, 1) := [])) sg"
    apply (subst upd)
    apply (rule invE)
    done

  have GE_base:
    "graph_summar_nt (summ sg) (nxt sg)
      (?osE(1 := op_state_base ?os_label_prop_consumed))"
    apply (subst upd)
    apply (rule GE)
    done



  have invFinal:
    "dataplane_tracker_inv
      (?osE(1 := op_state_base (fst (label_prop_input1_batched ?os_label_prop_consumed (input ?os_label_prop_consumed 1)))))
      (?cbufsB((1, 1) := [])) sg"
    by (rule dataplane_tracker_inv_label_prop_input1_batched
        [OF D invE_base GE_base Nxt IOC_consumed zero_consumed])







  have os_label_prop'_eq:
    "os_label_prop' = fst (label_prop_input1_batched ?os_label_prop_consumed (input ?os_label_prop_consumed 1))"
    using step unfolding label_prop_input1_loop_updates_def Let_def
    by (simp split: prod.splits)

  have os_final_eq:
    "os'(1 := op_state_base os_label_prop') =
      ?osE(1 := op_state_base (fst (label_prop_input1_batched ?os_label_prop_consumed (input ?os_label_prop_consumed 1))))"
    apply (subst os'_eq)
    apply (subst os_label_prop'_eq)
    apply (subst osE_eq)
    apply simp
    done

  have cbufs_final_eq: "cbufs' = ?cbufsB((1, 1) := [])"
    using cbufs'_eq by simp

  show ?thesis
    apply (subst os_final_eq)
    apply (subst cbufs_final_eq)
    apply (rule invFinal)
    done

qed


subsection \<open>Loop-update bridge and frame facts\<close>

lemma input_ocaps_inv_op_state_base:
  \<open>input_ocaps_inv (op_state_base os) = input_ocaps_inv os\<close>
  unfolding input_ocaps_inv_def op_state_base_def
  by simp

lemma label_prop_input1_loop_updates_corrected_os:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows
    \<open>(cbufs', os_label_prop', os'(1 := op_state_base os_label_prop)) =
      label_prop_input1_loop_updates cbufs os_label_prop (os(1 := op_state_base os_label_prop))\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def
  by (simp add: fun_upd_twist split: prod.splits)


subsection \<open>State extension and graph frame facts\<close>

lemma graph_produces[simp]:
  \<open>graph (produces os batch) = graph os\<close>
  unfolding produces_def by simp

lemma label_propagation_state_extend_decompose:
  fixes os :: \<open>('d, 'v::linorder, 't1, 't2) label_propagation_state\<close>
  shows \<open>os = operator_state.extend (op_state_base os)
    \<lparr>en1 = en1 os, de1 = de1 os, is_en1 = is_en1 os,
      en2 = en2 os, de2 = de2 os, is_en2 = is_en2 os,
      timestamps = timestamps os, graph = graph os,
      vertices = vertices os, label = label os\<rparr>\<close>
  by (simp add: op_state_base_def operator_state.defs)

lemma label_prop_input1_step_state_graph[simp]:
  \<open>graph (label_prop_input1_step_state os d t) = graph os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)

lemma vertices_label_prop_input1_step_state[simp]:
  \<open>vertices (label_prop_input1_step_state os d t) = vertices os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)

lemma graph_fst_label_prop_input1_batched[simp]:
  \<open>graph (fst (label_prop_input1_batched os msgs)) = graph os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)

lemma vertices_fst_label_prop_input1_batched[simp]:
  \<open>vertices (fst (label_prop_input1_batched os msgs)) = vertices os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)

lemma label_prop_input1_loop_updates_extension:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and ext: \<open>os_label_prop = operator_state.extend (op_state_base os_label_prop)
      \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr,
        timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
  shows \<open>os_label_prop' = operator_state.extend (op_state_base os_label_prop')
      \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr,
        timestamps = T, graph = G, vertices = V, label = label os_label_prop'\<rparr>\<close>
proof -
  let ?cons = \<open>CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?cons (input ?cons 1))\<close>
    using step unfolding label_prop_input1_loop_updates_def Let_def
    by (simp split: prod.splits)
  have en1_os: \<open>en1 os_label_prop = Inl\<close>
    by (subst ext) (simp add: operator_state.defs)
  have de1_os: \<open>de1 os_label_prop = projl\<close>
    by (subst ext) (simp add: operator_state.defs)
  have is_en1_os: \<open>is_en1 os_label_prop = isl\<close>
    by (subst ext) (simp add: operator_state.defs)
  have en2_os: \<open>en2 os_label_prop = Inr\<close>
    by (subst ext) (simp add: operator_state.defs)
  have de2_os: \<open>de2 os_label_prop = projr\<close>
    by (subst ext) (simp add: operator_state.defs)
  have is_en2_os: \<open>is_en2 os_label_prop = isr\<close>
    by (subst ext) (simp add: operator_state.defs)
  have timestamps_os: \<open>timestamps os_label_prop = T\<close>
    by (subst ext) (simp add: operator_state.defs)
  have graph_os: \<open>graph os_label_prop = G\<close>
    by (subst ext) (simp add: operator_state.defs)
  have vertices_os: \<open>vertices os_label_prop = V\<close>
    by (subst ext) (simp add: operator_state.defs)
  have en1_eq: \<open>en1 os_label_prop' = Inl\<close>
    unfolding os_label_prop'_eq using en1_os by simp
  have de1_eq: \<open>de1 os_label_prop' = projl\<close>
    unfolding os_label_prop'_eq using de1_os by simp
  have is_en1_eq: \<open>is_en1 os_label_prop' = isl\<close>
    unfolding os_label_prop'_eq using is_en1_os by simp
  have en2_eq: \<open>en2 os_label_prop' = Inr\<close>
    unfolding os_label_prop'_eq using en2_os by simp
  have de2_eq: \<open>de2 os_label_prop' = projr\<close>
    unfolding os_label_prop'_eq using de2_os by simp
  have is_en2_eq: \<open>is_en2 os_label_prop' = isr\<close>
    unfolding os_label_prop'_eq using is_en2_os by simp
  have timestamps_eq: \<open>timestamps os_label_prop' = T\<close>
    unfolding os_label_prop'_eq using timestamps_os by simp
  have graph_eq: \<open>graph os_label_prop' = G\<close>
    unfolding os_label_prop'_eq using graph_os by simp
  have vertices_eq: \<open>vertices os_label_prop' = V\<close>
    unfolding os_label_prop'_eq using vertices_os by simp
  have decomp: \<open>os_label_prop' = operator_state.extend (op_state_base os_label_prop')
      \<lparr>en1 = en1 os_label_prop', de1 = de1 os_label_prop', is_en1 = is_en1 os_label_prop',
        en2 = en2 os_label_prop', de2 = de2 os_label_prop', is_en2 = is_en2 os_label_prop',
        timestamps = timestamps os_label_prop', graph = graph os_label_prop',
        vertices = vertices os_label_prop', label = label os_label_prop'\<rparr>\<close>
    by (rule label_propagation_state_extend_decompose)
  show ?thesis
    using decomp en1_eq de1_eq is_en1_eq en2_eq de2_eq is_en2_eq timestamps_eq graph_eq vertices_eq
    by simp
qed

subsection \<open>Raw-summary preservation for loop updates\<close>

lemma label_prop_input1_loop_updates_intsum_corrected:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>\<forall>n. intsum ((os'(1 := op_state_base os_label_prop')) n) =
    intsum ((os(1 := op_state_base os_label_prop)) n)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def op_state_base_def drop_caps_def produces_def
  by (auto split: prod.splits if_splits)

lemma graph_summar_nt_label_prop_input1_loop_updates_corrected:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and GR: \<open>graph_summar_nt (summ sg) (nxt sg) (os(1 := op_state_base os_label_prop))\<close>
  shows \<open>graph_summar_nt (summ sg) (nxt sg) (os'(1 := op_state_base os_label_prop'))\<close>
proof -
  have intsum_eq: \<open>\<And>n. intsum ((os'(1 := op_state_base os_label_prop')) n) =
      intsum ((os(1 := op_state_base os_label_prop)) n)\<close>
    using label_prop_input1_loop_updates_intsum_corrected[OF step] by blast
  have \<open>graph_summar_nt (summ sg) (nxt sg) (os'(1 := op_state_base os_label_prop')) =
        graph_summar_nt (summ sg) (nxt sg) (os(1 := op_state_base os_label_prop))\<close>
    by (rule graph_summar_nt_intsum_cong) (rule intsum_eq)
  then show ?thesis using GR by simp
qed

subsection \<open>Input capability preservation for loop updates\<close>

lemma input_ocaps_inv_label_prop_input1_loop_updates_label:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and IOC: \<open>input_ocaps_inv os_label_prop\<close>
  shows \<open>input_ocaps_inv os_label_prop'\<close>
proof -
  let ?cons = \<open>CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?cons (input ?cons 1))\<close>
    using step unfolding label_prop_input1_loop_updates_def Let_def
    by (simp split: prod.splits)
  have outpu_upd: \<open>input_ocaps_inv (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
    using IOC by (simp add: input_ocaps_inv_def)
  hence \<open>input_ocaps_inv ?cons\<close>
    by (rule input_ocaps_inv_CONSUMES)
  hence \<open>input_ocaps_inv (fst (label_prop_input1_batched ?cons (input ?cons 1)))\<close>
    by (rule input_ocaps_inv_fst_label_prop_input1_batchedI)
  thus ?thesis unfolding os_label_prop'_eq .
qed

lemma input_ocaps_inv_label_prop_input1_loop_updates_os2:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and IOC: \<open>input_ocaps_inv (os 2)\<close>
    and Intsum: \<open>\<forall>n. intsum ((os(1 := op_state_base os_label_prop)) n) =
      (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
  shows \<open>input_ocaps_inv (os' 2)\<close>
proof -
  let ?buf = \<open>cbufs (2, 1) @ outpu os_label_prop 1\<close>
  let ?outpu_batch = \<open>map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
        (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?drops = \<open>map (\<lambda>t. Cap t 1)
        (ocaps (os 2) 1 @
          map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
            (cbufs (2, 1) @ outpu os_label_prop 1))\<close>
  let ?intermediate = \<open>drop_caps (produces (CONSUMES 1 ?buf (os 2)) ?outpu_batch) ?drops\<close>
  have os2'_eq:
    \<open>os' 2 = ?intermediate\<lparr>outpu := (outpu (os 2))(1 := []),
                            input := (input (os 2))(1 := [])\<rparr>\<close>
    using step unfolding label_prop_input1_loop_updates_def Let_def
    by (simp split: prod.splits)
  have intsum_2_0_1: \<open>intsum (os 2) 0 1 = []\<close>
    using Intsum[unfolded raw_summary_def, rule_format, of \<open>2 :: 3\<close>, simplified]
    using num2_neq(1) by force
  have intsum_2_1_0: \<open>intsum (os 2) 1 0 = []\<close>
    using Intsum[unfolded raw_summary_def, rule_format, of \<open>2 :: 3\<close>, simplified]
    using num2_neq(1) by force

  show ?thesis
    unfolding os2'_eq input_ocaps_inv_def
  proof (intro allI ballI)
    fix p p' t s
    assume t_in: \<open>t \<in> snd ` set (input
       (?intermediate\<lparr>outpu := (outpu (os 2))(1 := []),
                       input := (input (os 2))(1 := [])\<rparr>) p)\<close>
       and s_in: \<open>s \<in> set (intsum
       (?intermediate\<lparr>outpu := (outpu (os 2))(1 := []),
                       input := (input (os 2))(1 := [])\<rparr>) p p')\<close>
    have p_ne1: \<open>p \<noteq> 1\<close>
      using t_in by (auto split: if_splits)
    have p_eq0: \<open>p = (0 :: 2)\<close>
      using p_ne1 num2_neq(2) by blast
    have t_in_os2: \<open>t \<in> snd ` set (input (os 2) p)\<close>
      using t_in p_ne1
      by (auto simp: drop_caps_def produces_def input_CONSUMES split: if_splits)
    have s_in_os2: \<open>s \<in> set (intsum (os 2) p p')\<close>
      using s_in by (simp add: drop_caps_def produces_def)
    have orig: \<open>t -+- s \<in> set (ocaps (os 2) p')\<close>
      using IOC t_in_os2 s_in_os2 unfolding input_ocaps_inv_def by blast
    have p'_eq0: \<open>p' = (0 :: 2)\<close>
    proof (rule ccontr)
      assume \<open>p' \<noteq> 0\<close>
      hence \<open>p' = 1\<close> using num2_neq(1) by blast
      thus False using s_in_os2 intsum_2_0_1 p_eq0 by simp
    qed
    have ocaps_unchanged: \<open>ocaps ?intermediate 0 = ocaps (os 2) 0\<close>
    proof -
      have ocaps_drop_p0:
        \<open>ocaps (drop_caps (produces (CONSUMES 1 ?buf (os 2)) ?outpu_batch) ?drops) 0
       = ocaps (produces (CONSUMES 1 ?buf (os 2)) ?outpu_batch) 0\<close>
        unfolding drop_caps_def by (simp add: filter_False)

      have ocaps_produces_p0:
        \<open>ocaps (produces (CONSUMES 1 ?buf (os 2)) ?outpu_batch) 0
       = ocaps (CONSUMES (1 :: 2) ?buf (os 2)) 0\<close>
        unfolding produces_def by simp
      have ocaps_cons_p0: \<open>ocaps (CONSUMES (1 :: 2) ?buf (os 2)) 0 = ocaps (os 2) 0\<close>
        by (rule ocaps_CONSUMES_other_port[OF intsum_2_1_0])
      show ?thesis
        using ocaps_drop_p0 ocaps_produces_p0 ocaps_cons_p0 by simp
    qed
    show \<open>t -+- s \<in> set (ocaps
       (?intermediate\<lparr>outpu := (outpu (os 2))(1 := []),
                       input := (input (os 2))(1 := [])\<rparr>) p')\<close>
      using orig ocaps_unchanged p'_eq0 by simp
  qed
qed


subsection \<open>Label-update invariant preservation for loop updates\<close>

lemma label_prop_upd_inv_label_prop_input1_loop_updatesI:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and MSGS: \<open>\<And>d t. (d, t) \<in> set (cbufs (1, 1) @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)) \<Longrightarrow>
      myfst t \<in> set (timestamps os_label_prop) \<and>
      fst (de1 os_label_prop d) \<in> all_vertices os_label_prop (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow>
        snd (de1 os_label_prop d) \<in> cc_of (all_edges os_label_prop q) (fst (de1 os_label_prop d)))\<close>
  shows \<open>label_prop_upd_inv os_label_prop'\<close>
proof -
  let ?os_reset = \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>\<close>
  let ?buf = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?cons = \<open>CONSUMES 1 ?buf ?os_reset\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?cons (input ?cons 1))\<close>
    using step unfolding label_prop_input1_loop_updates_def Let_def
    by (simp split: prod.splits)
  have inv_reset: \<open>label_prop_upd_inv ?os_reset\<close>
    using INV by simp
  have inv_cons: \<open>label_prop_upd_inv ?cons\<close>
  proof (rule label_prop_upd_inv_CONSUMES_port1I[OF inv_reset])
    fix d t
    assume mem: \<open>(d, t) \<in> set ?buf\<close>
    have \<open>myfst t \<in> set (timestamps os_label_prop) \<and>
          fst (de1 os_label_prop d) \<in> all_vertices os_label_prop (myfst t) \<and>
          (\<forall>q. myfst t \<le> q \<longrightarrow>
            snd (de1 os_label_prop d) \<in> cc_of (all_edges os_label_prop q) (fst (de1 os_label_prop d)))\<close>
      by (rule MSGS[OF mem])
    thus \<open>myfst t \<in> set (timestamps ?os_reset) \<and>
          fst (de1 ?os_reset d) \<in> all_vertices ?os_reset (myfst t) \<and>
          (\<forall>q. myfst t \<le> q \<longrightarrow>
            snd (de1 ?os_reset d) \<in> cc_of (all_edges ?os_reset q) (fst (de1 ?os_reset d)))\<close>
      by simp
  qed
  show ?thesis
    unfolding os_label_prop'_eq
    by (rule label_prop_upd_inv_fst_label_prop_input1_batched_prefixI[where rest=Nil, OF _ inv_cons])
      simp
qed

lemma labels_inv_label_prop_input1_loop_updates_allI:
  fixes os_label_prop os_label_prop' :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os os' :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs cbufs' :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>

  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and MSGS: \<open>\<And>d t. (d, t) \<in> set (cbufs (1, 1) @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)) \<Longrightarrow>
      myfst t \<in> set (timestamps os_label_prop) \<and>
      fst (de1 os_label_prop d) \<in> all_vertices os_label_prop (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow>
        snd (de1 os_label_prop d) \<in> cc_of (all_edges os_label_prop q) (fst (de1 os_label_prop d)))\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
  shows \<open>\<forall>t. labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
proof
  fix t
  show \<open>labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
    by (rule labels_inv_label_prop_input1_loop_updatesI[
        where cbufs = cbufs and os_label_prop = os_label_prop and os = os
          and cbufs' = cbufs' and os_label_prop' = os_label_prop'
          and os' = os' and t = t])
      (use step INV MSGS LABELS in auto)
qed


subsection \<open>Pending-message time preservation for loop updates\<close>

lemma label_prop_input1_loop_updates_times_invI:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and TIMES: \<open>myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
        input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1)) \<subseteq> set (timestamps os_label_prop)\<close>
    and MSGS: \<open>\<And>d t. (d, t) \<in> set (cbufs (1, 1) @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)) \<Longrightarrow>
      myfst t \<in> set (timestamps os_label_prop) \<and>
      fst (de1 os_label_prop d) \<in> all_vertices os_label_prop (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow>
        snd (de1 os_label_prop d) \<in> cc_of (all_edges os_label_prop q) (fst (de1 os_label_prop d)))\<close>
  shows \<open>myfst ` snd ` set (input os_label_prop' 1 @ outpu os_label_prop' 1 @
      input (os' 2) 1 @ outpu (os' 2) 1 @ cbufs' (1, 1) @ cbufs' (2, 1))
    \<subseteq> set (timestamps os_label_prop')\<close>
proof -
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?base = \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>\<close>
  let ?consumed = \<open>CONSUMES 1 ?msgs ?base\<close>
  let ?full = \<open>input ?consumed 1\<close>

  have os'_eq: \<open>os_label_prop' = fst (label_prop_input1_batched ?consumed ?full)\<close>
    using step
    unfolding label_prop_input1_loop_updates_def Let_def
    by (auto split: prod.splits)

  have out_member_ts:
    \<open>\<And>d t. (d, t) \<in> set (outpu os_label_prop' 1) \<Longrightarrow>
      myfst t \<in> set (timestamps os_label_prop')\<close>
  proof -
    fix d t
    assume out_member: \<open>(d, t) \<in> set (outpu os_label_prop' 1)\<close>
    have consumed_out_empty: \<open>outpu ?consumed 1 = []\<close>
      by (simp add: fold_consumes)
    have outpu_eq:
      \<open>outpu os_label_prop' 1 =
        map (\<lambda>(x, cap). (x, capability.time cap))
          (filter (\<lambda>(x, cap). out cap = 1) (snd (label_prop_input1_batched ?consumed ?full)))\<close>
      using os'_eq consumed_out_empty
      by (simp add: outpu_fst_label_prop_input1_batched_eq)
    obtain cap where batch_member:
        \<open>(d, cap) \<in> set (snd (label_prop_input1_batched ?consumed ?full))\<close>
      and t_eq: \<open>t = capability.time cap\<close>
      using out_member outpu_eq by auto
    have produced_member:
      \<open>(out cap, capability.time cap, 1) \<in> set
        (map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
          (snd (label_prop_input1_batched ?consumed ?full)))\<close>
      using batch_member by (cases cap) force
    have ts_cap: \<open>myfst (capability.time cap) \<in> set (timestamps ?consumed)\<close>
      using label_prop_input1_batched_produced_memberD[OF produced_member]
      by blast


    then show \<open>myfst t \<in> set (timestamps os_label_prop')\<close>
      using os'_eq t_eq by simp
  qed

  show ?thesis
    using label_prop_input1_loop_updates_clears[OF step] out_member_ts
    by auto
qed



subsection \<open>Pending-message payload preservation for loop updates\<close>

lemma label_prop_input1_loop_updates_msgs_invI:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and TIMES: \<open>myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
        input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1)) \<subseteq> set (timestamps os_label_prop)\<close>
    and MSGS: \<open>\<And>d t. (d, t) \<in> set (cbufs (1, 1) @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)) \<Longrightarrow>
      myfst t \<in> set (timestamps os_label_prop) \<and>
      fst (de1 os_label_prop d) \<in> all_vertices os_label_prop (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow>
        snd (de1 os_label_prop d) \<in> cc_of (all_edges os_label_prop q) (fst (de1 os_label_prop d)))\<close>
  shows \<open>\<And>d t. (d, t) \<in> set (cbufs' (1, 1) @ outpu (os' 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os' 2) 1 @ cbufs' (2, 1) @ outpu os_label_prop' 1)) \<Longrightarrow>
      myfst t \<in> set (timestamps os_label_prop') \<and>
      fst (de1 os_label_prop' d) \<in> all_vertices os_label_prop' (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow>
        snd (de1 os_label_prop' d) \<in> cc_of (all_edges os_label_prop' q) (fst (de1 os_label_prop' d)))\<close>
proof -
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?base = \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>\<close>
  let ?consumed = \<open>CONSUMES 1 ?msgs ?base\<close>
  let ?full = \<open>input ?consumed 1\<close>

  have os'_eq: \<open>os_label_prop' = fst (label_prop_input1_batched ?consumed ?full)\<close>
    using step
    unfolding label_prop_input1_loop_updates_def Let_def
    by (auto split: prod.splits)

  have inv_consumed: \<open>label_prop_upd_inv ?consumed\<close>
  proof (rule label_prop_upd_inv_CONSUMES_port1I)
    show \<open>label_prop_upd_inv ?base\<close>
      using INV by simp
  next
    fix d t
    assume m: \<open>(d, t) \<in> set ?msgs\<close>
    show \<open>myfst t \<in> set (timestamps ?base) \<and>
      fst (de1 ?base d) \<in> all_vertices ?base (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow> snd (de1 ?base d) \<in> cc_of (all_edges ?base q) (fst (de1 ?base d)))\<close>
      using MSGS[OF m] by simp
  qed

  have all_edges_final: \<open>\<And>q. all_edges os_label_prop' q = all_edges ?consumed q\<close>
    using os'_eq by simp

  fix d t
  assume member: \<open>(d, t) \<in> set (cbufs' (1, 1) @ outpu (os' 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os' 2) 1 @ cbufs' (2, 1) @ outpu os_label_prop' 1))\<close>

  have shifted_member:
    \<open>(d, t) \<in> set (map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (outpu os_label_prop' 1))\<close>
    using member step by simp
  then obtain d0 t0 where out_member: \<open>(d0, t0) \<in> set (outpu os_label_prop' 1)\<close>
    and d_eq: \<open>d = d0\<close>
    and t_eq: \<open>t = t0 -+- MyPair 0 (Suc 0)\<close>
    by auto

  have consumed_out_empty: \<open>outpu ?consumed 1 = []\<close>
    by (simp add: fold_consumes)
  have outpu_eq:
    \<open>outpu os_label_prop' 1 =
      map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = 1) (snd (label_prop_input1_batched ?consumed ?full)))\<close>
    using os'_eq consumed_out_empty
    by (simp add: outpu_fst_label_prop_input1_batched_eq)
  obtain cap where batch_member:
      \<open>(d0, cap) \<in> set (snd (label_prop_input1_batched ?consumed ?full))\<close>
    and out_cap: \<open>out cap = 1\<close>
    and t0_eq: \<open>t0 = capability.time cap\<close>
    using out_member outpu_eq by auto

  obtain pre d_in t_in post os_pre where full_eq: \<open>?full = pre @ (d_in, t_in) # post\<close>
    and os_pre_eq: \<open>os_pre = fst (label_prop_input1_batched ?consumed pre)\<close>
    and step_member: \<open>(d0, cap) \<in> set (label_prop_input1_step_batch os_pre d_in t_in)\<close>
    using batch_member by (elim label_prop_input1_batched_batch_memberD)

  obtain v l cur_t v' where de1_pre: \<open>de1 os_pre d_in = (v, l)\<close>
    and cur_t_ts_pre: \<open>cur_t \<in> set (timestamps os_pre)\<close>
    and event_le_cur: \<open>myfst t_in \<le> cur_t\<close>
    and neigh: \<open>v' \<in> set (neighbors os_pre cur_t v)\<close>
    and d0_eq: \<open>d0 = en1 os_pre (v', l)\<close>
    and cap_eq: \<open>cap = Cap (MyPair cur_t (mysnd t_in)) 1\<close>
    using step_member by (elim label_prop_input1_step_batch_member_payloadD)

  have inv_pre: \<open>label_prop_upd_inv os_pre\<close>
  proof -
    have \<open>label_prop_upd_inv (fst (label_prop_input1_batched ?consumed pre))\<close>
      by (rule label_prop_upd_inv_fst_label_prop_input1_batched_prefixI
          [where rest = \<open>(d_in, t_in) # post\<close>])
        (use full_eq inv_consumed in simp_all)
    then show ?thesis
      using os_pre_eq by simp
  qed

  have in_full: \<open>(d_in, t_in) \<in> set (input ?consumed 1)\<close>
    using full_eq by simp
  have de1_consumed: \<open>de1 ?consumed d_in = (v, l)\<close>
    using de1_pre os_pre_eq by simp
  have pending_consumed:
    \<open>myfst t_in \<in> set (timestamps ?consumed) \<and>
      fst (de1 ?consumed d_in) \<in> all_vertices ?consumed (myfst t_in) \<and>
      (\<forall>q. myfst t_in \<le> q \<longrightarrow> snd (de1 ?consumed d_in) \<in> cc_of (all_edges ?consumed q) (fst (de1 ?consumed d_in)))\<close>
    using inv_consumed in_full unfolding label_prop_upd_inv_def by blast
  have l_cc_consumed: \<open>\<And>q. myfst t_in \<le> q \<Longrightarrow> l \<in> cc_of (all_edges ?consumed q) v\<close>
    using pending_consumed de1_consumed by simp

  have verts_pre: \<open>v \<in> all_vertices os_pre cur_t \<and> v' \<in> all_vertices os_pre cur_t\<close>
    by (rule label_prop_upd_inv_neighborsD[OF inv_pre neigh])
  have edge_cur_pre: \<open>(v, v') \<in> all_edges os_pre cur_t\<close>
    using verts_pre neigh unfolding all_edges_def by auto
  have all_edges_pre: \<open>\<And>q. all_edges os_pre q = all_edges ?consumed q\<close>
    using os_pre_eq by simp
  have edge_final: \<open>\<And>q. cur_t \<le> q \<Longrightarrow> (v, v') \<in> all_edges os_label_prop' q\<close>
  proof -
    fix q
    assume cur_t_le_q: \<open>cur_t \<le> q\<close>
    have \<open>(v, v') \<in> all_edges os_pre q\<close>
      using edge_cur_pre all_edges_mono[OF cur_t_le_q, of os_pre] by blast
    then show \<open>(v, v') \<in> all_edges os_label_prop' q\<close>
      using all_edges_pre[of q] all_edges_final[of q] by simp
  qed

  have t0_cur: \<open>t0 = MyPair cur_t (mysnd t_in)\<close>
    using t0_eq cap_eq by simp
  have t_fst: \<open>myfst t = cur_t\<close>
    using t_eq t0_cur by simp
  have decode: \<open>de1 os_label_prop' d = (v', l)\<close>
    using d_eq d0_eq os_pre_eq os'_eq EN1 DE1 by simp
  have ts_final: \<open>myfst t \<in> set (timestamps os_label_prop')\<close>
    using cur_t_ts_pre os_pre_eq os'_eq t_fst by simp
  have vertex_final: \<open>fst (de1 os_label_prop' d) \<in> all_vertices os_label_prop' (myfst t)\<close>
    using edge_final[OF order_refl, unfolded all_edges_def] decode t_fst by auto
  have cc_final: \<open>\<And>q. myfst t \<le> q \<Longrightarrow>
    snd (de1 os_label_prop' d) \<in> cc_of (all_edges os_label_prop' q) (fst (de1 os_label_prop' d))\<close>
  proof -
    fix q
    assume t_le_q: \<open>myfst t \<le> q\<close>
    have cur_t_le_q: \<open>cur_t \<le> q\<close>
      using t_le_q t_fst by simp
    have event_le_q: \<open>myfst t_in \<le> q\<close>
      using event_le_cur cur_t_le_q by simp
    have l_cc_final_v: \<open>l \<in> cc_of (all_edges os_label_prop' q) v\<close>
      using l_cc_consumed[OF event_le_q] all_edges_final[of q] by simp
    have reach: \<open>reachable (all_edges os_label_prop' q) v v'\<close>
      using edge_final[OF cur_t_le_q] unfolding reachable_def by auto
    have cc_eq: \<open>cc_of (all_edges os_label_prop' q) v = cc_of (all_edges os_label_prop' q) v'\<close>
      by (rule cc_of_eq_if_reachable[OF reach])
    show \<open>snd (de1 os_label_prop' d) \<in> cc_of (all_edges os_label_prop' q) (fst (de1 os_label_prop' d))\<close>
      using decode l_cc_final_v cc_eq by simp
  qed

  show \<open>myfst t \<in> set (timestamps os_label_prop') \<and>
    fst (de1 os_label_prop' d) \<in> all_vertices os_label_prop' (myfst t) \<and>
    (\<forall>q. myfst t \<le> q \<longrightarrow>
      snd (de1 os_label_prop' d) \<in> cc_of (all_edges os_label_prop' q) (fst (de1 os_label_prop' d)))\<close>
    using ts_final vertex_final cc_final by blast
qed


lemma label_prop_input1_loop_updates_preserves_dataplane_tracker_inv_corrected:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and sg :: \<open>(3, 2, (nat, nat) myprod) subgraph\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and GR: \<open>graph_summar_nt (summ sg) (nxt sg) (os(1 := op_state_base os_label_prop))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and Inv: \<open>dataplane_tracker_inv (os(1 := op_state_base os_label_prop)) cbufs sg\<close>
    and label_prop_extension:
      \<open>os_label_prop = operator_state.extend (op_state_base os_label_prop) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
          en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
    and Summ: \<open>summ sg = antichain_from_list \<circ>\<circ> raw_summary\<close>
    and Intsum: \<open>\<forall>n. intsum ((os(1 := op_state_base os_label_prop)) n) =
      (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    and IOC1: \<open>input_ocaps_inv os_label_prop\<close>
    and IOC2: \<open>input_ocaps_inv (os 2)\<close>
  shows \<open>dataplane_tracker_inv (os'(1 := op_state_base os_label_prop')) cbufs' sg\<close>
proof -
  have step':
    \<open>(cbufs', os_label_prop', os'(1 := op_state_base os_label_prop)) =
      label_prop_input1_loop_updates cbufs os_label_prop (os(1 := op_state_base os_label_prop))\<close>
    by (rule label_prop_input1_loop_updates_corrected_os[OF step])
  have label_prop_extension':
    \<open>os_label_prop = operator_state.extend ((os(1 := op_state_base os_label_prop)) 1)
      \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
    using label_prop_extension by simp
  have IOC1': \<open>input_ocaps_inv ((os(1 := op_state_base os_label_prop)) 1)\<close>
    using IOC1 by (simp add: input_ocaps_inv_op_state_base)
  have IOC2': \<open>input_ocaps_inv ((os(1 := op_state_base os_label_prop)) 2)\<close>
    using IOC2 by simp
  have inv':
    \<open>dataplane_tracker_inv
      ((os'(1 := op_state_base os_label_prop))(1 := op_state_base os_label_prop')) cbufs' sg\<close>
    by (rule label_prop_input1_loop_updates_preserves_dataplane_tracker_inv
        [OF step' D GR Nxt Inv label_prop_extension' Summ Intsum IOC1' IOC2'])

  then show ?thesis
    by simp
qed



(* Per-step invariant for label_prop_input1_loop_updates.

   Goal: one application of the step preserves, per-label, the zmset of the
   combined progress emitted by the "direct" form on both updated operator slots
   (1 and 2). With this, foo follows by induction on loop_updates.

   Caveats / known gaps (from review):
   (a) The direct form for os 2 is written here as "release_caps (os 2) 1", but
       the actual transformer used inside label_prop_input1_loop_updates is a
       drop_caps . produces . CONSUMES composite (see
       label_prop_input1_loop_updates_def). Proving this invariant likely
       requires either (i) replacing release_caps (os 2) 1 with that composite
       on both sides, or (ii) first showing release_caps (os 2) 1 equals the
       composite under the assumptions below and using that fact here.
   (b) release_caps reads ocaps AND input; the step clears input (os 2) 1,
       so the set of caps releasable before vs. after differs. The buffer
       invariant (dataplane_tracker_inv) is what balances this --- cbufs and
       outpu entries that get consumed are accounted for as pending caps.

   Assumptions, mirroring produ_fst_snd_loop_updates plus the buffer link:
     - step:                the single-step relation;
     - label_prop_extension: ties os_label_prop to (os 1) so labels match;
     - INV / LABELS / TIMES: the good-branch guards used by
                            produ_fst_snd_loop_updates;
     - DATAPLANE:           the standard dataplane/control-plane glue from
                            General.thy, which contains the Src_caps_inv /
                            Trg_caps_inv pieces that link cbufs to ocaps and
                            the progress fields. Whoever proves this lemma can
                            narrow this down to just the elements actually
                            needed (Src_caps_inv, Trg_caps_inv,
                            produ_consu_inter_supported, change_deltas_inv).
*)
lemma label_prop_input1_loop_updates_preserves_release_progress_zmset:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and sg :: \<open>(3, 2, (nat, nat) myprod) subgraph\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  assumes step:
    \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  and label_prop_extension:
    \<open>os_label_prop = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
  and INV: \<open>label_prop_upd_inv os_label_prop\<close>
  and LABELS: \<open>\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
  and TIMES: \<open>myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
        input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1)) \<subseteq> set (timestamps os_label_prop)\<close>
  and DATAPLANE: \<open>dataplane_tracker_inv os cbufs sg\<close>
  shows "\<forall> l. zmset (map snd (filter (\<lambda> (l', _, _). l = l') (
      extract_progress (1 :: 3) nt (snd (obtain_progress (release_caps os_label_prop' 1))) @
      extract_progress (2 :: 3) nt (snd (obtain_progress (release_caps (os' 2) 1))))))
   = zmset (map snd (filter (\<lambda> (l', _, _). l = l') (
      extract_progress (1 :: 3) nt (snd (obtain_progress (release_caps os_label_prop 1))) @
      extract_progress (2 :: 3) nt (snd (obtain_progress (release_caps (os 2) 1))))))"
  oops

section \<open>loop_updates\<close>

subsection \<open>Recursive function\<close>

function loop_updates where
  "loop_updates (cbufs :: 3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf) os_label_prop (os :: 3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state) = (
   if label_prop_upd_inv os_label_prop \<and> (\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
      (myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @ input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1)) \<subseteq> set (timestamps os_label_prop))
   then
     let (cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os in
     if input os_label_prop' 1 = []
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
      apply (metis label_prop_input1_loop_updates_clears(3))
      done
       apply simp_all
    subgoal sorry
    done
  done


declare loop_updates.simps[simp del]

subsection \<open>Operational simulation for loop_updates\<close>

lemma step_tau_pow_loop_updates:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes UPDATES:
    \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
    and NO: \<open>initia os_label_prop\<close>
    and I: \<open>intsum (os 2) = increment_summary (MyPair 0 1)\<close>
    and N: \<open>initia (os 2)\<close>
    and C1: "input_ocaps_inv (os 2)"
    and L: \<open>label_prop_upd_inv os_label_prop\<close>
    and M: \<open>\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and T: \<open>(myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @ input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1)) \<subseteq> set (timestamps os_label_prop))\<close>
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
      done
    subgoal for cbufs' os_label_prop' os'
      apply (rule rtranclp_trans)
       apply (rule loop_move_all_data_label_prop_input1_updates)
           apply (rule sym)
           apply assumption+
         apply simp_all
      apply (rule prems(1)[simplified, OF refl])
                apply simp_all
             apply (subst loop_updates.simps)
             apply simp
            apply (metis (no_types, lifting) label_prop_input1_loop_updates_clears(3))+
      done
    done
  done

lemma step_tau_pow_loop_updates_alt:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes NO: \<open>initia os_label_prop\<close>
    and I: \<open>intsum (os 2) = increment_summary (MyPair 0 1)\<close>
    and N: \<open>initia (os 2)\<close>
    and C1: "input_ocaps_inv (os 2)"
    and L: \<open>label_prop_upd_inv os_label_prop\<close>
    and M: \<open>\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and T: \<open>(myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @ input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1)) \<subseteq> set (timestamps os_label_prop))\<close>
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
    by (rule step_tau_pow_loop_updates[OF updates NO I N C1 L M T])
qed

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
    oops


subsection \<open>Frame and produced-progress facts for loop_updates\<close>

lemma fst_loop_updates[simp]:
  \<open>fst (loop_updates cbufs os_label_prop os) = cbufs((2, 1) := [], (1, 1) := [])\<close>
proof (induct cbufs os_label_prop os rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  obtain cbufs' os_label_prop' os' where triple:
    \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
  have cbufs'_eq: \<open>cbufs' = cbufs((2, 1) := [], (1, 1) := [])\<close>
    using triple by (metis fst_conv fst_label_prop_input1_loop_updates)
  have idemp_eq:
    \<open>(cbufs((2, 1) := [], (1, 1) := []))((2, 1) := [], (1, 1) := []) =
     cbufs((2, 1) := [], (1, 1) := [])\<close>
    by simp
  have ih_applied:
    \<open>input os_label_prop' 1 \<noteq> [] \<Longrightarrow>
     label_prop_upd_inv os_label_prop \<and>
     (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
     myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
       input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1))
       \<subseteq> set (timestamps os_label_prop) \<Longrightarrow>
     fst (loop_updates (cbufs((2, 1) := [], (1, 1) := [])) os_label_prop' os')
       = cbufs((2, 1) := [], (1, 1) := [])\<close>

    using 1(1)[OF _ triple[symmetric] refl refl] cbufs'_eq idemp_eq by metis
  show ?case
    by (subst loop_updates.simps) (auto simp: triple cbufs'_eq ih_applied)
qed

lemma produ_fst_snd_loop_updates_prefix:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  obtains produced where
    \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) = produ os_label_prop @ produced\<close>
    \<open>\<forall>p pt n. (p, pt, n) \<in> set produced \<longrightarrow>
      p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
proof (induct cbufs os_label_prop os arbitrary: thesis rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
      input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1))
      \<subseteq> set (timestamps os_label_prop)\<close>
  show ?case
  proof (cases ?good)
    case False
    have loop_eq: \<open>loop_updates cbufs os_label_prop os =
      (cbufs((2, 1) := [], (1, 1) := []), os_label_prop, os)\<close>
      by (subst loop_updates.simps) (use False in auto)
    show ?thesis
    proof (rule "1.prems"[of Nil])
      show \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) = produ os_label_prop @ []\<close>
        using loop_eq by simp
      show \<open>\<forall>p pt n. (p, pt, n) \<in> set [] \<longrightarrow>
        p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
        by simp
    qed
  next
    case True
    obtain cbufs' :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
      and os_label_prop' :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
      and os' :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
      where step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
      map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
        (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
    let ?consumed = \<open>CONSUMES 1 ?msgs (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
    let ?produced1 = \<open>map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
      (snd (label_prop_input1_batched ?consumed (input ?consumed 1)))\<close>
    have consumed_ts: \<open>timestamps ?consumed = timestamps os_label_prop\<close>
      by simp
    have produced1_props: \<open>\<forall>p pt n. (p, pt, n) \<in> set ?produced1 \<longrightarrow>
      p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
    proof (intro allI impI)
      fix p pt n
      assume \<open>(p, pt, n) \<in> set ?produced1\<close>
      then show \<open>p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
        by (elim label_prop_input1_batched_produced_memberD) (simp add: consumed_ts)
    qed
    have step_prod0:
      \<open>produ (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) =
        produ os_label_prop @ ?produced1\<close>
      unfolding label_prop_input1_loop_updates_def Let_def
      by (simp add: fold_consumes split_beta split: capability.splits)
    have step_prod: \<open>produ os_label_prop' = produ os_label_prop @ ?produced1\<close>
      using step_prod0 step by simp
    have step_os_label_prop':
      \<open>os_label_prop' = fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))\<close>
      using step by simp
    have step_ts: \<open>timestamps os_label_prop' = timestamps os_label_prop\<close>
      using step_os_label_prop'
      unfolding label_prop_input1_loop_updates_def Let_def
      by (simp add: fold_consumes split_beta)
    show ?thesis
    proof (cases \<open>input os_label_prop' 1 = []\<close>)
      case True
      have loop_eq: \<open>loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
        by (subst loop_updates.simps) (use \<open>?good\<close> step True in auto)
      show ?thesis
      proof (rule "1.prems"[of \<open>?produced1 @ []\<close>])
        show \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) =
          produ os_label_prop @ (?produced1 @ [])\<close>
          using loop_eq step_prod by simp
        show \<open>\<forall>p pt n. (p, pt, n) \<in> set (?produced1 @ []) \<longrightarrow>
          p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
          using produced1_props by simp
      qed
    next
      case False
      obtain produced2 where rec_prod:
        \<open>produ (fst (snd (loop_updates cbufs' os_label_prop' os'))) =
          produ os_label_prop' @ produced2\<close>
        and rec_props: \<open>\<forall>p pt n. (p, pt, n) \<in> set produced2 \<longrightarrow>
          p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop') \<and> MyPair (myfst pt) 0 \<le> pt\<close>
        using "1.hyps"[OF \<open>?good\<close> step[symmetric] refl refl False]
        by blast
      have loop_eq: \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs' os_label_prop' os'\<close>
        by (subst loop_updates.simps) (use \<open>?good\<close> step False in auto)
      show ?thesis
      proof (rule "1.prems"[of \<open>?produced1 @ produced2\<close>])
        show \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) =
          produ os_label_prop @ (?produced1 @ produced2)\<close>
          using loop_eq rec_prod step_prod by (simp add: append_assoc)
        show \<open>\<forall>p pt n. (p, pt, n) \<in> set (?produced1 @ produced2) \<longrightarrow>
          p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
          using produced1_props rec_props step_ts by auto
      qed
    qed
  qed
qed


lemma produ_fst_snd_loop_updatesE:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os_label_prop_consumed :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and TIMES: \<open>myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
        input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1))
      \<subseteq> set (timestamps os_label_prop)\<close>
    and os_label_prop_consumed_def:
    \<open>os_label_prop_consumed =
      CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  obtains produced where
    \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) =
      produ os_label_prop @
        map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
          (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))) @
        produced\<close>
    \<open>\<forall>p pt n. (p, pt, n) \<in> set (
        map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
          (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))) @ produced) \<longrightarrow>
      p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop_consumed) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
proof -
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
      input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1))
      \<subseteq> set (timestamps os_label_prop)\<close>
  have good: ?good
    using INV LABELS TIMES by simp
  obtain cbufs' :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and os_label_prop' :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os' :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    where step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
  let ?produced1 = \<open>map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
    (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1)))\<close>
  have consumed_ts: \<open>timestamps os_label_prop_consumed = timestamps os_label_prop\<close>
    using os_label_prop_consumed_def by simp
  have produced1_props: \<open>\<forall>p pt n. (p, pt, n) \<in> set ?produced1 \<longrightarrow>
    p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop_consumed) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
  proof (intro allI impI)
    fix p pt n
    assume \<open>(p, pt, n) \<in> set ?produced1\<close>
    then show \<open>p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop_consumed) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
      by (elim label_prop_input1_batched_produced_memberD) simp
  qed
  have step_prod0:
    \<open>produ (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) =
      produ os_label_prop @ ?produced1\<close>
    using os_label_prop_consumed_def
    unfolding label_prop_input1_loop_updates_def Let_def
    by (simp add: fold_consumes split_beta split: capability.splits)
  have step_prod: \<open>produ os_label_prop' = produ os_label_prop @ ?produced1\<close>
    using step_prod0 step by simp
  have step_os_label_prop':
    \<open>os_label_prop' = fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))\<close>
    using step by simp
  have step_ts: \<open>timestamps os_label_prop' = timestamps os_label_prop_consumed\<close>
    using step_os_label_prop' os_label_prop_consumed_def
    unfolding label_prop_input1_loop_updates_def Let_def
    by (simp add: fold_consumes split_beta)
  show ?thesis
  proof (cases \<open>input os_label_prop' 1 = []\<close>)
    case True
    have \<open>loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
      by (subst loop_updates.simps) (use good step True in auto)
    then have prod_eq: \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) =
      produ os_label_prop @ ?produced1 @ []\<close>
      using step_prod by simp
    show ?thesis
      by (rule that[OF prod_eq]) (use produced1_props in simp)
  next
    case False
    obtain produced2 where rec_prod:
      \<open>produ (fst (snd (loop_updates cbufs' os_label_prop' os'))) =
        produ os_label_prop' @ produced2\<close>
      and rec_props: \<open>\<forall>p pt n. (p, pt, n) \<in> set produced2 \<longrightarrow>
        p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop') \<and> MyPair (myfst pt) 0 \<le> pt\<close>
      by (elim produ_fst_snd_loop_updates_prefix)
    have \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs' os_label_prop' os'\<close>
      by (subst loop_updates.simps) (use good step False in auto)
    then have prod_eq: \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) =
      produ os_label_prop @ ?produced1 @ produced2\<close>
      using rec_prod step_prod by (simp add: append_assoc)
    have props: \<open>\<forall>p pt n. (p, pt, n) \<in> set (?produced1 @ produced2) \<longrightarrow>
      p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop_consumed) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
      using produced1_props rec_props step_ts by auto
    show ?thesis
      by (rule that[OF prod_eq props])
  qed
qed

lemma produ_fst_snd_loop_updates:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os_label_prop_consumed :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and TIMES: \<open>myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
        input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1))
      \<subseteq> set (timestamps os_label_prop)\<close>
    and os_label_prop_consumed_def:
    \<open>os_label_prop_consumed =
      CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  shows \<open>\<exists>produced.
    produ (fst (snd (loop_updates cbufs os_label_prop os))) =
      produ os_label_prop @
        map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
          (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))) @
        produced \<and>
    (\<forall>p pt n. (p, pt, n) \<in> set produced \<longrightarrow>
      p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop_consumed) \<and> MyPair (myfst pt) 0 \<le> pt) \<and>
    (\<forall>p pt n. (p, pt, n) \<in> set (
        map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
          (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1)))) \<longrightarrow>
      p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop_consumed) \<and> MyPair (myfst pt) 0 \<le> pt)\<close>
proof -
  obtain produced where prod_eq:
    \<open>produ (fst (snd (loop_updates cbufs os_label_prop os))) =
      produ os_label_prop @
        map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
          (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))) @
        produced\<close>
    and props: \<open>\<forall>p pt n. (p, pt, n) \<in> set (
        map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
          (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))) @ produced) \<longrightarrow>
      p = 1 \<and> n = 1 \<and> myfst pt \<in> set (timestamps os_label_prop_consumed) \<and> MyPair (myfst pt) 0 \<le> pt\<close>
    by (rule produ_fst_snd_loop_updatesE
        [where os = os and os_label_prop = os_label_prop
          and os_label_prop_consumed = os_label_prop_consumed and cbufs = cbufs,
          OF INV LABELS TIMES os_label_prop_consumed_def])
  show ?thesis
    using prod_eq props
    by (smt (verit, del_insts) append.assoc in_set_conv_decomp label_prop_input1_batched_produced_memberD)
qed

subsection \<open>Dataplane invariant preservation for loop_updates\<close>

(* Preservation of dataplane_tracker_inv by the entire loop_updates iteration. *)
lemma loop_updates_preserves_dataplane_tracker_inv:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and sg :: \<open>(3, 2, (nat, nat) myprod) subgraph\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  assumes step:
    \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
  and D: \<open>dataflow_topology (summ sg) (-+-)\<close>
  and GR: \<open>graph_summar_nt (summ sg) (nxt sg) (os(1 := op_state_base os_label_prop))\<close>
  and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
  and Inv: \<open>dataplane_tracker_inv (os(1 := op_state_base os_label_prop)) cbufs sg\<close>
  and label_prop_extension:
    \<open>os_label_prop = operator_state.extend (op_state_base os_label_prop) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
  and Summ: \<open>summ sg = antichain_from_list \<circ>\<circ> raw_summary\<close>
  and Intsum: \<open>\<forall>n. intsum ((os(1 := op_state_base os_label_prop)) n) =
    (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
  and IOC1: \<open>input_ocaps_inv os_label_prop\<close>
  and IOC2: \<open>input_ocaps_inv (os 2)\<close>
  and INV: \<open>label_prop_upd_inv os_label_prop\<close>
  and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
  and TIMES: \<open>myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
        input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1)) \<subseteq> set (timestamps os_label_prop)\<close>
  and MSGS: \<open>\<And>d t. (d, t) \<in> set (cbufs (1, 1) @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)) \<Longrightarrow>
      myfst t \<in> set (timestamps os_label_prop) \<and>
      fst (de1 os_label_prop d) \<in> all_vertices os_label_prop (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow>
        snd (de1 os_label_prop d) \<in> cc_of (all_edges os_label_prop q) (fst (de1 os_label_prop d)))\<close>
  shows \<open>dataplane_tracker_inv (os'(1 := op_state_base os_label_prop')) cbufs' sg\<close>
  using step D GR Nxt Inv label_prop_extension Summ Intsum IOC1 IOC2 INV LABELS TIMES MSGS
proof (induct cbufs os_label_prop os arbitrary: cbufs' os_label_prop' os' T G V L rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  note loop_step = "1.prems"(1)
  note D0 = "1.prems"(2)
  note GR0 = "1.prems"(3)
  note Nxt0 = "1.prems"(4)
  note Inv0 = "1.prems"(5)
  note Ext0 = "1.prems"(6)
  note Summ0 = "1.prems"(7)
  note Intsum0 = "1.prems"(8)
  note IOC10 = "1.prems"(9)
  note IOC20 = "1.prems"(10)
  note INV0 = "1.prems"(11)
  note LABELS0 = "1.prems"(12)
  note TIMES0 = "1.prems"(13)
  note MSGS0 = "1.prems"(14)

  have good: \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
      input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1))
      \<subseteq> set (timestamps os_label_prop)\<close>
    using INV0 LABELS0 TIMES0 by simp

  obtain cbufs1 os_label_prop1 os1 where step1:
    \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
    by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto

  have Inv1: \<open>dataplane_tracker_inv (os1(1 := op_state_base os_label_prop1)) cbufs1 sg\<close>
    by (rule label_prop_input1_loop_updates_preserves_dataplane_tracker_inv_corrected
        [OF step1[symmetric] D0 GR0 Nxt0 Inv0 Ext0 Summ0 Intsum0 IOC10 IOC20])

  show ?case
  proof (cases \<open>input os_label_prop1 1 = []\<close>)
    case True
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (subst loop_updates.simps) (use good step1 True in auto)
    show ?thesis
      using loop_step loop_eq Inv1 by (simp add: fun_upd_def)
  next
    case False
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs1 os_label_prop1 os1\<close>
      by (subst loop_updates.simps) (use good step1 False in auto)
    have step_rec: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs1 os_label_prop1 os1\<close>
      using loop_step loop_eq by simp
    have GR1: \<open>graph_summar_nt (summ sg) (nxt sg) (os1(1 := op_state_base os_label_prop1))\<close>
      by (rule graph_summar_nt_label_prop_input1_loop_updates_corrected[OF step1[symmetric] GR0])
    have Ext1:
      \<open>os_label_prop1 = operator_state.extend (op_state_base os_label_prop1)
        \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
          en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V,
          label = label os_label_prop1\<rparr>\<close>
      by (rule label_prop_input1_loop_updates_extension[OF step1[symmetric] Ext0])

    have Intsum1: \<open>\<forall>n. intsum ((os1(1 := op_state_base os_label_prop1)) n) =
      (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
      using label_prop_input1_loop_updates_intsum_corrected[OF step1[symmetric]] Intsum0 by simp
    have IOC11: \<open>input_ocaps_inv os_label_prop1\<close>
      by (rule input_ocaps_inv_label_prop_input1_loop_updates_label[OF step1[symmetric] IOC10])
    have IOC21: \<open>input_ocaps_inv (os1 2)\<close>
      by (rule input_ocaps_inv_label_prop_input1_loop_updates_os2[OF step1[symmetric] IOC20 Intsum0])
    have INV1: \<open>label_prop_upd_inv os_label_prop1\<close>
      by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] INV0 MSGS0])
    have LABELS1: \<open>\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)\<close>
      by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] INV0 MSGS0 LABELS0])
    have TIMES1: \<open>myfst ` snd ` set (input os_label_prop1 1 @ outpu os_label_prop1 1 @
        input (os1 2) 1 @ outpu (os1 2) 1 @ cbufs1 (1, 1) @ cbufs1 (2, 1))
      \<subseteq> set (timestamps os_label_prop1)\<close>
      by (rule label_prop_input1_loop_updates_times_invI[OF step1[symmetric] INV0 LABELS0 TIMES0 MSGS0])
    have EN10: \<open>en1 os_label_prop = Inl\<close>
      using arg_cong[OF Ext0, of en1]
      by (simp add: operator_state.defs)
    have DE10: \<open>de1 os_label_prop = projl\<close>
      using arg_cong[OF Ext0, of de1]
      by (simp add: operator_state.defs)
    have MSGS1: \<open>\<And>d t. (d, t) \<in> set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)) \<Longrightarrow>
      myfst t \<in> set (timestamps os_label_prop1) \<and>
      fst (de1 os_label_prop1 d) \<in> all_vertices os_label_prop1 (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow>
        snd (de1 os_label_prop1 d) \<in> cc_of (all_edges os_label_prop1 q) (fst (de1 os_label_prop1 d)))\<close>
      by (rule label_prop_input1_loop_updates_msgs_invI
          [OF step1[symmetric] EN10 DE10 INV0 LABELS0 TIMES0 MSGS0])




    show ?thesis
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False
          step_rec D0 GR1 Nxt0 Inv1 Ext1 Summ0 Intsum1 IOC11 IOC21 INV1 LABELS1 TIMES1 MSGS1])
  qed
qed


subsection \<open>Progress comparison for loop_updates\<close>

(* foo: the loop's combined emitted progress matches a single direct release_caps,
   per-label. Proof plan: induction on loop_updates, using
   label_prop_input1_loop_updates_preserves_release_progress_zmset as the
   step case; the else-branch (guard fails) clears cbufs (1,1) and cbufs (2,1)
   but leaves os_label_prop, os unchanged, so we need the good-branch guards
   (mirror of produ_fst_snd_loop_updates).
*)
lemma foo:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and sg :: \<open>(3, 2, (nat, nat) myprod) subgraph\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  assumes label_prop_extension:
    \<open>os_label_prop = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
  and INV: \<open>label_prop_upd_inv os_label_prop\<close>
  and LABELS: \<open>\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
  and TIMES: \<open>myfst ` snd ` set (input os_label_prop 1 @ outpu os_label_prop 1 @
        input (os 2) 1 @ outpu (os 2) 1 @ cbufs (1, 1) @ cbufs (2, 1)) \<subseteq> set (timestamps os_label_prop)\<close>
  and DATAPLANE: \<open>dataplane_tracker_inv os cbufs sg\<close>
  and "xs =
      extract_progress (1 :: 3) nt (snd (obtain_progress (fst (snd (loop_updates cbufs os_label_prop os))))) @
      extract_progress (2 :: 3) nt (snd (obtain_progress (snd (snd (loop_updates cbufs os_label_prop os)) 2)))"
  and "ys =
      extract_progress (1 :: 3) nt (snd (obtain_progress (release_caps os_label_prop 1))) @
      extract_progress (2 :: 3) nt (snd (obtain_progress (release_caps (os 2) 1)))"
  shows "\<forall> l \<in> fst ` set xs. zmset (map snd (filter (\<lambda> (l', _, _). l = l') xs)) = zmset (map snd (filter (\<lambda> (l', _, _). l = l') ys))"
  oops


lemma extract_prog_three_fold:
  shows  \<open>extract_progress 0 eds (snd (obtain_progress os0)) @
   extract_progress 1 eds (snd (obtain_progress os1)) @
   extract_progress 2 eds (snd (obtain_progress os2)) =
   extract_prog [0 :: 3, 1, 2] eds (\<lambda> nid. if nid = 0 then os0 else if nid = 1 then os1 else os2)\<close>
  by (simp add: extract_prog_def)
lemma buff_sim_aux[simp]:
  "(\<lambda>p'. if Inr (1, 0) = p'
                    then drop (length (cbufs (1, 0)) -+- length (outpu (os 0) 0) -+- length (filter is_Data (ltaken n lxs)))
                          (((\<lambda>p'a. if p' = p'a then map Inr (outpu (os 0) 0) @ map (\<lambda>ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n lxs)) else []) >>
                            case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
                            p')
                    else ((\<lambda>p'. if Inr (1, 0) = p' then map Inr (outpu (os 0) 0) @ map (\<lambda>ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n lxs)) else []) >>
                          case_sum (\<lambda>x. []) (\<lambda>x. map Inr (cbufs x)))
                          p') = case_sum (\<lambda>x. []) (\<lambda>x. map Inr ((cbufs((1, 0) := [])) x))"
  apply (rule ext)+
  unfolding BULK_BENQ_def
  apply (auto split: sum.splits)
  done

lemma label_propagation_correctness:
  fixes lxs :: \<open>((nat, nat) myprod, nat \<times> nat) event llist\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and os_input :: \<open>(2, nat \<times> nat + nat set set, nat \<times> nat, (nat, nat) myprod) input_state\<close>
    and os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and cbufs chns :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and sg :: \<open>(3, 2, (nat, nat) myprod) subgraph\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
    and S SO SP D :: \<open>((3 \<times> 2) \<times> (nat \<times> nat + nat set set) \<times> (nat, nat) myprod) cset\<close>
  assumes
    subgraph_inv:
    \<open>summ sg = antichain_from_list \<circ>\<circ> raw_summary\<close> \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and
    os_inv:
    \<open>os_input = operator_state.extend (os 0) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
      es = (\<lambda>_. LNil)(0 := lxs)\<rparr>\<close> \<open>input (os 0) = (\<lambda>_. [])\<close> \<open>initia (os 0)\<close>
    \<open>os_label_prop = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
    \<open>ty1_check os_input (curry cbufs 0)\<close> \<open>label_prob_ty2_check os_label_prop (curry cbufs 1)\<close>
    \<open>\<forall>n. intsum (os n) = (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    \<open>input_ocaps_inv (os 2)\<close>
    \<open>initia (os 2)\<close>
    and buffers_inv:
    \<open>chns = outputs_at_target (summ sg) os >> cbufs >> inputs_at_target os\<close>
    and dataplane_inv:
    \<open>dataplane_tracker_inv os cbufs sg\<close>
    and csets_inv:
    \<open>SP = cimage
      (\<lambda>t. ((1, 0), (Inr (ccs
        (set (icoll (map (\<lambda>(x, t'). Data t' (projl x)) (chns (1, 0)) @@- lxs) t)
        \<union> all_edges os_label_prop (myfst t))), t)))
      (cUn (cUn (ts lxs) (cset_from_list (map snd (chns (1, 0))))) ((\<lambda> t. MyPair t 0) |`| (cset_from_list (timestamps os_label_prop))))\<close>
    \<open>SO = cset_from_list (map (\<lambda>x. ((1, 0), x)) (outpu (os 1) 0))\<close>
    and input_stream_inv:
    \<open>timely_input_stream lxs (mset (ocaps (os 0) 0))\<close>
    and label_prop_inv:
    \<open>(\<forall> t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t))\<close>
    \<open>(\<forall> t \<in> set (timestamps os_label_prop). \<not> frontier_less_equal (exit_scope myfst (front (os 1) 0 + front (os 1) 1)) t \<longrightarrow> labels_stable (all_edges os_label_prop t) (min_label os_label_prop t))\<close>
    \<open>\<forall> t \<in> myfst ` snd ` set (input (os 1) 0) \<union> myfst ` snd ` set (input (os 1) 1). frontier_less_equal (exit_scope myfst (front (os 1) 1)) t\<close>
    \<open>\<forall>t \<in> event.time ` lset lxs \<union> snd ` set (chns (1, 0)) \<union> set (ocaps (os 1) 0). mysnd t = 0\<close>
    \<open>label_prop_upd_inv os_label_prop\<close>
    \<open>input_ocaps_inv (os 1)\<close>
  shows \<open>set_op S D (dataflow_op sg (G_op os_input os_label_prop (os 2) cbufs))
         \<approx> set_spec_op (cUn (cUn S SO) SP) D\<close>
  using assms
proof (coinduction arbitrary: S SO SP D lxs os os_input os_label_prop cbufs chns sg T G V L
    rule: weakBisimWeakUptoBisimCong)
  case SIM1
  note subgraph_inv = SIM1(1,2)
    and os_inv = SIM1(3-11)
    and buffers_inv = SIM1(12)
    and dataplane_inv = SIM1(13)
    and csets_inv = SIM1(14,15)
    and input_stream_inv = SIM1(16)
    and label_prop_inv = SIM1(17-)
  have D: \<open>dataflow_topology (summ sg) (-+-)\<close> 
    unfolding subgraph_inv comp_def
    apply (subst dataflow_tree_to_graph_raw_summary[symmetric])
    using dataflow_topology_from_tree.dataflow_topology_axioms[unfolded comp_def]
    apply auto
    done
  also have G: "graph_summar_nt (summ sg) (subgraph.nxt sg) os"
    apply -
    apply (rule graph_summar_nt[simplified, OF _ subgraph_inv(1)])
      apply (rule sym)
      apply (rule dataflow_tree_to_graph_raw_summary)
    using os_inv(7) apply assumption
    using subgraph_inv(2) apply assumption
    done
  show ?case (is \<open>wsim ((~) OO \<U> ?R OO (\<approx>)) _ _\<close>)
  proof -
    define R where \<open>R = ?R\<close>
    show ?thesis
      using [[goals_limit=16]]
      unfolding R_def[symmetric]
      unfolding wsim_def dataflow_tree_to_operator_def  ooo_input_op_def label_propagation_op_def increment_op_def
      apply simp
      apply (intro allI impI)
      apply (repeat_new \<open>erule conjE step_dataflow_op_elim step_set_op_elim step_map_op_elim
  step_comp_op_elim step_loop_op_elim step_builder_op_elim; simp?; hypsubst_thin?\<close>;
          auto 0 0 split: if_splits option.splits dest!: num2_neq simp flip: ooo_input_op_def label_propagation_op_def increment_op_def; hypsubst_thin?)
      subgoal
        apply (intro exI conjI relcomppI)
           apply (rule step_set_spec_op_intro_Out)
              apply (rule refl)
             apply simp
            apply assumption
           apply (rule refl)
          apply (rule bisim_refl)
         defer
         apply (rule wbisim_refl)
        apply (rule wb_upto_b_base)
        apply (unfold R_def)
        apply (intro exI conjI)
                            apply (simp add: dataflow_tree_to_operator_def)
        using SIM1 by (simp_all add: comp_def)
      subgoal for d t xs
        apply (intro exI conjI relcomppI)
           apply (rule rtranclp.rtrancl_refl)
          apply (rule bisim_refl)
         defer
         apply (rule wbisim_refl)
        apply (rule wb_upto_b_base)
        apply (unfold R_def)
        apply (rule exI[of _ S])
        apply (rule exI[of _ SO])
        apply (rule exI[of _ SP])
        apply (rule exI[of _ D])
        apply (rule exI[of _ lxs])
        apply (rule exI[of _ \<open>os(0 := (os 0)\<lparr>outpu := (outpu (os 0))(0 := xs)\<rparr>)\<close>])
        apply (rule exI[of _ \<open>os_input\<lparr>outpu := (outpu os_input)(0 := xs)\<rparr>\<close>])
        apply (rule exI[of _ os_label_prop])
        apply (rule exI[of _ \<open>BENQ (1, 0) (d, t) cbufs\<close>])
        apply (intro exI conjI)
                            defer
                            apply (rule refl)
        using subgraph_inv(1) apply simp
                            apply (simp_all add: operator_state.defs(3) subgraph_inv(2) os_inv)
        using os_inv(1,5)
                    apply (simp add: ty1_check_def operator_state.defs(3) BENQ_def)
                    apply (frule spec[of _ 0])
                    apply fastforce
        using os_inv(1,4-6)
                   apply (simp add: ty1_check_def label_prob_ty2_check_def operator_state.defs(3) BENQ_def)
                   apply (drule spec[of _ 0])
                   apply simp
                  apply (rule dataplane_tracker_inv_update_outputs[OF dataplane_inv _ _ _ _ G, where nid=0 and xs=\<open>[(d, t)]\<close> and ys=xs and p=0])
                     apply simp
                    apply (simp add: fun_upd_def)
                   apply (simp add: BENQ_def)
                  apply (simp add: subgraph_inv(1) raw_summary_def antichain_from_list_singleton)
                 apply (subgoal_tac \<open>outputs_at_target (summ sg) (os(0 := (os 0)\<lparr>outpu := (outpu (os 0))(0 := xs)\<rparr>)) >> BENQ (1, 0) (d, t) cbufs
  = outputs_at_target (summ sg) os >> cbufs\<close>)
                  apply (simp add: csets_inv(1) buffers_inv os_inv(4,7) operator_state.defs(3))
                 apply (simp add: outputs_at_target_raw_summary subgraph_inv(1) BENQ_def BULK_BENQ_def fun_eq_iff)
                apply (simp add: csets_inv(2))
               apply (rule input_stream_inv)
        using label_prop_inv(1) apply (simp add: os_inv(4,7) operator_state.defs(3))
        using label_prop_inv(2) apply (simp add: os_inv(4,7) operator_state.defs(3))
            apply (simp add: label_prop_inv(3))
        using buffers_inv label_prop_inv(4) apply (simp add: BULK_BENQ_def subgraph_inv(1) outputs_at_target_raw_summary)
        using label_prop_inv(5) apply (simp add: os_inv(4,7) operator_state.defs(3))
         apply (rule label_prop_inv(6))
        apply (clarsimp simp add: dataflow_tree_to_operator_def intro!: arg_cong[where f=\<open>set_op _ _\<close>] arg_cong[where f=\<open>dataflow_op _\<close>] arg_cong[where f=\<open>map_op _ _\<close>])
        apply (rule arg_cong2[where f=\<open>\<lambda>buf op. comp_op _ buf _ op\<close>])
         apply (fastforce simp add: BENQ_def)
        apply (rule loop_op_buf_cong[OF refl])
         apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
         apply (rule comp_op_buf_cong[OF refl refl refl])
         apply (simp add: ran_comp_wire BENQ_def)
        apply (simp add: ran_loop_wire BENQ_def)
        done
      subgoal for p d t
        apply (subgoal_tac \<open>p = 0\<close>)
         defer
         apply (clarsimp simp add: ran_loop_wire dest!: num2_neq(2))
        apply (intro exI conjI relcomppI)
           apply (rule rtranclp.rtrancl_refl)
          apply (rule bisim_refl)
         defer
         apply (rule wbisim_refl)
        apply (rule wb_upto_b_base)
        apply (unfold R_def)
        apply (rule exI[of _ S])
        apply (rule exI[of _ SO])
        apply (rule exI[of _ SP])
        apply (rule exI[of _ D])
        apply (rule exI[of _ lxs])
        apply (rule exI[of _ \<open>os(1 := consumes (os 1) p t d)\<close>])
        apply (rule exI[of _ os_input])
        apply (rule exI[of _ \<open>consumes os_label_prop p t d\<close>])
        apply (rule exI[of _ \<open>BTL (1, p) cbufs\<close>])
        apply (intro exI conjI)
                            defer
                            apply (rule refl)
        using subgraph_inv(1) apply simp
                            apply (simp_all add: operator_state.defs(3) subgraph_inv(2) os_inv)
                     apply (simp add: consumes_def add_caps_def BENQ_def)
                     apply (intro conjI)
                         apply (simp add: raw_summary_def fun_eq_iff)
                        apply (rule refl)
                       apply (rule refl)
                      apply (rule refl)
                     apply (rule refl)
        using os_inv(1,5)
                    apply (simp add: ty1_check_def operator_state.defs(3) BTL_def)
                    apply blast
        using os_inv(1,4-6)
                   apply (simp add: ty1_check_def label_prob_ty2_check_def operator_state.defs(3) BTL_def BHD_def)
                   apply (erule conjE)
                   apply (rotate_tac 9)
                   apply (drule spec[of _ 0])
                   apply (simp add: Ball_def)
                   apply (meson img_fst in_fst_imageE in_set_tlD)
                  apply (rule dataplane_tracker_inv_consumes[OF dataplane_inv _ D G, where xs=\<open>tl (cbufs (1, p))\<close>])
                  apply (simp add: BHD_def)
                 apply (simp add: csets_inv(1) buffers_inv os_inv(4,7) operator_state.defs(3) consumes_def)
                apply (simp add: csets_inv(2))
               apply (rule input_stream_inv)
        using label_prop_inv(1) apply (simp add: os_inv(4,7) operator_state.defs(3))
        using label_prop_inv(2) apply (simp add: os_inv(4,7) operator_state.defs(3) consumes_def)
        subgoal
          using dataplane_inv unfolding dataplane_tracker_inv_def
          apply (simp add: label_prop_inv(3))
          apply (elim exE conjE)
          subgoal premises prems for caps
            using prems(2,10-12) prems(4)[symmetric] unfolding front_inv_def imp_front_inv_def chnls_imp_front_inv_def
            apply simp
            apply (rule contrapos_pp[OF _ frontier_less_equal_exit_scope, rotated, where t1=\<open>t -+- MyPair 0 1\<close>])
             apply simp
            apply (drule spec2[of _ 1 1])
            apply (drule spec[of _ \<open>Loc 1 (Trg 1)\<close>])
            apply (drule spec2[of _ 1 0])
            apply (drule bspec[of _ _ \<open>(d, t)\<close>])
             apply (simp add: BULK_BENQ_def BHD_def)
             apply (rule disjI1)
             apply (metis list.set_sel(1))
            apply (rule frontier_less_equal_le_trans[rotated])
             apply (rule order.trans)
              apply assumption
             apply assumption
            apply (rule frontier_less_equal_ifrontier_trans[OF D, where l=\<open>Loc 1 (Trg 0)\<close>])
            using path_weight_loop_increment apply (simp add: subgraph_inv(1))
            apply simp
            done
          done
        subgoal premises prems
          using prems(2) prems(4)[symmetric] buffers_inv label_prop_inv(4) hd_in_set
          by (fastforce simp add: raw_summary_def BULK_BENQ_def BHD_def)
        using label_prop_inv(5) apply (simp add: os_inv(4,7) operator_state.defs(3) consumes_def)
          apply (subst label_prop_upd_inv_cong; simp add: BENQ_def)
         apply (rule inputs_ocaps_inv_consumes[OF label_prop_inv(6)])
        apply (clarsimp simp add: dataflow_tree_to_operator_def intro!: arg_cong[where f=\<open>set_op _ _\<close>] arg_cong[where f=\<open>dataflow_op _\<close>] arg_cong[where f=\<open>map_op _ _\<close>])
        apply (rule arg_cong2[where f=\<open>\<lambda>buf op. comp_op _ buf _ op\<close>])
         apply (simp add: BTL_def fun_eq_iff map_tl split: sum.splits)
        apply (rule loop_op_buf_cong[OF refl])
         apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
         apply (rule comp_op_buf_cong[OF refl refl refl])
         apply (simp add: ran_comp_wire BTL_def)
        apply (simp add: ran_loop_wire BTL_def)
        done
      subgoal for os_input'
        apply (clarsimp simp add: ooo_input_op_logic_def split: llist.splits event.splits)
        subgoal
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.rtrancl_refl)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          apply (unfold R_def)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI[of _ \<open>os(0 := drop_caps (os 0) (map (\<lambda>t. Cap t 0) (ocaps (os 0) 0)))\<close>])
          apply (rule exI[of _ os_input'])
          apply (intro exI conjI)
                              defer
                              apply (rule refl)
                              apply (rule subgraph_inv(1))
                              apply (rule subgraph_inv(2))
          using os_inv(1) apply (simp add: operator_state.defs(3) drop_caps_def)
          using os_inv(2) apply simp
          using os_inv(3) apply simp
          using os_inv(4) apply simp
          using os_inv(5) apply (simp add: ty1_check_def)
          using os_inv(4,6) apply fast
          using os_inv(7) apply simp
          using os_inv(8) apply simp
          using os_inv(9) apply simp
          using buffers_inv apply fast
          using dataplane_tracker_inv_drop_caps_all[OF D G subgraph_inv(2) dataplane_inv] apply blast
                   apply (simp add: csets_inv(1) buffers_inv os_inv(1,4) operator_state.defs(3))
                  apply (simp add: csets_inv(2))
                 apply (simp add: ocaps_drop_caps_all(1))
          using label_prop_inv(1) os_inv(4) apply fast
          using label_prop_inv(2) os_inv(4) apply simp
          using label_prop_inv(3) apply simp
          using label_prop_inv(4) apply (simp add: os_inv(1) operator_state.defs(3) buffers_inv)
          using label_prop_inv(5) os_inv(4) apply fast
          using label_prop_inv(6) apply fastforce
          apply (simp add: dataflow_tree_to_operator_def os_inv(4))
          done
        subgoal for lxs' t v w
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.rtrancl_refl)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          apply (unfold R_def)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI[of _ lxs'])
          apply (rule exI[of _ \<open>os(0 := produce (os 0) (Cap t 0) [en1 os_input (v, w)])\<close>])
          apply (rule exI[of _ os_input'])
          apply (rule exI)
          apply (rule exI[of _ cbufs])
          apply (rule exI[of _ \<open>BENQ (1, 0) (en1 os_input (v, w), t) chns\<close>])
          apply (intro exI conjI)
                              defer
                              apply (rule refl)
                              apply (rule subgraph_inv(1))
                              apply (rule subgraph_inv(2))
          using os_inv(1) apply (simp add: produce_def operator_state.defs(3))
          using os_inv(2) apply (simp add: produce_def)
          using os_inv(3) apply (simp add: produce_def)
          using os_inv(4) apply simp
          using os_inv(1,5) apply (simp add: produce_def ty1_check_def operator_state.defs(3))
          using os_inv(4,6) apply simp
          using os_inv(7) apply (simp add: produce_def)

          using os_inv(8) apply simp
          using os_inv(9) apply simp
                     apply (simp add: buffers_inv BENQ_def BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def fun_eq_iff produce_def)
                    apply (rule dataplane_tracker_inv_produce_singleton[OF D G subgraph_inv(2) dataplane_inv, where t=t and nid=0 and p=0])
          using input_stream_inv apply (fastforce simp add: timely_input_stream_def os_inv(1) operator_state.defs(3))
                    apply (rule refl)
                   apply (simp add: csets_inv(1) os_inv(1,4) operator_state.defs(3))
                  apply (simp add: csets_inv(2))
          using input_stream_inv apply (fastforce simp add: os_inv(1) operator_state.defs(3) produce_def)
          using label_prop_inv(1) os_inv(4) apply fast
          using label_prop_inv(2) os_inv(4) apply simp
          using label_prop_inv(3) apply simp
          using label_prop_inv(4) apply (simp add: os_inv(1) operator_state.defs(3) buffers_inv BENQ_def)
          using label_prop_inv(5) os_inv(4) apply fast
          using label_prop_inv(6) apply fastforce
          apply (simp add: dataflow_tree_to_operator_def os_inv(4))
          done
        subgoal for lxs' t
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.rtrancl_refl)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          apply (unfold R_def)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI[of _ lxs'])
          apply (rule exI[of _ \<open>os(0 := drop_cap (os 0) (Cap t 0))\<close>])
          apply (rule exI[of _ os_input'])
          apply (intro exI conjI)
                              defer
                              apply (rule refl)
                              apply (rule subgraph_inv(1))
                              apply (rule subgraph_inv(2))
          using os_inv(1) apply (simp add: drop_cap_def operator_state.defs(3))
          using os_inv(2) apply (simp add: drop_cap_def)
          using os_inv(3) apply (simp add: drop_cap_def)
          using os_inv(4) apply simp
          using os_inv(5) apply (simp add: drop_cap_def ty1_check_def)
          using os_inv(4,6) apply simp
          using os_inv(7) apply (simp add: drop_cap_def)
          using os_inv(8) apply simp
          using os_inv(9) apply simp
                     apply (simp add: buffers_inv)
                    apply (rule dataplane_tracker_inv_drop_cap[OF D G subgraph_inv(2) dataplane_inv, where t=t and nid=0 and p=0])
          using input_stream_inv apply (fastforce simp add: timely_input_stream_def os_inv(1) operator_state.defs(3))
                    apply (rule refl)
                   apply (simp add: csets_inv(1) os_inv(1,4) operator_state.defs(3) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
                   apply (subst (1 2) icoll_lshift)
          using timely_input_stream_expires_le input_stream_inv apply blast
          using timely_input_stream_expires_le input_stream_inv apply blast
                   apply simp
                  apply (simp add: csets_inv(2))
          using input_stream_inv apply (fastforce simp add: os_inv(1) operator_state.defs(3) drop_cap_def)
          using label_prop_inv(1) os_inv(4) apply fast
          using label_prop_inv(2) os_inv(4) apply simp
          using label_prop_inv(3) apply simp
          using label_prop_inv(4) apply (simp add: os_inv(1) operator_state.defs(3) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
          using label_prop_inv(5) os_inv(4) apply fast
          using label_prop_inv(6) apply fastforce
          apply (simp add: dataflow_tree_to_operator_def os_inv(4))
          done
        subgoal for lxs' t
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.rtrancl_refl)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          apply (unfold R_def)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI[of _ lxs'])
          apply (rule exI[of _ \<open>os(0 := add_cap (os 0) 0 t)\<close>])
          apply (rule exI[of _ os_input'])
          apply (intro exI conjI)
                              defer
                              apply (rule refl)
                              apply (rule subgraph_inv(1))
                              apply (rule subgraph_inv(2))
          using os_inv(1) apply (simp add: add_cap_def operator_state.defs(3))
          using os_inv(2) apply (simp add: add_cap_def)
          using os_inv(3) apply (simp add: add_cap_def)
          using os_inv(4) apply simp
          using os_inv(5) apply (simp add: add_cap_def ty1_check_def)
          using os_inv(4,6) apply simp
          using os_inv(7) apply (simp add: add_cap_def)
          using os_inv(8) apply simp
          using os_inv(9) apply simp
                     apply (simp add: buffers_inv)
                    apply (rule dataplane_tracker_inv_add_cap[OF D dataplane_inv G, where t=t and nid=0 and p=0])
          using input_stream_inv apply (fastforce simp add: os_inv(1) operator_state.defs(3) timely_input_stream_def)
                    apply (rule refl)
                   apply (simp add: csets_inv(1) os_inv(1,4) operator_state.defs(3) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
                   apply (subst (1 2) icoll_lshift)
          using timely_input_stream_expires_le input_stream_inv apply blast
          using timely_input_stream_expires_le input_stream_inv apply blast
                   apply (simp add: add_cap_def)
                  apply (simp add: csets_inv(2))
          using input_stream_inv apply (force simp add: os_inv(1) operator_state.defs(3) add_cap_def)
          using label_prop_inv(1) os_inv(4) apply fast
          using label_prop_inv(2) os_inv(4) apply simp
          using label_prop_inv(3) apply simp
          using label_prop_inv(4) apply (simp add: os_inv(1) operator_state.defs(3) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def add_cap_def)
          using label_prop_inv(5) os_inv(4) apply fast
          using label_prop_inv(6) apply fastforce
          apply (simp add: dataflow_tree_to_operator_def os_inv(4))
          done
        done
      subgoal for d t xs
        apply (intro exI conjI)
         apply (rule rtranclp.rtrancl_refl)
        apply (intro relcomppI)
          apply (rule bisim_refl)
         defer
         apply (rule wbisim_refl)
        apply (rule wb_upto_b_base)
        apply (unfold R_def[simplified])
        apply (rule exI[of _ S])
        apply (rule exI[of _ D])
        apply (rule exI[of _ lxs])
        apply (rule exI[of _ \<open>os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(1 := xs)\<rparr>)\<close>])
        apply (rule exI[of _ \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := xs)\<rparr>\<close>])
        apply (rule exI[of _ \<open>BENQ (2, 1) (d, t) cbufs\<close>])
        apply (rule exI[of _ sg])
        apply (intro conjI)
                           apply (clarsimp simp add: dataflow_tree_to_operator_def os_inv(1)
            intro!: arg_cong[where f=\<open>set_op _ _\<close>] arg_cong[where f=\<open>dataflow_op _\<close>]
            arg_cong[where f=\<open>map_op _ _\<close>])
                           apply (rule comp_op_buf_cong[OF refl refl])
                            apply (rule loop_op_buf_cong[OF refl])
                            apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
                            apply (rule comp_op_buf_cong[OF refl refl refl])
                            apply (simp add: ran_comp_wire)
                            apply (simp add: ran_loop_wire BENQ_def)
                           apply (clarsimp simp add: BENQ_def ran_def split: sum.splits)
                           apply (metis obj_sumE prod.exhaust)
                          apply (simp add: cimage_cUn csets_inv buffers_inv outputs_at_target_raw_summary subgraph_inv(1) os_inv(1,4) operator_state.defs(3) BENQ_def BULK_BENQ_def all_edges_def all_vertices_def neighbors_def)
                         apply (rule subgraph_inv(1))
                        apply (rule subgraph_inv(2))
                       apply (simp add: os_inv(2))
                      apply (simp add: os_inv(3))
                     apply (simp add: os_inv(4) operator_state.defs(3))
        using os_inv(1,5) apply (simp add: BENQ_def ty1_check_def)
        using os_inv(6) apply (simp add: BENQ_def label_prob_ty2_check_def)
        using os_inv(7) apply simp
        using os_inv(8) apply simp
        using os_inv(9) apply simp
               apply (rule dataplane_tracker_inv_update_outputs[OF dataplane_inv _ _ _ _ G, where nid=1 and p=1 and xs=\<open>[(d, t)]\<close>])
                  apply (simp add: os_inv(4) operator_state.defs(3))
                 apply (simp add: fun_upd_def)
                apply (simp add: BENQ_def)
               apply (simp add: subgraph_inv(1) raw_summary_def antichain_from_list_singleton)
              apply (simp add: input_stream_inv)
        subgoal
          using label_prop_inv
          by (simp add: all_edges_def all_vertices_def min_label_def neighbors_def labels_inv_def labels_stable_def)
        subgoal premises aux
          apply safe
          using label_prop_inv(2)
          by (simp add: all_edges_def all_vertices_def min_label_def neighbors_def labels_inv_def labels_stable_def)
        subgoal premises aux
          using label_prop_inv(3)
          by auto
        subgoal premises aux
          using label_prop_inv(4)
          by (simp add: buffers_inv BENQ_def BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1))
        subgoal premises aux
          using label_prop_inv(5)
          unfolding label_prop_upd_inv_def
          by (auto del: disjCI)
        subgoal premises aux
          using label_prop_inv(6)
          unfolding input_ocaps_inv_def
          by auto
        done
      subgoal for d t
        apply (intro exI conjI relcomppI)
           apply (rule rtranclp.rtrancl_refl)
          apply (rule bisim_refl)
         defer
         apply (rule wbisim_refl)
        apply (rule wb_upto_b_base)
        apply (unfold R_def[simplified])
        apply (rule exI[of _ S])
        apply (rule exI[of _ D])
        apply (rule exI[of _ lxs])
        apply (rule exI[of _ \<open>os(2 := consumes (os 2) 1 t d)\<close>])
        apply (rule exI[of _ os_label_prop])
        apply (rule exI[of _ \<open>BTL (2, 1) cbufs\<close>])
        apply (rule exI[of _ sg])
        apply (intro conjI)
                           apply (clarsimp simp add: dataflow_tree_to_operator_def os_inv(1)
            intro!: arg_cong[where f=\<open>set_op _ _\<close>] arg_cong[where f=\<open>dataflow_op _\<close>]
            arg_cong[where f=\<open>map_op _ _\<close>])
                           apply (rule comp_op_buf_cong[OF refl refl])
                            apply (rule loop_op_buf_cong[OF refl])
                            apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
                            apply (rule comp_op_buf_cong[OF refl refl refl])
                            apply (simp add: ran_comp_wire BTL_def map_tl)
                            apply (simp add: ran_loop_wire BTL_def)
                           apply (simp add: BTL_def ran_def split: sum.splits)
                           apply (metis prod.exhaust sum.exhaust)
                          apply (simp add: csets_inv buffers_inv BULK_BENQ_def BENQ_def BTL_def cimage_cUn)
                         apply (rule subgraph_inv(1))
                        apply (rule subgraph_inv(2))
        using os_inv(2) apply simp
        using os_inv(3) apply simp
        using os_inv(4) apply force
        using os_inv(1,5) apply (simp add: ty1_check_def operator_state.defs(3) BTL_def)
        using os_inv(4,6) apply (simp add:  label_prob_ty2_check_def operator_state.defs(3) BTL_def)
        using os_inv(7) apply force
        using os_inv(8) apply (simp add: inputs_ocaps_inv_consumes)
        using os_inv(9) apply simp
               apply (rule dataplane_tracker_inv_consumes[OF dataplane_inv _ D G, where xs=\<open>tl (cbufs (2, 1))\<close>])
               apply (simp add: BHD_def)
        using input_stream_inv apply simp
        using label_prop_inv(1) apply (simp add: os_inv(4,7) operator_state.defs(3))
        using label_prop_inv(2) apply (simp add: os_inv(4,7) operator_state.defs(3) consumes_def)
        using label_prop_inv(3) apply simp
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def BTL_def BENQ_def)
         apply (rule label_prop_inv(5))
        using label_prop_inv(6) apply simp
        done
      subgoal for os'
        unfolding label_propagation_op_logic_def trace_simp
        apply clarsimp
        apply (elim disjE)
          prefer 3
        subgoal
          apply (simp split: if_splits prod.splits)
          apply hypsubst_thin
          apply (intro exI conjI relcomppI)
             apply (rule rtranclp.intros(1))
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          unfolding R_def[simplified]
          apply (rule exI[of _ S])
          apply (rule exI[of _ "D"])
          apply (rule exI[of _ lxs])
          apply (rule exI[of _ "os(1 := drop_caps
                       (produces (os 1)
                         (label_prop_output_batch os_label_prop
                           (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0))))
                       (map (\<lambda>t. Cap t 0) (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0))))"])
          apply (rule exI[of _ "drop_caps
                       (produces os_label_prop
                         (label_prop_output_batch os_label_prop
                           (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0))))
                       (map (\<lambda>t. Cap t 0) (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0)))"])
          apply (rule exI[of _ cbufs])
          apply (rule exI[of _ sg])
          apply (intro conjI)
          subgoal
            by (simp add: dataflow_tree_to_operator_def os_inv(1))
          subgoal premises aux
            apply (rule arg_cong2[where f=set_spec_op])
             apply (simp_all add: subgraph_inv(1) buffers_inv csets_inv(1,2) outputs_at_target_raw_summary BULK_BENQ_def flip: list_diff_append map_append filter_append)
            apply (simp only: cUn_assoc)
            apply (rule arg_cong2[where f=cUn])
             apply simp
            apply (subst cset_eq_iff)
            apply (intro allI iffI)
            subgoal for x
              apply (cases x)
              subgoal for p d t
                apply hypsubst_thin
                apply (subst (asm) icoll_lshift)
                subgoal
                  using input_stream_inv timely_input_stream_expires_le 
                  by auto
                subgoal
                  apply (subst icoll_lshift)
                  subgoal
                    using input_stream_inv timely_input_stream_expires_le 
                    by auto
                  subgoal
                    subgoal
                      apply (clarsimp del: disjCI simp add: inputs_at_target_def cUn_assoc cimage_cUn)
                      apply (elim disjE; simp?)
                      done
                    done
                  done
                done
              done
            subgoal for x
              apply (cases x)
              subgoal for p d t
                apply hypsubst_thin
                apply (subst (asm) icoll_lshift)
                subgoal
                  using input_stream_inv timely_input_stream_expires_le 
                  by auto
                subgoal
                  apply (subst icoll_lshift)
                  subgoal
                    using input_stream_inv timely_input_stream_expires_le 
                    by auto
                  subgoal
                    apply (clarsimp del: disjCI simp add: label_prop_output_batch_def cimage_iff os_inv(4) operator_state.defs inputs_at_target_def cUn_assoc cimage_cUn)
                    apply (elim disjE; (clarsimp del: disjCI simp add: cimage_iff)?; hypsubst_thin?)
                    subgoal for t'
                      apply (rule disjI2)
                      apply (rule disjI2)
                      apply (rule disjI2)
                      apply (rule disjI2)
                      apply (rule disjI2)
                      unfolding release_caps_def drop_caps_def
                      apply (subgoal_tac "myfst t' |\<in>| cset_from_list T ")
                      subgoal
                        apply (rule cBexI[rotated])
                         apply assumption
                        apply simp
                        apply (subgoal_tac "filter (\<lambda>y. y \<le> myfst t') T \<noteq> []")
                        subgoal
                          apply (subgoal_tac "icoll (llist_of (map (\<lambda>(x, t'). Data t' (projl x)) (input (os 1) 0) @ map (\<lambda>(x, t'). Data t' (projl x)) (cbufs (1, 0)) @ map (\<lambda>(x, t'). Data t' (projl x)) (outpu (os 0) 0))) (MyPair (myfst t') 0) = []")
                          subgoal
                            apply (subgoal_tac "icoll lxs (MyPair (myfst t') 0) = []")
                            subgoal
                              apply simp
                              apply (rule components_from_labels_correct)
                              subgoal
                                using label_prop_inv(1)[unfolded os_inv(4) operator_state.defs, simplified, rule_format, of "myfst t'"]
                                by auto

                              subgoal
                                using label_prop_inv(2)[unfolded os_inv(4) operator_state.defs, simplified, rule_format, of "myfst t'"] 
                                by auto
                              done
                            subgoal
                              apply (subgoal_tac "\<forall>x. x \<in> lset lxs \<longrightarrow> is_Data x \<longrightarrow> frontier_less_equal (front (os 1) 0) (event.time x)")
                              subgoal
                                apply (drule frontier_less_equal_exit_scope)
                                apply (drule not_frontier_less_equal_sum)
                                apply clarsimp
                                unfolding icoll_def
                                apply simp
                                apply (subst lfilter_False)
                                 apply simp_all
                                apply (clarsimp split: event.splits)
                                apply (metis (no_types, opaque_lifting) MyPair_mono dataflow_topology_from_tree.zero_le dual_order.eq_iff event.discI(1) event.sel(1) frontier_less_equal_trans myprod.exhaust myprod.sel(1))
                                done
                              subgoal
                                apply safe
                                subgoal for x
                                  apply (drule timely_input_stream_frontier_less_equal[OF input_stream_inv, rule_format, of x])
                                   apply assumption
                                  using dataplane_inv[unfolded dataplane_tracker_inv_def, simplified, rule_format] apply -
                                  apply clarsimp
                                  unfolding front_inv_def imp_front_inv_def
                                  apply (drule spec[of _ 1])
                                  apply (drule spec[of _ 0])
                                  apply (drule spec[of _ "Loc 1 (Trg 0)"])
                                  apply (rule frontier_less_equal_le_trans[rotated])
                                   apply (rule order.trans)
                                    apply assumption
                                   apply assumption
                                  subgoal for caps
                                    unfolding Src_caps_inv_def
                                    apply (drule spec[of _ 0])
                                    apply (drule spec[of _ 0])
                                    unfolding c_pts_inv_def
                                    apply (drule spec[of _ "Loc 0 (Src 0)"])
                                    apply simp
                                    apply (rule frontier_less_equal_ifrontier_from_Src[where p=0 and s=0 and nid=0 and os=os and nt="subgraph.nxt sg", simplified, OF D])
                                    subgoal
                                      apply (drule sym[of _ "to_zmset (ocaps (os 0) 0)"])
                                      unfolding extract_prog_def
                                      apply simp
                                      apply (simp add:  c_pts_change_multiplicities SIM1(1,2) comp_def  zmset_filter_extract_progress_Src_consumes_diff)
                                      done
                                    subgoal premises aux
                                      apply (simp add: subgraph_inv)
                                      apply (rule path_weight_direct_0path[OF dataflow_topology.axioms(1)[OF]])
                                      using D[unfolded subgraph_inv] apply assumption
                                      apply (subst raw_summary_def)
                                      apply simp
                                      apply code_simp
                                      done
                                    apply assumption
                                    done
                                  done
                                done
                              done
                            done
                          subgoal
                            apply (subgoal_tac "\<forall> t \<in> snd ` set ((outputs_at_target (summ sg) os >> cbufs) (1, 0)). frontier_less_equal (front (os 1) 0) t")
                             defer
                            subgoal
                              apply safe
                              subgoal for _ a t
                                apply simp
                                using dataplane_inv[unfolded dataplane_tracker_inv_def, simplified] apply -
                                apply safe
                                unfolding front_inv_def imp_front_inv_def
                                apply (drule spec[of _ 1])
                                apply (drule spec[of _ 0])
                                apply (drule spec[of _ "Loc 1 (Trg 0)"])
                                unfolding chnls_imp_front_inv_def
                                apply (drule spec[of _ 1])
                                apply (drule spec[of _ 0])
                                apply (drule bspec[of _ _ t])
                                subgoal 
                                  by blast
                                apply (drule frontier_less_equal_le_trans)
                                 apply (rule order.trans[rotated])
                                  apply assumption+
                                done
                              done
                            subgoal
                              apply (simp add: icoll_append)
                              apply (intro conjI)
                              subgoal
                                (* issue: things can still be in the input buffer, but not yet processed, so the frontier advances without processing the new edge?
                                   maybe not because the loop capabilities are still on hold *)
                                using label_prop_inv(3) apply -
                                subgoal
                                  unfolding icoll_def
                                  apply (subst lfilter_False)
                                  subgoal
                                    apply clarsimp
                                    apply (drule bspec, simp)
                                     apply simp
                                    subgoal for a b
                                      apply (cases b; cases t'; simp; hypsubst_thin?)
                                      subgoal for t1 t2 t3
                                        apply (subgoal_tac "\<not> frontier_less_equal (exit_scope myfst (front (os 1) 1)) t2")
                                        subgoal
                                          using frontier_less_equal_trans 
                                          by (metis (no_types, lifting) label_prop_inv(3)  Un_iff image_eqI img_snd myprod.sel(1))
                                        subgoal
                                          using exit_scope_plus_distrib
                                          by (metis not_frontier_less_equal_sum)
                                        done
                                      done
                                    subgoal for a b
                                      apply (cases b; cases t'; simp; hypsubst_thin?)
                                      subgoal for t1 t2 t3
                                        apply (subgoal_tac "\<not> frontier_less_equal (exit_scope myfst (front (os 1) 1)) t2")
                                        subgoal
                                          using frontier_less_equal_trans 
                                          by (metis (no_types, lifting) label_prop_inv(3)  Un_iff image_eqI img_snd myprod.sel(1))
                                        subgoal
                                          using exit_scope_plus_distrib
                                          by (metis not_frontier_less_equal_sum)
                                        done
                                      done
                                    done
                                  subgoal
                                    by simp
                                  done
                                done
                              subgoal
                                apply (drule frontier_less_equal_exit_scope)
                                apply (drule not_frontier_less_equal_sum)
                                apply clarsimp
                                unfolding icoll_def
                                apply (subst lfilter_False)
                                subgoal
                                  apply clarsimp
                                  unfolding BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary
                                  apply simp
                                  apply (metis (no_types, opaque_lifting) MyPair_le Un_iff bot_nat_0.extremum frontier_less_equal_trans myprod.exhaust myprod.sel(1) snd_eqD trivial_dataflow_topology_interpretation.sum_le_zeroD)
                                  done
                                subgoal
                                  by simp
                                done
                              subgoal
                                apply (drule frontier_less_equal_exit_scope)
                                apply (drule not_frontier_less_equal_sum)
                                apply clarsimp
                                unfolding icoll_def
                                apply (subst lfilter_False)
                                subgoal
                                  apply clarsimp
                                  unfolding BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary
                                  apply simp
                                  apply (metis (no_types, opaque_lifting) MyPair_le Un_iff bot_nat_0.extremum frontier_less_equal_trans myprod.exhaust myprod.sel(1) snd_eqD trivial_dataflow_topology_interpretation.sum_le_zeroD)
                                  done
                                subgoal
                                  by simp
                                done
                              done
                            done
                          done
                        subgoal
                          by (metis List.empty_filter_conv order_class.order_eq_iff)
                        done
                      subgoal
                        by auto
                      done
                    done
                  done
                done
              done
            done
          subgoal
            using subgraph_inv by auto
          subgoal
            using subgraph_inv by auto
          subgoal
            using os_inv(2) by force
          subgoal
            using os_inv(3) by force
          subgoal
            apply (rule exI[of _ T])
            apply (rule exI[of _ G])
            apply (rule exI[of _ V])
            apply (rule exI[of _ L])
            apply (simp add: operator_state.defs)
            unfolding drop_caps_def produces_def release_caps_def
            apply (simp add: os_inv(4) operator_state.defs)
            done
          subgoal
            using os_inv(5) apply -
            unfolding ty1_check_def os_inv(1)
            apply (auto simp add: operator_state.defs)
            done
          subgoal
            using os_inv(6) 
            unfolding label_prob_ty2_check_def os_inv(4)  
              drop_caps_def produces_def release_caps_def label_prop_output_batch_def
            by (auto simp add: operator_state.defs)
          subgoal
            using os_inv(7) 
            unfolding input_ocaps_inv_def  os_inv(4)  
              drop_caps_def produces_def release_caps_def
            by (auto simp add: os_inv(7)[rule_format, of 1] raw_summary_def operator_state.defs dest!: in_set_list_diffD del: in_set_list_diffI intro!: in_set_list_diffI)
          using os_inv(8) apply simp
          using os_inv(9) apply simp
          subgoal premises aux
            apply (rule iffD1[OF dataplane_tracker_inv_clean, rotated 2, of _ _ sg "upfro sg"])
              apply (rule dataplane_tracker_inv_produces_drops[OF D, where nid=1 and os=os 
                  and drops = "\<lambda> p. if p = 1
                         then []
                         else filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0)"
                  and produs="map (\<lambda> t . (0, MyPair t 0, 1)) (rmdups {} (map myfst (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0))))"
                  and oputs="(\<lambda> p. if p = 1 then [] else map (\<lambda>t. (en2 os_label_prop (components_from_labels (all_edges os_label_prop t) (min_label os_label_prop t)), (MyPair t 0)))
                          (rmdups {} (map myfst (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0)))))"])
                         apply (rule refl)+
                    prefer 9
            subgoal
              apply (intro allI impI conjI)
                     apply simp
              subgoal
                apply (rule ext)+
                unfolding produces_def drop_caps_def
                apply auto
                subgoal
                  apply (subst filter_False)
                   apply auto
                  done
                subgoal for p
                  apply (subst (2) filter_True)
                   apply clarsimp
                   apply (metis num2_neq(2))
                  apply (simp add: comp_def)
                  done
                done
              subgoal
                by auto
              subgoal
                unfolding produces_def drop_caps_def
                by auto
              subgoal
                unfolding produces_def drop_caps_def label_prop_output_batch_def
                by auto
              subgoal
                apply (rule ext)+
                unfolding produces_def drop_caps_def
                apply (auto simp add: filter_True)
                apply (subst filter_True)
                 apply auto
                subgoal for p a t
                  apply (subgoal_tac "p = 0")
                  subgoal
                    using label_prop_inv(3)[rule_format, of "myfst t"] apply -
                    apply (drule meta_mp)
                    subgoal
                      by auto
                    subgoal
                      by (simp add: os_inv(4) operator_state.defs exit_scope_plus_distrib frontier_less_equal_antichain_plusI2)
                    done
                  subgoal
                    by (metis num2_neq(2))
                  done
                done
              subgoal
                apply (rule ext)+
                unfolding produces_def drop_caps_def label_prop_output_batch_def
                apply (clarsimp simp add: operator_state.defs os_inv(4) filter_empty_conv)
                subgoal for p
                  apply (subgoal_tac "p = 0")
                  subgoal
                    apply (subst (2) filter_True)
                    subgoal
                      by auto
                    subgoal
                      by simp
                    done
                  subgoal
                    by (metis num2_neq(2))
                  done
                done
              subgoal for nid
                unfolding produces_def drop_caps_def
                by auto
              done
            subgoal
              using num2_neq(2) by (force simp add: operator_state.defs os_inv(4))
            subgoal
              apply (clarsimp simp add: operator_state.defs os_inv(4))
              subgoal for x
                using label_prop_inv(4)[unfolded buffers_inv, simplified]
                by (metis UnCI myprod.collapse)
              done
            subgoal 
              apply (clarsimp simp add: operator_state.defs os_inv(4))
              subgoal for p x
                using label_prop_inv(4)[unfolded buffers_inv, simplified]
                by (metis (full_types) UnCI myprod.exhaust_sel num2_neq(2))
              done
            subgoal 
              apply (auto simp add: filter_False comp_def operator_state.defs os_inv(4))
              subgoal for p
                apply (subgoal_tac "p = 0")
                subgoal
                  by (auto simp add: filter_True comp_def operator_state.defs os_inv(4))
                subgoal
                  by (metis num2_neq(2))
                done
              done
            subgoal
              using G by assumption
            subgoal
              using subgraph_inv(2) by assumption
            subgoal
              using dataplane_inv by assumption
            subgoal
              by auto
            done
          subgoal
            using input_stream_inv timely_input_stream_expires_le 
            by auto
          subgoal
            using label_prop_inv(1)
            by auto
          subgoal
            using label_prop_inv(2) by auto
          subgoal
            using label_prop_inv(3) by auto
          subgoal
            using label_prop_inv(4) buffers_inv
            unfolding drop_caps_def release_caps_def produces_def
            by (auto simp add: BULK_BENQ_def outputs_at_target_raw_summary inputs_at_target_def subgraph_inv(1) dest!: in_set_list_diffD)
          subgoal
            using label_prop_inv(5) by simp
          subgoal premises aux
            using label_prop_inv(6) apply -
            unfolding input_ocaps_inv_def drop_caps_def
            apply (auto simp add: filter_False os_inv(7)[rule_format, unfolded raw_summary_def, simplified])
            subgoal 
              by fastforce
            subgoal
              apply (drule spec2[of _  0 1])
              apply simp
              apply (drule bspec[of _ ])
               apply assumption
              apply (simp add: filter_True comp_def )
              done
            subgoal for a b
              apply (drule spec2[of _  0 0])
              apply simp
              apply (drule bspec[of _ ])
               apply assumption
              apply (simp add: filter_True comp_def )
              apply (rule in_set_list_diffI)
               apply fastforce
              apply simp
              using label_prop_inv(3)[rule_format, of "myfst b"] apply -
              apply (drule meta_mp)
              subgoal
                by force
              subgoal
                apply (simp add: operator_state.defs os_inv(4) exit_scope_plus_distrib)
                apply (auto intro: frontier_less_equal_antichain_plusI2)
                done
              done
            subgoal for a b
              apply (drule spec2[of _  0 0])
              apply simp
              apply (drule bspec[of _ ])
               apply assumption
              apply (simp add: filter_True comp_def )
              apply (rule in_set_list_diffI)
               apply fastforce
              apply simp
              using label_prop_inv(3)[rule_format, of "myfst b"] apply -
              apply (drule meta_mp)
              subgoal
                by force
              subgoal
                apply (simp add: operator_state.defs os_inv(4) exit_scope_plus_distrib)
                apply (auto intro: frontier_less_equal_antichain_plusI2)
                done
              done
            done
          done
        subgoal
          apply (simp  del: filter.simps split: list.splits)
          subgoal for x xs
            apply (cases x; simp del: filter.simps)
            apply hypsubst_thin
            subgoal for d t
              apply (simp del: filter.simps split: prod.splits)
              subgoal for v1 v2 l1 l2
                apply hypsubst_thin
                apply (intro exI conjI relcomppI)
                   apply (rule rtranclp.intros(1))
                  apply (rule bisim_refl)
                 defer
                 apply (rule wbisim_refl)
                apply (rule wb_upto_b_base)
                unfolding R_def[simplified]
                apply (rule exI[of _ S])
                apply (rule exI[of _ D])
                apply (rule exI[of _ lxs])
                apply (rule exI[of _ "os(1 := release_caps
                       (drop_caps
                         (produces
                           (add_caps (input_tl (os 1) 0)
                             (map snd
                               (label_prop_edge_batch os_label_prop (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                                 (myfst t) l1 l2 t)))
                           (label_prop_edge_batch os_label_prop (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (myfst t) l1 l2 t))
                         (map snd
                           (label_prop_edge_batch os_label_prop (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (myfst t) l1 l2 t)))
                       1)"])
                apply (rule exI[of _ "release_caps
                       (drop_caps
                         (produces
                           (add_caps (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (map snd
                               (label_prop_edge_batch os_label_prop (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                                 (myfst t) l1 l2 t)))
                           (label_prop_edge_batch os_label_prop (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (myfst t) l1 l2 t))
                         (map snd
                           (label_prop_edge_batch os_label_prop (label_prop_edge_record_update (input_tl os_label_prop 0) (myfst t) v1 v2 l1 l2)
                             (myfst t) l1 l2 t)))
                       1"])
                apply (rule exI[of _ cbufs])
                apply (rule exI[of _ sg])
                apply (intro conjI)
                subgoal
                  by (simp add: operator_state.defs dataflow_tree_to_operator_def os_inv(1))
                subgoal premises aux
                  using aux(1,2,3) apply -
                  apply (simp  del: filter.simps add: label_prop_edge_batch_def label_prop_edge_record_update_def buffers_inv operator_state.defs os_inv(4) csets_inv(1))
                  apply (rule arg_cong2[where f=set_spec_op])
                   apply (simp_all del: filter.simps)
                  apply (clarsimp simp del: filter.simps del: disjCI simp add: inputs_at_target_def BULK_BENQ_def operator_state.defs outputs_at_target_raw_summary subgraph_inv buffers_inv csets_inv(1) os_inv(4))
                  subgoal
                    apply (subst (1) icoll_LCons_Data)
                    subgoal
                      using input_stream_inv timely_input_stream_expires_le 
                      by auto
                    subgoal
                      apply (simp add: input_tl_def)
                      apply (subgoal_tac "t = MyPair (myfst t) 0")
                      subgoal
                        apply (subst (1) all_edges_eq[rotated, where V=V and label_sync=L and input_sync="input (os 1)"])
                        subgoal 
                          using label_prop_inv(5)[unfolded os_inv(4) operator_state.defs] by simp
                        subgoal by simp
                        subgoal
                          apply simp
                          apply (rule arg_cong2[where f=cinsert])
                          subgoal
                            apply (simp add: insert_commute ccs_insert_symmetric)
                            apply (subst ccs_insert_swap)
                            apply auto
                            done
                          subgoal
                            apply (subst (1 3) cUn_assoc)
                            apply (rule arg_cong2[where f=cUn])
                            subgoal
                              by simp
                            subgoal
                              apply (subst (1) icoll_LCons_Data)
                              subgoal
                                using input_stream_inv timely_input_stream_expires_le 
                                by auto
                              subgoal 
                                apply (subst (3) cimage_cUn)
                                apply (subst (2) cUn_assoc)
                                apply (rule arg_cong2[where f=cUn])
                                 apply (simp add:  csets_inv(2))
                                apply (subst (1) cfilter_False)
                                subgoal
                                  unfolding label_prop_neighbor_batch_def
                                  by auto
                                subgoal
                                  apply simp
                                  apply (rule cimage_cong)
                                  subgoal
                                    by simp
                                  subgoal for t''
                                    apply (cases "t \<le> t''")
                                    subgoal
                                      apply (subst all_edges_eq_le[rotated, where V=V and label_sync=L and input_sync="input (os 1)"])
                                      subgoal using label_prop_inv(5)[unfolded os_inv(4) operator_state.defs] by simp
                                      subgoal 
                                        using myfst_mono by blast
                                      subgoal by simp
                                      subgoal
                                        apply (subst insert_commute)
                                        apply (simp add: ccs_insert_symmetric)
                                        done
                                      done
                                    subgoal
                                      apply (subst all_edges_eq_not_le[rotated, where V=V and label_sync=L and input_sync="input (os 1)"])
                                      subgoal
                                        by (metis MyPair_mono bot_nat_0.extremum myprod.exhaust_sel)
                                      subgoal
                                        by simp
                                      subgoal
                                        apply simp
                                        done
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          done
                        done
                      subgoal
                        using label_prop_inv(4)[rule_format, of t] apply -
                        apply (drule meta_mp)
                         apply (simp add: buffers_inv BULK_BENQ_def inputs_at_target_def)
                        subgoal
                          apply (cases t)
                          apply auto
                          done
                        done
                      done
                    done
                  done
                subgoal
                  using subgraph_inv(1) by assumption
                subgoal
                  using subgraph_inv(2) by assumption
                subgoal
                  using os_inv(2)
                  by auto
                subgoal
                  using os_inv(3)
                  by auto
                subgoal 
                  apply (simp del: filter.simps add:  operator_state.defs os_inv(4) )
                  apply (rule exI[of _ "Cons (myfst t) T"])
                  apply (rule exI[of _ "G(myfst t := (map_entry v1 (Cons v2) (G (myfst t)))(v2 := Cons v1 (G (myfst t) v2)))"])
                  apply (rule exI[of _ "map_entry (myfst t) (append [v1, v2]) V"])
                  apply (rule exI[of _ "L(myfst t := (L (myfst t))(l1 := l2))"])
                  apply (simp del: filter.simps)
                  apply (auto simp add: label_prop_neighbor_batch_def add_caps_def comp_def operator_state.defs  produces_def release_caps_def drop_caps_def label_prop_edge_batch_def label_prop_edge_record_update_def input_tl_def)
                  done
                subgoal 
                  using os_inv(1,5)
                  unfolding ty1_check_def
                  by (auto simp add: operator_state.defs produces_def release_caps_def drop_caps_def)
                subgoal premises aux
                  using os_inv(4,6) aux(1,2,3) apply -
                  unfolding label_prob_ty2_check_def add_caps_def input_tl_def label_prop_edge_batch_def label_prop_edge_record_update_def label_prop_neighbor_batch_def
                  apply (auto 0 0 simp add: os_inv(1,4) image_iff operator_state.defs produces_def release_caps_def drop_caps_def)
                  subgoal
                    by (metis UnI1 img_fst list.set_intros(2))
                  subgoal
                    by auto
                  subgoal
                    by force
                  subgoal
                    by force
                  done
                subgoal premises aux
                  unfolding add_caps_def
                  using os_inv(7) by auto
                using os_inv(8) apply simp
                using os_inv(9) apply simp
                subgoal premises aux
                  apply (rule dataplane_tracker_inv_release_caps_update[OF D])
                    apply (rule dataplane_tracker_inv_add_caps_produces_drop_caps_update[OF D])
                  using dataplane_inv apply simp
                  using G apply simp
                  using subgraph_inv(2) apply assumption 
                  subgoal
                    apply (subgoal_tac "t \<in> set (ocaps (os 1) 1)")
                    subgoal
                      unfolding label_prop_edge_batch_def label_prop_neighbor_batch_def label_prop_edge_record_update_def
                      apply (auto del: disjCI simp add: image_iff split_beta)
                      apply (rule bexI[rotated])
                       apply assumption
                      apply (simp add: less_eq_myprod_def)
                      done
                    subgoal
                      apply (rule  label_prop_inv(6)[unfolded input_ocaps_inv_def, rule_format, of _ 0 0, simplified])
                      subgoal
                        using aux(2,3) 
                        by (simp add: os_inv(4) operator_state.defs)
                      subgoal
                        by (simp add: zero_myprod_def os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                      done
                    done
                  subgoal 
                    using G
                    by (smt (verit) Timely_Operator_State.intsum_add_caps array_rules(3,4) graph_summar_nt_intsum_cong intsum_drop_caps intsum_input_tl
                        intsum_produces)
                  using subgraph_inv(2) apply assumption 
                  done
                subgoal premises aux
                  using input_stream_inv by simp
                subgoal
                  apply safe
                  subgoal for t''
                    apply (rule labels_inv_input0_preserved[where xs=xs])
                    using label_prop_inv(1) apply blast
                    subgoal
                      using label_prop_inv(5) by assumption
                    subgoal
                      by (clarsimp simp add: input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def operator_state.defs os_inv(4) release_caps_def drop_caps_def produces_def)
                        apply (clarsimp simp add: label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def operator_state.defs os_inv(4) release_caps_def drop_caps_def produces_def)
                        apply simp
                       apply (clarsimp simp add: label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def operator_state.defs os_inv(4) release_caps_def drop_caps_def produces_def)
                       apply simp
                      apply (clarsimp simp add: label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def operator_state.defs os_inv(4) release_caps_def drop_caps_def produces_def)
                     apply (clarsimp simp add: label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def operator_state.defs os_inv(4) release_caps_def drop_caps_def produces_def)
                     apply simp
                    apply (clarsimp simp add: label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def operator_state.defs os_inv(4) release_caps_def drop_caps_def produces_def)
                    done
                  done

                subgoal premises aux
                  apply safe
                  subgoal for t'
                    apply (subst (asm) label_prop_edge_record_update_def)
                    apply simp      
                    apply (elim disjE)
                    subgoal
                      apply (subgoal_tac "frontier_less_equal (exit_scope myfst (front (os 1) 1)) t'")
                      subgoal
                        by (simp add: exit_scope_plus_distrib frontier_less_equal_antichain_plusI2)
                      subgoal
                        using aux(2) label_prop_inv(3)[rule_format] by (auto simp add: os_inv(4) operator_state.defs)
                      done
                    subgoal
                      apply (subgoal_tac "\<not> myfst t \<le> t'")
                      subgoal
                        apply (rule labels_stable_input0_preserved)
                              apply (rule label_prop_inv(2)[unfolded os_inv(4) operator_state.defs, simplified, rule_format, of t'])
                               apply (simp add: os_inv(4) operator_state.defs)
                              apply assumption+
                        using aux[unfolded os_inv(4) operator_state.defs, simplified] apply (auto simp add: label_prop_edge_record_update_def  os_inv(4) operator_state.defs)
                        done
                      subgoal
                        using aux(2) apply -
                        using label_prop_inv(3)[rule_format, of "myfst t"] apply -
                        apply (drule meta_mp)
                        subgoal
                          by (auto simp add: os_inv(4) operator_state.defs)
                        subgoal
                          by (metis exit_scope_plus_distrib frontier_less_equal_antichain_plusI2 frontier_less_equal_trans)
                        done
                      done
                    done
                  done
                subgoal premises aux
                  using aux(2) label_prop_inv(3) 
                  by (auto simp add:  os_inv(4) operator_state.defs input_tl_def)
                subgoal premises
                  using label_prop_inv(4)
                  by (auto simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def input_tl_def release_caps_def drop_caps_def add_caps_def label_prop_edge_record_update_def label_prop_edge_batch_def label_prop_neighbor_batch_def dest!: in_set_list_diffD in_set_tlD)
                subgoal
                  apply (rule label_prop_upd_inv_input0_preserved)
                         apply (rule label_prop_inv(5))
                        apply (simp_all add: operator_state.defs os_inv(4))
                  unfolding label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def release_caps_def drop_caps_def add_caps_def
                  by (auto simp add: operator_state.defs os_inv(4)  input_tl_def release_caps_def drop_caps_def produces_def)
                subgoal premises aux
                  apply simp
                  apply (rule input_ocaps_inv_release_capsI)
                  apply (rule input_ocaps_inv_drop_produces_add_capsI)
                  using label_prop_inv(6) input_ocaps_inv_input_tlI apply fast
                  done
                done
              done
            done
          done
        subgoal
          apply (simp  del: filter.simps split: list.splits)
          subgoal for x xs
            apply (cases x; simp del: filter.simps)
            apply hypsubst_thin
            subgoal for d t
              apply (simp del: filter.simps split: prod.splits)
              subgoal for v l
                apply hypsubst_thin
                apply (intro exI conjI relcomppI)
                   apply (rule rtranclp.intros(1))
                  apply (rule bisim_refl)
                 defer
                 apply (rule wbisim_refl)
                apply (rule wb_upto_b_base)
                unfolding R_def[simplified]
                apply (rule exI[of _ S])
                apply (rule exI[of _ D])
                apply (rule exI[of _ lxs])
                apply (rule exI[of _ "os(1 := release_caps
                       (drop_caps
                         (produces
                           (add_caps (input_tl (os 1) 1)
                             (map snd
                               (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v l t)))
                           (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v l t))
                         (map snd (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v l t)))
                       1)"])
                apply (rule exI[of _ "release_caps
                       (drop_caps
                         (produces
                           (add_caps (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l))
                             (map snd
                               (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v l t)))
                           (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v l t))
                         (map snd (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v l t)))
                       1"])
                apply (rule exI[of _ cbufs])
                apply (rule exI[of _ sg])
                apply (intro conjI)
                subgoal
                  by (simp add: operator_state.defs dataflow_tree_to_operator_def os_inv(1))
                subgoal premises aux
                  using aux(2,3) apply -
                  apply (simp  del: filter.simps add: label_prop_edge_batch_def label_prop_edge_record_update_def buffers_inv operator_state.defs os_inv(4) csets_inv(1))
                  apply (rule arg_cong2[where f=set_spec_op])
                   apply (clarsimp simp del: filter.simps del: disjCI simp add: inputs_at_target_def BULK_BENQ_def operator_state.defs outputs_at_target_raw_summary subgraph_inv buffers_inv csets_inv(1) os_inv(4))
                  subgoal
                    apply (simp add: cUn_assoc)
                    apply (rule arg_cong2[where f=cUn])
                    subgoal
                      by simp
                    subgoal
                      apply (subst (3) cimage_cUn)
                      apply (simp add: cUn_assoc)
                      apply (rule arg_cong2[where f=cUn])
                      subgoal
                        by (simp add: csets_inv(2))
                      subgoal
                        apply (subst (1) cfilter_False)
                        subgoal
                          unfolding label_prop_label_batch_def label_prop_neighbor_batch_def
                          by auto
                        subgoal
                          apply simp
                          apply (rule cimage_cong)
                          subgoal
                            unfolding input_tl_def
                            by simp
                          subgoal for tt
                            unfolding input_tl_def
                            by simp
                          done
                        done
                      done
                    done
                  subgoal
                    by simp
                  done
                subgoal
                  using subgraph_inv(1) by assumption
                subgoal
                  using subgraph_inv(2) by assumption
                subgoal
                  using os_inv(2) by simp
                subgoal
                  by (simp add: os_inv(3,4) operator_state.defs)
                subgoal
                  apply (rule exI[of _ T])
                  apply (rule exI[of _ G])
                  apply (rule exI[of _ V])
                  apply (rule exI[of _ "label (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l))"])
                  apply simp
                  apply (simp add: operator_state.defs)
                  unfolding release_caps_def drop_caps_def produces_def add_caps_def input_tl_def label_prop_label_record_update_def
                  by (simp add: operator_state.defs os_inv(4))
                    (* show but finishes *)
                subgoal
                  using os_inv(1,5)
                  by (simp add:  operator_state.defs)
                subgoal
                  using os_inv(2,4,6) apply -
                  apply simp
                  apply (rule label_prob_ty2_check_producesI)
                    apply simp
                    apply (rule label_prob_ty2_check_input_tlI)
                    apply (auto simp add: operator_state.defs label_prop_label_batch_def label_prop_neighbor_batch_def)
                  done
                subgoal
                  using os_inv(7) by simp
                using os_inv(8) apply simp
                using os_inv(9) apply simp
                subgoal
                  apply (rule dataplane_tracker_inv_release_caps_update[OF D])
                    apply (rule dataplane_tracker_inv_add_caps_produces_drop_caps_update[OF D])
                  subgoal
                    using dataplane_inv by simp
                  subgoal
                    using G by simp
                  subgoal
                    using subgraph_inv(2) by assumption
                  subgoal
                    unfolding label_prop_label_batch_def label_prop_neighbor_batch_def
                    apply (clarsimp simp add: os_inv(4) operator_state.defs)
                    using label_prop_inv(6)[unfolded input_ocaps_inv_def os_inv(7)[rule_format] raw_summary_def, simplified, rule_format, of "(d, t)" 1 1 0, simplified]
                    apply (metis (no_types, lifting) dual_order.eq_iff less_eq_myprod_def list.set_intros(1) myprod.sel(1,2) zero_myprod_def)
                    done
                  subgoal premises
                    using G
                    by (smt (verit, best) Timely_Operator_State.intsum_add_caps fun_upd_other fun_upd_same graph_summar_nt_intsum_cong intsum_drop_caps intsum_input_tl intsum_produces)
                  subgoal
                    using subgraph_inv(2) by assumption
                  done
                subgoal
                  using input_stream_inv by simp
                subgoal
                  apply safe
                  subgoal for ta
                    apply simp
                    apply (rule labels_inv_input1_preserved_record_update_tl[
                          of os_label_prop d t v l "myfst t"
                          "label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)" ta,
                          simplified])
                       apply (rule label_prop_inv(1)[rule_format])
                      apply (rule label_prop_inv(5))
                     apply simp_all
                    done
                  done
                subgoal
                  apply safe
                  subgoal for t'
                    apply simp
                    apply (rule labels_stable_input1_preserved_record_update_tl)
                    using label_prop_inv(2) apply fast
                    using label_prop_inv(3)[rule_format, of "myfst t"] apply -
                    apply (drule meta_mp)
                    subgoal
                      by (simp add: os_inv(4) operator_state.defs)
                    subgoal
                      by (metis (no_types, lifting) exit_scope_plus_distrib frontier_less_equal_antichain_plusI2 frontier_less_equal_trans)
                    done
                  done
                subgoal
                  unfolding input_tl_def
                  using label_prop_inv(3)
                  by (simp add: image_iff os_inv(4) operator_state.defs)
                subgoal
                  using label_prop_inv(4)
                  by (auto simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def input_tl_def release_caps_def drop_caps_def add_caps_def label_prop_label_batch_def label_prop_neighbor_batch_def dest!: in_set_list_diffD)
                subgoal
                  apply simp
                  apply (rule label_prop_upd_inv_input1_preserved[])
                           apply (rule label_prop_inv(5))
                          apply (simp_all add: label_prop_label_record_update_def input_tl_def image_iff os_inv(4) operator_state.defs)
                  done
                subgoal
                  apply simp
                  apply (rule input_ocaps_inv_release_capsI)
                  apply (rule input_ocaps_inv_drop_produces_add_capsI)
                  apply (rule input_ocaps_inv_input_tlI)
                  using label_prop_inv(6) apply -
                  apply (simp add: os_inv(4) operator_state.defs)
                  done
                done
              done
            done
          done
        done
      subgoal for os_incr'
        apply (clarsimp simp add: increment_op_logic_def if_splits)
        apply (intro exI conjI relcomppI)
           apply (rule rtranclp.rtrancl_refl)
          apply (rule bisim_refl)
         defer
         apply (rule wbisim_refl)
        apply (rule wb_upto_b_base)
        apply (unfold R_def[simplified])
        apply (rule exI[of _ S])
        apply (rule exI[of _ D])
        apply (rule exI[of _ lxs])
        apply (rule exI[of _ \<open>os(2 := os_incr')\<close>])
        apply (rule exI[of _ os_label_prop])
        apply (rule exI[of _ cbufs])
        apply (rule exI[of _ sg])
        apply (intro conjI)
                           apply (simp add: dataflow_tree_to_operator_def os_inv(1))
                          apply (simp add: csets_inv buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def cimage_cUn)
                         apply (rule subgraph_inv(1))
                        apply (rule subgraph_inv(2))
        using os_inv(2) apply simp
        using os_inv(3) apply simp
        using os_inv(4) apply force
        using os_inv(1,5) apply simp
                   apply (rule os_inv(6))
        using os_inv(7) apply force
        using os_inv(7,8) apply (clarsimp simp add: input_ocaps_inv_def drop_caps_def produces_def raw_summary_def filter_False)
        using os_inv(9) apply simp
        subgoal
          using dataplane_tracker_inv_produces_drops[OF D refl refl refl refl refl _ _ _ _ G subgraph_inv(2) dataplane_inv,
              where nid=2 and drops=\<open>(\<lambda>_. [])(1 := ocaps (os 2) 1)\<close> and produs=\<open>map (\<lambda>(_, t). (1, t + MyPair 0 1, 1)) (input (os 2) 1)\<close>
                and oputs=\<open>(\<lambda>_. [])(1 := map (\<lambda>(d, t). (d, t + MyPair 0 1)) (input (os 2) 1))\<close>]
          apply -
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          using os_inv(7,8) apply (clarsimp simp add: split_beta input_ocaps_inv_def raw_summary_def)
          apply (drule meta_mp)
          using os_inv(7,8) apply (fastforce simp add: split_beta input_ocaps_inv_def raw_summary_def)

          apply (drule meta_mp)
           apply (clarsimp simp add: comp_def split_beta filter_True filter_False)
          apply (subst dataplane_tracker_inv_clean_input)
           defer
           apply assumption
          apply (clarsimp simp add: drop_caps_def produces_def comp_def split_beta fun_eq_iff)
          apply (rule conjI; clarsimp)
          subgoal for p
            by (cases \<open>p = 1\<close>; clarsimp dest!: num2_neq(2) simp add: filter_True filter_False comp_def)
          subgoal for p
            by (cases \<open>p = 1\<close>; clarsimp simp add: filter_True filter_False)
          done
        using input_stream_inv apply simp
             apply (rule label_prop_inv(1))
        using label_prop_inv(2) apply simp
        using label_prop_inv(3) apply simp
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
         apply (rule label_prop_inv(5))
        using label_prop_inv(6) apply simp
        done
      subgoal 
        sorry
      subgoal 
        sorry
      subgoal 
        sorry
      subgoal 
        sorry
      subgoal 
        sorry
      subgoal
        apply (insert dataplane_inv subgraph_inv(1))
        apply (unfold dataplane_tracker_inv_def propagation_inv_def)
        apply (elim exE conjE; hypsubst_thin)
        apply (rule FalseE)
        apply (rule propagate_all_terminates[OF D, unfolded not_def, rule_format])
        by (auto simp add: raw_summary_def)
      subgoal 
        sorry
      subgoal for d t xs
        apply (intro exI conjI)
         apply (rule rtranclp.rtrancl_refl)
        apply (intro relcomppI)
          apply (rule bisim_refl)
         defer
         apply (rule wbisim_refl)
        apply (rule wb_upto_b_base)
        apply (unfold R_def[simplified])
        apply (rule exI[of _ \<open>cinsert ((1, 0), d, t) S\<close>])
        apply (rule exI[of _ D])
        apply (rule exI[of _ lxs])
        apply (rule exI[of _ \<open>os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(0 := xs)\<rparr>)\<close>])
        apply (rule exI[of _ \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(0 := xs)\<rparr>\<close>])
        apply (rule exI[of _ cbufs])
        apply (rule exI[of _ sg])
        apply (intro exI conjI)
                           apply (simp add: dataflow_tree_to_operator_def os_inv(1))
        subgoal
          apply (simp add: subgraph_inv outputs_at_target_raw_summary csets_inv(1,2) buffers_inv os_inv(4) operator_state.defs(3))
          apply (rule arg_cong2[where f=set_spec_op])
           apply (rule arg_cong2[where f=cinsert])
            apply simp_all
          apply (rule arg_cong2[where f=cUn])
           apply simp
          apply (rule cimage_cong)
          subgoal
            by simp
          subgoal premises for tt
            unfolding all_edges_def all_vertices_def set_neighbors
            by simp
          done
                         apply (rule subgraph_inv(1))
                        apply (rule subgraph_inv(2))
                       apply (simp add: os_inv(2))
                      apply (simp add: os_inv(3))
                     apply (simp add: os_inv(4) operator_state.defs(3))
        using os_inv(1,5) apply simp
        using os_inv(6) unfolding label_prob_ty2_check_def apply simp
        using os_inv(7) apply simp
        using os_inv(8) apply simp
        using os_inv(9) apply simp
               apply (rule dataplane_tracker_inv_update_outputs_outside[OF dataplane_inv _ _ G])
                apply (simp add: fun_upd_def)
               apply (simp add: subgraph_inv(1) raw_summary_def)
              apply (subgoal_tac \<open>outputs_at_target (summ sg) (os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(0 := xs)\<rparr>)) (1, 0)
  = outputs_at_target (summ sg) os (1, 0)\<close>)
               apply (simp add: csets_inv(1) buffers_inv BULK_BENQ_def all_edges_def all_vertices_def neighbors_def)
               apply (simp add: subgraph_inv(1) outputs_at_target_raw_summary)
               apply (simp add: input_stream_inv)
              apply (simp add: subgraph_inv os_inv(4) operator_state.defs outputs_at_target_raw_summary)
        subgoal
          using label_prop_inv
          by (simp_all add: all_edges_def all_vertices_def min_label_def neighbors_def labels_inv_def labels_stable_def)

        subgoal premises aux
          apply safe
          using label_prop_inv(2)
          by (simp add: all_edges_def all_vertices_def min_label_def neighbors_def labels_inv_def labels_stable_def)

        subgoal premises aux
          using label_prop_inv(3)
          by auto
        subgoal premises aux
          using label_prop_inv(4)
          by (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1))
        subgoal premises aux
          using label_prop_inv(5)
          unfolding label_prop_upd_inv_def 
          by (auto del: disjCI simp add: )
        subgoal premises aux
          using label_prop_inv(6) 
          unfolding input_ocaps_inv_def
          by auto
        done
      done
  qed
next
  case SIM2
  note subgraph_inv = SIM2(1,2)
    and os_inv = SIM2(3-11)
    and buffers_inv = SIM2(12)
    and dataplane_inv = SIM2(13)
    and csets_inv = SIM2(14,15)
    and input_stream_inv = SIM2(16)
    and label_prop_inv = SIM2(17-)
  have D: \<open>dataflow_topology (summ sg) (-+-)\<close> 
    unfolding subgraph_inv comp_def
    apply (subst dataflow_tree_to_graph_raw_summary[symmetric])
    using dataflow_topology_from_tree.dataflow_topology_axioms[unfolded comp_def]
    apply auto
    done
  also have G: "graph_summar_nt (summ sg) (subgraph.nxt sg) os"
    apply -
    apply (rule graph_summar_nt[simplified, OF _ subgraph_inv(1)])
      apply (rule sym)
      apply (rule dataflow_tree_to_graph_raw_summary)
    using os_inv(7) apply assumption
    using subgraph_inv(2) apply assumption
    done
  show ?case (is \<open>wsim ((~) OO \<U> ?R OO (\<approx>)) _ _\<close>)
  proof -
    define R where "R = ?R"
    show ?thesis 
      apply -
      unfolding R_def[symmetric]
      unfolding wsim_def
      apply simp
      apply (intro allI impI)
      apply (repeat_new \<open>erule conjE step_set_spec_op_elim; simp?; hypsubst_thin?\<close>;
          clarsimp split: if_splits option.splits dest!: num2_neq simp flip: ooo_input_op_def label_propagation_op_def increment_op_def; hypsubst_thin?)
      subgoal for nid p WCC t
        apply (clarsimp simp flip: cin.rep_eq simp add: image_iff buffers_inv csets_inv(1,2))
        apply (subst (asm) disj_assoc[symmetric])
        apply (erule disjE)
        subgoal
          apply (intro exI conjI)
           apply (rule wstep_trans(1))
            apply (rule relpowp_imp_rtranclp[
                where n="length (outpu (os 1) 0)"]) 
            apply (rule step_set_op_steps_Out_intro[where xs="outpu (os 1) 0"  and p="(1, 0)"])
              apply (rule steps_Tau_dataflow_op_steps_Out_intro[where xs="outpu (os 1) 0" and nid = 1 and p = 0])
               apply (subst dataflow_tree_to_operator_def)
               apply simp
               apply (rule steps_map_op[where xs="map _ (outpu (os 1) 0)", rotated 2])
                 apply (rule steps_comp_op_R_Out[where xs="map _ (outpu (os 1) 0)" and p="Inr (1, 0)"])
                    apply (rule steps_Out_loop_op_intro[where xs="map _ (outpu (os 1) 0)" and p="Inr (1, 0)"])
                       apply (rule steps_map_op[where xs="map _ (outpu (os 1) 0)" , rotated 2])
                         apply (rule steps_comp_op_L_Out[where xs="map _ (outpu (os 1) 0)"])
                             apply (rule steps_map_op[where xs="map _ (outpu (os 1) 0)", rotated 2])
                              apply (rule steps_label_propagation_op_Write_Some[where ys=Nil])
                              apply simp
                              apply (rule refl)+
                              apply (simp add: os_inv(4) operator_state.defs)
                              apply (rule refl)+
                             apply force
                            apply fastforce
                           apply (rule refl)+
                         apply fastforce
                        apply (rule refl)+
                       apply fastforce
                      apply fastforce
                     apply (rule refl)+
                 apply fastforce
                apply (rule refl)+
               apply fastforce
              apply (rule refl)+
           apply (rule step_set_op_intro_Out)
              apply (rule refl)+
             apply force
            apply simp
           apply (rule refl)+
          apply (intro relcomppI)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_sym)
          apply (rule wb_upto_b_base)
          apply (unfold R_def[simplified])
          apply (rule exI[of _ "cUn (Pair (1, 0) |`| cset_from_list (outpu (os 1) 0)) S"])
          apply (rule exI[of _ "cinsert ((nid, p), WCC, t) D"])
          apply (rule exI[of _ lxs])
          apply (rule exI[of _ "os(1 := (os 1)\<lparr>outpu := (outpu os_label_prop)(0 := [])\<rparr>)"])
          apply (rule exI[of _ "os_label_prop\<lparr>outpu := (outpu os_label_prop)(0 := [])\<rparr>"])
          apply (rule exI[of _ cbufs])
          apply (rule exI[of _ sg])
          apply (intro conjI)
          subgoal
            by (simp add: label_propagation_op_def operator_state.defs dataflow_tree_to_operator_def os_inv(1))
          subgoal premises
            apply (rule arg_cong2[where f=set_spec_op])
             apply simp_all
            apply (subst cUn_commute)
            apply (rule arg_cong2[where f=cUn])
             apply simp
            apply (rule cimage_cong)
            subgoal
              by (simp  del: filter.simps add: subgraph_inv outputs_at_target_raw_summary csets_inv(2) label_prop_edge_batch_def label_prop_edge_record_update_def buffers_inv operator_state.defs os_inv(4) csets_inv(1))
            subgoal
              by (simp  del: filter.simps add: subgraph_inv all_edges_def all_vertices_def csets_inv(2) outputs_at_target_raw_summary label_prop_edge_batch_def label_prop_edge_record_update_def buffers_inv operator_state.defs os_inv(4) csets_inv(1))
            done
          subgoal
            using subgraph_inv(1) by assumption
          subgoal
            using subgraph_inv(2) by assumption
          subgoal
            using os_inv by simp
          subgoal
            using os_inv by simp
          subgoal
            apply (rule exI[of _ T])
            apply (rule exI[of _ G])
            apply (rule exI[of _ V])
            apply (rule exI[of _ L])
            apply (simp add: os_inv(4) operator_state.defs os_inv(1))
            done
          subgoal
            using os_inv(5)
            by (simp add:  os_inv(4) operator_state.defs os_inv(1))
          subgoal
            using os_inv(6) 
            by (simp add: label_prob_ty2_check_def os_inv(4) operator_state.defs os_inv(1))
          subgoal
            using os_inv(7) 
            by simp
          using os_inv(8) apply simp
          using os_inv(9) apply simp
          subgoal
            apply (rule dataplane_tracker_inv_update_outputs_outside[OF dataplane_inv, where nid=1 and p=0 and xs=Nil])
            subgoal
              apply (clarsimp simp add: os_inv(4) operator_state.defs os_inv(1))
              apply (metis (no_types, lifting) array_rules(3,4))
              done
            subgoal
              by (simp add: subgraph_inv raw_summary_def)
            subgoal
              using G by assumption
            done
          subgoal
            by (simp add: input_stream_inv)
          subgoal
            using label_prop_inv(1)
            by auto
          subgoal
            using label_prop_inv(2)
            by simp
          subgoal
            using label_prop_inv(3)
            by simp
          subgoal
            using label_prop_inv(4)
            by (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1))
          subgoal
            using label_prop_inv(5)
            by simp
          subgoal
            using label_prop_inv(6) unfolding input_ocaps_inv_def
            by simp
          done
        subgoal premises prems
          using timely_input_stream_advances_frontier[OF input_stream_inv, of t] apply -
          apply clarsimp
          subgoal premises stream_move for n
            using dataplane_inv[unfolded dataplane_tracker_inv_def, simplified] apply -
            apply clarsimp
            subgoal premises dt_inv for cap
              using propagate_all_frontier_change_multiplicities_c_imp_correctnessE[OF D, of "pt_tr sg" "extract_progress 0 (graph_to_nxt (antichain_from_list \<circ>\<circ> raw_summary)) (snd (obtain_progress os_input))", unfolded subgraph_inv(1), simplified]
              apply -
              apply (drule meta_mp)
              subgoal
                using dt_inv(8)[unfolded propagation_inv_def subgraph_inv(1)] by auto
              apply (drule meta_mp)
              subgoal
                using dt_inv(8)[unfolded propagation_inv_def subgraph_inv(1)] by auto
              apply (drule meta_mp)
              subgoal
                using dt_inv(8)[unfolded propagation_inv_def subgraph_inv(1)] by auto
              apply (drule meta_mp)
              subgoal 
                unfolding extract_progress_def
                apply (clarsimp simp add: obtain_progress_def subgraph_inv(1,2) set_map_filter split_beta operator_state.defs os_inv(1) image_iff split: option.splits)
                subgoal for l t
                  using loc_3_2_cases[of l]
                  using dt_inv(7)[unfolded change_deltas_inv_def]
                  by (fastforce del: disjCI split: option.splits)
                done
              apply (drule meta_mp)
              subgoal 
                apply clarsimp
                subgoal for l t m
                  apply (subst frontier_less_equal_iff2[symmetric])
                  apply (rule frontier_less_equal_le_trans[rotated])
                   apply (rule dt_inv(5)[unfolded imp_front_inv_def, rule_format, of l])
                  apply (rule dt_inv(9)[unfolded extract_prog_changes_above_impl_inv_def changes_above_impl_inv_def, simplified, rule_format, where xs=Nil and x="(l, t, m)" and nid=0, simplified])
                  apply (clarsimp simp add: obtain_progress_def subgraph_inv(1,2) set_map_filter split_beta operator_state.defs os_inv(1) image_iff split: option.splits)
                  done
                done
              apply (drule meta_mp)
              subgoal
                using raw_summary_no_self_loop by auto
              apply clarsimp
              subgoal premises first_propa for c'

                apply (intro exI conjI[rotated])
                 apply (intro relcomppI)
                   apply (rule bisim_refl)
                  defer
                  apply (rule wbisim_refl)
                 apply (rule wstep_trans(1))
                  apply (rule transitive_closurep_trans'(2))


                   apply (rule converse_rtranclp_into_rtranclp) 
                    apply (rule step_set_op_intro_Tau_2)
                      apply simp
                     apply (rule step_Tau_dataflow_op_Out_Inl_intro[where nid=0])
                      apply (subst dataflow_tree_to_operator_def)
                      apply simp
                      apply (rule step_map_op)
                       apply (rule step_comp_op_L_Out)
                          apply (rule step_map_op)
                           apply (rule step_ooo_input_op_Write_None_alt)
                            apply (rule refl)+
                          apply simp
                         apply fastforce
                        apply (rule refl)+
                      apply simp
                     apply (rule refl)+

                   apply (rule converse_rtranclp_into_rtranclp) 
                    apply (rule step_set_op_intro_Tau_2)
                      apply simp
                     apply (rule step_Tau_dataflow_op_Inp_Inl_intro)
                        apply (rule step_map_op)
                         apply (rule step_comp_op_R_Inp)
                            apply (rule step_Inp_loop_op)
                             apply (rule step_map_op)
                              apply (rule step_comp_op_L_Inp)
                                apply (rule step_map_op)
                                 apply (rule step_label_propagation_op_Read_None)
                                  apply (rule refl)+
                                apply simp
                               apply (rule refl)+
                             apply simp
                            apply (auto simp add: ran_def split: sum.splits option.splits prod.splits)[1]
                           apply (auto simp add: ran_def split: sum.splits option.splits prod.splits)[1]
                          apply (rule refl)+
                        apply simp
                       apply (simp add:   subgraph_inv)
                using first_propa(1) apply assumption
                      apply (rule refl)+

                   apply (rule transitive_closurep_trans'(2))
                    apply (rule relpowp_imp_rtranclp[where n="n"]) 
                    apply (rule step_n_Taus_set_op)
                     apply (rule step_tau_pow_dataflow_op)
                     apply simp
                     apply (rule step_tau_pow_map_op)
                     apply (rule step_taus_L_pow_comp_op_steps_intro)
                      apply (rule step_tau_pow_map_op)
                      apply (rule step_compower_ooo_input_op_iterates_n[where p=0])
                subgoal
                  using input_stream_inv 
                  by (simp add: os_inv(1) obtain_progress_def operator_state.defs)
                subgoal
                  by simp
                subgoal
                  using os_inv(3)
                  by (simp add: os_inv(1) obtain_progress_def operator_state.defs)
                subgoal
                  using stream_move
                  by (simp add: os_inv(1) obtain_progress_def operator_state.defs)
                       apply (rule refl)+

                   apply (rule transitive_closurep_trans'(2))
                    apply (rule relpowp_imp_rtranclp[where n="(length (outpu (os 0) 0)) + length (filter is_Data (ltaken n lxs))"]) 
                    apply (rule step_n_Taus_set_op)
                     apply (rule step_tau_pow_dataflow_op)
                     apply (rule step_tau_pow_map_op)
                     apply (rule step_tau_Out_pow_comp_op_steps_intro[where xs="map (\<lambda> (t, d). Inr (t, d)) (outpu (os 0) 0) @ map (\<lambda> ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n lxs))" and p="Inr (0, 0)"])
                        apply (rule steps_map_op[where xs="map (\<lambda> x. Out (Some 0) (Inr x)) (outpu (os 0) 0) @ map (\<lambda> e. case e of Data t d \<Rightarrow> Out (Some 0) (Inr (Inl d, t))) (filter is_Data (ltaken n lxs))"])
                          apply (rule refl)+
                         apply simp
                subgoal
                  by (auto simp add: comp_def split: IO.splits event.splits)
                        apply (rule steps_ooo_input_op_Write_Some[where ys="Nil" and xs="outpu (os 0) 0 @ map (\<lambda> ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs))" and p=0])
                           apply simp
                          apply (simp add: obtain_progress_def operator_state.defs os_inv(1))
                         apply (rule refl)+
                        apply simp
                subgoal
                  by (auto simp add: comp_def split: IO.splits event.splits)
                       apply simp
                      apply fastforce
                     apply (rule refl)+

                   apply (rule transitive_closurep_trans'(2))
                    apply (rule relpowp_imp_rtranclp[where n="(length (cbufs (1, 0)) + length (outpu (os 0) 0) + length (filter is_Data (ltaken n lxs)))"]) 
                    apply (rule step_n_Taus_set_op)
                     apply (rule step_tau_pow_dataflow_op)
                     apply simp
                     apply (rule step_tau_pow_map_op)
                     apply (rule step_tau_Inp_pow_comp_op_steps_intro
                    [where n="(length (cbufs (1, 0)) + length (outpu (os 0) 0) + length (filter is_Data (ltaken n lxs)))" and p="Inr (1, 0)" and xs="map Inr (cbufs (1, 0)) @ map Inr (outpu (os 0) 0) @ map (\<lambda> ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n lxs))"])
                          apply (rule steps_Inp_loop_op_intro[where p="Inr (1, 0)" and xs="map Inr (cbufs (1, 0)) @ map Inr (outpu (os 0) 0) @ map (\<lambda> ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n lxs))"])
                             apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Inl (Inr (1, 0))) (_ x)) (cbufs (1, 0)) @ map (\<lambda> x. Inp (Inl (Inr (1, 0))) (_ x)) (outpu (os 0) 0)  @ map (\<lambda> x. Inp (Inl (Inr (1, 0))) (_ x)) (filter is_Data (ltaken n lxs))"])
                               apply (rule refl)+
                              apply fastforce
                             apply (rule steps_comp_op_L_Inp[where xs="map Inr (cbufs (1, 0)) @ map Inr (outpu (os 0) 0) @ map (\<lambda> ev. case ev of Data t d \<Rightarrow> Inr (Inl d, t)) (filter is_Data (ltaken n lxs))"and p="Inr (1, 0)"])
                                apply (rule steps_map_op[where xs="map (\<lambda> x. Inp (Some 0) (Inr x)) (cbufs (1, 0)) @ map (\<lambda> x. Inp (Some 0) (Inr x)) (outpu (os 0) 0) @ map (\<lambda> x. Inp (Some 0) (Inr x)) (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs)))" ])
                                  apply (rule refl)+
                subgoal
                  by (auto simp add: comp_def split: IO.splits event.splits)
                                apply (rule steps_label_propagation_op_Read_Some[where p=0 and xs="cbufs (1, 0) @ outpu (os 0) 0 @ map (\<lambda> ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs))"])
                                 apply (rule refl)+
                                apply simp
                               apply (rule refl)+
                             apply simp
                subgoal
                  by (auto simp add: comp_def ran_def split: sum.splits IO.splits event.splits)                
                           apply (rule refl)+
                         apply simp
                subgoal
                  by (auto simp add: ran_def split: sum.splits)
                subgoal
                  unfolding BULK_BENQ_def
                  by simp
                subgoal
                  unfolding BULK_BENQ_def
                  by simp
                     apply (rule refl)+

                   apply (rule transitive_closurep_trans'(2))
                    apply (rule relpowp_imp_rtranclp[where n="(length (input (os 1) 0)) + length (cbufs (1, 0)) + length (outpu (os 0) 0) + length (filter is_Data (ltaken n lxs))"]) 
                    apply (rule step_n_Taus_set_op)
                     apply (rule step_tau_pow_dataflow_op)
                     apply simp
                     apply (rule step_tau_pow_map_op)
                     apply (rule step_taus_R_pow_comp_op_steps_intro)
                      apply (rule step_taus_loop_op_steps_intro)
                       apply (rule step_tau_pow_map_op)
                       apply (rule step_taus_L_pow_comp_op_steps_intro)
                        apply (rule step_tau_pow_map_op)
                        apply (rule step_compower_label_propagation_op_input0_eq_alt[where msgs="input (os 1) 0 @ cbufs (1, 0) @ outpu (os 0) 0 @ map (\<lambda>ev. case ev of Data t d \<Rightarrow> (Inl d, t)) (filter is_Data (ltaken n lxs))" and ys="[]"])
                subgoal
                  unfolding input_fold_consumes 
                  by (simp add: os_inv(4) operator_state.defs)
                          apply simp
                         apply (simp add: os_inv(3,4) operator_state.defs)
                        apply (rule refl)+

                   apply (rule transitive_closurep_trans'(2))
                    apply (rule step_Taus_set_op)
                     apply (rule step_Taus_dataflow_op_Taus_intro)
                     apply (rule step_star_map_op)
                     apply (rule step_comp_op_R_Tau_start)
                     apply (rule step_tau_pow_loop_updates_alt)
                           apply simp
                subgoal
                  using os_inv(7)[unfolded raw_summary_def, rule_format, of 2,  simplified] 
                  using num2_neq(1) by force
                using os_inv(9) apply simp
                using os_inv(8) apply simp
                subgoal
                  apply (simp only: CONSUMES_CONSUMES)
                  apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI)
                   apply (simp add: operator_state.defs os_inv(4) input_CONSUMES)
                  apply (simp add:  label_prop_inv(5) input_CONSUMES)
                  done
                subgoal
                  apply safe
                  subgoal for t
                    apply (rule labels_inv_fst_label_prop_input0_batched_inputI)
                      apply (simp add: operator_state.defs os_inv(4) input_CONSUMES)
                    subgoal for q
                      using label_prop_inv(1) by auto
                    subgoal
                      apply (simp only: CONSUMES_CONSUMES)
                      using label_prop_inv(5) apply simp
                      done
                    done
                  done
                subgoal
                  apply (simp only: CONSUMES_CONSUMES)
                  apply (clarsimp del: disjCI simp add: input_CONSUMES split_beta image_iff simp del: fold_append)
                  sorry 
                    apply (rule refl)

                   apply (rule converse_rtranclp_into_rtranclp) 
                    apply (rule step_set_op_intro_Tau_2)
                      apply simp
                     apply (rule step_Tau_dataflow_op_Out_Inl_intro[where nid=0])
                      apply (rule step_map_op)
                       apply (rule step_comp_op_L_Out)
                          apply (rule step_map_op)
                           apply (rule step_ooo_input_op_Write_None_alt)
                            apply (rule refl)+
                          apply simp
                         apply force
                        apply (rule refl)+
                      apply simp
                     apply fastforce
                    apply (rule refl)+


                   apply (rule converse_rtranclp_into_rtranclp) 
                    apply (rule step_set_op_intro_Tau_2)
                      apply simp
                     apply (rule step_Tau_dataflow_op_Out_Inl_intro[where nid=1])
                      apply (rule step_map_op)
                       apply (rule step_comp_op_R_Out)
                         apply (rule step_Out_loop_op)
                           apply (rule step_map_op)
                            apply (rule step_comp_op_L_Out)
                               apply (rule step_map_op)
                                apply (rule step_label_propagation_op_Write_None_alt)
                                 apply (rule refl)+
                               apply simp
                              apply force
                             apply (rule refl)+
                           apply simp
                          apply force
                         apply (rule refl)+
                      apply simp
                     apply simp
                    apply (rule refl)+

                   apply (rule converse_rtranclp_into_rtranclp) 
                    apply (rule step_set_op_intro_Tau_2)
                      apply simp
                     apply (rule step_Tau_dataflow_op_Out_Inl_intro[where nid=2])
                      apply (rule step_map_op)
                       apply (rule step_comp_op_R_Out)
                         apply (rule step_Out_loop_op)
                           apply (rule step_map_op)
                            apply (rule step_comp_op_R_Out)
                              apply (rule step_map_op)
                               apply (rule step_increment_op_Write_None_alt)
                                apply (rule refl)+
                              apply simp
                             apply (rule refl)+
                           apply simp
                          apply force
                         apply (rule refl)+
                      apply simp
                     apply simp
                    apply (rule refl)+
                   apply (simp add: flip: fold_append change_multiplicities_append_alt)
                sorry
              done
            done
          done
        done
      done
  qed
qed

end
