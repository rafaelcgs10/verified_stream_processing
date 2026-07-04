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
  "../Correctness/Progress"
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
    and wf_upd: \<open>wf_label_prop_updates os (set xs)\<close>
  shows \<open>label_prop_upd_inv (CONSUMES (1 :: 2) xs os)\<close>
proof -
  let ?os' = \<open>CONSUMES (1 :: 2) xs os\<close>
  have input_eq: \<open>set (input ?os' 1) = set (input os 1) \<union> set xs\<close>
    by (simp add: input_CONSUMES)
  show ?thesis
    using inv wf_upd
    unfolding label_prop_upd_inv_def wf_label_prop_updates_def
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

lemma label_prop_input1_loop_updates_cbufs_11:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>cbufs' (1, 1) = []\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_cbufs_21:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>cbufs' (2, 1) = []\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_input_label_1:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>input os_label_prop' 1 = []\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_input_label_0:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>input os_label_prop' 0 = input os_label_prop 0\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_input_os2_1:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>input (os' 2) 1 = []\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_outpu_os2_1:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>outpu (os' 2) 1 = []\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_initia_label:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>initia os_label_prop' = initia os_label_prop\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_front_label:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>front os_label_prop' = front os_label_prop\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_initia_os2:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>initia (os 2) = initia (os' 2)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_front_os2:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>front (os 2) = front (os' 2)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_intsum_os2:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>intsum (os 2) = intsum (os' 2)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_intsum_label:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>intsum os_label_prop = intsum os_label_prop'\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_en1_label:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>en1 os_label_prop = en1 os_label_prop'\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_en2_label:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>en2 os_label_prop = en2 os_label_prop'\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_de1_label:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>de1 os_label_prop = de1 os_label_prop'\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_de2_label:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>de2 os_label_prop = de2 os_label_prop'\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_en1_os2:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>en1 (os 2) = en1 (os' 2)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_en2_os2:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>en2 (os 2) = en2 (os' 2)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_de1_os2:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>de1 (os 2) = de1 (os' 2)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_de2_os2:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>de2 (os 2) = de2 (os' 2)\<close>
  using step
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
  obtains v l l' cur_t v' where
    \<open>de1 os d = (v, l)\<close>
    \<open>l' = min (min_label os (myfst t) v) l\<close>
    \<open>cur_t \<in> set (timestamps os)\<close>
    \<open>myfst t \<le> cur_t\<close>
    \<open>v' \<in> set (neighbors os cur_t v)\<close>
    \<open>x = en1 os (v', l')\<close>
    \<open>cap = Cap (MyPair cur_t (mysnd t)) 1\<close>
proof -
  obtain v l where de1_eq: \<open>de1 os d = (v, l)\<close>
    by (cases \<open>de1 os d\<close>)
  show ?thesis
    using member that[of v l \<open>min (min_label os (myfst t) v) l\<close>] de1_eq
    unfolding label_prop_input1_step_batch_def label_prop_label_batch_def
      label_prop_neighbor_batch_def Let_def
    by (auto split: if_splits)
qed


lemma label_prop_input1_step_batch_unfold:
  \<open>label_prop_input1_step_batch os d t =
    label_prop_label_batch os
      (label_prop_label_record_update (input_tl os 1) (myfst t) (fst (de1 os d))
        (min (min_label os (myfst t) (fst (de1 os d))) (snd (de1 os d))))
      (myfst t) (fst (de1 os d)) (min (min_label os (myfst t) (fst (de1 os d))) (snd (de1 os d))) t\<close>
  unfolding label_prop_input1_step_batch_def Let_def by simp

lemma label_prop_input1_step_batch_nonempty_unfoldD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_input1_step_batch os d t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
  shows \<open>label_prop_label_batch os
    (label_prop_label_record_update (input_tl os 1) (myfst t) (fst (de1 os d))
      (min (min_label os (myfst t) (fst (de1 os d))) (snd (de1 os d))))
    (myfst t) (fst (de1 os d)) (min (min_label os (myfst t) (fst (de1 os d))) (snd (de1 os d))) t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
  using assms[unfolded label_prop_input1_step_batch_unfold] by assumption

lemma label_prop_input1_step_batch_nonemptyD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_input1_step_batch os d t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
  obtains v l l' cur_t v' where
    \<open>de1 os d = (v, l)\<close>
    \<open>cur_t \<in> set (timestamps os)\<close>
    \<open>myfst t \<le> cur_t\<close>
    \<open>v' \<in> set (neighbors os cur_t v)\<close>
    \<open>l' = min (min_label os (myfst t) v) l\<close>
    \<open>l' < min_label os cur_t v\<close>
    \<open>l' < min_label
      (label_prop_label_record_update (input_tl os 1) (myfst t) v l')
      cur_t v'\<close>
proof -
  let ?v = \<open>fst (de1 os d)\<close>
  let ?l = \<open>snd (de1 os d)\<close>
  let ?l' = \<open>min (min_label os (myfst t) ?v) ?l\<close>
  let ?updated = \<open>label_prop_label_record_update (input_tl os 1) (myfst t) ?v ?l'\<close>
  have de1_eq: \<open>de1 os d = (?v, ?l)\<close>
    by simp
  have batch_nonempty:
    \<open>label_prop_label_batch os ?updated (myfst t) ?v ?l' t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
    by (rule label_prop_input1_step_batch_nonempty_unfoldD[OF assms])


  show ?thesis
  proof (rule label_prop_label_batch_nonemptyD[OF batch_nonempty])
    fix cur_t v'
    assume cur_t_in: \<open>cur_t \<in> set (timestamps os)\<close>
      and time_le: \<open>myfst t \<le> cur_t\<close>
      and v'_in: \<open>v' \<in> set (neighbors os cur_t ?v)\<close>
      and old_guard: \<open>?l' < min_label os cur_t ?v\<close>
      and updated_guard: \<open>?l' < min_label ?updated cur_t v'\<close>
    show thesis
      using that[OF de1_eq cur_t_in time_le v'_in refl old_guard updated_guard] .
  qed
qed



lemma label_prop_input1_step_batch_nonempty_strict_updateD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_input1_step_batch os d t \<noteq> []\<close>
    and ts_t: \<open>myfst t \<in> set (timestamps os)\<close>
  obtains v l l' where
    \<open>de1 os d = (v, l)\<close>
    \<open>l' = min (min_label os (myfst t) v) l\<close>
    \<open>l' < min_label os (myfst t) v\<close>
    \<open>min_label
      (label_prop_label_record_update (input_tl os 1) (myfst t) v l')
      (myfst t) v < min_label os (myfst t) v\<close>
proof -
  obtain v l l' cur_t v' where de1_eq: \<open>de1 os d = (v, l)\<close>
    and cur_t_in: \<open>cur_t \<in> set (timestamps os)\<close>
    and time_le: \<open>myfst t \<le> cur_t\<close>
    and v'_in: \<open>v' \<in> set (neighbors os cur_t v)\<close>
    and l': \<open>l' = min (min_label os (myfst t) v) l\<close>
    and strict_cur: \<open>l' < min_label os cur_t v\<close>
    using label_prop_input1_step_batch_nonemptyD[OF assms(1)] by metis
  have mono: \<open>min_label os cur_t v \<le> min_label os (myfst t) v\<close>
    using min_label_mono_time[OF ts_t time_le] .
  have strict_myfst: \<open>l' < min_label os (myfst t) v\<close>
    using strict_cur mono by linarith
  let ?updated = \<open>label_prop_label_record_update (input_tl os 1) (myfst t) v l'\<close>
  have label_eq: \<open>label ?updated = (label os)(myfst t := (label os (myfst t))(v := l'))\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  have ts_eq: \<open>timestamps ?updated = timestamps os\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  have l_in_set: \<open>l' \<in> insert (label ?updated (myfst t) v)
      ((\<lambda>t'. label ?updated t' v) ` {t' \<in> set (timestamps ?updated). t' \<le> myfst t})\<close>
    using label_eq by simp
  have min_le_l: \<open>min_label ?updated (myfst t) v \<le> l'\<close>
    using l_in_set unfolding min_label_def by (intro Min_le) auto
  have strict_update: \<open>min_label ?updated (myfst t) v < min_label os (myfst t) v\<close>
    using min_le_l strict_myfst by linarith
  show ?thesis
    using that[OF de1_eq l' strict_myfst strict_update] .
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

lemma filter_label_prop_input1_step_batch_out_neq[simp]:
  assumes \<open>p \<noteq> (1 :: 2)\<close>
  shows \<open>filter (\<lambda>(x, cap). out cap = p) (label_prop_input1_step_batch os d t) = []\<close>
  using assms
  by (auto simp add: filter_empty_conv elim!: label_prop_input1_step_batch_memberD)

lemma filter_snd_label_prop_input1_batched_out_neq[simp]:
  assumes \<open>p \<noteq> (1 :: 2)\<close>
  shows \<open>filter (\<lambda>(x, cap). out cap = p) (snd (label_prop_input1_batched os msgs)) = []\<close>
  using assms
  by (auto simp add: filter_empty_conv elim!: label_prop_input1_batched_batch_memberD label_prop_input1_step_batch_memberD)

lemma outpu_0_fst_snd_label_prop_input1_loop_updates[simp]:
  \<open>outpu (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) (0 :: 2) =
    outpu os_label_prop 0\<close>
  unfolding label_prop_input1_loop_updates_def Let_def
  by (simp add: fold_consumes)

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



lemma label_prop_input1_batched_outpu_nonempty_strict_updateD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>outpu os 1 = []\<close>
    and \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  obtains pre d t post os_pre v l l' where
    \<open>msgs = pre @ (d, t) # post\<close>
    \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    \<open>de1 os_pre d = (v, l)\<close>
    \<open>myfst t \<in> set (timestamps os)\<close>
    \<open>l' = min (min_label os_pre (myfst t) v) l\<close>
    \<open>l' < min_label os_pre (myfst t) v\<close>
    \<open>min_label
      (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l')
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
    using dt_in_input wf_upd unfolding wf_label_prop_updates_def by fast
  have ts_t_pre: \<open>myfst t \<in> set (timestamps os_pre)\<close>
    using ts_t_os os_pre_eq by simp
  obtain v l l' where de1_eq: \<open>de1 os_pre d = (v, l)\<close>
    and l': \<open>l' = min (min_label os_pre (myfst t) v) l\<close>
    and strict: \<open>l' < min_label os_pre (myfst t) v\<close>
    and update_strict:
    \<open>min_label (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l')
        (myfst t) v < min_label os_pre (myfst t) v\<close>
    using step_batch_nonempty ts_t_pre
    by (elim label_prop_input1_step_batch_nonempty_strict_updateD)
  show ?thesis
    using that[OF msgs_eq os_pre_eq de1_eq ts_t_os l' strict update_strict] .
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
  let ?batch = \<open>label_prop_label_batch os ?os'' ?t1 ?v ?new t\<close>
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
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>labels_inv (all_edges (label_prop_input1_step_state os d t) q)
    (min_label (label_prop_input1_step_state os d t) q)\<close>
proof -
  obtain v l where de1_eq: \<open>de1 os d = (v, l)\<close>
    by (cases \<open>de1 os d\<close>)
  let ?t1 = \<open>myfst t\<close>
  let ?l' = \<open>min (min_label os ?t1 v) l\<close>
  let ?os'' = \<open>label_prop_label_record_update (input_tl os 1) ?t1 v ?l'\<close>
  have step_eq: \<open>label_prop_input1_step_state os d t =
    release_caps (drop_caps (produces (add_caps ?os''
      (map snd (label_prop_label_batch os ?os'' ?t1 v ?l' t)))
      (label_prop_label_batch os ?os'' ?t1 v ?l' t))
      (map snd (label_prop_label_batch os ?os'' ?t1 v ?l' t))) 1\<close>
    using de1_eq unfolding label_prop_input1_step_state_def Let_def by simp
  have \<open>labels_inv (all_edges ?os'' q) (min_label ?os'' q)\<close>
    by (rule labels_inv_input1_preserved_record_update_tl[OF labels inv _ de1_eq refl refl wf_upd])
      (use input1 in simp)
  then show ?thesis
    unfolding step_eq by simp
qed

lemma label_prop_upd_inv_label_prop_input1_step_stateI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes inv: \<open>label_prop_upd_inv os\<close>
    and input1: \<open>input os 1 = (d, t) # xs\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>label_prop_upd_inv (label_prop_input1_step_state os d t)\<close>
proof -
  obtain v l where de1_eq: \<open>de1 os d = (v, l)\<close>
    by (cases \<open>de1 os d\<close>)
  let ?t1 = \<open>myfst t\<close>
  let ?l' = \<open>min (min_label os ?t1 v) l\<close>
  let ?os'' = \<open>label_prop_label_record_update (input_tl os 1) ?t1 v ?l'\<close>
  have step_eq: \<open>label_prop_input1_step_state os d t =
    release_caps (drop_caps (produces (add_caps ?os''
      (map snd (label_prop_label_batch os ?os'' ?t1 v ?l' t)))
      (label_prop_label_batch os ?os'' ?t1 v ?l' t))
      (map snd (label_prop_label_batch os ?os'' ?t1 v ?l' t))) 1\<close>
    using de1_eq unfolding label_prop_input1_step_state_def Let_def by simp
  have os''_inv: \<open>label_prop_upd_inv ?os''\<close>
    by (rule label_prop_upd_inv_input1_preserved[OF inv input1 _ de1_eq refl _ _ _ _ _ wf_upd])
      (use input1 in \<open>simp_all add: label_prop_label_record_update_def input_tl_def\<close>)

  then show ?thesis
    unfolding step_eq by simp
qed

lemma wf_label_prop_updates_label_prop_input1_step_stateI:
  assumes input1: \<open>input os 1 = (d, t) # xs\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>wf_label_prop_updates (label_prop_input1_step_state os d t)
    (set (input (label_prop_input1_step_state os d t) 1))\<close>
proof -
  let ?step = \<open>label_prop_input1_step_state os d t\<close>
  have input_step: \<open>input ?step 1 = xs\<close>
    using input1 by simp
  have subset: \<open>set xs \<subseteq> set (input os 1)\<close>
    using input1 by auto
  show ?thesis
    using wf_upd subset
    unfolding wf_label_prop_updates_def input_step by auto
qed

lemma label_prop_upd_inv_fst_label_prop_input1_batched_prefixI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes input_eq: \<open>input os 1 = msgs @ rest\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>label_prop_upd_inv (fst (label_prop_input1_batched os msgs))\<close>
  using input_eq inv wf_upd
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
    by (rule label_prop_upd_inv_label_prop_input1_step_stateI[OF Cons.prems(2) input1 Cons.prems(3)])
  have wf_step: \<open>wf_label_prop_updates ?step (set (input ?step 1))\<close>
    by (rule wf_label_prop_updates_label_prop_input1_step_stateI[OF input1 Cons.prems(3)])
  have input_step: \<open>input ?step 1 = msgs @ rest\<close>
    using input1 by simp
  have ih: \<open>label_prop_upd_inv (fst (label_prop_input1_batched ?step msgs))\<close>
    by (rule Cons.hyps[OF input_step inv_step wf_step])
  then show ?case
    using msg_eq by (cases \<open>label_prop_input1_batched ?step msgs\<close>) simp
qed

lemma labels_inv_fst_label_prop_input1_batched_prefixI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes input_eq: \<open>input os 1 = msgs @ rest\<close>
    and labels: \<open>\<And>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>labels_inv (all_edges (fst (label_prop_input1_batched os msgs)) q)
    (min_label (fst (label_prop_input1_batched os msgs)) q)\<close>
  using input_eq labels inv wf_upd
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
    by (rule labels_inv_label_prop_input1_step_stateI[OF Cons.prems(2) Cons.prems(3) input1 Cons.prems(4)])
  have inv_step: \<open>label_prop_upd_inv ?step\<close>
    by (rule label_prop_upd_inv_label_prop_input1_step_stateI[OF Cons.prems(3) input1 Cons.prems(4)])
  have wf_step: \<open>wf_label_prop_updates ?step (set (input ?step 1))\<close>
    by (rule wf_label_prop_updates_label_prop_input1_step_stateI[OF input1 Cons.prems(4)])
  have input_step: \<open>input ?step 1 = msgs @ rest\<close>
    using input1 by simp
  have ih: \<open>labels_inv (all_edges (fst (label_prop_input1_batched ?step msgs)) q)
    (min_label (fst (label_prop_input1_batched ?step msgs)) q)\<close>
    by (rule Cons.hyps[OF input_step labels_step inv_step wf_step])
  then show ?case
    using msg_eq
    by (cases \<open>label_prop_input1_batched ?step msgs\<close>) simp

qed

lemma labels_inv_fst_label_prop_input1_batched_inputI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes labels: \<open>\<And>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
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
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  obtains q v where
    \<open>q \<in> set (timestamps os)\<close>
    \<open>v \<in> edge_vertices (all_edges os q)\<close>
    \<open>min_label (fst (label_prop_input1_batched os msgs)) q v < min_label os q v\<close>
proof -
  obtain pre d t post os_pre v l l' where
    msgs_eq: \<open>msgs = pre @ (d, t) # post\<close>
    and os_pre_eq: \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    and de1_pre_eq: \<open>de1 os_pre d = (v, l)\<close>
    and l': \<open>l' = min (min_label os_pre (myfst t) v) l\<close>
    and strict_pre: \<open>l' < min_label os_pre (myfst t) v\<close>
    and update_strict:
    \<open>min_label (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l') (myfst t) v
        < min_label os_pre (myfst t) v\<close>
    apply (rule label_prop_input1_batched_outpu_nonempty_strict_updateD[OF out_empty out_nonempty, OF INV msgs_input wf_upd])
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
    using dt_in_input wf_upd unfolding wf_label_prop_updates_def by fast+
  have v_in_all: \<open>v \<in> all_vertices os (myfst t)\<close>
    using v_vertex_raw de1_os_eq by simp
  have v_in_edge: \<open>v \<in> edge_vertices (all_edges os (myfst t))\<close>
    using v_in_all edge_vertices_all_edges[OF INV] by simp

  let ?step = \<open>label_prop_input1_step_state os_pre d t\<close>
  let ?new = \<open>min (min_label os_pre (myfst t) v) l\<close>
  have new_eq_l: \<open>?new = l'\<close> by (rule sym[OF l'])
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
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
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
      [OF out_empty out_batch INV msgs_input wf_upd]
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
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
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
      [OF os'_def out_empty out_nonempty INV msgs_input labels_os labels_os' wf_upd]
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
    and labels_os: \<open>\<And>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and wf_upd: \<open>wf_label_prop_updates os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
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
  have wf_base_msgs: \<open>wf_label_prop_updates ?base (set ?msgs)\<close>
    using wf_upd[unfolded wf_label_prop_updates_un]
    unfolding wf_label_prop_updates_def by simp
  have inv_consumed: \<open>label_prop_upd_inv ?consumed\<close>
    by (rule label_prop_upd_inv_CONSUMES_port1I[OF _ wf_base_msgs])
      (use INV in simp)
  have labels_consumed: \<open>\<And>t. labels_inv (all_edges ?consumed t) (min_label ?consumed t)\<close>
    using labels_os by simp
  have wf_consumed: \<open>wf_label_prop_updates ?consumed (set (input ?consumed 1))\<close>
    using wf_upd
    unfolding wf_label_prop_updates_def by (simp add: input_CONSUMES Un_commute)
  show ?thesis
    using os_label_prop'_eq labels_inv_fst_label_prop_input1_batched_inputI
      [OF labels_consumed inv_consumed wf_consumed, of t]
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
    and wf_upd: \<open>wf_label_prop_updates os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
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
  have wf_base_msgs: \<open>wf_label_prop_updates ?base (set ?msgs)\<close>
    using wf_upd[unfolded wf_label_prop_updates_un]
    unfolding wf_label_prop_updates_def by simp
  have inv_consumed: \<open>label_prop_upd_inv ?consumed\<close>
    by (rule label_prop_upd_inv_CONSUMES_port1I[OF _ wf_base_msgs])
      (use INV in simp)
  have wf_consumed: \<open>wf_label_prop_updates ?consumed (set (input ?consumed 1))\<close>
    using wf_upd
    unfolding wf_label_prop_updates_def by (simp add: input_CONSUMES Un_commute)
  have labels_consumed: \<open>\<And>t. labels_inv (all_edges ?consumed t) (min_label ?consumed t)\<close>
    using labels_os by simp
  have labels_os': \<open>\<And>t. labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
    by (rule labels_inv_label_prop_input1_loop_updatesI[OF UPDATES INV labels_os wf_upd])
  have consumed_decrease:
    \<open>sum_list (map (\<lambda>t. labels_measure (all_edges os_label_prop' t) (min_label os_label_prop' t))
        (timestamps os_label_prop'))
      < sum_list (map (\<lambda>t. labels_measure (all_edges ?consumed t) (min_label ?consumed t))
        (timestamps ?consumed))\<close>
    using labels_measure_sum_fst_label_prop_input1_batched_decreases_if_output_nonempty
      [of os_label_prop' ?consumed \<open>input ?consumed 1\<close>]
      os_label_prop'_eq consumed_outpu out_nonempty inv_consumed msgs_input_self
      labels_consumed labels_os' wf_consumed
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

lemma filter_cap_out_map_neq[simp]:
  assumes \<open>p \<noteq> q\<close>
  shows \<open>filter (\<lambda>cap. out cap = p) (map (\<lambda>t. Cap t q) xs) = []\<close>
  using assms by (induct xs) auto

lemma filter_cap_out_map_image_neq[simp]:
  assumes \<open>p \<noteq> q\<close>
  shows \<open>filter (\<lambda>cap. out cap = p) (map (\<lambda>x. Cap (f x) q) xs) = []\<close>
  using assms by (induct xs) auto

lemma filter_snd_label_prop_label_batch_out_neq[simp]:
  assumes \<open>p \<noteq> (1 :: 2)\<close>
  shows \<open>filter (\<lambda>cap. out cap = p)
    (map snd (label_prop_label_batch old_os updated_os event_t v l t)) = []\<close>
proof -
  have aux:
    \<open>filter (\<lambda>cap. out cap = p)
      (map snd (concat (map (\<lambda>cur_t.
        if l < min_label old_os cur_t v then
          map (\<lambda>v'. (en1 old_os (v', l), Cap (MyPair cur_t (mysnd t)) 1))
            (filter (\<lambda>v'. l < min_label updated_os cur_t v') (neighbors old_os cur_t v))
        else []) ts))) = []\<close> for ts
    using assms by (induct ts) (auto simp: comp_def)

  show ?thesis
    unfolding label_prop_label_batch_def label_prop_neighbor_batch_def Let_def
    using aux by simp
qed


lemma ocaps_release_caps_empty_inputs:
  assumes empty: \<open>\<And>p' s. s \<in> set (intsum os p' p) \<Longrightarrow> input os p' = []\<close>
  shows \<open>ocaps (release_caps os p) p = []\<close>
proof -
  have justifications_empty:
    \<open>concat (map (\<lambda>(p', s). map (((+) s) \<circ> snd) (input os p'))
      (concat (map (\<lambda>p'. map (\<lambda>s. (p', s)) (intsum os p' p)) enum_class.enum))) = []\<close>
    using empty
    by (auto simp: concat_eq_Nil_conv)
  have cap_times:
    \<open>map time (filter (\<lambda>cap. out cap = p) (map (\<lambda>t. Cap t p) xs)) = xs\<close> for xs
    by (induct xs) simp_all
  show ?thesis
    unfolding release_caps_def drop_caps_def Let_def
    by (simp add: justifications_empty cap_times)
qed

lemma ocaps_1_label_prop_input1_step_state_empty:
  assumes input0_empty: \<open>input os (0 :: 2) = []\<close>
    and input1_single: \<open>input os (1 :: 2) = [(d, t)]\<close>
  shows \<open>ocaps (label_prop_input1_step_state os d t) (1 :: 2) = []\<close>
  unfolding label_prop_input1_step_state_def Let_def
  apply (rule ocaps_release_caps_empty_inputs)
  subgoal for p' s
    using input0_empty input1_single
    by (cases p' rule: num2_cases) (simp_all add: input_tl_def)
  done

lemma ocaps_1_fst_label_prop_input1_batched_empty:
  assumes input0_empty: \<open>input os (0 :: 2) = []\<close>
    and msgs_eq: \<open>msgs = input os (1 :: 2)\<close>
    and nonempty_or_empty: \<open>msgs \<noteq> [] \<or> ocaps os (1 :: 2) = []\<close>
  shows \<open>ocaps (fst (label_prop_input1_batched os msgs)) (1 :: 2) = []\<close>
  using assms
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg) simp
  define os' where \<open>os' = label_prop_input1_step_state os d t\<close>
  have input1_os: \<open>input os (1 :: 2) = (d, t) # msgs\<close>
    using Cons.prems(2) msg_eq by simp
  have input0_os': \<open>input os' (0 :: 2) = []\<close>
    using Cons.prems(1) by (simp add: os'_def)
  have msgs_os': \<open>msgs = input os' (1 :: 2)\<close>
    using input1_os by (simp add: os'_def)
  have nonempty_or_empty': \<open>msgs \<noteq> [] \<or> ocaps os' (1 :: 2) = []\<close>
  proof (cases \<open>msgs = []\<close>)
    case True
    then have \<open>ocaps os' (1 :: 2) = []\<close>
      using ocaps_1_label_prop_input1_step_state_empty[OF Cons.prems(1), of d t]
        input1_os
      by (simp add: os'_def)
    then show ?thesis by simp
  next
    case False
    then show ?thesis by simp
  qed
  have rec: \<open>ocaps (fst (label_prop_input1_batched os' msgs)) (1 :: 2) = []\<close>
    by (rule Cons.hyps[OF input0_os' msgs_os' nonempty_or_empty'])
  show ?case
    using msg_eq rec
    by (cases \<open>label_prop_input1_batched os' msgs\<close>) (simp add: os'_def)
qed

lemma ocaps_1_fst_snd_label_prop_input1_loop_updates_empty:
  assumes input0_empty: \<open>input os_label_prop (0 :: 2) = []\<close>
    and no_stale:
    \<open>input os_label_prop (1 :: 2) @
        cbufs (1, 1) @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1) = [] \<Longrightarrow>
        ocaps os_label_prop (1 :: 2) = []\<close>
  shows \<open>ocaps (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) (1 :: 2) = []\<close>
proof -
  let ?incoming = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?consumed = \<open>CONSUMES 1 ?incoming
    (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  have input0_consumed: \<open>input ?consumed (0 :: 2) = []\<close>
    using input0_empty by (simp add: input_CONSUMES)
  have nonempty_or_empty: \<open>input ?consumed (1 :: 2) \<noteq> [] \<or> ocaps ?consumed (1 :: 2) = []\<close>
  proof (cases \<open>input ?consumed (1 :: 2) = []\<close>)
    case False
    then show ?thesis by simp
  next
    case True
    have stale: \<open>ocaps os_label_prop (1 :: 2) = []\<close>
      using True no_stale by (simp add: input_CONSUMES fold_consumes)
    show ?thesis
      using True stale by (simp add: input_CONSUMES fold_consumes)
  qed
  have batch:
    \<open>ocaps (fst (label_prop_input1_batched ?consumed (input ?consumed (1 :: 2)))) (1 :: 2) = []\<close>
    by (rule ocaps_1_fst_label_prop_input1_batched_empty
        [OF input0_consumed refl nonempty_or_empty])
  show ?thesis
    using batch
    unfolding label_prop_input1_loop_updates_def Let_def
    by simp
qed






lemma ocaps_0_label_prop_input1_step_state[simp]:
  \<open>ocaps (label_prop_input1_step_state os d t) (0 :: 2) = ocaps os 0\<close>
  unfolding label_prop_input1_step_state_def release_caps_def drop_caps_def add_caps_def
    produces_def input_tl_def
  by (simp add: Let_def)




lemma ocaps_0_fst_label_prop_input1_batched[simp]:
  \<open>ocaps (fst (label_prop_input1_batched os msgs)) (0 :: 2) = ocaps os 0\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta split: prod.splits)

lemma intsum_fst_snd_label_prop_input1_loop_updates[simp]:
  \<open>intsum (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) =
    intsum os_label_prop\<close>
  unfolding label_prop_input1_loop_updates_def Let_def
  by clarsimp

lemma ocaps_0_fst_snd_label_prop_input1_loop_updates[simp]:
  assumes H: \<open>intsum os_label_prop (1 :: 2) (0 :: 2) = []\<close>
  shows \<open>ocaps (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) 0 =
    ocaps os_label_prop 0\<close>
  using H
  unfolding label_prop_input1_loop_updates_def Let_def
  by (clarsimp simp add: fold_consumes)

lemma ocaps_1_snd_snd_label_prop_input1_loop_updates_empty:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes H: \<open>intsum (os (2 :: 3)) (1 :: 2) (1 :: 2) = [MyPair 0 (Suc 0)]\<close>
  shows \<open>ocaps ((snd (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) 2) (1 :: 2) = []\<close>
proof -
  have cap_times:
    \<open>map time (filter (\<lambda>cap. out cap = (1 :: 2)) (map (\<lambda>t. Cap t (1 :: 2)) xs)) = xs\<close> for xs
    by (induct xs) simp_all
  have concat_shift:
    \<open>concat (map (\<lambda>(d, t). [t -+- MyPair 0 (Suc 0)]) xs) =
      map (\<lambda>(d, t). t -+- MyPair 0 (Suc 0)) xs\<close>
    for xs :: \<open>('d \<times> (nat, nat) myprod) list\<close>
    by (induct xs) auto
  show ?thesis
    using H
    unfolding label_prop_input1_loop_updates_def Let_def
    by (simp add: drop_caps_def produces_def fold_consumes cap_times concat_shift
        flip: list_diff_append map_append filter_append)
qed




lemma timestamps_fst_snd_label_prop_input1_loop_updates[simp]:
  \<open>timestamps (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) =
    timestamps os_label_prop\<close>
  unfolding label_prop_input1_loop_updates_def Let_def
  by clarsimp


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


subsection \<open>Operational normal forms for label_prop_input1_loop_updates\<close>

lemma label_prop_input1_loop_updates_os2_state:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
  shows \<open>os' 2 =
    drop_caps
      (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2))
        (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
      (map (\<lambda>t. Cap t 1)
        (ocaps (os 2) 1 @
          map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
            (cbufs (2, 1) @ outpu os_label_prop 1)))
      \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>\<close>
  using step[symmetric]
  unfolding label_prop_input1_loop_updates_def Let_def
  by (simp split: prod.splits)

lemma label_prop_input1_loop_updates_consu_os2:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
  shows \<open>consu (os' 2) = consu (os 2) @
    map (\<lambda>(d, t). ((1 :: 2), t, (1 :: int))) (cbufs (2, 1) @ outpu os_label_prop 1)\<close>
proof -
  have os2_eq: \<open>os' 2 =
    drop_caps
      (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2))
        (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
      (map (\<lambda>t. Cap t 1)
        (ocaps (os 2) 1 @
          map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
            (cbufs (2, 1) @ outpu os_label_prop 1)))
      \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>\<close>
    by (rule label_prop_input1_loop_updates_os2_state[OF step])
  show ?thesis
    unfolding os2_eq
    by (simp add: produces_def drop_caps_def fold_consumes split_beta)
qed

lemma label_prop_input1_loop_updates_produ_os2:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
  shows \<open>produ (os' 2) = produ (os 2) @
    map (\<lambda>(d, t). ((1 :: 2), t -+- MyPair 0 (Suc 0), (1 :: int)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
proof -
  have os2_eq: \<open>os' 2 =
    drop_caps
      (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2))
        (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
      (map (\<lambda>t. Cap t 1)
        (ocaps (os 2) 1 @
          map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
            (cbufs (2, 1) @ outpu os_label_prop 1)))
      \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>\<close>
    by (rule label_prop_input1_loop_updates_os2_state[OF step])
  show ?thesis
    unfolding os2_eq
    by (simp add: produces_def drop_caps_def fold_consumes split_beta)
qed

lemma label_prop_input1_loop_updates_inter_os2:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
  shows \<open>inter (os' 2) = inter (os 2) @
    concat (map (\<lambda>(d, t). concat (map (\<lambda>p'. map (\<lambda>t'. ((p' :: 2), t + t', (1 :: int)))
      (intsum (os 2) 1 p')) enum_class.enum))
      (cbufs (2, 1) @ outpu os_label_prop 1)) @
    map (\<lambda>t. ((1 :: 2), t, -(1 :: int))) (ocaps (os 2) 1) @
    map (\<lambda>(d, t). ((1 :: 2), t -+- MyPair 0 (Suc 0), -(1 :: int)))
      (cbufs (2, 1) @ outpu os_label_prop 1)\<close>
proof -
  have os2_eq: \<open>os' 2 =
    drop_caps
      (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2))
        (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
      (map (\<lambda>t. Cap t 1)
        (ocaps (os 2) 1 @
          map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
            (cbufs (2, 1) @ outpu os_label_prop 1)))
      \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>\<close>
    by (rule label_prop_input1_loop_updates_os2_state[OF step])
  show ?thesis
    unfolding os2_eq
    by (simp add: produces_def drop_caps_def fold_consumes split_beta)
qed

lemma label_prop_input1_loop_updates_label_batched:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os_label_prop_consumed :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
    and consumed_def: \<open>os_label_prop_consumed =
      CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  shows \<open>os_label_prop' =
    fst (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))\<close>
  using step[symmetric] consumed_def
  unfolding label_prop_input1_loop_updates_def Let_def
  by (auto split: prod.splits)

lemma label_prop_input1_loop_updates_outpu_label_1_batched:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os_label_prop_consumed :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
    and consumed_def: \<open>os_label_prop_consumed =
      CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  shows \<open>outpu os_label_prop' 1 =
    map (\<lambda>(x, cap). (x, capability.time cap))
      (filter (\<lambda>(x, cap). out cap = (1 :: 2))
        (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))))\<close>
proof -
  have batched: \<open>os_label_prop' =
    fst (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))\<close>
    by (rule label_prop_input1_loop_updates_label_batched[OF step consumed_def])
  have consumed_out_empty: \<open>outpu os_label_prop_consumed 1 = []\<close>
    using consumed_def by (simp add: fold_consumes)
  show ?thesis
    using batched consumed_out_empty
    by (simp add: outpu_fst_label_prop_input1_batched_eq)
qed

lemma label_prop_input1_loop_updates_produ_label:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os_label_prop_consumed :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
    and consumed_def: \<open>os_label_prop_consumed =
      CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  shows \<open>produ os_label_prop' = produ os_label_prop @
    map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
      (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1)))\<close>
proof -
  have \<open>produ (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) = produ os_label_prop @
    map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
      (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1)))\<close>
    using consumed_def
    by (rule produ_fst_snd_label_prop_input1_loop_updates
        [where os_label_prop_consumed = os_label_prop_consumed
          and cbufs = cbufs
          and os_label_prop = os_label_prop
          and os = os])
  then show ?thesis
    using step by simp
qed

lemma fst_label_prop_input1_loop_updates_update[simp]:
  \<open>fst (label_prop_input1_loop_updates cbufs os_label_prop (os(n := X))) =
    fst (label_prop_input1_loop_updates cbufs os_label_prop os)\<close>
  unfolding label_prop_input1_loop_updates_def
  by clarsimp

lemma fst_snd_label_prop_input1_loop_updates_update[simp]:
  assumes n2: \<open>n \<noteq> (2 :: 3)\<close>
  shows \<open>fst (snd (label_prop_input1_loop_updates cbufs os_label_prop (os(n := X)))) =
    fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))\<close>
  using n2
  unfolding label_prop_input1_loop_updates_def
  by clarsimp

lemma snd_snd_label_prop_input1_loop_updates_unchanged[simp]:
  assumes n2: \<open>n \<noteq> (2 :: 3)\<close>
  shows \<open>snd (snd (label_prop_input1_loop_updates cbufs os_label_prop os)) n = os n\<close>
  using n2
  unfolding label_prop_input1_loop_updates_def
  by clarsimp



lemma snd_snd_label_prop_input1_loop_updates_update[simp]:
  assumes nm: \<open>n \<noteq> m\<close>
  shows \<open>snd (snd (label_prop_input1_loop_updates cbufs os_label_prop (os(n := X)))) m =
    snd (snd (label_prop_input1_loop_updates cbufs os_label_prop os)) m\<close>
  using nm
  unfolding label_prop_input1_loop_updates_def
  by clarsimp

lemma fst_label_prop_input1_loop_updates_cbufs_cleared[simp]:
  assumes k: \<open>k = (((1 :: 3), (1 :: 2))) \<or> k = (((2 :: 3), (1 :: 2)))\<close>
  shows \<open>fst (label_prop_input1_loop_updates (cbufs(k := X)) os_label_prop os) =
    fst (label_prop_input1_loop_updates cbufs os_label_prop os)\<close>
  using k
  unfolding label_prop_input1_loop_updates_def
  by (auto simp add: fun_upd_twist)


lemma fst_snd_label_prop_input1_loop_updates_cbufs_irrelevant[simp]:
  assumes k11: \<open>k \<noteq> (((1 :: 3), (1 :: 2)))\<close>
    and k21: \<open>k \<noteq> (((2 :: 3), (1 :: 2)))\<close>
  shows \<open>fst (snd (label_prop_input1_loop_updates (cbufs(k := X)) os_label_prop os)) =
    fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))\<close>
  using k11 k21
  unfolding label_prop_input1_loop_updates_def
  by clarsimp

lemma snd_snd_label_prop_input1_loop_updates_cbufs_irrelevant[simp]:
  assumes k21: \<open>k \<noteq> (((2 :: 3), (1 :: 2)))\<close>
  shows \<open>snd (snd (label_prop_input1_loop_updates (cbufs(k := X)) os_label_prop os)) =
    snd (snd (label_prop_input1_loop_updates cbufs os_label_prop os))\<close>
  using k21
  unfolding label_prop_input1_loop_updates_def
  by clarsimp




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

lemma op_state_base_obtain_progress:
  \<open>op_state_base (fst (obtain_progress os)) = fst (obtain_progress (op_state_base os))\<close>
  unfolding op_state_base_def obtain_progress_def
  by (rule operator_state_eqI) simp_all

lemma op_state_base_front_initia_update[simp]:

  \<open>op_state_base (os\<lparr>front := F, initia := I\<rparr>) = (op_state_base os)\<lparr>front := F, initia := I\<rparr>\<close>
  unfolding op_state_base_def
  by (rule operator_state_eqI) simp_all

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

subsection \<open>Dataplane preservation for input-0 batches\<close>

lemma label_prop_input0_step_batch_caps:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes IOC: \<open>input_ocaps_inv os\<close>
    and zero: \<open>0 \<in> set (intsum os (0 :: 2) (1 :: 2))\<close>
    and input: \<open>(d, t) \<in> set (input os (0 :: 2))\<close>
    and member: \<open>(x, cap) \<in> set (label_prop_input0_step_batch os d t)\<close>
  shows \<open>\<exists>t'\<in>set (ocaps os (out cap)). t' \<le> capability.time cap\<close>
  using member input IOC zero
  unfolding label_prop_input0_step_batch_def label_prop_edge_batch_def
    label_prop_neighbor_batch_def input_ocaps_inv_def
  apply (auto simp add: zero_myprod_def less_eq_myprod_def split: if_splits)
  subgoal
    apply (rule bexI[where x=t])
     apply (cases t; simp add: less_eq_myprod_def)
    apply force
    done
  subgoal
    apply (rule bexI[where x=t])
     apply (cases t; simp add: less_eq_myprod_def)
    apply force
    done
  subgoal
    apply (rule bexI[where x=t])
     apply (cases t; simp add: less_eq_myprod_def)
    apply force
    done
  subgoal
    apply (rule bexI[where x=t])
     apply (cases t; simp add: less_eq_myprod_def)
    apply force
    done
  done

lemma input_ocaps_inv_label_prop_input0_step_stateI:
  assumes \<open>input_ocaps_inv os\<close>
  shows \<open>input_ocaps_inv (label_prop_input0_step_state os d t)\<close>
  unfolding label_prop_input0_step_state_def Let_def
  apply (rule input_ocaps_inv_release_capsI)
  apply (rule input_ocaps_inv_drop_produces_add_capsI)
  using assms
  by (auto dest: in_set_tlD simp add: input_ocaps_inv_def input_tl_def label_prop_edge_record_update_def)





lemma dataplane_tracker_inv_label_prop_input0_step_state:
  fixes ls :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>'nid :: {enum, linorder} \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
  assumes D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and Inv: \<open>dataplane_tracker_inv (os(nid := op_state_base ls)) cbufs sg\<close>
    and G: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and IOC: \<open>input_ocaps_inv ls\<close>
    and zero: \<open>0 \<in> set (intsum ls (0 :: 2) (1 :: 2))\<close>
    and input: \<open>input ls (0 :: 2) = (d, t) # xs\<close>
  shows \<open>dataplane_tracker_inv (os(nid := op_state_base (label_prop_input0_step_state ls d t))) cbufs sg\<close>
proof -
  let ?ls1 = \<open>input_tl ls (0 :: 2)\<close>
  let ?v1 = \<open>fst (de1 ls d)\<close>
  let ?v2 = \<open>snd (de1 ls d)\<close>
  let ?t1 = \<open>myfst t\<close>
  let ?l1 = \<open>min_label ls ?t1 ?v1\<close>
  let ?l2 = \<open>min_label ls ?t1 ?v2\<close>
  let ?v = \<open>if ?l1 > ?l2 then ?v1 else ?v2\<close>
  let ?l = \<open>if ?l1 > ?l2 then ?l2 else ?l1\<close>
  let ?ls2 = \<open>label_prop_edge_record_update ?ls1 ?t1 ?v1 ?v2 ?v ?l\<close>
  let ?batch = \<open>label_prop_input0_step_batch ls d t\<close>
  have inv_base2: \<open>dataplane_tracker_inv (os(nid := op_state_base ?ls2)) cbufs sg\<close>
  proof -
    have fields: \<open>\<forall>nid'. intsum ((os(nid := op_state_base ls)) nid') = intsum ((os(nid := op_state_base ?ls2)) nid') \<and>
      ocaps ((os(nid := op_state_base ls)) nid') = ocaps ((os(nid := op_state_base ?ls2)) nid') \<and>
      consu ((os(nid := op_state_base ls)) nid') = consu ((os(nid := op_state_base ?ls2)) nid') \<and>
      inter ((os(nid := op_state_base ls)) nid') = inter ((os(nid := op_state_base ?ls2)) nid') \<and>
      produ ((os(nid := op_state_base ls)) nid') = produ ((os(nid := op_state_base ?ls2)) nid') \<and>
      outpu ((os(nid := op_state_base ls)) nid') = outpu ((os(nid := op_state_base ?ls2)) nid') \<and>
      front ((os(nid := op_state_base ls)) nid') = front ((os(nid := op_state_base ?ls2)) nid')\<close>
      by (auto simp add: op_state_base_def input_tl_def label_prop_edge_record_update_def)
    show ?thesis
      using iffD1[OF dataplane_tracker_inv_clean_input[OF fields] Inv] .
  qed
  have G_base2: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls2))\<close>
  proof -
    have geq: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls2)) =
      graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
      by (rule graph_summar_nt_intsum_cong)
        (simp add: op_state_base_def input_tl_def label_prop_edge_record_update_def)
    show ?thesis
      using geq G by simp
  qed
  have input_member: \<open>(d, t) \<in> set (input ls (0 :: 2))\<close>
    using input by simp
  have batch_caps: \<open>\<And>x cap. (x, cap) \<in> set ?batch \<Longrightarrow>
    \<exists>t'\<in>set (ocaps (op_state_base ?ls2) (out cap)). t' \<le> capability.time cap\<close>
    using label_prop_input0_step_batch_caps[OF IOC zero input_member]
    by (simp add: op_state_base_def input_tl_def label_prop_edge_record_update_def)
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
    \<open>op_state_base (label_prop_input0_step_state ls d t) =
      release_caps (drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch)) 1\<close>
    unfolding label_prop_input0_step_state_def label_prop_input0_step_batch_def Let_def
    by simp
  show ?thesis
    using inv_release by (simp add: step_base)
qed

lemma dataplane_tracker_inv_label_prop_input0_batched:
  fixes ls :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>'nid :: {enum, linorder} \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
  assumes D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and Inv: \<open>dataplane_tracker_inv (os(nid := op_state_base ls)) cbufs sg\<close>
    and G: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and IOC: \<open>input_ocaps_inv ls\<close>
    and zero: \<open>0 \<in> set (intsum ls (0 :: 2) (1 :: 2))\<close>
  shows \<open>dataplane_tracker_inv
    (os(nid := op_state_base (fst (label_prop_input0_batched ls (input ls (0 :: 2)))))) cbufs sg\<close>
proof -
  have aux:
    \<open>msgs = input ls (0 :: 2) \<Longrightarrow>
      dataplane_tracker_inv (os(nid := op_state_base ls)) cbufs sg \<Longrightarrow>
      graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls)) \<Longrightarrow>
      input_ocaps_inv ls \<Longrightarrow>
      0 \<in> set (intsum ls (0 :: 2) (1 :: 2)) \<Longrightarrow>
      dataplane_tracker_inv
        (os(nid := op_state_base (fst (label_prop_input0_batched ls (input ls (0 :: 2)))))) cbufs sg\<close>
    for msgs ls
  proof (induct msgs arbitrary: ls)
    case Nil
    then show ?case by simp
  next
    case (Cons msg msgs)
    obtain d t where msg_eq: \<open>msg = (d, t)\<close>
      by (cases msg)
    have input_eq: \<open>input ls (0 :: 2) = (d, t) # msgs\<close>
      using Cons.prems(1) msg_eq by simp
    let ?ls' = \<open>label_prop_input0_step_state ls d t\<close>
    have inv_step: \<open>dataplane_tracker_inv (os(nid := op_state_base ?ls')) cbufs sg\<close>
      by (rule dataplane_tracker_inv_label_prop_input0_step_state[OF D Cons.prems(2) Cons.prems(3) Nxt Cons.prems(4) Cons.prems(5) input_eq])
    have G_step: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls'))\<close>
    proof -
      have geq: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls')) =
        graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
        by (rule graph_summar_nt_intsum_cong) (simp add: label_prop_input0_step_state_def Let_def op_state_base_def)
      show ?thesis
        using geq Cons.prems(3) by simp
    qed
    have IOC_step: \<open>input_ocaps_inv ?ls'\<close>
      by (rule input_ocaps_inv_label_prop_input0_step_stateI[OF Cons.prems(4)])
    have zero_step: \<open>0 \<in> set (intsum ?ls' (0 :: 2) (1 :: 2))\<close>
      using Cons.prems(5) by simp
    have input_step: \<open>msgs = input ?ls' (0 :: 2)\<close>
      using input_eq by simp
    have rec: \<open>dataplane_tracker_inv
      (os(nid := op_state_base (fst (label_prop_input0_batched ?ls' (input ?ls' (0 :: 2)))))) cbufs sg\<close>
      by (rule Cons.hyps[OF input_step inv_step G_step IOC_step zero_step])
    obtain ls_final batches where rec_eq:
      \<open>label_prop_input0_batched ?ls' msgs = (ls_final, batches)\<close>
      by (cases \<open>label_prop_input0_batched ?ls' msgs\<close>)
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
  define b1 where "b1 = cbufs (1, 1)"

  define b21 where "b21 = cbufs (2, 1)"

  define out1 where "out1 = outpu os_label_prop 1"

  define in21 where "in21 = input (os 2) 1"

  define inc where "inc = MyPair (0 :: nat) (Suc 0)"
  define ts_caps2_extra where "ts_caps2_extra = map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- inc) (b21 @ out1)"

  define ts_drop where "ts_drop = ocaps (os 2) 1 @ ts_caps2_extra"

  define batch where "batch = map (\<lambda>x. (fst x, Cap (snd x -+- inc) (1 :: 2))) (in21 @ b21 @ out1)"

  define os2_consumed where "os2_consumed = CONSUMES 1 (b21 @ out1) (os 2)"

  define os2_after_prod where "os2_after_prod = produces os2_consumed batch"

  define os2_after_drop where "os2_after_drop = drop_caps os2_after_prod (map (\<lambda>t. Cap t 1) ts_drop)"

  define os2' where
    "os2' = os2_after_drop\<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>"


  have cbufs'_eq: "cbufs' = cbufs((2, 1) := [], (1, 1) := [])"
    and os'_eq: "os' = os(2 := os2')"
    using step
    unfolding label_prop_input1_loop_updates_def Let_def
      os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
      ts_drop_def ts_caps2_extra_def batch_def
      b21_def out1_def in21_def inc_def
    by (simp_all split: prod.splits)

  define os_label_prop_consumed where
    "os_label_prop_consumed = CONSUMES 1
      (b1 @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- inc)) (in21 @ b21 @ out1))
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

  have out1_eq: "out1 = outpu (os 1) 1"
    using label_prop_extension by (simp add: out1_def operator_state.defs)

  have edge12: "summ sg (Loc (1 :: 3) (Src (1 :: 2))) (Loc (2 :: 3) (Trg (1 :: 2))) \<noteq> {}\<^sub>A"
    using Summ
    by (simp add: raw_summary_def antichain_from_list_singleton)

  have edge21: "summ sg (Loc (2 :: 3) (Src (1 :: 2))) (Loc (1 :: 3) (Trg (1 :: 2))) \<noteq> {}\<^sub>A"
    using Summ
    by (simp add: raw_summary_def antichain_from_list_singleton)

  define osA where
    "osA = os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>,
               2 := os2_consumed)"

  define cbufsA where "cbufsA = cbufs((2, 1) := [])"


  have invA: "dataplane_tracker_inv osA cbufsA sg"
  proof -
    have raw: "dataplane_tracker_inv
      (os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>,
          2 := CONSUMES 1 (cbufs (2, 1) @ outpu (os 1) 1) (os 2)))
      (cbufs((2, 1) := [])) sg"
      by (rule dataplane_tracker_inv_outpu_then_fold_consumes
          [where nid_up=1 and p_up=1 and nid_dn=2 and p_dn=1,
            OF Inv D GR Nxt edge12]) simp
    show ?thesis
      using raw out1_eq
      by (simp add: osA_def cbufsA_def os2_consumed_def b21_def)
  qed

  have GA: "graph_summar_nt (summ sg) (nxt sg) osA"
  proof -
    have "graph_summar_nt (summ sg) (nxt sg) osA = graph_summar_nt (summ sg) (nxt sg) os"
      by (rule graph_summar_nt_intsum_cong)
        (simp add: osA_def os2_consumed_def fold_consumes)
    then show ?thesis
      using GR by simp
  qed

  define msgsA where "msgsA = b1 @ outpu (os 2) 1"

  define osB where
    "osB = osA(2 := (osA 2)\<lparr>outpu := (outpu (osA 2))(1 := [])\<rparr>,
                1 := CONSUMES 1 msgsA (osA 1))"

  define cbufsB where "cbufsB = cbufsA((1, 1) := [])"


  have invB: "dataplane_tracker_inv osB cbufsB sg"
  proof -
    have raw: "dataplane_tracker_inv
      (osA(2 := (osA 2)\<lparr>outpu := (outpu (osA 2))(1 := [])\<rparr>,
             1 := CONSUMES 1 (cbufsA (1, 1) @ outpu (osA 2) 1) (osA 1)))
      (cbufsA((1, 1) := [])) sg"
      by (rule dataplane_tracker_inv_outpu_then_fold_consumes
          [where nid_up=2 and p_up=1 and nid_dn=1 and p_dn=1,
            OF invA D GA Nxt edge21]) simp
    show ?thesis
      using raw
      by (simp add: osB_def cbufsB_def msgsA_def b1_def
          cbufsA_def osA_def os2_consumed_def fold_consumes)
  qed

  have GB: "graph_summar_nt (summ sg) (nxt sg) osB"
  proof -
    have "graph_summar_nt (summ sg) (nxt sg) osB = graph_summar_nt (summ sg) (nxt sg) os"
      by (rule graph_summar_nt_intsum_cong)
        (simp add: osB_def osA_def os2_consumed_def fold_consumes)
    then show ?thesis
      using GR by simp
  qed

  define caps_drop where "caps_drop = map (\<lambda>t. Cap t (1 :: 2)) ts_drop"

  define produs where "produs = map (\<lambda>(x, cap). (out cap, capability.time cap, 1 :: int)) batch"

  define oputs where "oputs = (\<lambda>p. map (\<lambda>(x, cap). (x, capability.time cap)) (filter (\<lambda>(x, cap). out cap = p) batch))"



  have concat_shift:
    "concat (map (\<lambda>(d, t). [t -+- inc]) xs) = map (\<lambda>(d :: nat \<times> nat + nat set set, t). t -+- inc) xs" for xs
    by (induct xs) auto
  have osB2_ocaps1:
    "ocaps (osB 2) 1 = ocaps (os 2) 1 @ map (\<lambda>(d, t). t -+- inc) (b21 @ out1)"
    using Intsum unfolding concat_shift[symmetric]
    by (simp add: osB_def osA_def os2_consumed_def fold_consumes raw_summary_def inc_def)

  have input_caps2:
    "\<And>d t. (d, t) \<in> set in21 \<Longrightarrow> t -+- inc \<in> set (ocaps (os 2) 1)"
  proof -
    fix d t
    assume mem: "(d, t) \<in> set in21"
    have inc: "inc \<in> set (intsum (os 2) 1 1)"
      using Intsum by (simp add: inc_def raw_summary_def)
    show "t -+- inc \<in> set (ocaps (os 2) 1)"
      using IOC2 mem inc unfolding input_ocaps_inv_def in21_def by fastforce
  qed

  have shifted_caps_B:
    "\<And>d t. (d, t) \<in> set (in21 @ b21 @ out1) \<Longrightarrow> t -+- inc \<in> set (ocaps (osB 2) 1)"
    using input_caps2 osB2_ocaps1 by auto

  have prod_caps_B: "\<forall>(p, t, m) \<in> set produs. m > 0 \<and> t \<in> set (ocaps (osB 2) p)"
  proof (rule ballI)
    fix y :: "2 \<times> (nat, nat) myprod \<times> int"

    assume y: "y \<in> set produs"
    then obtain x where x_mem: "x \<in> set (in21 @ b21 @ out1)"
      and y_eq: "y = (1, snd x -+- inc, 1)"
      unfolding produs_def batch_def by auto
    obtain d t where x_eq: "x = (d, t)"
      by (cases x)
    show "case y of (p, t, m) \<Rightarrow> 0 < m \<and> t \<in> set (ocaps (osB 2) p)"
      using shifted_caps_B[of d t] x_mem x_eq y_eq by simp
  qed

  have ts_drop_subset_B: "mset ts_drop \<subseteq># mset (ocaps (osB 2) 1)"
    using osB2_ocaps1 by (simp add: split_beta ts_drop_def ts_caps2_extra_def)

  have drops_subset_B:
    "\<forall>p'. mset (map capability.time (filter (\<lambda>c. out c = p') caps_drop)) \<subseteq># mset (ocaps (osB 2) p')"
    unfolding caps_drop_def
    by (rule cap_times_filter_single_port_subset[OF ts_drop_subset_B])

  have oputs_caps_B: "\<forall>p. snd ` set (oputs p) \<subseteq> set (ocaps (osB 2) p)"
    unfolding oputs_def
    by (rule produced_oputs_caps_from_produs[OF prod_caps_B[unfolded produs_def]])

  have oputs_produs_B:
    "\<forall>p. to_zmset (map snd (oputs p)) = zmset (map snd (filter (\<lambda>x. p = fst x) produs))"
    unfolding oputs_def produs_def
    by (rule produced_oputs_produs_zmset)

  define drop_times where "drop_times = (\<lambda>p. map capability.time (filter (\<lambda>c. out c = p) caps_drop))"

  define os2C_abs where
    "os2C_abs = (osB 2)\<lparr>
    outpu := (\<lambda>p. outpu (osB 2) p @ oputs p),
    ocaps := (\<lambda>p. list_diff (ocaps (osB 2) p) (drop_times p)),
    input := (\<lambda>p. filter (\<lambda>(_, t). t \<notin> set (drop_times p)) (input (osB 2) p)),
    produ := produ (osB 2) @ produs,
    inter := operator_state.inter (osB 2) @ map (\<lambda>cap. (out cap, capability.time cap, - 1)) caps_drop\<rparr>"

  define osC_abs where "osC_abs = osB(2 := os2C_abs)"


  have invC_abs: "dataplane_tracker_inv osC_abs cbufsB sg"
    unfolding osC_abs_def os2C_abs_def drop_times_def
    by (rule dataplane_tracker_inv_produces_drops_dropcaps_shape
        [OF D refl refl refl refl refl drops_subset_B prod_caps_B oputs_caps_B oputs_produs_B GB Nxt invB])

  have GC_abs: "graph_summar_nt (summ sg) (nxt sg) osC_abs"
  proof -
    have "graph_summar_nt (summ sg) (nxt sg) osC_abs = graph_summar_nt (summ sg) (nxt sg) osB"
      by (rule graph_summar_nt_intsum_cong) (simp add: osC_abs_def os2C_abs_def)
    then show ?thesis
      using GB by simp
  qed

  define osD where
    "osD = osC_abs(2 := (osC_abs 2)\<lparr>outpu := (outpu (osC_abs 2))(1 := [])\<rparr>,
                   1 := CONSUMES 1 (cbufsB (1, 1) @ outpu (osC_abs 2) 1) (osC_abs 1))"


  have invD: "dataplane_tracker_inv osD (cbufsB((1, 1) := [])) sg"
    unfolding osD_def
    by (rule dataplane_tracker_inv_outpu_then_fold_consumes
        [where nid_up=2 and p_up=1 and nid_dn=1 and p_dn=1,
          OF invC_abs D GC_abs Nxt edge21]) simp

  have oputs1_map:
    "map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = 1)
          (map (\<lambda>x. (fst x, Cap (snd x -+- inc) 1)) xs)) =
      map (\<lambda>(d, t). (d, t -+- inc)) xs" for xs
    by (induct xs) (auto split: prod.splits)

  have oputs1_eq:
    "oputs 1 = map (\<lambda>(d, t). (d, t -+- inc)) (in21 @ b21 @ out1)"
    unfolding oputs_def batch_def
    by (simp add: oputs1_map)

  have out_label_prop: "outpu os_label_prop = outpu (os 1)"
    using label_prop_extension by (simp add: operator_state.defs)

  have base_clear:
    "op_state_base (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>) =
      (os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>"
    using base_label_prop out_label_prop by simp

  have osB1:
    "osB 1 = CONSUMES 1 msgsA ((os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>)"
    by (simp add: osB_def osA_def)

  have osC_abs_1: "osC_abs 1 = osB 1"
    by (simp add: osC_abs_def)

  have osC_abs_out2_1: "outpu (osC_abs 2) 1 = oputs 1"
    by (simp add: osC_abs_def os2C_abs_def osB_def osA_def os2_consumed_def fold_consumes)

  have osD_to_B: "osD 1 = CONSUMES 1 (oputs 1) (osB 1)"
  proof -
    have raw: "osD 1 = CONSUMES 1 (cbufsB (1, 1) @ outpu (osC_abs 2) 1) (osC_abs 1)"
      by (simp add: osD_def)
    have msgs: "cbufsB (1, 1) @ outpu (osC_abs 2) 1 = oputs 1"
      using osC_abs_out2_1 by (simp add: cbufsB_def cbufsA_def)
    show ?thesis
      apply (subst raw)
      apply (subst msgs)
      apply (subst osC_abs_1)
      apply (rule refl)
      done
  qed

  have osD_to_base:
    "osD 1 = CONSUMES 1 (msgsA @ oputs 1) ((os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>)"
    apply (subst osD_to_B)
    apply (subst osB1)
    apply (rule CONSUMES_CONSUMES)
    done

  have msgs_oputs_eq:
    "msgsA @ oputs 1 =
      b1 @ outpu (os 2) 1 @ map (\<lambda>(d, t). (d, t -+- inc)) (in21 @ b21 @ out1)"
    using oputs1_eq by (simp add: msgsA_def)

  have label_prop_consumed_base:
    "op_state_base os_label_prop_consumed =
      CONSUMES 1 (msgsA @ oputs 1) ((os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>)"
    unfolding os_label_prop_consumed_def
    apply (simp only: op_state_base_CONSUMES)
    apply (subst base_clear)
    apply (subst msgs_oputs_eq)
    apply (rule refl)
    done

  have osD_slot1: "osD 1 = op_state_base os_label_prop_consumed"
    apply (subst osD_to_base)
    apply (subst label_prop_consumed_base)
    apply (rule refl)
    done

  define osE :: "3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state"
    where "osE = osD(2 := (osD 2)\<lparr>input := (input (os 2))(1 := [])\<rparr>)"


  have invE: "dataplane_tracker_inv osE (cbufsB((1, 1) := [])) sg"
    unfolding osE_def
    by (rule dataplane_tracker_inv_input_update
        [where nid=2 and inp="(input (os 2))(1 := [])", OF invD])


  have oputs_other_map:
    "p \<noteq> 1 \<Longrightarrow>
      map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = p)
          (map (\<lambda>x. (fst x, Cap (snd x -+- inc) 1)) xs)) = []" for p :: 2 and xs
    by (induct xs) (auto split: prod.splits)

  have oputs_other: "p \<noteq> 1 \<Longrightarrow> oputs p = []" for p :: 2
    unfolding oputs_def batch_def
    by (rule oputs_other_map)

  have osB2_eq: "osB 2 = os2_consumed\<lparr>outpu := (outpu (os 2))(1 := [])\<rparr>"
    by (simp add: osB_def osA_def os2_consumed_def fold_consumes)

  have osE2_outpu: "outpu (osE 2) = outpu os2'"
  proof (rule ext)
    fix p :: 2
    show "outpu (osE 2) p = outpu os2' p"
    proof (cases "p = 1")
      case True
      then show ?thesis
        by (simp add: osE_def osD_def os2'_def drop_caps_def produces_def)
    next
      case False
      then show ?thesis
        using oputs_other[OF False]
        by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
            os2'_def drop_caps_def produces_def)
    qed
  qed

  have osE2_eq: "osE 2 = os2'"
  proof (rule operator_state_eqI)
    show "intsum (osE 2) = intsum os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          fold_consumes drop_caps_def produces_def)
    show "consu (osE 2) = consu os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          fold_consumes drop_caps_def produces_def)
    show "operator_state.inter (osE 2) = operator_state.inter os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          caps_drop_def
          fold_consumes drop_caps_def produces_def)
    show "produ (osE 2) = produ os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          produs_def
          fold_consumes drop_caps_def produces_def)
    show "input (osE 2) = input os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          fold_consumes drop_caps_def produces_def)
    show "outpu (osE 2) = outpu os2'"
      by (rule osE2_outpu)
    show "front (osE 2) = front os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          fold_consumes drop_caps_def produces_def)
    show "ocaps (osE 2) = ocaps os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          drop_times_def caps_drop_def
          fold_consumes drop_caps_def produces_def)
    show "initia (osE 2) = initia os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          fold_consumes drop_caps_def produces_def)
    show "operator_state.more (osE 2) = operator_state.more os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          fold_consumes drop_caps_def produces_def)
  qed

  have osE_eq: "osE = os(2 := os2', 1 := op_state_base os_label_prop_consumed)"
  proof (rule ext)
    fix nid'
    show "osE nid' = (os(2 := os2', 1 := op_state_base os_label_prop_consumed)) nid'"
    proof (cases "nid' = 1")
      case True
      then show ?thesis
        using osD_slot1 by (simp add: osE_def)
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
          using False
          by (simp add: osE_def osD_def osC_abs_def osB_def osA_def)
      qed
    qed
  qed

  have intsum_os2': "intsum os2' = intsum (os 2)"
    by (simp add: os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
        fold_consumes drop_caps_def produces_def)

  have intsum_consumed_base:
    "intsum (op_state_base os_label_prop_consumed) = intsum (os 1)"
  proof -
    have "intsum (op_state_base os_label_prop_consumed) =
      intsum (op_state_base (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>))"
      by (simp add: os_label_prop_consumed_def intsum_consumes_fold)
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


  have GE: "graph_summar_nt (summ sg) (nxt sg) osE"
  proof -
    have geq:
      "graph_summar_nt (summ sg) (nxt sg)
        (os(2 := os2', 1 := op_state_base os_label_prop_consumed)) =
       graph_summar_nt (summ sg) (nxt sg) os"
      by (rule graph_summar_nt_intsum_cong)
        (simp add: intsum_os2' intsum_consumed_base intsum_label_base)
    have "graph_summar_nt (summ sg) (nxt sg) osE = graph_summar_nt (summ sg) (nxt sg) os"
      apply (subst osE_eq)
      apply (rule geq)
      done
    then show ?thesis
      using GR by simp
  qed

  have IOC_consumed: "input_ocaps_inv os_label_prop_consumed"
  proof -
    have "input_ocaps_inv (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)"
      using IOC_label_prop unfolding input_ocaps_inv_def by simp
    then show ?thesis
      unfolding os_label_prop_consumed_def
      by (rule input_ocaps_inv_CONSUMES)
  qed

  have zero_consumed: "0 \<in> set (intsum os_label_prop_consumed 1 1)"
    using zero_label_prop
    by (simp add: os_label_prop_consumed_def intsum_consumes_fold)

  have upd: "osE(1 := op_state_base os_label_prop_consumed) = osE"
    apply (subst osE_eq)
    apply (subst osE_eq)
    apply simp
    done

  have invE_base:
    "dataplane_tracker_inv (osE(1 := op_state_base os_label_prop_consumed))
      (cbufsB((1, 1) := [])) sg"
    apply (subst upd)
    apply (rule invE)
    done

  have GE_base:
    "graph_summar_nt (summ sg) (nxt sg)
      (osE(1 := op_state_base os_label_prop_consumed))"
    apply (subst upd)
    apply (rule GE)
    done



  have invFinal:
    "dataplane_tracker_inv
      (osE(1 := op_state_base (fst (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1)))))
      (cbufsB((1, 1) := [])) sg"
    by (rule dataplane_tracker_inv_label_prop_input1_batched
        [OF D invE_base GE_base Nxt IOC_consumed zero_consumed])







  have os_label_prop'_eq:
    "os_label_prop' = fst (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))"
    using step
    unfolding label_prop_input1_loop_updates_def Let_def
      os_label_prop_consumed_def b1_def in21_def b21_def out1_def inc_def
    by (simp split: prod.splits)

  have os_final_eq:
    "os'(1 := op_state_base os_label_prop') =
      osE(1 := op_state_base (fst (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))))"
    apply (subst os'_eq)
    apply (subst os_label_prop'_eq)
    apply (subst osE_eq)
    apply simp
    done

  have cbufs_final_eq: "cbufs' = cbufsB((1, 1) := [])"
    using cbufs'_eq by (simp add: cbufsB_def cbufsA_def)

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
    and wf_upd: \<open>wf_label_prop_updates os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
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
  have wf_reset_buf: \<open>wf_label_prop_updates ?os_reset (set ?buf)\<close>
    using wf_upd[unfolded wf_label_prop_updates_un]
    unfolding wf_label_prop_updates_def by simp
  have inv_cons: \<open>label_prop_upd_inv ?cons\<close>
    by (rule label_prop_upd_inv_CONSUMES_port1I[OF inv_reset wf_reset_buf])
  have wf_cons: \<open>wf_label_prop_updates ?cons (set (input ?cons 1))\<close>
    using wf_upd
    unfolding wf_label_prop_updates_def by (simp add: input_CONSUMES Un_commute)
  show ?thesis
    unfolding os_label_prop'_eq
    by (rule label_prop_upd_inv_fst_label_prop_input1_batched_prefixI
        [where rest=Nil, OF _ inv_cons wf_cons])
      simp
qed

lemma labels_inv_label_prop_input1_loop_updates_allI:
  fixes os_label_prop os_label_prop' :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os os' :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs cbufs' :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>

assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  and INV: \<open>label_prop_upd_inv os_label_prop\<close>
  and wf_upd: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
shows \<open>\<forall>t. labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
proof
  fix t
  show \<open>labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
    by (rule labels_inv_label_prop_input1_loop_updatesI[
          where cbufs = cbufs and os_label_prop = os_label_prop and os = os
            and cbufs' = cbufs' and os_label_prop' = os_label_prop'
            and os' = os' and t = t])
        (use step INV wf_upd LABELS in auto)
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
    and wf_upd: \<open>wf_label_prop_updates os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  shows \<open>wf_label_prop_updates os_label_prop'
      (set (cbufs' (1, 1) @ outpu (os' 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os' 2) 1 @ cbufs' (2, 1) @ outpu os_label_prop' 1)))\<close>
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

  have wf_base_msgs: \<open>wf_label_prop_updates ?base (set ?msgs)\<close>
    using wf_upd[unfolded wf_label_prop_updates_un]
    unfolding wf_label_prop_updates_def by simp
  have inv_consumed: \<open>label_prop_upd_inv ?consumed\<close>
    by (rule label_prop_upd_inv_CONSUMES_port1I[OF _ wf_base_msgs])
      (use INV in simp)
  have wf_consumed: \<open>wf_label_prop_updates ?consumed (set (input ?consumed 1))\<close>
    using wf_upd
    unfolding wf_label_prop_updates_def by (simp add: input_CONSUMES Un_commute)

  have all_edges_final: \<open>\<And>q. all_edges os_label_prop' q = all_edges ?consumed q\<close>
    using os'_eq by simp

  let ?msgs' = \<open>cbufs' (1, 1) @ outpu (os' 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os' 2) 1 @ cbufs' (2, 1) @ outpu os_label_prop' 1)\<close>

  have per_msg: \<open>\<And>d t. (d, t) \<in> set ?msgs' \<Longrightarrow>
      myfst t \<in> set (timestamps os_label_prop') \<and>
      fst (de1 os_label_prop' d) \<in> all_vertices os_label_prop' (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow>
        snd (de1 os_label_prop' d) \<in> cc_of (all_edges os_label_prop' q) (fst (de1 os_label_prop' d)))\<close>
  proof -
    fix d t
    assume member: \<open>(d, t) \<in> set ?msgs'\<close>

    have shifted_member:
      \<open>(d, t) \<in> set (map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (outpu os_label_prop' 1))\<close>
      using member step 
      by (simp add: label_prop_input1_loop_updates_cbufs_11 label_prop_input1_loop_updates_cbufs_21 label_prop_input1_loop_updates_input_os2_1 label_prop_input1_loop_updates_outpu_os2_1)
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

    obtain v l l' cur_t v' where de1_pre: \<open>de1 os_pre d_in = (v, l)\<close>
      and l'_def: \<open>l' = min (min_label os_pre (myfst t_in) v) l\<close>
      and cur_t_ts_pre: \<open>cur_t \<in> set (timestamps os_pre)\<close>
      and event_le_cur: \<open>myfst t_in \<le> cur_t\<close>
      and neigh: \<open>v' \<in> set (neighbors os_pre cur_t v)\<close>
      and d0_eq: \<open>d0 = en1 os_pre (v', l')\<close>
      and cap_eq: \<open>cap = Cap (MyPair cur_t (mysnd t_in)) 1\<close>
      using step_member by (elim label_prop_input1_step_batch_member_payloadD)

    have inv_pre: \<open>label_prop_upd_inv os_pre\<close>
    proof -
      have \<open>label_prop_upd_inv (fst (label_prop_input1_batched ?consumed pre))\<close>
        by (rule label_prop_upd_inv_fst_label_prop_input1_batched_prefixI
            [where rest = \<open>(d_in, t_in) # post\<close>, OF _ inv_consumed wf_consumed])
          (use full_eq in simp)
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
      using wf_consumed in_full unfolding wf_label_prop_updates_def by blast
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
    have decode: \<open>de1 os_label_prop' d = (v', l')\<close>
      using d_eq d0_eq os_pre_eq os'_eq EN1 DE1 by simp
    have ts_final: \<open>myfst t \<in> set (timestamps os_label_prop')\<close>
      using cur_t_ts_pre os_pre_eq os'_eq t_fst by simp
    have vertex_final: \<open>fst (de1 os_label_prop' d) \<in> all_vertices os_label_prop' (myfst t)\<close>
      using edge_final[OF order_refl, unfolded all_edges_def] decode t_fst by auto
    have labels_inv_consumed: \<open>\<And>q. labels_inv (all_edges ?consumed q) (min_label ?consumed q)\<close>
      using LABELS by simp
    have labels_inv_pre: \<open>\<And>q. labels_inv (all_edges os_pre q) (min_label os_pre q)\<close>
      unfolding os_pre_eq
      by (rule labels_inv_fst_label_prop_input1_batched_prefixI
          [where rest = \<open>(d_in, t_in) # post\<close>, OF _ labels_inv_consumed inv_consumed wf_consumed])
        (use full_eq in simp)
    have v_in_vertices_pre: \<open>v \<in> all_vertices os_pre (myfst t_in)\<close>
      using pending_consumed de1_consumed os_pre_eq
      unfolding all_vertices_def by simp
    have v_in_edge_vertices_pre: \<open>v \<in> edge_vertices (all_edges os_pre (myfst t_in))\<close>
      using v_in_vertices_pre edge_vertices_all_edges[OF inv_pre] by simp
    have min_label_pre_cc:
      \<open>min_label os_pre (myfst t_in) v \<in> cc_of (all_edges os_pre (myfst t_in)) v\<close>
      using labels_inv_pre[of \<open>myfst t_in\<close>] v_in_edge_vertices_pre
      unfolding labels_inv_def by blast
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
      have min_label_cc_final_v:
        \<open>min_label os_pre (myfst t_in) v \<in> cc_of (all_edges os_label_prop' q) v\<close>
        using min_label_pre_cc all_edges_pre[of \<open>myfst t_in\<close>] all_edges_final[of q]
          all_edges_mono[OF event_le_q, of ?consumed] cc_of_mono
        by metis
      have l'_cc_final_v: \<open>l' \<in> cc_of (all_edges os_label_prop' q) v\<close>
        using l'_def l_cc_final_v min_label_cc_final_v by (auto simp: min_def)
      have reach: \<open>reachable (all_edges os_label_prop' q) v v'\<close>
        using edge_final[OF cur_t_le_q] unfolding reachable_def by auto
      have cc_eq: \<open>cc_of (all_edges os_label_prop' q) v = cc_of (all_edges os_label_prop' q) v'\<close>
        by (rule cc_of_eq_if_reachable[OF reach])
      show \<open>snd (de1 os_label_prop' d) \<in> cc_of (all_edges os_label_prop' q) (fst (de1 os_label_prop' d))\<close>
        using decode l'_cc_final_v cc_eq by simp
    qed

    show \<open>myfst t \<in> set (timestamps os_label_prop') \<and>
    fst (de1 os_label_prop' d) \<in> all_vertices os_label_prop' (myfst t) \<and>
    (\<forall>q. myfst t \<le> q \<longrightarrow>
      snd (de1 os_label_prop' d) \<in> cc_of (all_edges os_label_prop' q) (fst (de1 os_label_prop' d)))\<close>
      using ts_final vertex_final cc_final by blast
  qed
  show ?thesis
    unfolding wf_label_prop_updates_def
    by (intro ballI) (clarify, rule per_msg, simp)
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


section \<open>loop_updates\<close>

subsection \<open>Recursive function\<close>

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

lemma input_ocaps_inv_empty_inputsI:
  assumes \<open>\<forall>p. input os p = []\<close>
  shows \<open>input_ocaps_inv os\<close>
  using assms unfolding input_ocaps_inv_def by simp
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

lemma input_0_fst_label_prop_input0_batched_empty:
  assumes \<open>msgs = input os (0 :: 2)\<close>
  shows \<open>input (fst (label_prop_input0_batched os msgs)) (0 :: 2) = []\<close>
  using assms by simp

lemma filter_label_prop_input0_step_batch_out_neq[simp]:
  assumes \<open>p \<noteq> (1 :: 2)\<close>
  shows \<open>filter (\<lambda>(x, cap). out cap = p) (label_prop_input0_step_batch os d t) = []\<close>
  using assms
  unfolding label_prop_input0_step_batch_def label_prop_edge_batch_def
    label_prop_neighbor_batch_def
  by (auto simp add: filter_empty_conv split: if_splits)

lemma filter_snd_label_prop_input0_batched_out_neq[simp]:
  assumes \<open>p \<noteq> (1 :: 2)\<close>
  shows \<open>filter (\<lambda>(x, cap). out cap = p) (snd (label_prop_input0_batched os msgs)) = []\<close>
  using assms
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  obtain os' batches where rec_eq:
    \<open>label_prop_input0_batched (label_prop_input0_step_state os d t) msgs = (os', batches)\<close>
    by (cases \<open>label_prop_input0_batched (label_prop_input0_step_state os d t) msgs\<close>)
  have rec: \<open>filter (\<lambda>(x, cap). out cap = p) batches = []\<close>
    using Cons.hyps[OF Cons.prems, of \<open>label_prop_input0_step_state os d t\<close>] rec_eq
    by simp
  show ?case
    using Cons.prems rec unfolding msg_eq
    by (simp add: rec_eq)
qed

lemma outpu_0_fst_label_prop_input0_batched[simp]:
  \<open>outpu (fst (label_prop_input0_batched os msgs)) (0 :: 2) = outpu os 0\<close>
  by simp

lemma all_edges_eq_graph_entries:
  assumes inv: \<open>label_prop_upd_inv os\<close>
  shows \<open>all_edges os q = {e. \<exists>t\<in>set (timestamps os). t \<le> q \<and> snd e \<in> set (graph os t (fst e))}\<close>
proof (intro set_eqI iffI)
  fix e
  assume e_in: \<open>e \<in> all_edges os q\<close>
  obtain v w where e: \<open>e = (v, w)\<close>
    by (cases e)
  then obtain t where \<open>t \<in> set (timestamps os)\<close> \<open>t \<le> q\<close> \<open>w \<in> set (graph os t v)\<close>
    using e_in unfolding all_edges_def set_neighbors by auto
  then show \<open>e \<in> {e. \<exists>t\<in>set (timestamps os). t \<le> q \<and> snd e \<in> set (graph os t (fst e))}\<close>
    using e by auto
next
  fix e
  assume e_in: \<open>e \<in> {e. \<exists>t\<in>set (timestamps os). t \<le> q \<and> snd e \<in> set (graph os t (fst e))}\<close>
  then obtain t where t: \<open>t \<in> set (timestamps os)\<close> \<open>t \<le> q\<close>
    and graph_edge: \<open>snd e \<in> set (graph os t (fst e))\<close>
    by auto
  have vertices: \<open>fst e \<in> set (vertices os t)\<close> \<open>snd e \<in> set (vertices os t)\<close>
    using label_prop_upd_inv_graph_edgeD[OF inv graph_edge] by auto
  have all_vertices: \<open>fst e \<in> all_vertices os q\<close> \<open>snd e \<in> all_vertices os q\<close>
    using t vertices unfolding all_vertices_def by auto
  have neighbor: \<open>snd e \<in> set (neighbors os q (fst e))\<close>
    using t graph_edge unfolding set_neighbors by auto
  show \<open>e \<in> all_edges os q\<close>
    using all_vertices neighbor unfolding all_edges_def by (cases e) auto
qed

lemma all_edges_label_prop_input0_step_state_eq:
  assumes INV: \<open>label_prop_upd_inv os\<close>
  shows \<open>all_edges (label_prop_input0_step_state os d t) q =
    all_edges os q \<union>
      (if myfst t \<le> q then
        {(fst (de1 os d), snd (de1 os d)), (snd (de1 os d), fst (de1 os d))}
       else {})\<close>
proof -
  let ?v1 = \<open>fst (de1 os d)\<close>
  let ?v2 = \<open>snd (de1 os d)\<close>
  let ?t1 = \<open>myfst t\<close>
  let ?l1 = \<open>min_label os ?t1 ?v1\<close>
  let ?l2 = \<open>min_label os ?t1 ?v2\<close>
  let ?v = \<open>if ?l1 > ?l2 then ?v1 else ?v2\<close>
  let ?l = \<open>if ?l1 > ?l2 then ?l2 else ?l1\<close>
  let ?G = \<open>(graph os)(?t1 := (graph os ?t1)
    (?v1 := ?v2 # graph os ?t1 ?v1, ?v2 := ?v1 # graph os ?t1 ?v2))\<close>
  let ?V = \<open>(vertices os)(?t1 := [?v1, ?v2] @ vertices os ?t1)\<close>
  let ?os' = \<open>label_prop_edge_record_update (input_tl os 0) ?t1 ?v1 ?v2 ?v ?l\<close>
  have step_edges: \<open>all_edges (label_prop_input0_step_state os d t) q = all_edges ?os' q\<close>
    by simp
  have os'_fields:
    \<open>timestamps ?os' = ?t1 # timestamps os\<close>
    \<open>graph ?os' = ?G\<close>
    \<open>vertices ?os' = ?V\<close>
    by (simp_all add: label_prop_edge_record_update_def input_tl_def)
  have old_edges:
    \<open>all_edges os q = {e. \<exists>t\<in>set (timestamps os). t \<le> q \<and> snd e \<in> set (graph os t (fst e))}\<close>
    by (rule all_edges_eq_graph_entries[OF INV])
  have new_graph_edgeD:
    \<open>\<And>t' e. snd e \<in> set (?G t' (fst e)) \<Longrightarrow> fst e \<in> set (?V t') \<and> snd e \<in> set (?V t')\<close>
  proof -
    fix t' e
    assume graph_edge: \<open>snd e \<in> set (?G t' (fst e))\<close>
    obtain x y where e: \<open>e = (x, y)\<close>
      by (cases e)
    show \<open>fst e \<in> set (?V t') \<and> snd e \<in> set (?V t')\<close>
      using graph_edge label_prop_upd_inv_graph_edgeD[OF INV]
      unfolding e by (auto split: if_splits)
  qed
  have new_edges:
    \<open>all_edges ?os' q = {e. \<exists>t\<in>set (?t1 # timestamps os). t \<le> q \<and> snd e \<in> set (?G t (fst e))}\<close>
  proof (intro set_eqI iffI)
    fix e
    assume e_in: \<open>e \<in> all_edges ?os' q\<close>
    then obtain t' where t': \<open>t' \<in> set (?t1 # timestamps os)\<close> \<open>t' \<le> q\<close>
      and graph_edge: \<open>snd e \<in> set (?G t' (fst e))\<close>
      using os'_fields unfolding all_edges_def set_neighbors by (cases e) auto
    show \<open>e \<in> {e. \<exists>t\<in>set (?t1 # timestamps os). t \<le> q \<and> snd e \<in> set (?G t (fst e))}\<close>
      using t' graph_edge by blast
  next
    fix e
    assume e_in: \<open>e \<in> {e. \<exists>t\<in>set (?t1 # timestamps os). t \<le> q \<and> snd e \<in> set (?G t (fst e))}\<close>
    then obtain t' where t': \<open>t' \<in> set (?t1 # timestamps os)\<close> \<open>t' \<le> q\<close>
      and graph_edge: \<open>snd e \<in> set (?G t' (fst e))\<close>
      by blast
    have vertices: \<open>fst e \<in> set (?V t')\<close> \<open>snd e \<in> set (?V t')\<close>
      using new_graph_edgeD[OF graph_edge] by auto
    have t'_new: \<open>t' \<in> {u \<in> set (timestamps ?os'). u \<le> q}\<close>
      using t' os'_fields(1) by auto
    have vertices_new: \<open>fst e \<in> set (vertices ?os' t')\<close> \<open>snd e \<in> set (vertices ?os' t')\<close>
      using vertices os'_fields(3) by auto
    have all_vertices: \<open>fst e \<in> all_vertices ?os' q\<close> \<open>snd e \<in> all_vertices ?os' q\<close>
      using t'_new vertices_new unfolding all_vertices_def by blast+
    have graph_new: \<open>snd e \<in> set (graph ?os' t' (fst e))\<close>
      using graph_edge os'_fields(2) by auto
    have neighbor: \<open>snd e \<in> set (neighbors ?os' q (fst e))\<close>
      using t'_new graph_new unfolding set_neighbors by blast
    show \<open>e \<in> all_edges ?os' q\<close>
      using all_vertices neighbor unfolding all_edges_def by (cases e) auto
  qed
  have graph_entries:
    \<open>{e. \<exists>t\<in>set (?t1 # timestamps os). t \<le> q \<and> snd e \<in> set (?G t (fst e))} =
      {e. \<exists>t\<in>set (timestamps os). t \<le> q \<and> snd e \<in> set (graph os t (fst e))} \<union>
      (if ?t1 \<le> q then {(?v1, ?v2), (?v2, ?v1)} else {})\<close>
  proof (intro set_eqI iffI)
    fix e
    assume e_in: \<open>e \<in> {e. \<exists>t\<in>set (?t1 # timestamps os). t \<le> q \<and> snd e \<in> set (?G t (fst e))}\<close>
    then obtain t' where t': \<open>t' \<in> set (?t1 # timestamps os)\<close> \<open>t' \<le> q\<close>
      and graph_edge: \<open>snd e \<in> set (?G t' (fst e))\<close>
      by blast
    show \<open>e \<in> {e. \<exists>t\<in>set (timestamps os). t \<le> q \<and> snd e \<in> set (graph os t (fst e))} \<union>
      (if ?t1 \<le> q then {(?v1, ?v2), (?v2, ?v1)} else {})\<close>
    proof (cases \<open>t' = ?t1\<close>)
      case False
      then have \<open>t' \<in> set (timestamps os)\<close>
        using t' by auto
      moreover have \<open>snd e \<in> set (graph os t' (fst e))\<close>
        using graph_edge False by auto
      ultimately show ?thesis
        using t' by auto
    next
      case t1_eq: True
      show ?thesis
      proof (cases \<open>?t1 \<in> set (timestamps os)\<close>)
        case in_ts: True
        have old_or_new:
          \<open>snd e \<in> set (graph os ?t1 (fst e)) \<or>
            (fst e = ?v1 \<and> snd e = ?v2) \<or> (fst e = ?v2 \<and> snd e = ?v1)\<close>
          using graph_edge t1_eq by (cases e) (auto split: if_splits)
        then show ?thesis
          using t' t1_eq in_ts by (cases e) auto
      next
        case not_ts: False
        have empty: \<open>graph os ?t1 (fst e) = []\<close>
          using label_prop_upd_inv_graph_empty_if_not_timestamp[OF INV not_ts, of \<open>fst e\<close>] .
        have new_edge:
          \<open>(fst e = ?v1 \<and> snd e = ?v2) \<or> (fst e = ?v2 \<and> snd e = ?v1)\<close>
          using graph_edge t1_eq empty by (cases e) (auto split: if_splits)
        then show ?thesis
          using t' t1_eq by (cases e) auto
      qed
    qed
  next
    fix e
    assume e_in: \<open>e \<in> {e. \<exists>t\<in>set (timestamps os). t \<le> q \<and> snd e \<in> set (graph os t (fst e))} \<union>
      (if ?t1 \<le> q then {(?v1, ?v2), (?v2, ?v1)} else {})\<close>
    from e_in consider
      (old) t' where \<open>t' \<in> set (timestamps os)\<close> \<open>t' \<le> q\<close> \<open>snd e \<in> set (graph os t' (fst e))\<close>
    | (new) \<open>?t1 \<le> q\<close> \<open>e = (?v1, ?v2) \<or> e = (?v2, ?v1)\<close>
      by (cases \<open>?t1 \<le> q\<close>) auto
    then show \<open>e \<in> {e. \<exists>t\<in>set (?t1 # timestamps os). t \<le> q \<and> snd e \<in> set (?G t (fst e))}\<close>
    proof cases
      case old
      then have \<open>snd e \<in> set (?G t' (fst e))\<close>
        by (cases e) auto
      then show ?thesis
        using old by auto
    next
      case new
      then show ?thesis
        by auto
    qed
  qed
  show ?thesis
    using step_edges old_edges new_edges graph_entries by simp
qed

lemma all_edges_fst_label_prop_input0_batched_prefix_eq:
  assumes input_eq: \<open>input os 0 = msgs @ rest\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>all_edges (fst (label_prop_input0_batched os msgs)) q =
    all_edges os q \<union>
      (\<Union>(d, t)\<in>set msgs. if myfst t \<le> q then
        {(fst (de1 os d), snd (de1 os d)), (snd (de1 os d), fst (de1 os d))}
       else {})\<close>
  using input_eq inv wf_upd
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case
    by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  let ?step = \<open>label_prop_input0_step_state os d t\<close>
  have input0: \<open>input os 0 = (d, t) # (msgs @ rest)\<close>
    using Cons.prems(1) msg_eq by simp
  have input_step: \<open>input ?step 0 = msgs @ rest\<close>
    using input0 by simp
  have inv_step: \<open>label_prop_upd_inv ?step\<close>
    by (rule label_prop_upd_inv_label_prop_input0_step_stateI[OF Cons.prems(2) input0 Cons.prems(3)])
  have wf_step: \<open>wf_label_prop_updates ?step (set (input ?step 1))\<close>
    by (rule wf_label_prop_updates_label_prop_input0_step_stateI[OF Cons.prems(2) Cons.prems(3)])
  have ih:
    \<open>all_edges (fst (label_prop_input0_batched ?step msgs)) q =
      all_edges ?step q \<union>
        (\<Union>(d, t)\<in>set msgs. if myfst t \<le> q then
          {(fst (de1 ?step d), snd (de1 ?step d)), (snd (de1 ?step d), fst (de1 ?step d))}
         else {})\<close>
    by (rule Cons.hyps[OF input_step inv_step wf_step])
  have step_edges:
    \<open>all_edges ?step q = all_edges os q \<union>
      (if myfst t \<le> q then
        {(fst (de1 os d), snd (de1 os d)), (snd (de1 os d), fst (de1 os d))}
       else {})\<close>
    by (rule all_edges_label_prop_input0_step_state_eq[OF Cons.prems(2)])
  show ?case
    using ih step_edges msg_eq
    by (cases \<open>label_prop_input0_batched ?step msgs\<close>)
      (auto simp add: Un_assoc Un_left_commute Un_commute)
qed

lemma all_edges_fst_label_prop_input0_batched_input_eq:
  assumes input_eq: \<open>input os 0 = msgs\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>all_edges (fst (label_prop_input0_batched os msgs)) q =
    all_edges os q \<union>
      (\<Union>(d, t)\<in>set msgs. if myfst t \<le> q then
        {(fst (de1 os d), snd (de1 os d)), (snd (de1 os d), fst (de1 os d))}
       else {})\<close>
  by (rule all_edges_fst_label_prop_input0_batched_prefix_eq[where rest=Nil])
    (use assms in simp_all)

lemma set_icoll_llist_of:
  \<open>set (icoll (llist_of xs) t) = {d. \<exists>t'. Data t' d \<in> set xs \<and> t' \<le> t}\<close>
  apply (induction xs)
   apply (simp add: icoll_def)
  apply (auto simp: icoll_def split: event.splits)
  done

lemma set_icoll_llist_of_map_Data_pair:
  \<open>set (icoll (llist_of (map (\<lambda>(x, t'). Data t' (f x)) xs)) t) =
    (\<lambda>x. f (fst x)) ` {x \<in> set xs. snd x \<le> t}\<close>
  apply (auto simp: set_icoll_llist_of split_beta)
  done

lemma set_icoll_lshift:
  \<open>lfinite (lfilter (\<lambda>e. event.time e \<le> t) lxs) \<Longrightarrow>
    set (icoll (xs @@- lxs) t) = set (icoll (llist_of xs) t) \<union> set (icoll lxs t)\<close>
  apply (simp add: icoll_lshift)
  done

lemma icoll_empty_if_no_data_le:
  assumes \<open>\<And>t' d. t' \<le> t \<Longrightarrow> Data t' d \<notin> lset lxs\<close>
  shows \<open>icoll lxs t = []\<close>
  unfolding icoll_def
  apply (subst lfilter_False)
   apply (use assms in \<open>auto split: event.splits\<close>)
  done

lemma set_icoll_ltaken_if_no_ldropn_data_le:
  assumes finite: \<open>lfinite (lfilter (\<lambda>e. event.time e \<le> t) (ldropn n lxs))\<close>
    and no_data: \<open>\<And>t' d. t' \<le> t \<Longrightarrow> Data t' d \<notin> lset (ldropn n lxs)\<close>
  shows \<open>set (icoll lxs t) = {d. \<exists>t'. Data t' d \<in> set (ltaken n lxs) \<and> t' \<le> t}\<close>
  apply (subst (1) ltaken_lshift_ldropn[symmetric, of lxs n])
  apply (subst icoll_lshift)
  using finite apply blast
  apply (simp add: icoll_empty_if_no_data_le[OF no_data] set_icoll_llist_of)
  done

lemma timely_input_stream_ldropn_no_data_le_if_not_frontier_less_equal:
  assumes stream: \<open>timely_input_stream lxs C\<close>
    and n_le: \<open>enat n \<le> llength lxs\<close>
    and not_frontier: \<open>\<not> frontier_less_equal
      (frontier (zmset_of (C + event.time `# filter_mset is_Mint (mset (ltaken n lxs)) -
        event.time `# filter_mset is_Drop (mset (ltaken n lxs))))) t\<close>
    and u_le: \<open>u \<le> t\<close>
  shows \<open>Data u d \<notin> lset (ldropn n lxs)\<close>
  apply (rule notI)
  apply (rule vacant_monotone_not_in_lset[where e=\<open>Data u d\<close> and t=t and
        C=\<open>C + event.time `# filter_mset is_Mint (mset (ltaken n lxs)) -
          event.time `# filter_mset is_Drop (mset (ltaken n lxs))\<close> and lxs=\<open>ldropn n lxs\<close>])
     apply assumption
    apply (simp add: u_le)
   apply (rule not_frontier_less_equal_vacant[OF not_frontier])
  using timely_input_stream_ldrop[OF n_le stream]
  apply (simp add: timely_input_stream_def)
  done

lemma Field_Un_converse[simp]:
  \<open>Field (A \<union> A\<inverse>) = Field A\<close>
  apply auto
  done

lemma ccs_eq_if_undirected_Field:
  assumes \<open>A \<union> A\<inverse> = B \<union> B\<inverse>\<close>
    and \<open>Field A = Field B\<close>
  shows \<open>ccs A = ccs B\<close>
  using assms
  unfolding Wcc.is_cc_def Wcc.is_subcc_def Wcc.reachable_def Wcc.edge_vertices_def
  apply simp
  done

lemma ccs_eq_if_undirected:
  assumes \<open>A \<union> A\<inverse> = B \<union> B\<inverse>\<close>
  shows \<open>ccs A = ccs B\<close>
  apply (rule ccs_eq_if_undirected_Field)
   apply (rule assms)
  using assms
  apply (metis Field_Un_converse)
  done

lemma ccs_Un_symmetric_edge_image:
  fixes A :: \<open>('a::order \<times> 'a) set\<close>
  shows \<open>ccs (A \<union> f ` X) = ccs (A \<union> (\<Union>x\<in>X. {f x, (snd (f x), fst (f x))}))\<close>
  apply (rule ccs_eq_if_undirected)
  apply force
  done

lemma myprod_le_iff_myfst_le_if_mysnd_zero:
  fixes s t :: \<open>('a::ord, 'b::{zero, order}) myprod\<close>
  assumes \<open>mysnd s = 0\<close>
    and \<open>mysnd t = 0\<close>
  shows \<open>s \<le> t \<longleftrightarrow> myfst s \<le> myfst t\<close>
  using assms
  apply (cases s; cases t)
  apply auto
  done

lemma myfst_le_if_myprod_le_mysnd_zero:
  fixes s t :: \<open>('a::ord, 'b::{zero, order}) myprod\<close>
  assumes \<open>s \<le> t\<close>
    and \<open>mysnd s = 0\<close>
    and \<open>mysnd t = 0\<close>
  shows \<open>myfst s \<le> myfst t\<close>
  using assms
  apply (simp add: myprod_le_iff_myfst_le_if_mysnd_zero)
  done

lemma myprod_le_if_myfst_le_mysnd_zero:
  fixes s t :: \<open>('a::ord, 'b::{zero, order}) myprod\<close>
  assumes \<open>myfst s \<le> myfst t\<close>
    and \<open>mysnd s = 0\<close>
    and \<open>mysnd t = 0\<close>
  shows \<open>s \<le> t\<close>
  using assms
  apply (simp add: myprod_le_iff_myfst_le_if_mysnd_zero)
  done




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
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  shows \<open>dataplane_tracker_inv (os'(1 := op_state_base os_label_prop')) cbufs' sg\<close>
  using step D GR Nxt Inv label_prop_extension Summ Intsum IOC1 IOC2 INV LABELS WF

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
  note WF0 = "1.prems"(13)

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

  have Inv1: \<open>dataplane_tracker_inv (os1(1 := op_state_base os_label_prop1)) cbufs1 sg\<close>
    by (rule label_prop_input1_loop_updates_preserves_dataplane_tracker_inv_corrected
        [OF step1[symmetric] D0 GR0 Nxt0 Inv0 Ext0 Summ0 Intsum0 IOC10 IOC20])

  show ?case
  proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
    case True
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      apply (subst loop_updates.simps)
      using good step1 True by simp
    show ?thesis
      using loop_step loop_eq Inv1 by (simp add: fun_upd_def)
  next
    case False
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs1 os_label_prop1 os1\<close>
      apply (subst loop_updates.simps)
      using good step1 False by simp
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
      by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] INV0 WF0])
    have LABELS1: \<open>\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)\<close>
      by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] INV0 WF0 LABELS0])
    have EN10: \<open>en1 os_label_prop = Inl\<close>
      using arg_cong[OF Ext0, of en1]
      by (simp add: operator_state.defs)
    have DE10: \<open>de1 os_label_prop = projl\<close>
      using arg_cong[OF Ext0, of de1]
      by (simp add: operator_state.defs)
    have INPUT11: \<open>input os_label_prop1 1 = []\<close>
      by (rule label_prop_input1_loop_updates_input_label_1[OF step1[symmetric]])
    have WF_msgs1: \<open>wf_label_prop_updates os_label_prop1
      (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
      by (rule label_prop_input1_loop_updates_msgs_invI
          [OF step1[symmetric] EN10 DE10 INV0 LABELS0 WF0])
    have WF1: \<open>wf_label_prop_updates os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
      using INPUT11 WF_msgs1 by simp

    show ?thesis
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False
            step_rec D0 GR1 Nxt0 Inv1 Ext1 Summ0 Intsum1 IOC11 IOC21 INV1 LABELS1 WF1])

  qed
qed


subsection \<open>Progress comparison for loop_updates\<close>

lemma loop_updates_final_dataplane_tracker_inv_for_progress:
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
    and D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and GR: \<open>graph_summar_nt (summ sg) (nxt sg) (os(1 := op_state_base os_label_prop))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and Summ: \<open>summ sg = antichain_from_list \<circ>\<circ> raw_summary\<close>
    and Intsum: \<open>\<forall>n. intsum ((os(1 := op_state_base os_label_prop)) n) =
        (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    and IOC1: \<open>input_ocaps_inv os_label_prop\<close>
    and IOC2: \<open>input_ocaps_inv (os 2)\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and DATAPLANE: \<open>dataplane_tracker_inv os cbufs sg\<close>
  shows \<open>dataplane_tracker_inv
    ((snd (snd (loop_updates cbufs os_label_prop os)))
      (1 := op_state_base (fst (snd (loop_updates cbufs os_label_prop os)))))
    (fst (loop_updates cbufs os_label_prop os)) sg\<close>
proof -
  let ?res = \<open>loop_updates cbufs os_label_prop os\<close>
  have step: \<open>(fst ?res, fst (snd ?res), snd (snd ?res)) = ?res\<close>
    by (cases ?res) simp
  have base_label_prop: \<open>op_state_base os_label_prop = os 1\<close>
    using label_prop_extension
    unfolding op_state_base_def
    by (simp add: operator_state.defs)
  have base_inv: \<open>dataplane_tracker_inv (os(1 := op_state_base os_label_prop)) cbufs sg\<close>
    using DATAPLANE by (simp add: base_label_prop)
  have ext_base:
    \<open>os_label_prop = operator_state.extend (op_state_base os_label_prop)
      \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T,
        graph = G, vertices = V, label = L\<rparr>\<close>
    using label_prop_extension
    by (simp add: op_state_base_def operator_state.defs)
  show ?thesis
    by (rule loop_updates_preserves_dataplane_tracker_inv
        [OF step D GR Nxt base_inv ext_base Summ Intsum IOC1 IOC2 INV LABELS WF])

qed

lemma zmset_filter_eq_if_c_pts_change_multiplicities_eq:
  assumes \<open>c_pts (change_multiplicities su xs c) l =
    c_pts (change_multiplicities su ys c) l\<close>
  shows \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') xs)) =
    zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys))\<close>
  using assms
  by (simp add: c_pts_change_multiplicities)

lemma extract_prog_two_12:
  shows \<open>extract_progress (1 :: 3) eds (snd (obtain_progress os1)) @
    extract_progress (2 :: 3) eds (snd (obtain_progress os2)) =
    extract_prog [1 :: 3, 2] eds (\<lambda>nid. if nid = 1 then os1 else os2)\<close>
  by (simp add: extract_prog_def)

lemma produces_Nil[simp]:
  "produces os [] = os"
  unfolding produces_def
  by simp

lemma CM_equiv_empty_filter_notin:
  assumes \<open>l \<notin> fst ` set xs\<close>
  shows \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') xs)) = {#}\<^sub>z\<close>
  using assms by (induct xs) auto

lemma CM_equiv_trans:
  assumes \<open>CM_equiv xs ys\<close> and \<open>CM_equiv ys zs\<close>
  shows \<open>CM_equiv xs zs\<close>
proof -
  have step: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') xs)) =
      zmset (map snd (filter (\<lambda>(l', _, _). l = l') zs))\<close>
    if \<open>l \<in> fst ` set xs \<union> fst ` set zs\<close> for l
  proof -
    have xy: \<open>l \<in> fst ` set xs \<union> fst ` set ys \<Longrightarrow>
      zmset (map snd (filter (\<lambda>(l', _, _). l = l') xs)) =
      zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys))\<close>
      using assms(1) unfolding CM_equiv_def by blast
    have yz: \<open>l \<in> fst ` set ys \<union> fst ` set zs \<Longrightarrow>
      zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys)) =
      zmset (map snd (filter (\<lambda>(l', _, _). l = l') zs))\<close>
      using assms(2) unfolding CM_equiv_def by blast
    show ?thesis
    proof (cases \<open>l \<in> fst ` set xs\<close>)
      case True
      have xs_ys: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') xs)) =
        zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys))\<close>
        using True xy by simp
      show ?thesis
      proof (cases \<open>l \<in> fst ` set ys \<union> fst ` set zs\<close>)
        case True
        then show ?thesis
          using xs_ys yz by simp
      next
        case False
        then have ys_empty: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys)) = {#}\<^sub>z\<close>
          by (intro CM_equiv_empty_filter_notin) auto
        have zs_empty: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') zs)) = {#}\<^sub>z\<close>
          using False by (intro CM_equiv_empty_filter_notin) auto
        show ?thesis
          using xs_ys ys_empty zs_empty by simp
      qed
    next
      case False_xs: False
      have xs_empty: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') xs)) = {#}\<^sub>z\<close>
        by (rule CM_equiv_empty_filter_notin[OF False_xs])
      have z_in: \<open>l \<in> fst ` set zs\<close>
        using that False_xs by simp
      have ys_zs: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys)) =
        zmset (map snd (filter (\<lambda>(l', _, _). l = l') zs))\<close>
        using z_in yz by simp
      show ?thesis
      proof (cases \<open>l \<in> fst ` set ys\<close>)
        case True
        have xs_ys: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') xs)) =
          zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys))\<close>
          using True xy by simp
        show ?thesis
          using xs_ys ys_zs by simp
      next
        case False
        have ys_empty: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys)) = {#}\<^sub>z\<close>
          by (rule CM_equiv_empty_filter_notin[OF False])
        show ?thesis
          using xs_empty ys_empty ys_zs by simp
      qed
    qed
  qed
  show ?thesis
    unfolding CM_equiv_def
    using step by blast
qed



lemma CM_equiv_append:
  assumes ac: "CM_equiv a c" and bd: "CM_equiv b d"
  shows "CM_equiv (a @ b) (c @ d)"
proof (unfold CM_equiv_def, intro ballI)
  fix l
  assume "l \<in> fst ` set (a @ b) \<union> fst ` set (c @ d)"
  let ?F = "\<lambda>xs. filter (\<lambda>(l', _, _). l = l') xs"
  have part_a: "zmset (map snd (?F a)) = zmset (map snd (?F c))"
  proof (cases "l \<in> fst ` set a \<union> fst ` set c")
    case True
    with ac show ?thesis unfolding CM_equiv_def by blast
  next
    case False
    hence "?F a = []" "?F c = []"
      by (force simp: filter_empty_conv image_iff split: prod.splits)+
    thus ?thesis by simp
  qed
  have part_b: "zmset (map snd (?F b)) = zmset (map snd (?F d))"
  proof (cases "l \<in> fst ` set b \<union> fst ` set d")
    case True
    with bd show ?thesis unfolding CM_equiv_def by blast
  next
    case False
    hence "?F b = []" "?F d = []"
      by (force simp: filter_empty_conv image_iff split: prod.splits)+
    thus ?thesis by simp
  qed
  show "zmset (map snd (?F (a @ b))) = zmset (map snd (?F (c @ d)))"
    by (simp add: part_a part_b)
qed

lemma filter_extract_progress_outside:
  assumes "node l \<noteq> nid"
  shows "filter (\<lambda>(l', _, _). l = l') (extract_progress nid nt st) =
    List.map_filter
      (\<lambda>(p, t, m). case nt (nid, p) of None \<Rightarrow> None
         | Some (nid', p') \<Rightarrow>
             if l = Loc nid' (Trg p') then Some (Loc nid' (Trg p'), t, m) else None)
      (prod st)"
proof -
  have cons_empty:
    "filter (\<lambda>(l', _, _). l = l')
       (map (\<lambda>(p, t, m). (Loc nid (Trg p), t, -m)) xs) = []" for xs
    by (induct xs) (use assms in \<open>auto split: prod.splits\<close>)
  have inte_empty:
    "filter (\<lambda>(l', _, _). l = l')
       (map (\<lambda>(p, y). (Loc nid (Src p), y)) xs) = []" for xs
    by (induct xs) (use assms in \<open>auto split: prod.splits\<close>)
  have prod_eq:
    "filter (\<lambda>(l', _, _). l = l')
       (List.map_filter
          (\<lambda>(p, t, m). case_option None (\<lambda>(nid', p'). Some (Loc nid' (Trg p'), t, m))
                          (nt (nid, p)))
          xs)
     = List.map_filter
        (\<lambda>(p, t, m). case nt (nid, p) of None \<Rightarrow> None
           | Some (nid', p') \<Rightarrow>
               if l = Loc nid' (Trg p') then Some (Loc nid' (Trg p'), t, m) else None)
        xs" for xs
    by (induct xs) (auto simp: List.map_filter_def split: option.splits prod.splits)
  show ?thesis
    unfolding extract_progress_def
    by (simp add: cons_empty inte_empty prod_eq)
qed

lemma map_filter_append:
  "List.map_filter f (xs @ ys) = List.map_filter f xs @ List.map_filter f ys"
  by (induct xs) (auto simp: List.map_filter_def split: option.splits)

lemma dataplane_tracker_inv_buffer_balance_aux:
  fixes os :: "3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state"
    and cbufs :: "3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf"
    and sg :: "(3, 2, (nat, nat) myprod) subgraph"
  assumes D: "dataplane_tracker_inv os cbufs sg"
    and conn_eq: "(outputs_at_target (summ sg) os >> cbufs) (2, 1)
                  = outpu (os 1) 1 @ cbufs (2, 1)"
  shows "to_zmset (map snd (outpu (os 1) 1)) + to_zmset (map snd (cbufs (2, 1)))
       = c_pts (change_multiplicities (summ sg)
                  (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) (Loc 2 (Trg 1))"
proof -
  from D obtain caps where
    Trg: "Trg_caps_inv caps (outputs_at_target (summ sg) os >> cbufs)" and
    cp: "c_pts_inv (change_multiplicities (summ sg)
            (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) caps"
    unfolding dataplane_tracker_inv_def by blast
  have caps_eq:
    "caps (Loc 2 (Trg 1)) = to_zmset (map snd ((outputs_at_target (summ sg) os >> cbufs) (2, 1)))"
    using Trg unfolding Trg_caps_inv_def by blast
  have caps_simp:
    "caps (Loc 2 (Trg 1)) = to_zmset (map snd (outpu (os 1) 1)) + to_zmset (map snd (cbufs (2, 1)))"
    using caps_eq conn_eq by (simp add: to_zmset_append)
  have c_pts_eq:
    "c_pts (change_multiplicities (summ sg)
              (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) (Loc 2 (Trg 1))
     = caps (Loc 2 (Trg 1))"
    using cp unfolding c_pts_inv_def by simp
  show ?thesis
    using caps_simp c_pts_eq by simp
qed

lemma extract_prog_at_loc_2_trg_1:
  fixes os :: "3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state"
  assumes nt_1_1: "nt (1::3, 1::2) = Some ((2::3), (1::2))"
    and nt_1_0: "nt ((1::3), (0::2)) = None"
    and nt_2_0: "nt ((2::3), (0::2)) = None"
    and nt_2_1: "nt ((2::3), (1::2)) = Some ((1::3), (1::2))"
    and nt_0_0: "nt ((0::3), (0::2)) = None"
    and nt_0_1: "nt ((0::3), (1::2)) = None"
  shows "zmset (map snd (filter (\<lambda>(l', _, _). Loc (2::3) (Trg (1::2)) = l')
                  (extract_prog Enum.enum nt os)))
       = zmset (map (\<lambda>(p, t, m). (t, m))
                  (filter (\<lambda>(p, _, _). p = (1::2)) (produ (os 1))))
       - zmset (map (\<lambda>(p, t, m). (t, m))
                  (filter (\<lambda>(p, _, _). p = (1::2)) (consu (os 2))))"
proof -
  let ?F = "\<lambda>xs. filter (\<lambda>(l', _, _). Loc (2::3) (Trg (1::2)) = l') xs"
  have nt_1_cases: "nt ((1::3), q) = (if q = (1::2) then Some (2, 1) else None)" for q
    using nt_1_0 nt_1_1 by (cases "q = 1") (auto, metis num2_neq(2))
  have nt_2_cases: "nt ((2::3), q) = (if q = (1::2) then Some (1, 1) else None)" for q
    using nt_2_0 nt_2_1 by (cases "q = 1") (auto, metis num2_neq(2))
  have nt_0_all: "nt ((0::3), q) = None" for q :: 2
    using nt_0_0 nt_0_1 by (cases "q = 1") (auto, metis num2_neq(2))
      (* unfold extract_prog *)
  have ep_unfold: "extract_prog Enum.enum nt os
    = extract_progress 0 nt (snd (obtain_progress (os 0)))
    @ extract_progress 1 nt (snd (obtain_progress (os 1)))
    @ extract_progress 2 nt (snd (obtain_progress (os 2)))"
    unfolding extract_prog_def by simp
      (* helper inductive facts *)
  have map_filter_None_const:
    "List.map_filter (\<lambda>(p, t, m). None) xs = []" for xs :: "('a \<times> 'b \<times> 'c) list"
    by (induct xs) (auto simp: List.map_filter_def split: prod.splits)
  have cons_empty_other_nid:
    "filter (\<lambda>(l', _, _). Loc (2::3) (Trg (1::2)) = l')
       (map (\<lambda>(p, t, m). (Loc nid (Trg p), t, -m)) xs) = []"
    if "nid \<noteq> (2::3)" for nid xs
    by (induct xs) (use that in \<open>auto split: prod.splits\<close>)
  have inter_empty:
    "filter (\<lambda>(l', _, _). Loc (2::3) (Trg (1::2)) = l')
       (map (\<lambda>(p, y). (Loc nid (Src p), y)) xs) = []" for nid xs
    by (induct xs) (auto split: prod.splits)
  have prod_empty_when_nt_None:
    "List.map_filter (\<lambda>(p, t, m). case nt (nid, p) of None \<Rightarrow> None
                              | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) xs = []"
    if "\<And>p. nt (nid, p) = None" for nid xs
    by (induct xs) (auto simp: List.map_filter_def that split: prod.splits)
  have prod_match_nt_1:
    "filter (\<lambda>(l', _, _). Loc (2::3) (Trg (1::2)) = l')
       (List.map_filter (\<lambda>(p, t, m). case nt ((1::3), p) of None \<Rightarrow> None
                                       | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) xs)
     = map (\<lambda>(p, t, m). (Loc 2 (Trg 1), t, m))
         (filter (\<lambda>(p, _, _). p = (1::2)) xs)" for xs
    by (induct xs)
      (auto simp: List.map_filter_def nt_1_cases split: prod.splits if_splits)
  have prod_empty_nt_2:
    "filter (\<lambda>(l', _, _). Loc (2::3) (Trg (1::2)) = l')
       (List.map_filter (\<lambda>(p, t, m). case nt ((2::3), p) of None \<Rightarrow> None
                                       | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) xs) = []" for xs
    by (induct xs)
      (auto simp: List.map_filter_def nt_2_cases split: prod.splits if_splits)
  have cons_match_2:
    "filter (\<lambda>(l', _, _). Loc (2::3) (Trg (1::2)) = l')
       (map (\<lambda>(p, t, m). (Loc (2::3) (Trg p), t, -m)) xs)
     = map (\<lambda>(p, t, m). (Loc 2 (Trg 1), t, -m))
         (filter (\<lambda>(p, _, _). p = (1::2)) xs)" for xs
    by (induct xs) (auto split: prod.splits)
      (* assemble *)
  have nid0_empty: "?F (extract_progress 0 nt (snd (obtain_progress (os 0)))) = []"
    unfolding extract_progress_def obtain_progress_def
    by (simp add: split_beta cons_empty_other_nid inter_empty
        prod_empty_when_nt_None[OF nt_0_all])
  have nid1_routed:
    "?F (extract_progress 1 nt (snd (obtain_progress (os 1))))
    = map (\<lambda>(p, t, m). (Loc 2 (Trg 1), t, m))
        (filter (\<lambda>(p, _, _). p = 1) (produ (os 1)))"
    unfolding extract_progress_def obtain_progress_def
    by (simp add: split_beta cons_empty_other_nid inter_empty prod_match_nt_1)
  have nid2_cons_only:
    "?F (extract_progress 2 nt (snd (obtain_progress (os 2))))
    = map (\<lambda>(p, t, m). (Loc 2 (Trg 1), t, -m))
        (filter (\<lambda>(p, _, _). p = 1) (consu (os 2)))"
    unfolding extract_progress_def obtain_progress_def
    by (simp add: split_beta cons_match_2 inter_empty prod_empty_nt_2)
  have filtered_eq:
    "?F (extract_prog Enum.enum nt os)
    = map (\<lambda>(p, t, m). (Loc 2 (Trg 1), t, m))
        (filter (\<lambda>(p, _, _). p = 1) (produ (os 1)))
    @ map (\<lambda>(p, t, m). (Loc 2 (Trg 1), t, -m))
        (filter (\<lambda>(p, _, _). p = 1) (consu (os 2)))"
    unfolding ep_unfold filter_append
    using nid0_empty nid1_routed nid2_cons_only by simp
      (* final zmset arithmetic *)
  have map_snd_drop_loc_pos:
    "map snd (map (\<lambda>(p, t, m). (Loc (2::3) (Trg (1::2)), t, m)) xs) 
     = map (\<lambda>(p, t, m). (t, m)) xs" for xs :: "(2 \<times> (nat, nat) myprod \<times> int) list"
    by (induct xs) (auto split: prod.splits)
  have map_snd_drop_loc_neg:
    "map snd (map (\<lambda>(p, t, m). (Loc (2::3) (Trg (1::2)), t, -m)) xs) 
     = map (\<lambda>(p, t, m). (t, -m)) xs" for xs :: "(2 \<times> (nat, nat) myprod \<times> int) list"
    by (induct xs) (auto split: prod.splits)
  have zmset_neg_3:
    "zmset (map (\<lambda>(p, t, m). (t, -m)) xs) = - zmset (map (\<lambda>(p, t, m). (t, m)) xs)"
    for xs :: "(2 \<times> (nat, nat) myprod \<times> int) list"
    by (simp add: case_prod_unfold)
  show ?thesis
    unfolding filtered_eq
    by (simp add: case_prod_beta' comp_def split_beta map_append zmset_append map_snd_drop_loc_pos map_snd_drop_loc_neg zmset_neg_3)
qed

lemma dataplane_buffer_consu_produ_balance:
  fixes os :: "3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state"
    and cbufs :: "3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf"
    and sg :: "(3, 2, (nat, nat) myprod) subgraph"
  assumes D: "dataplane_tracker_inv os cbufs sg"
    and Nxt: "nxt sg = nt"
    and conn_eq: "(outputs_at_target (summ sg) os >> cbufs) (2, 1)
                  = outpu (os 1) 1 @ cbufs (2, 1)"
    and nt_1_1: "nt (1::3, 1::2) = Some ((2::3), (1::2))"
    and nt_1_0: "nt ((1::3), (0::2)) = None"
    and nt_2_0: "nt ((2::3), (0::2)) = None"
    and nt_2_1: "nt ((2::3), (1::2)) = Some ((1::3), (1::2))"
    and nt_0_0: "nt ((0::3), (0::2)) = None"
    and nt_0_1: "nt ((0::3), (1::2)) = None"
  shows "to_zmset (map snd (outpu (os 1) 1)) + to_zmset (map snd (cbufs (2, 1)))
       + zmset (map (\<lambda>(p, t, m). (t, m))
                  (filter (\<lambda>(p, _, _). p = (1::2)) (consu (os 2))))
       = c_pts (pt_tr sg) (Loc (2::3) (Trg (1::2)))
       + zmset (map (\<lambda>(p, t, m). (t, m))
                  (filter (\<lambda>(p, _, _). p = (1::2)) (produ (os 1))))"
proof -
  have buffer_balance:
    "to_zmset (map snd (outpu (os 1) 1)) + to_zmset (map snd (cbufs (2, 1)))
     = c_pts (change_multiplicities (summ sg)
                (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) (Loc 2 (Trg 1))"
    using D conn_eq by (rule dataplane_tracker_inv_buffer_balance_aux)
  also have "c_pts (change_multiplicities (summ sg)
                (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) (Loc 2 (Trg 1))
           = c_pts (pt_tr sg) (Loc 2 (Trg 1))
           + zmset (map snd (filter (\<lambda>(l', _, _). Loc 2 (Trg 1) = l')
                  (extract_prog Enum.enum (nxt sg) os)))"
    by (simp add: c_pts_change_multiplicities)
  also have "zmset (map snd (filter (\<lambda>(l', _, _). Loc 2 (Trg 1) = l')
                  (extract_prog Enum.enum (nxt sg) os)))
           = zmset (map (\<lambda>(p, t, m). (t, m))
                      (filter (\<lambda>(p, _, _). p = 1) (produ (os 1))))
           - zmset (map (\<lambda>(p, t, m). (t, m))
                      (filter (\<lambda>(p, _, _). p = 1) (consu (os 2))))"
    using nt_1_1 nt_1_0 nt_2_0 nt_2_1 nt_0_0 nt_0_1
    unfolding Nxt[symmetric]
    by (rule extract_prog_at_loc_2_trg_1)
  finally show ?thesis by simp
qed

lemma dataplane_tracker_inv_buffer_balance:
  fixes os :: "3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state"
    and cbufs :: "3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf"
    and sg :: "(3, 2, (nat, nat) myprod) subgraph"
  assumes D: "dataplane_tracker_inv os cbufs sg"
    and conn_eq: "(outputs_at_target (summ sg) os >> cbufs) (2, 1)
                  = outpu (os 1) 1 @ cbufs (2, 1)"
  shows "to_zmset (map snd (outpu (os 1) 1)) + to_zmset (map snd (cbufs (2, 1)))
       = c_pts (change_multiplicities (summ sg) 
                  (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) (Loc 2 (Trg 1))"
proof -
  from D obtain caps where
    Trg: "Trg_caps_inv caps (outputs_at_target (summ sg) os >> cbufs)" and
    cp: "c_pts_inv (change_multiplicities (summ sg)
            (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) caps"
    unfolding dataplane_tracker_inv_def by blast
  have caps_eq:
    "caps (Loc 2 (Trg 1)) = to_zmset (map snd ((outputs_at_target (summ sg) os >> cbufs) (2, 1)))"
    using Trg unfolding Trg_caps_inv_def by blast
  have caps_simp:
    "caps (Loc 2 (Trg 1)) = to_zmset (map snd (outpu (os 1) 1)) + to_zmset (map snd (cbufs (2, 1)))"
    using caps_eq conn_eq by (simp add: to_zmset_append)
  have c_pts_eq:
    "c_pts (change_multiplicities (summ sg)
              (extract_prog Enum.enum (nxt sg) os) (pt_tr sg)) (Loc 2 (Trg 1))
     = caps (Loc 2 (Trg 1))"
    using cp unfolding c_pts_inv_def by simp
  show ?thesis
    using caps_simp c_pts_eq by simp
qed

lemma filter_extract_progress_Trg:
  shows "filter (\<lambda>(l', _, _). Loc nid (Trg p) = l') (extract_progress nid' nt st) =
    (if nid = nid' then
       map (\<lambda>(p', t, m). (Loc nid (Trg p), t, -m))
         (filter (\<lambda>(p', _, _). p' = p) (cons st))
     else []) @
    List.map_filter (\<lambda>(p_in, t, m).
      case nt (nid', p_in) of None \<Rightarrow> None
      | Some (nid'', p''') \<Rightarrow>
          if nid = nid'' \<and> p = p''' then Some (Loc nid (Trg p), t, m) else None)
    (prod st)"
proof -
  have cons_simp:
    "filter (\<lambda>(l', _, _). Loc nid (Trg p) = l')
       (map (\<lambda>(p'', t, m). (Loc nid' (Trg p''), t, -m)) xs) =
     (if nid = nid' then
        map (\<lambda>(p'', t, m). (Loc nid (Trg p), t, -m))
          (filter (\<lambda>(p'', _, _). p'' = p) xs)
      else [])" for xs
    by (induct xs) (auto split: prod.splits)
  have inter_empty:
    "filter (\<lambda>(l', _, _). Loc nid (Trg p) = l')
       (map (\<lambda>(p'', y). (Loc nid' (Src p''), y)) xs) = []" for xs
    by (induct xs) (auto split: prod.splits)
  have prod_simp:
    "filter (\<lambda>(l', _, _). Loc nid (Trg p) = l')
       (List.map_filter (\<lambda>(p_in, t, m). case_option None (\<lambda>(nid'', p''').
          Some (Loc nid'' (Trg p'''), t, m)) (nt (nid', p_in))) xs) =
     List.map_filter (\<lambda>(p_in, t, m).
       case nt (nid', p_in) of None \<Rightarrow> None
       | Some (nid'', p''') \<Rightarrow>
           if nid = nid'' \<and> p = p''' then Some (Loc nid (Trg p), t, m) else None)
     xs" for xs
    by (induct xs) (auto simp: List.map_filter_def split: option.splits prod.splits)
  show ?thesis
    unfolding extract_progress_def
    by (simp add: cons_simp inter_empty prod_simp split_beta)
qed

lemma filter_extract_progress_Src:
  shows "filter (\<lambda>(l', _, _). Loc nid (Src p) = l') (extract_progress nid' nt st) =
    (if nid = nid' then
      map (\<lambda>(p', y). (Loc nid (Src p), y))
        (filter (\<lambda>(p', _). p' = p) (inte st))
    else [])"
proof -
  have cons_empty:
    "filter (\<lambda>(l', _, _). Loc nid (Src p) = l')
       (map (\<lambda>(p'', t, m). (Loc nid' (Trg p''), t, -m)) xs) = []" for xs
    by (induct xs) (auto split: prod.splits)
  have inter_simp:
    "filter (\<lambda>(l', _, _). Loc nid (Src p) = l')
       (map (\<lambda>(p'', y). (Loc nid' (Src p''), y)) xs) =
     (if nid = nid' then
        map (\<lambda>(p'', y). (Loc nid (Src p), y))
          (filter (\<lambda>(p'', _). p'' = p) xs)
      else [])" for xs
    by (induct xs) (auto split: prod.splits)
  have prod_empty:
    "filter (\<lambda>(l', _, _). Loc nid (Src p) = l')
       (List.map_filter (\<lambda>(p'', t, m). case_option None (\<lambda>(nid'', p'''). 
          Some (Loc nid'' (Trg p'''), t, m)) (nt (nid', p''))) xs) = []" for xs
    by (induct xs) (auto simp: List.map_filter_def split: option.splits prod.splits)
  show ?thesis
    unfolding extract_progress_def
    by (simp add: cons_empty inter_simp prod_empty split_beta)
qed


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

(* TODO: Move. *)
lemma wf_label_prop_updates_consumes[simp]:
  \<open>wf_label_prop_updates (consumes os p t d) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  by (simp add: wf_label_prop_updates_def consumes_def all_vertices_def all_edges_def neighbors_def)

lemma wf_label_prop_updates_CONSUMES[simp]:
  \<open>wf_label_prop_updates (CONSUMES p ys os) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  by (induct ys arbitrary: os) clarsimp+

lemma wf_label_prop_updates_intsum_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>intsum := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_consu_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>consu := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_inter_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>inter := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_produ_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>produ := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_input_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>input := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_outpu_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>outpu := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_front_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>front := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_ocaps_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>ocaps := xs\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_initia_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>initia := b\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_en1_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>en1 := f\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_is_en1_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>is_en1 := f\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_en2_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>en2 := f\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_de2_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>de2 := f\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_is_en2_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>is_en2 := f\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

lemma wf_label_prop_updates_label_update[simp]:
  \<open>wf_label_prop_updates (os\<lparr>label := f\<rparr>) S \<longleftrightarrow> wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

(* TODO: Move. *)
lemma wf_label_prop_updates_cong:
  \<open>de1 os = de1 os' \<Longrightarrow> timestamps os = timestamps os' \<Longrightarrow> graph os = graph os' \<Longrightarrow>
  vertices os = vertices os' \<Longrightarrow> S = S' \<Longrightarrow>
  wf_label_prop_updates os S \<longleftrightarrow> wf_label_prop_updates os' S'\<close>
  unfolding wf_label_prop_updates_def all_vertices_def all_edges_def neighbors_def by simp

(* TODO: Move. *)
lemma wf_label_prop_updates_subset:
  \<open>wf_label_prop_updates os S \<Longrightarrow> S' \<subseteq> S \<Longrightarrow> wf_label_prop_updates os S'\<close>
  unfolding wf_label_prop_updates_def by fast

(* TODO: Move. *)
lemma wf_label_prop_updates_Un:
  \<open>S'' = S \<union> S' \<Longrightarrow> wf_label_prop_updates os S'' \<longleftrightarrow> wf_label_prop_updates os S \<and> wf_label_prop_updates os S'\<close>
  unfolding wf_label_prop_updates_def by force

(* TODO: Move. *)
lemma wf_label_prop_updates_os_mono:
  assumes \<open>wf_label_prop_updates os S\<close> \<open>de1 os = de1 os'\<close> \<open>set (timestamps os) \<subseteq> set (timestamps os')\<close>
    \<open>\<forall>t. set (vertices os t) \<subseteq> set (vertices os' t) \<and> (\<forall>v. set (graph os t v) \<subseteq> set (graph os' t v))\<close>
    \<open>S = S'\<close>
  shows \<open>wf_label_prop_updates os' S'\<close>
proof -
  { fix d t
    assume d_t: \<open>(d, t) \<in> S\<close>
    let ?t0 = \<open>myfst t\<close>
    have t0: \<open>?t0 \<in> set (timestamps os')\<close> (is ?A)
      using assms(1,3) d_t unfolding wf_label_prop_updates_def by fast
    have all_vertices_subset: \<open>\<forall>t'. all_vertices os t' \<subseteq> all_vertices os' t'\<close>
      using assms(3,4) d_t unfolding wf_label_prop_updates_def all_vertices_def by blast
    hence fst_de1: \<open>fst (de1 os d) \<in> all_vertices os' ?t0\<close> (is ?B)
      using assms(1) d_t unfolding wf_label_prop_updates_def by fast
    have \<open>\<forall>t' \<ge> ?t0. \<forall>v. set (neighbors os t' v) \<subseteq> set (neighbors os' t' v)\<close>
      unfolding neighbors_def using assms(3,4) by force
    hence \<open>\<forall>t' \<ge> ?t0. all_edges os t' \<subseteq> all_edges os' t'\<close>
      unfolding all_edges_def using all_vertices_subset by fast
    hence \<open>\<forall>t' \<ge> ?t0. snd (de1 os d) \<in> cc_of (all_edges os' t') (fst (de1 os d))\<close> (is ?C)
      using assms(1) d_t cc_of_mono prod.simps(2) unfolding wf_label_prop_updates_def
      by (metis (mono_tags, lifting))
    hence \<open>?A \<and> ?B \<and> ?C\<close> using t0 fst_de1 by blast
  }
  thus ?thesis unfolding wf_label_prop_updates_def assms(5) using assms(2) by force
qed

lemma wf_label_prop_updates_label_prop_input0_step_state_monoI:
  assumes H: \<open>wf_label_prop_updates os S\<close>
  shows \<open>wf_label_prop_updates (label_prop_input0_step_state os d t) S\<close>
proof (rule wf_label_prop_updates_os_mono[OF H])
  show \<open>de1 os = de1 (label_prop_input0_step_state os d t)\<close>
    by simp
  show \<open>set (timestamps os) \<subseteq> set (timestamps (label_prop_input0_step_state os d t))\<close>
    by auto
  show \<open>\<forall>t'. set (vertices os t') \<subseteq> set (vertices (label_prop_input0_step_state os d t) t') \<and>
    (\<forall>v. set (graph os t' v) \<subseteq> set (graph (label_prop_input0_step_state os d t) t' v))\<close>
    unfolding label_prop_input0_step_state_def label_prop_edge_record_update_def input_tl_def
    by (auto simp: Let_def split: if_splits)
  show \<open>S = S\<close>
    by simp
qed

lemma wf_label_prop_updates_fst_label_prop_input0_batched_monoI:
  assumes H: \<open>wf_label_prop_updates os S\<close>
  shows \<open>wf_label_prop_updates (fst (label_prop_input0_batched os xs)) S\<close>
  using H
proof (induct xs arbitrary: os)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  obtain d t where x_eq: \<open>x = (d, t)\<close>
    by (cases x)
  have step: \<open>wf_label_prop_updates (label_prop_input0_step_state os d t) S\<close>
    by (rule wf_label_prop_updates_label_prop_input0_step_state_monoI[OF Cons.prems])
  have rec: \<open>wf_label_prop_updates (fst (label_prop_input0_batched (label_prop_input0_step_state os d t) xs)) S\<close>
    by (rule Cons.hyps[OF step])
  show ?case
    using rec unfolding x_eq
    by (cases \<open>label_prop_input0_batched (label_prop_input0_step_state os d t) xs\<close>) simp
qed

lemma wf_label_prop_updates_label_prop_input1_step_state_monoI:
  assumes H: \<open>wf_label_prop_updates os S\<close>
  shows \<open>wf_label_prop_updates (label_prop_input1_step_state os d t) S\<close>
proof (rule wf_label_prop_updates_os_mono[OF H])
  show \<open>de1 os = de1 (label_prop_input1_step_state os d t)\<close>
    unfolding label_prop_input1_step_state_def label_prop_label_record_update_def input_tl_def
    by (simp add: Let_def)
  show \<open>set (timestamps os) \<subseteq> set (timestamps (label_prop_input1_step_state os d t))\<close>
    by simp
  show \<open>\<forall>t'. set (vertices os t') \<subseteq> set (vertices (label_prop_input1_step_state os d t) t') \<and>
    (\<forall>v. set (graph os t' v) \<subseteq> set (graph (label_prop_input1_step_state os d t) t' v))\<close>
    unfolding label_prop_input1_step_state_def label_prop_label_record_update_def input_tl_def
    by (auto simp: Let_def split: if_splits)
  show \<open>S = S\<close>
    by simp
qed

lemma wf_label_prop_updates_fst_label_prop_input1_batched_monoI:
  assumes H: \<open>wf_label_prop_updates os S\<close>
  shows \<open>wf_label_prop_updates (fst (label_prop_input1_batched os xs)) S\<close>
  using H
proof (induct xs arbitrary: os)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  obtain d t where x_eq: \<open>x = (d, t)\<close>
    by (cases x)
  have step: \<open>wf_label_prop_updates (label_prop_input1_step_state os d t) S\<close>
    by (rule wf_label_prop_updates_label_prop_input1_step_state_monoI[OF Cons.prems])
  have rec: \<open>wf_label_prop_updates (fst (label_prop_input1_batched (label_prop_input1_step_state os d t) xs)) S\<close>
    by (rule Cons.hyps[OF step])
  show ?case
    using rec unfolding x_eq
    by (cases \<open>label_prop_input1_batched (label_prop_input1_step_state os d t) xs\<close>) simp
qed

lemma wf_label_prop_updates_label_prop_input1_loop_updates_monoI:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and H: \<open>wf_label_prop_updates os_label_prop S\<close>
  shows \<open>wf_label_prop_updates os_label_prop' S\<close>
proof -
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?cons = \<open>CONSUMES 1 ?msgs (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?cons (input ?cons 1))\<close>
    using step unfolding label_prop_input1_loop_updates_def Let_def
    by (simp split: prod.splits)
  have cons_wf: \<open>wf_label_prop_updates ?cons S\<close>
    using H by simp
  show ?thesis
    unfolding os_label_prop'_eq
    by (rule wf_label_prop_updates_fst_label_prop_input1_batched_monoI[OF cons_wf])
qed

lemma wf_label_prop_updates_loop_updates_monoI:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
    and H: \<open>wf_label_prop_updates os_label_prop S\<close>
  shows \<open>wf_label_prop_updates os_label_prop' S\<close>
  using step H
proof (induct cbufs os_label_prop os arbitrary: cbufs' os_label_prop' os' S rule: loop_updates.induct)
  case (1 cbufs os_label_prop os)
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?good = \<open>label_prop_upd_inv os_label_prop \<and>
    (\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)) \<and>
    wf_label_prop_updates os_label_prop (set (input os_label_prop 1) \<union> set ?msgs)\<close>
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
    note good = True
    obtain cbufs1 os_label_prop1 os1 where step1:
      \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (cases \<open>label_prop_input1_loop_updates cbufs os_label_prop os\<close>) auto
    have wf1: \<open>wf_label_prop_updates os_label_prop1 S\<close>
      by (rule wf_label_prop_updates_label_prop_input1_loop_updates_monoI[OF step1[symmetric] "1.prems"(2)])
    show ?thesis
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
      show ?thesis
        by (rule "1.hyps"[OF good step1[symmetric] refl refl False step_rec wf1])
    qed
  qed
qed


lemma label_prop_upd_inv_loop_updatesI:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
  shows \<open>label_prop_upd_inv os_label_prop'\<close>
  using step INV LABELS WF EN1 DE1
proof (induct cbufs os_label_prop os arbitrary: cbufs' os_label_prop' os' rule: loop_updates.induct)
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
    by (rule label_prop_upd_inv_label_prop_input1_loop_updatesI[OF step1[symmetric] "1.prems"(2) "1.prems"(4)])
  show ?case
  proof (cases \<open>outpu os_label_prop1 1 = []\<close>)
    case True
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (subst loop_updates.simps) (use good step1 True in simp)
    show ?thesis
      using "1.prems"(1) loop_eq INV1 by simp
  next
    case False
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs1 os_label_prop1 os1\<close>
      by (subst loop_updates.simps) (use good step1 False in simp)
    have step_rec: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs1 os_label_prop1 os1\<close>
      using "1.prems"(1) loop_eq by simp
    have LABELS1: \<open>\<forall>t. labels_inv (all_edges os_label_prop1 t) (min_label os_label_prop1 t)\<close>
      by (rule labels_inv_label_prop_input1_loop_updates_allI[OF step1[symmetric] "1.prems"(2) "1.prems"(4) "1.prems"(3)])
    have input1_empty: \<open>input os_label_prop1 1 = []\<close>
      by (rule label_prop_input1_loop_updates_input_label_1[OF step1[symmetric]])
    have wf1_msgs:
      \<open>wf_label_prop_updates os_label_prop1
        (set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
      by (rule label_prop_input1_loop_updates_msgs_invI
          [OF step1[symmetric] "1.prems"(5) "1.prems"(6) "1.prems"(2) "1.prems"(3) "1.prems"(4)])
    have WF1: \<open>wf_label_prop_updates os_label_prop1
      (set (input os_label_prop1 1) \<union>
       set (cbufs1 (1, 1) @ outpu (os1 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os1 2) 1 @ cbufs1 (2, 1) @ outpu os_label_prop1 1)))\<close>
      using input1_empty wf1_msgs by simp
    have EN1_1: \<open>en1 os_label_prop1 = Inl\<close>
      using label_prop_input1_loop_updates_en1_label[OF step1[symmetric]] "1.prems"(5) by simp
    have DE1_1: \<open>de1 os_label_prop1 = projl\<close>
      using label_prop_input1_loop_updates_de1_label[OF step1[symmetric]] "1.prems"(6) by simp
    show ?thesis
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False step_rec INV1 LABELS1 WF1 EN1_1 DE1_1])
  qed
qed
subsection \<open>Auxiliary label-invariant preservation for correctness proof\<close>

lemma labels_inv_fst_label_prop_input0_batched_input_allI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes input_eq: \<open>input os 0 = msgs\<close>
    and labels: \<open>\<forall>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>\<forall>q. labels_inv (all_edges (fst (label_prop_input0_batched os msgs)) q)
    (min_label (fst (label_prop_input0_batched os msgs)) q)\<close>
proof
  fix q
  show \<open>labels_inv (all_edges (fst (label_prop_input0_batched os msgs)) q)
    (min_label (fst (label_prop_input0_batched os msgs)) q)\<close>
    by (rule labels_inv_fst_label_prop_input0_batched_inputI[OF input_eq _ inv wf_upd])
      (use labels in simp)
qed

lemma labels_inv_loop_updates_allI:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs os_label_prop os\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and WF: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
  shows \<open>\<forall>t. labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
  using step INV LABELS WF EN1 DE1
proof (induct cbufs os_label_prop os arbitrary: cbufs' os_label_prop' os' rule: loop_updates.induct)
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
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = (cbufs1, os_label_prop1, os1)\<close>
      by (subst loop_updates.simps) (use good step1 True in simp)
    show ?thesis
      using "1.prems"(1) loop_eq LABELS1 by simp
  next
    case False
    have loop_eq: \<open>loop_updates cbufs os_label_prop os = loop_updates cbufs1 os_label_prop1 os1\<close>
      by (subst loop_updates.simps) (use good step1 False in simp)
    have step_rec: \<open>(cbufs', os_label_prop', os') = loop_updates cbufs1 os_label_prop1 os1\<close>
      using "1.prems"(1) loop_eq by simp
    show ?thesis
      by (rule "1.hyps"[OF good step1[symmetric] refl refl False step_rec INV1 LABELS1 WF1 EN1_1 DE1_1])
  qed
qed


(* TODO: Move. *)
lemma label_prop_edge_batch_in_timestamps:
  \<open>(d, cap) \<in> set (label_prop_edge_batch old_os updated_os event_t vertex new_label event_time)
  \<Longrightarrow> myfst (capability.time cap) \<in> set (timestamps updated_os)\<close>
  unfolding label_prop_edge_batch_def label_prop_neighbor_batch_def by force

(* TODO: Move. *)
lemma label_prop_label_batch_in_timestamps:
  \<open>(d, cap) \<in> set (label_prop_label_batch old_os updated_os event_t vertex new_label event_time)
  \<Longrightarrow> myfst (capability.time cap) \<in> set (timestamps old_os)\<close>
  unfolding label_prop_label_batch_def label_prop_neighbor_batch_def by force

(* TODO: Move. *)
lemma all_vertices_add_caps[simp]:
  \<open>all_vertices (add_caps os caps) = all_vertices os\<close>
  unfolding all_vertices_def by simp

(* TODO: Move. *)
lemma label_prop_edge_batch_all_vertices:
  assumes \<open>updated_os = label_prop_edge_record_update (input_tl old_os 0) (event_t :: _ :: {plus, order}) v1 v2 vertex new_label\<close>
    \<open>batch = label_prop_edge_batch old_os updated_os event_t vertex new_label event_time\<close>
    \<open>en1 old_os = Inl\<close> \<open>de1 old_os = projl\<close> \<open>label_prop_upd_inv updated_os\<close> \<open>(d, cap) \<in> set batch\<close>
    \<open>t = myfst (capability.time cap)\<close> \<open>v = fst (de1 old_os d)\<close>
  shows \<open>v \<in> all_vertices updated_os t\<close>
proof -
  have \<open>v \<in> set (neighbors updated_os t vertex)\<close>
    using assms(2-4,6,7,8) by (force simp add: label_prop_edge_batch_def label_prop_neighbor_batch_def)
  then obtain t' where t': \<open>t' \<in> set (timestamps updated_os)\<close> \<open>t' \<le> t\<close>
    \<open>v \<in> set (graph updated_os t' vertex)\<close> unfolding neighbors_def by auto
  hence \<open>v \<in> set (vertices updated_os t')\<close>
    using label_prop_upd_inv_graph_edgeD[OF assms(5)] by blast
  thus ?thesis unfolding all_vertices_def using t'(1,2) by blast
qed

(* TODO: Move. *)
lemma label_prop_label_batch_all_vertices:
  assumes \<open>updated_os = label_prop_label_record_update old_os event_t vertex assigned_label\<close>
    \<open>batch = label_prop_label_batch old_os updated_os event_t vertex new_label event_time\<close>
    \<open>en1 old_os = Inl\<close> \<open>de1 old_os = projl\<close> \<open>label_prop_upd_inv old_os\<close> \<open>(d, cap) \<in> set batch\<close>
    \<open>t = myfst (capability.time cap)\<close> \<open>v = fst (de1 old_os d)\<close>
  shows \<open>v \<in> all_vertices updated_os t\<close>
proof -
  have \<open>v \<in> set (neighbors old_os t vertex)\<close>
    using assms(2-4,6,7,8) by (force simp add: label_prop_label_batch_def label_prop_neighbor_batch_def)
  then obtain t' where t': \<open>t' \<in> set (timestamps old_os)\<close> \<open>t' \<le> t\<close>
    \<open>v \<in> set (graph old_os t' vertex)\<close> unfolding neighbors_def by auto
  hence \<open>v \<in> set (vertices old_os t')\<close>
    using label_prop_upd_inv_graph_edgeD[OF assms(5)] by blast
  hence \<open>v \<in> all_vertices old_os t\<close> unfolding all_vertices_def using t'(1,2) by blast
  thus ?thesis by (simp add: assms(1) label_prop_label_record_update_def all_vertices_def)
qed

(* TODO: Move. *)
lemma neighbors_reachable:
  \<open>label_prop_upd_inv os \<Longrightarrow> w \<in> set (neighbors os t v) \<Longrightarrow> reachable (all_edges os t) v w\<close>
  unfolding all_edges_def reachable_def using label_prop_upd_inv_neighborsD by blast

(* TODO: Move. *)
lemma reachable_subset:
  \<open>A \<subseteq> B \<Longrightarrow> reachable A x y \<Longrightarrow> reachable B x y\<close>
  using converse_mono rtrancl_mono_mp sup_mono unfolding reachable_def
  by meson

(* TODO: Move. *)
lemma label_prop_edge_batch_cc_of_all_edges:
  assumes \<open>updated_os = label_prop_edge_record_update (input_tl old_os 0) (myfst (t :: _ :: {plus, order})) v1 v2 vertex new_label\<close>
    \<open>batch = label_prop_edge_batch old_os updated_os (myfst t) vertex new_label t\<close>
    \<open>en1 old_os = Inl\<close> \<open>de1 old_os = projl\<close> \<open>label_prop_upd_inv updated_os\<close> \<open>(d, cap) \<in> set batch\<close>
    \<open>myfst (capability.time cap) \<le> t'\<close> \<open>(v, w) = de1 old_os d\<close>
    \<open>(vertex, new_label) = (if min_label old_os (myfst t) v2 < min_label old_os (myfst t) v1
      then (v1, min_label old_os (myfst t) v2)
      else (v2, min_label old_os (myfst t) v1))\<close>
    \<open>\<forall>t. labels_inv (all_edges updated_os t) (min_label updated_os t)\<close>
  shows \<open>w \<in> cc_of (all_edges updated_os t') v\<close>
proof -
  let ?t0 = \<open>myfst (capability.time cap)\<close>
  have myfst_t_t': \<open>myfst t \<le> t'\<close> using assms(2-4,6,7)
    by (force simp add: label_prop_edge_batch_def label_prop_neighbor_batch_def)
  have vertex_v1_v2: \<open>vertex = v1 \<or> vertex = v2\<close> using assms(9) by (simp split: if_splits)
  have w_new_label: \<open>w = new_label\<close> using assms(2-4,6,8)
    by (force simp add: label_prop_edge_batch_def label_prop_neighbor_batch_def)
  have \<open>v \<in> set (neighbors updated_os ?t0 vertex)\<close>
    using assms(2-4,6,8) by (force simp add: label_prop_edge_batch_def label_prop_neighbor_batch_def)
  hence \<open>reachable (all_edges updated_os ?t0) vertex v\<close>
    using neighbors_reachable[OF assms(5)] by blast
  hence reachable_vertex_v: \<open>reachable (all_edges updated_os t') vertex v\<close>
    using all_edges_mono[OF assms(7)] reachable_subset by metis
  have new_label_le: \<open>new_label \<le> min_label old_os (myfst t) vertex\<close> using assms(9) by (simp split: if_splits)
  hence \<open>min_label updated_os (myfst t) vertex = new_label\<close>
  proof -
    let ?A = \<open>(\<lambda>t'. label updated_os t' vertex) ` {t' \<in> set (timestamps updated_os). t' \<le> myfst t}\<close>
    have \<open>\<forall>l \<in> ?A. new_label \<le> l\<close>
      using new_label_le by (force simp add: assms(1) min_label_def label_prop_edge_record_update_def)
    then show ?thesis using Min_insert2[where a=new_label and A=\<open>?A\<close>] unfolding min_label_def
      by (force simp add: assms(1) label_prop_edge_record_update_def)
  qed
  moreover have \<open>vertex \<in> edge_vertices (all_edges updated_os (myfst t))\<close>
    using edge_vertices_all_edges[OF assms(5)] vertex_v1_v2
    by (force simp add: assms(1) label_prop_edge_record_update_def all_vertices_def)
  ultimately have \<open>new_label \<in> cc_of (all_edges updated_os (myfst t)) vertex\<close>
    using assms(10) unfolding labels_inv_def by fast
  moreover have \<open>all_edges updated_os (myfst t) \<subseteq> all_edges updated_os t'\<close>
    by (rule all_edges_mono[OF myfst_t_t'])
  ultimately have \<open>new_label \<in> cc_of (all_edges updated_os t') vertex\<close> using cc_of_mono by blast
  thus ?thesis using w_new_label cc_of_eq_if_reachable[OF reachable_vertex_v] by blast
qed

lemma wf_label_prop_updates_label_prop_input0_step_state_output1_shiftI:
  fixes os :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and d :: \<open>nat \<times> nat + nat set set\<close>
    and t :: \<open>(nat, nat) myprod\<close>
    and rest :: \<open>((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) list\<close>
    and S :: \<open>((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) set\<close>
  assumes input0: \<open>input os (0 :: 2) = (d, t) # rest\<close>
    and EN1: \<open>en1 os = Inl\<close>
    and DE1: \<open>de1 os = projl\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and LABELS: \<open>\<forall>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and WF_input1: \<open>wf_label_prop_updates os (set (input os (1 :: 2)))\<close>
    and WF: \<open>wf_label_prop_updates os
      (S \<union> ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (outpu os (1 :: 2))))\<close>
  shows \<open>wf_label_prop_updates (label_prop_input0_step_state os d t)
      (S \<union> ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) `
        set (outpu (label_prop_input0_step_state os d t) (1 :: 2))))\<close>
proof -
  let ?step = \<open>label_prop_input0_step_state os d t\<close>
  let ?v1 = \<open>fst (de1 os d)\<close>
  let ?v2 = \<open>snd (de1 os d)\<close>
  let ?t1 = \<open>myfst t\<close>
  let ?l1 = \<open>min_label os ?t1 ?v1\<close>
  let ?l2 = \<open>min_label os ?t1 ?v2\<close>
  let ?v = \<open>if ?l1 > ?l2 then ?v1 else ?v2\<close>
  let ?l = \<open>if ?l1 > ?l2 then ?l2 else ?l1\<close>
  let ?updated = \<open>label_prop_edge_record_update (input_tl os 0) ?t1 ?v1 ?v2 ?v ?l\<close>
  let ?batch = \<open>label_prop_edge_batch os ?updated ?t1 ?v ?l t\<close>
  let ?shift = \<open>\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))\<close>
  have batch_eq: \<open>label_prop_input0_step_batch os d t = ?batch\<close>
    unfolding label_prop_input0_step_batch_def by (simp add: Let_def)
  have old_wf: \<open>wf_label_prop_updates ?step
      (S \<union> ?shift ` set (outpu os 1))\<close>
    by (rule wf_label_prop_updates_label_prop_input0_step_state_monoI[OF WF])
  have updated_inv: \<open>label_prop_upd_inv ?updated\<close>
  proof (rule label_prop_upd_inv_input0_preserved[OF INV])
    show \<open>timestamps ?updated = ?t1 # timestamps os\<close>
      by (simp add: label_prop_edge_record_update_def input_tl_def)
    show \<open>graph ?updated = (graph os)(?t1 := (graph os ?t1)(?v1 := ?v2 # graph os ?t1 ?v1,
        ?v2 := ?v1 # graph os ?t1 ?v2))\<close>
      by (simp add: label_prop_edge_record_update_def input_tl_def)
    show \<open>vertices ?updated = map_entry ?t1 ((@) [?v1, ?v2]) (vertices os)\<close>
      by (simp add: label_prop_edge_record_update_def input_tl_def)
    show \<open>label ?updated = (label os)(?t1 := (label os ?t1)(?v := ?l))\<close>
      by (simp add: label_prop_edge_record_update_def input_tl_def)
    show \<open>input ?updated 1 = input os 1\<close>
      by (simp add: label_prop_edge_record_update_def input_tl_def)
    show \<open>de1 ?updated = de1 os\<close>
      by (simp add: label_prop_edge_record_update_def input_tl_def)
    show \<open>(?v, ?l) = (if min_label os ?t1 ?v2 < min_label os ?t1 ?v1
        then (?v1, min_label os ?t1 ?v2)
        else (?v2, min_label os ?t1 ?v1))\<close>
      by simp
    show \<open>wf_label_prop_updates os (set (input os 1))\<close>
      by (rule WF_input1)
  qed
  have updated_labels: \<open>\<forall>q. labels_inv (all_edges ?updated q) (min_label ?updated q)\<close>
  proof
    fix q
    show \<open>labels_inv (all_edges ?updated q) (min_label ?updated q)\<close>
    proof (rule labels_inv_input0_preserved[OF _ INV])
      show \<open>\<And>q. labels_inv (all_edges os q) (min_label os q)\<close>
        using LABELS by blast
      show \<open>input ?updated = (input os)(0 := tl (input os 0))\<close>
        by (simp add: label_prop_edge_record_update_def input_tl_def)
      show \<open>timestamps ?updated = ?t1 # timestamps os\<close>
        by (simp add: label_prop_edge_record_update_def input_tl_def)
      show \<open>graph ?updated = (graph os)(?t1 := (graph os ?t1)(?v1 := ?v2 # graph os ?t1 ?v1,
          ?v2 := ?v1 # graph os ?t1 ?v2))\<close>
        by (simp add: label_prop_edge_record_update_def input_tl_def)
      show \<open>vertices ?updated = map_entry ?t1 ((@) [?v1, ?v2]) (vertices os)\<close>
        by (simp add: label_prop_edge_record_update_def input_tl_def)
      show \<open>label ?updated = (label os)(?t1 := (label os ?t1)(?v := ?l))\<close>
        by (simp add: label_prop_edge_record_update_def input_tl_def)
      show \<open>(?v, ?l) = (if min_label os ?t1 ?v2 < min_label os ?t1 ?v1
          then (?v1, min_label os ?t1 ?v2)
          else (?v2, min_label os ?t1 ?v1))\<close>
        by simp
    qed
  qed
  have new_wf: \<open>wf_label_prop_updates ?step
      (?shift ` set (map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = (1 :: 2)) ?batch)))\<close>
    unfolding wf_label_prop_updates_def
  proof (intro ballI)
    fix x
    assume x_in: \<open>x \<in> ?shift ` set (map (\<lambda>(x, cap). (x, capability.time (cap :: (2, (nat, nat) myprod) capability)))
      (filter (\<lambda>(x, cap). out cap = 1) ?batch))\<close>
    obtain y where x_y: \<open>x = ?shift y\<close>
      and y_in: \<open>y \<in> set (map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = (1 :: 2)) ?batch))\<close>
    proof -
      show thesis
        apply (rule imageE[OF x_in])
        subgoal for y
          apply (erule that[of y])
          apply assumption
          done
        done
    qed
    have y_in_image: \<open>y \<in> (\<lambda>(x, cap). (x, capability.time cap)) `
        set (filter (\<lambda>(x, cap). out cap = (1 :: 2)) ?batch)\<close>
      by (rule y_in[unfolded set_map])
    obtain z where y_z:
      \<open>y = (case z of (x, cap) \<Rightarrow> (x, capability.time cap))\<close>
      and z_in: \<open>z \<in> set (filter (\<lambda>(x, cap). out cap = (1 :: 2)) ?batch)\<close>
    proof (rule imageE[OF y_in_image])
      fix z
      assume y_z': \<open>y = (case z of (x, cap) \<Rightarrow> (x, capability.time cap))\<close>
        and z_in': \<open>z \<in> set (filter (\<lambda>(x, cap). out cap = (1 :: 2)) ?batch)\<close>
      show thesis
      proof (rule that)
        show \<open>y = (case z of (x, cap) \<Rightarrow> (x, capability.time cap))\<close>
          by (rule y_z')
        show \<open>z \<in> set (filter (\<lambda>(x, cap). out cap = (1 :: 2)) ?batch)\<close>
          by (rule z_in')
      qed
    qed
    obtain d' cap where z_eq: \<open>z = (d', cap)\<close>
      by (cases z)
    have z_filter: \<open>z \<in> {z \<in> set ?batch. (case z of (x, cap) \<Rightarrow> out cap = 1)}\<close>
      using z_in unfolding set_filter .
    have z_mem_out: \<open>z \<in> set ?batch \<and> (case z of (x, cap) \<Rightarrow> out cap = 1)\<close>
      using z_filter unfolding mem_Collect_eq .
    have z_mem: \<open>z \<in> set ?batch\<close>
      using z_mem_out by (rule conjunct1)
    have z_out: \<open>case z of (x, cap) \<Rightarrow> out cap = 1\<close>
      using z_mem_out by (rule conjunct2)
    have batch_mem: \<open>(d', cap) \<in> set ?batch\<close>
      using z_mem unfolding z_eq .
    have out_cap: \<open>out cap = 1\<close>
      using z_out unfolding z_eq by simp
    have y_eq: \<open>y = (d', capability.time cap)\<close>
      using y_z unfolding z_eq by simp
    have x_eq: \<open>x = (d', capability.time cap -+- MyPair 0 (Suc 0))\<close>
      using x_y y_eq by simp




    have ts: \<open>myfst (capability.time cap) \<in> set (timestamps ?updated)\<close>
      by (rule label_prop_edge_batch_in_timestamps[OF batch_mem])
    have vertex: \<open>fst (de1 os d') \<in> all_vertices ?updated (myfst (capability.time cap))\<close>
      by (rule label_prop_edge_batch_all_vertices[OF refl refl EN1 DE1 updated_inv batch_mem refl refl])
    have cc: \<open>snd (de1 os d') \<in> cc_of (all_edges ?updated q) (fst (de1 os d'))\<close>
      if le: \<open>myfst (capability.time cap) \<le> q\<close> for q
    proof -
      have pair: \<open>(fst (de1 os d'), snd (de1 os d')) = de1 os d'\<close>
        by simp
      have vertex_label: \<open>(?v, ?l) = (if min_label os ?t1 ?v2 < min_label os ?t1 ?v1
          then (?v1, min_label os ?t1 ?v2)
          else (?v2, min_label os ?t1 ?v1))\<close>
        by simp
      show ?thesis
        by (rule label_prop_edge_batch_cc_of_all_edges
            [OF refl refl EN1 DE1 updated_inv batch_mem le pair vertex_label updated_labels])
    qed
    show \<open>case x of (d, t) \<Rightarrow> myfst t \<in> set (timestamps ?step) \<and>
      fst (de1 ?step d) \<in> all_vertices ?step (myfst t) \<and>
      (\<forall>t'\<ge>myfst t. snd (de1 ?step d) \<in> cc_of (all_edges ?step t') (fst (de1 ?step d)))\<close>
      using ts vertex cc x_eq
      unfolding label_prop_input0_step_state_def
      by (auto simp: Let_def)
  qed
  have outpu_step: \<open>set (outpu ?step 1) = set (outpu os 1) \<union>
      set (map (\<lambda>(x, cap). (x, capability.time (cap :: (2, (nat, nat) myprod) capability ))) (filter (\<lambda>(x, cap). out cap = 1) ?batch))\<close>
    by (simp add: batch_eq)
  show ?thesis
    using old_wf new_wf
    unfolding outpu_step image_Un Un_assoc[symmetric]
    by (simp add: wf_label_prop_updates_un)
qed

lemma wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI:
  fixes os :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
  assumes input0: \<open>input os 0 = msgs @ rest\<close>
    and EN1: \<open>en1 os = Inl\<close>
    and DE1: \<open>de1 os = projl\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and LABELS: \<open>\<forall>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and WF_input1: \<open>wf_label_prop_updates os (set (input os 1))\<close>
    and WF: \<open>wf_label_prop_updates os
      (S \<union> ((\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) ` set (outpu os 1)))\<close>
  shows \<open>wf_label_prop_updates (fst (label_prop_input0_batched os msgs))
      (S \<union> ((\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) `
        set (outpu (fst (label_prop_input0_batched os msgs)) 1)))\<close>
  using input0 EN1 DE1 INV LABELS WF_input1 WF
proof (induct msgs arbitrary: os S)
  case Nil
  then show ?case
    by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  have input_step0: \<open>input os 0 = (d, t) # (msgs @ rest)\<close>
    using Cons.prems(1) msg_eq by simp
  let ?step = \<open>label_prop_input0_step_state os d t\<close>
  have step_wf: \<open>wf_label_prop_updates ?step
      (S \<union> ((\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) ` set (outpu ?step 1)))\<close>
    by (rule wf_label_prop_updates_label_prop_input0_step_state_output1_shiftI
        [OF input_step0 Cons.prems(2) Cons.prems(3) Cons.prems(4) Cons.prems(5)
          Cons.prems(6) Cons.prems(7)])
  have input_rec: \<open>input ?step 0 = msgs @ rest\<close>
    using input_step0 by simp
  have EN1_rec: \<open>en1 ?step = Inl\<close>
    using Cons.prems(2) by simp
  have DE1_rec: \<open>de1 ?step = projl\<close>
    using Cons.prems(3) by simp
  have INV_rec: \<open>label_prop_upd_inv ?step\<close>
    by (rule label_prop_upd_inv_label_prop_input0_step_stateI
        [OF Cons.prems(4) input_step0 Cons.prems(6)])
  have labels_os: \<open>labels_inv (all_edges os q) (min_label os q)\<close> for q
    using Cons.prems(5) by (rule spec)
  have LABELS_rec: \<open>\<forall>q. labels_inv (all_edges ?step q) (min_label ?step q)\<close>
  proof
    fix q
    show \<open>labels_inv (all_edges ?step q) (min_label ?step q)\<close>
      by (rule labels_inv_label_prop_input0_step_stateI[OF labels_os Cons.prems(4) input_step0])
  qed
  have WF_input1_rec: \<open>wf_label_prop_updates ?step (set (input ?step 1))\<close>
    by (rule wf_label_prop_updates_label_prop_input0_step_stateI
        [OF Cons.prems(4) Cons.prems(6)])
  have rec: \<open>wf_label_prop_updates (fst (label_prop_input0_batched ?step msgs))
      (S \<union> ((\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) `
        set (outpu (fst (label_prop_input0_batched ?step msgs)) 1)))\<close>
    by (rule Cons.hyps[OF input_rec EN1_rec DE1_rec INV_rec LABELS_rec WF_input1_rec step_wf])
  show ?case
    using rec unfolding msg_eq
    by (cases \<open>label_prop_input0_batched ?step msgs\<close>) simp
qed


(* FIXME: move me to AntichainOrder.thy *)
lemma  frontier_less_equal_pluss_le:
  \<open>frontier_less_equal (A + B) t \<Longrightarrow> A \<le> B \<Longrightarrow> frontier_less_equal A t\<close>
  by (meson frontier_less_equal_iff2 frontier_less_equal_le_trans in_sum_antichainD)

lemma exit_scope_ifrontier_L1T0_le_L1T1_empty_loop:
  fixes c :: \<open>((3, 2) location, (nat, nat) myprod) configuration\<close>
  assumes D: \<open>dataflow_topology
    (antichain_from_list \<circ>\<circ> (raw_summary :: (3, 2) location \<Rightarrow> (3, 2) location \<Rightarrow> (nat, nat) myprod list))
    (((-+-) :: (nat, nat) myprod \<Rightarrow> (nat, nat) myprod \<Rightarrow> (nat, nat) myprod))\<close>

and empty_L1S1:
\<open>c_pts c (Loc (1 :: 3) (Src (1 :: 2))) = {#}\<^sub>z\<close>
and empty_L2T1:
\<open>c_pts c (Loc (2 :: 3) (Trg (1 :: 2))) = {#}\<^sub>z\<close>
and empty_L2S1:
\<open>c_pts c (Loc (2 :: 3) (Src (1 :: 2))) = {#}\<^sub>z\<close>
and empty_L1T1:
\<open>c_pts c (Loc (1 :: 3) (Trg (1 :: 2))) = {#}\<^sub>z\<close>
shows \<open>exit_scope myfst (ifrontier
      (antichain_from_list \<circ>\<circ> (raw_summary :: (3, 2) location \<Rightarrow> (3, 2) location \<Rightarrow> (nat, nat) myprod list))
      (-+-) c (Loc 1 (Trg 0)))
    \<le> exit_scope myfst (ifrontier
      (antichain_from_list \<circ>\<circ> (raw_summary :: (3, 2) location \<Rightarrow> (3, 2) location \<Rightarrow> (nat, nat) myprod list))
      (-+-) c (Loc 1 (Trg 1)))\<close>

proof -
  let ?su = \<open>antichain_from_list \<circ>\<circ> (raw_summary :: (3, 2) location \<Rightarrow> (3, 2) location \<Rightarrow> (nat, nat) myprod list)\<close>

  let ?L0T0 = \<open>Loc (0 :: 3) (Trg (0 :: 2))\<close>
  let ?L0S0 = \<open>Loc (0 :: 3) (Src (0 :: 2))\<close>
  let ?L1T0 = \<open>Loc (1 :: 3) (Trg (0 :: 2))\<close>
  let ?L1S1 = \<open>Loc (1 :: 3) (Src (1 :: 2))\<close>
  let ?L2T1 = \<open>Loc (2 :: 3) (Trg (1 :: 2))\<close>
  let ?L2S1 = \<open>Loc (2 :: 3) (Src (1 :: 2))\<close>
  let ?L1T1 = \<open>Loc (1 :: 3) (Trg (1 :: 2))\<close>

  have rhs_member_to_lhs_fle:
    \<open>frontier_less_equal (exit_scope myfst (ifrontier ?su (-+-) c ?L1T0)) y\<close>
    if y_in: \<open>y \<in>\<^sub>A exit_scope myfst (ifrontier ?su (-+-) c ?L1T1)\<close> for y :: nat
  proof -
    obtain a :: \<open>(nat, nat) myprod\<close> where
      a_in: \<open>a \<in>\<^sub>A ifrontier ?su (-+-) c ?L1T1\<close> and y_eq: \<open>myfst a = y\<close>
      using y_in by (rule exit_scope_memberE)
    have rhs_fle: \<open>frontier_less_equal (ifrontier ?su (-+-) c ?L1T1) a\<close>
      using a_in unfolding frontier_less_equal_iff2 by blast
    have decomp:
      \<open>\<exists>l s t. s \<in>\<^sub>A graph.path_weight ?su l ?L1T1 \<and>
        frontier_less_equal (frontier (c_pts c l)) t \<and> a = t -+- s\<close>
      apply (rule frontier_less_equal_ifrontierE[where su = ?su and c = c and l' = ?L1T1 and t = a])
       apply (rule rhs_fle)
      apply (rule D)
      done
    obtain l :: \<open>(3, 2) location\<close> and s :: \<open>(nat, nat) myprod\<close> and t :: \<open>(nat, nat) myprod\<close> where
      s_in: \<open>s \<in>\<^sub>A graph.path_weight ?su l ?L1T1\<close>
      and source_fle: \<open>frontier_less_equal (frontier (c_pts c l)) t\<close>
      and a_eq: \<open>a = t -+- s\<close>
      using decomp by blast



    have loc_cases:
      \<open>l = ?L0T0 \<or> l = ?L0S0 \<or> l = ?L1T0 \<or>
       l = ?L1S1 \<or> l = ?L2T1 \<or> l = ?L2S1 \<or> l = ?L1T1\<close>
      using loc_3_2_cases[of l] s_in by auto
    consider (base) \<open>l = ?L0T0 \<or> l = ?L0S0 \<or> l = ?L1T0\<close> |
      (empty) \<open>l = ?L1S1 \<or> l = ?L2T1 \<or> l = ?L2S1 \<or> l = ?L1T1\<close>
      using loc_cases by blast
    then show ?thesis
    proof cases
      case base
      have zero_in: \<open>(0 :: (nat, nat) myprod) \<in>\<^sub>A graph.path_weight ?su l ?L1T0\<close>
        using base by auto
      have lhs_fle0: \<open>frontier_less_equal (ifrontier ?su (-+-) c ?L1T0) (t -+- 0)\<close>
        using frontier_less_equal_ifrontierI[where su = ?su and c = c and l = l
            and l' = ?L1T0 and t = t and t' = \<open>0 :: (nat, nat) myprod\<close>]
          D zero_in source_fle
        by blast
      have lhs_fle: \<open>frontier_less_equal (ifrontier ?su (-+-) c ?L1T0) t\<close>
        using lhs_fle0 by simp
      obtain b :: \<open>(nat, nat) myprod\<close> where
        b_in: \<open>b \<in>\<^sub>A ifrontier ?su (-+-) c ?L1T0\<close> and b_le: \<open>b \<le> t\<close>
        using lhs_fle unfolding frontier_less_equal_iff2 by blast
      have s_eq: \<open>s = MyPair 0 1\<close>
        using base s_in by (auto simp add: member_antichain.rep_eq)
      have myfst_b_le_y: \<open>myfst b \<le> y\<close>
        using myfst_mono[OF b_le] a_eq y_eq s_eq by simp
      have \<open>frontier_less_equal (exit_scope myfst (ifrontier ?su (-+-) c ?L1T0)) (myfst b)\<close>
        using b_in by (rule frontier_less_equal_exit_scopeI)
      then show ?thesis
        using myfst_b_le_y by (rule frontier_less_equal_trans)
    next
      case empty
      then have False
        using source_fle empty_L1S1 empty_L2T1 empty_L2S1 empty_L1T1 by auto
      then show ?thesis by simp
    qed
  qed
  show ?thesis
    unfolding less_eq_antichain_def
  proof safe
    fix y :: nat
    assume y_in: \<open>y \<in>\<^sub>A exit_scope myfst (ifrontier ?su (-+-) c ?L1T1)\<close>
    obtain x :: nat where x_in: \<open>x \<in>\<^sub>A exit_scope myfst (ifrontier ?su (-+-) c ?L1T0)\<close>
      and x_le: \<open>x \<le> y\<close>
      using rhs_member_to_lhs_fle[OF y_in] unfolding frontier_less_equal_iff2 by blast
    show \<open>\<exists>x. x \<in>\<^sub>A exit_scope myfst (ifrontier ?su (-+-) c ?L1T0) \<and> x \<le> y\<close>
      using x_in x_le by blast
  qed
qed








lemma wf_label_prop_updates_clean_image[simp]:
  \<open>wf_label_prop_updates os ((\<lambda>(d, t). (d, t -+- MyPair 0 g)) ` S) \<longleftrightarrow>
   wf_label_prop_updates os S\<close>
  unfolding wf_label_prop_updates_def
  by auto

(* TODO: Move. *)
lemma label_prop_label_batch_cc_of_all_edges:
  assumes \<open>(updated_os :: (_, nat, nat, nat) label_propagation_state) = label_prop_label_record_update (input_tl old_os 1) (myfst t) vertex assigned_label\<close>
    \<open>batch = label_prop_label_batch old_os updated_os (myfst t) vertex assigned_label t\<close>
    \<open>en1 old_os = Inl\<close> \<open>de1 old_os = projl\<close> \<open>label_prop_upd_inv old_os\<close> \<open>(d, cap) \<in> set batch\<close>
    \<open>myfst (capability.time cap) \<le> t'\<close> \<open>(v, w) = de1 old_os d\<close>
    \<open>\<forall>t. labels_inv (all_edges updated_os t) (min_label updated_os t)\<close>
    \<open>assigned_label = min (min_label old_os (myfst t) vertex) l\<close>
    \<open>vertex \<in> edge_vertices (all_edges updated_os (myfst t))\<close>
  shows \<open>w \<in> cc_of (all_edges old_os t') v\<close>
proof -
  let ?t0 = \<open>myfst (capability.time cap)\<close>
  have myfst_t_t': \<open>myfst t \<le> t'\<close> using assms(2-4,6,7)
    by (force simp add: label_prop_label_batch_def label_prop_neighbor_batch_def)
  have w_assigned_label: \<open>w = assigned_label\<close> using assms(2-4,6,8)
    by (force simp add: label_prop_label_batch_def label_prop_neighbor_batch_def)
  have \<open>v \<in> set (neighbors old_os ?t0 vertex)\<close>
    using assms(2-4,6,8)
    by (force simp add: label_prop_label_batch_def label_prop_neighbor_batch_def)
  hence \<open>reachable (all_edges updated_os ?t0) vertex v\<close>
    using neighbors_reachable[OF assms(5)] by (simp add: assms(1))
  hence reachable_vertex_v: \<open>reachable (all_edges updated_os t') vertex v\<close>
    using all_edges_mono[OF assms(7)] reachable_subset by metis
  have \<open>min_label updated_os (myfst t) vertex = assigned_label\<close>
  proof -
    let ?A = \<open>(\<lambda>t'. label updated_os t' vertex) ` {t' \<in> set (timestamps updated_os). t' \<le> myfst t}\<close>
    have \<open>\<forall>l \<in> ?A. assigned_label \<le> l\<close>
      by (simp add: assms(1,10) label_prop_label_record_update_def)
        (insert min_label_le_current_labelI min_label_mono_time  le_trans min.coboundedI1, blast)
    then show ?thesis using Min_insert2[where a=assigned_label and A=\<open>?A\<close>] unfolding min_label_def
      by (force simp add: assms(1) label_prop_label_record_update_def)
  qed
  hence \<open>assigned_label \<in> cc_of (all_edges updated_os (myfst t)) vertex\<close>
    using assms(9,11) unfolding labels_inv_def by fast
  moreover have \<open>all_edges updated_os (myfst t) \<subseteq> all_edges updated_os t'\<close>
    by (rule all_edges_mono[OF myfst_t_t'])
  ultimately have \<open>assigned_label \<in> cc_of (all_edges updated_os t') vertex\<close> using cc_of_mono by blast
  hence \<open>assigned_label \<in> cc_of (all_edges updated_os t') v\<close>
    using cc_of_eq_if_reachable[OF reachable_vertex_v] by blast
  thus ?thesis by (simp add: assms(1) w_assigned_label)
qed

(* FIXME: move me to Timely_Operator_State.thy. *)
lemma ocaps_drop_caps_port_disjoint[simp]:
  fixes os :: "('p, 'd, 't :: plus, 'more) operator_state_scheme"
    and caps :: "('p, 't) capability list"

assumes "\<And>cap. cap \<in> set caps \<Longrightarrow> out cap \<noteq> p"
shows "ocaps (drop_caps os caps) p = ocaps os p"
proof -
  have "filter (\<lambda>cap. out cap = p) caps = []"
    using assms by (induction caps) auto
  then show ?thesis
    unfolding drop_caps_def by simp
qed


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
    \<open>\<forall>(d, _) \<in> set (outpu (os 2) 1 @ input (os 2) 1 @ cbufs (2, 1)). is_en1 os_label_prop d\<close>
    and buffers_inv:
    \<open>chns = outputs_at_target (summ sg) os >> cbufs >> inputs_at_target os\<close>
    \<open>cbufs (0, 0) = []\<close>
    and dataplane_inv:
    \<open>dataplane_tracker_inv os cbufs sg\<close>
    and csets_inv:
    \<open>SP = cimage
      (\<lambda>t. ((1, 0), (Inr (ccs
        (set (icoll (map (\<lambda>(x, t'). Data t' (projl x)) (chns (1, 0)) @@- lxs) t)
        \<union> all_edges os_label_prop (myfst t))), t)))
      (cUn (cUn (ts lxs) (cset_from_list (map snd (chns (1, 0))))) ((\<lambda> t. MyPair t 0) |`| (cfilter (\<lambda> t. t \<in> myfst ` set (ocaps (os 1) 0)) (cset_from_list (timestamps os_label_prop)))))\<close>
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
    \<open>wf_label_prop_updates os_label_prop (set (chns (1, 1) @ map (\<lambda>(d, t). (d, t + MyPair 0 1)) (chns (2, 1))))\<close>
  shows \<open>set_op S D (dataflow_op sg (G_op os_input os_label_prop (os 2) cbufs))
         \<approx> set_spec_op (cUn (cUn S SO) SP) D\<close>
  using assms
proof (coinduction arbitrary: S SO SP D lxs os os_input os_label_prop cbufs chns sg T G V L
    rule: weakBisimWeakUptoBisimCong)
  case SIM1
  note subgraph_inv = SIM1(1,2)
    and os_inv = SIM1(3-12)
    and buffers_inv = SIM1(13,14)
    and dataplane_inv = SIM1(15)
    and csets_inv = SIM1(16,17)
    and input_stream_inv = SIM1(18)
    and label_prop_inv = SIM1(19-)

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
        using os_inv(4,10) apply (simp add: BENQ_def operator_state.defs(3))
        using buffers_inv(2) apply (simp add: BENQ_def)
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
        using label_prop_inv(7) apply (simp add: os_inv(4,7) buffers_inv BULK_BENQ_def BENQ_def outputs_at_target_raw_summary subgraph_inv(1) image_Un operator_state.defs(3) Un_assoc)
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
        using os_inv(4,10) apply (simp add: BTL_def operator_state.defs(3))
        using buffers_inv(2) apply (simp add: BTL_def)
                   apply (rule dataplane_tracker_inv_consumes[OF dataplane_inv _ D G, where xs=\<open>tl (cbufs (1, p))\<close>])

                   apply (simp add: BHD_def)
        subgoal
          apply (subgoal_tac "MyPair (myfst t) 0 \<in> snd ` set (((outputs_at_target (summ sg) os >> cbufs) >> inputs_at_target os) (1, 0))")
          subgoal
            apply (simp add: csets_inv(1) buffers_inv os_inv(4,7) operator_state.defs(3) consumes_def)
            apply (subgoal_tac "raw_summary (Loc (1 :: 3) (Trg (0 :: 2))) (Loc (1 :: 3) (Src (0 :: 2))) = [0]")
            subgoal
              apply simp
              apply (rule cimage_cong)
              subgoal
                by auto
              subgoal
                by auto
              done
            subgoal
              unfolding raw_summary_def
                zero_myprod_def by force
            done
          subgoal
            using label_prop_inv(4)[unfolded buffers_inv] apply -
            unfolding BULK_BENQ_def inputs_at_target_def subgraph_inv(1) outputs_at_target_raw_summary BHD_def
            apply clarsimp
            apply (metis (no_types, lifting) Un_iff hd_in_set img_snd myprod.exhaust_sel)
            done
          done
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
        using label_prop_inv(7) apply (simp add: os_inv(4,7) operator_state.defs(3) buffers_inv)
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
          using os_inv(4,10) apply (simp add: operator_state.defs(3))
          using buffers_inv(1) apply fast
          using buffers_inv(2) apply simp
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
          using label_prop_inv(7) apply (simp add: os_inv(4) buffers_inv)
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
          using os_inv(4,10) apply (simp add: operator_state.defs(3))                    apply (simp add: buffers_inv BENQ_def BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def fun_eq_iff produce_def)
          using buffers_inv(2) apply simp
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
          using label_prop_inv(7) apply (simp add: os_inv(4) BENQ_def)
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
          using os_inv(4,10) apply simp                    apply (simp add: buffers_inv)
          using buffers_inv(2) apply simp
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
          using label_prop_inv(7) apply (simp add: os_inv(4) buffers_inv outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def inputs_at_target_def)
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
          using os_inv(4,10) apply simp                    apply (simp add: buffers_inv)
          using buffers_inv(2) apply simp
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
          using label_prop_inv(7) apply (simp add: os_inv(4) buffers_inv outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def inputs_at_target_def)
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
        using os_inv(6,10) apply (simp add: label_prob_ty2_check_def)
        using buffers_inv(2) apply (simp add: BENQ_def)
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
        apply (subst wf_label_prop_updates_cong[where os'=os_label_prop
              and S'=\<open>set (chns (1, 1) @ map (\<lambda>(d, t). (d, t -+- MyPair 0 1)) (chns (2, 1)))\<close>])
        using label_prop_inv(7) apply (auto simp add: os_inv(4) operator_state.defs(3) buffers_inv outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def BENQ_def inputs_at_target_def image_Un)
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
        using os_inv(10) apply (simp add: BHD_def BTL_def split_beta )
                  apply (metis Un_iff in_hd_or_tl_conv)
        using buffers_inv(2) apply (simp add: BTL_def)
                apply (rule dataplane_tracker_inv_consumes[OF dataplane_inv _ D G, where xs=\<open>tl (cbufs (2, 1))\<close>])
                apply (simp add: BHD_def)
        using input_stream_inv apply simp
        using label_prop_inv(1) apply (simp add: os_inv(4,7) operator_state.defs(3))
        using label_prop_inv(2) apply (simp add: os_inv(4,7) operator_state.defs(3) consumes_def)
        using label_prop_inv(3) apply simp
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def BTL_def BENQ_def)
          apply (rule label_prop_inv(5))
        using label_prop_inv(6) apply simp
        using label_prop_inv(7)
        apply (subst wf_label_prop_updates_cong[OF refl refl refl refl _])
         defer
         apply assumption
        apply (simp add: buffers_inv BULK_BENQ_def BTL_def BENQ_def BHD_def image_set map_consI(2) flip: set_append)
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
                      apply (subgoal_tac "ocaps os_label_prop 0 = ocaps (os 1) 0")
                      subgoal
                        apply (cases "frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t)")
                        subgoal
                          apply (clarsimp del: disjCI simp add: cimage_iff inputs_at_target_def cUn_assoc cimage_cUn)
                          apply (elim disjE; (clarsimp del: disjCI)?; (elim disjE)?; (clarsimp del: disjCI)?; hypsubst_thin?)
                          subgoal for t'
                            apply (rule disjI2)
                            apply (rule disjI2)
                            apply (rule disjI2)
                            apply (rule disjI2)
                            apply (rule disjI2)
                            apply (rule disjI2)
                            apply (rule cBexI[of _ "myfst  t'"])
                             apply (simp_all add: image_iff)
                            apply (rule bexI[of _ " t'"])
                             apply (simp_all add: filter_True comp_def drop_caps_def image_iff)
                            done
                          done
                        subgoal
                          apply (clarsimp del: disjCI simp add: cimage_iff inputs_at_target_def cUn_assoc cimage_cUn)
                          apply (elim disjE; (clarsimp del: disjCI)?; (elim disjE)?; (clarsimp del: disjCI)?; hypsubst_thin?)
                          subgoal for  t'
                            apply (rule disjI2)
                            apply (rule disjI1)
                            apply (rule cBexI[of _ "(_, Cap (MyPair (myfst  t') 0) 0)"])
                             apply simp_all
                            unfolding label_prop_output_batch_def
                            apply (simp add: image_iff)
                            apply (rule exI[of _  t'])
                            apply (simp add: operator_state.defs os_inv(4))
                            apply (subgoal_tac "icoll (llist_of (map (\<lambda>(x, t'). Data t' (projl x)) (input (os 1) 0) @ map (\<lambda>(x, t'). Data t' (projl x)) (cbufs (1, 0)) @ map (\<lambda>(x, t'). Data t' (projl x)) (outpu (os 0) 0))) (MyPair (myfst  t') 0) = []")
                            subgoal
                              apply (subgoal_tac "icoll lxs (MyPair (myfst  t') 0) = []")
                              subgoal
                                apply simp
                                apply (rule sym)
                                apply (rule components_from_labels_correct)
                                subgoal
                                  using label_prop_inv(1)[unfolded os_inv(4) operator_state.defs, simplified, rule_format, of "myfst  t'"]
                                  by auto
                                subgoal
                                  using label_prop_inv(2)[unfolded os_inv(4) operator_state.defs, simplified, rule_format, of "myfst  t'"] 
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
                          done
                        done
                      subgoal
                        by (simp add: operator_state.defs os_inv(4))
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
                         apply simp
                         apply force
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
                    subgoal  for t'
                      unfolding drop_caps_def
                      apply (clarsimp del: disjCI simp add: filter_True comp_def)
                      apply force
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
          using os_inv(10) apply simp
          using buffers_inv(2) apply simp
          subgoal premises aux
            apply (rule iffD1[OF dataplane_tracker_inv_clean, rotated 2, of _ _ sg "upfro sg"])
              apply (rule dataplane_tracker_inv_produces_drops[OF D, where nid=1 and os=os 
                  and drops = "\<lambda> p. if p = 1
                         then []
                         else filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0)"
                  and produs="map (\<lambda> t . (0, MyPair t 0, 1)) (remdups (map myfst (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0))))"
                  and oputs="(\<lambda> p. if p = 1 then [] else map (\<lambda>t. (en2 os_label_prop (components_from_labels (all_edges os_label_prop t) (min_label os_label_prop t)), (MyPair t 0)))
                          (remdups (map myfst (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (front os_label_prop 0 + front os_label_prop 1)) (myfst t) \<and> myfst t \<in> set (timestamps os_label_prop)) (ocaps os_label_prop 0)))))"])
                         apply (rule refl)+
                    prefer 9
            subgoal
              apply (intro allI impI conjI)
                     apply simp
              subgoal
                apply (rule ext)+
                unfolding produces_def drop_caps_def
                apply auto
                subgoal for x
                  apply (subgoal_tac "x = 0")
                  subgoal
                    apply clarsimp
                    apply (subst (2) filter_True)
                     apply (simp_all add: comp_def)
                    done
                  subgoal
                    by (metis num2_neq(2))
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
          subgoal
            apply (subst wf_label_prop_updates_cong)
            using label_prop_inv(7)
            by (auto simp add: produces_def buffers_inv outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def inputs_at_target_def label_prop_output_batch_def)
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
                        apply (subgoal_tac \<open>myfst t \<in> myfst ` set (ocaps (os 1) (0 :: 2))\<close>)
                         prefer 2
                        subgoal
                          apply (subgoal_tac \<open>t \<in> set (ocaps (os 1) (0 :: 2))\<close>)
                           apply force
                          apply (insert label_prop_inv(6) aux(2) os_inv(7))
                          unfolding input_ocaps_inv_def
                          apply (drule spec[where x=\<open>0 :: 2\<close>])
                          apply (drule spec[where x=\<open>0 :: 2\<close>])
                          apply (drule bspec[where x=t])
                           apply (simp add: os_inv(4) operator_state.defs)
                          apply (drule bspec[where x=\<open>MyPair 0 0\<close>])
                           apply (simp add: raw_summary_def)
                          apply (simp add: MyPair_zero_zero_sum2)


                          done


                        apply (simp only: cfilter_cinsert)
                        apply (simp add: release_caps_def drop_caps_def add_caps_def trace_simp
                            list_diff_append_cancel_right)

                        apply (subst (1) all_edges_eq[rotated, where V=V and label_sync=L and input_sync="input (os 1)"])
                        subgoal 
                          using label_prop_inv(5)[unfolded os_inv(4) operator_state.defs]
                          by (simp add: label_prop_upd_inv_def)
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
                                apply (subst (2) cfilter_False)
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
                  apply simp
                  apply (rule label_prob_ty2_check_producesI)
                  subgoal
                    using os_inv(4,6) by auto
                  subgoal
                    using os_inv(4,6) aux(1,2,3) apply -
                    unfolding label_prob_ty2_check_def add_caps_def input_tl_def label_prop_edge_batch_def label_prop_edge_record_update_def label_prop_neighbor_batch_def
                    by (auto 0 0 simp add: os_inv(1,4) image_iff operator_state.defs produces_def release_caps_def drop_caps_def)
                  subgoal
                    using os_inv(4,6) aux(1,2,3) apply -
                    unfolding label_prob_ty2_check_def add_caps_def input_tl_def label_prop_edge_batch_def label_prop_edge_record_update_def label_prop_neighbor_batch_def
                    by (auto 0 0 simp add: os_inv(1,4) image_iff operator_state.defs produces_def release_caps_def drop_caps_def)
                  done
                subgoal premises aux
                  unfolding add_caps_def
                  using os_inv(7) by auto
                using os_inv(8) apply simp
                using os_inv(9) apply simp
                using os_inv(10) apply simp
                using buffers_inv(2) apply simp
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
                  using label_prop_inv(7)
                  by (auto intro: wf_label_prop_updates_subset simp add: buffers_inv BULK_BENQ_def inputs_at_target_def operator_state.defs os_inv(4) input_tl_def release_caps_def drop_caps_def produces_def)
                subgoal premises aux
                  apply simp
                  apply (rule input_ocaps_inv_release_capsI)
                  apply (rule input_ocaps_inv_drop_produces_add_capsI)
                  using label_prop_inv(6) input_ocaps_inv_input_tlI apply fast
                  done
                subgoal
                  apply (subst wf_label_prop_updates_Un[where S=\<open>set (chns (1, 1) @ map (\<lambda>(d, t). (d, t -+- MyPair 0 1)) (chns (2, 1)))\<close>
                        and S'=\<open>set (map (\<lambda>(d, cap :: (2, (nat, nat) myprod) capability). (d, capability.time cap + MyPair 0 1)) (label_prop_edge_batch os_label_prop
             (label_prop_edge_record_update (os_label_prop\<lparr>input := (input os_label_prop)(0 := xs)\<rparr>) (myfst t) v1 v2 l1 l2) (myfst t) l1 l2 t))\<close>])
                   apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def input_tl_def image_Un flip: set_filter)
                   apply (subst filter_True)
                    apply (simp add: label_prop_edge_batch_def label_prop_neighbor_batch_def)
                    apply fastforce
                   apply fast
                  apply (rule conjI)
                   apply (rule wf_label_prop_updates_os_mono[OF label_prop_inv(7) _ _ _ refl])
                     apply simp
                    apply (clarsimp simp add: label_prop_edge_record_update_def)
                   apply (intro allI conjI)
                    apply (clarsimp simp add: label_prop_edge_record_update_def)
                   apply (force simp add: produces_def label_prop_edge_record_update_def)
                  apply simp
                  apply (clarsimp del: disjCI simp add: wf_label_prop_updates_def)
                  subgoal for d' cap
                    apply (intro conjI allI)
                      apply (clarsimp del: disjCI simp add: image_iff set_neighbors label_prop_neighbor_batch_def label_prop_edge_batch_def add_caps_def label_prop_edge_record_update_def)
                      apply fastforce
                     apply (rule label_prop_edge_batch_all_vertices[OF _ refl _ _ _ _ refl refl, of _ os_label_prop \<open>myfst t\<close> _ _ l1 l2 d' cap])
                         apply (simp add: input_tl_def label_prop_edge_record_update_def)
                    using os_inv(4) apply (simp add: operator_state.defs(3))
                    using os_inv(4) apply (simp add: operator_state.defs(3))
                    subgoal
                      apply (rule label_prop_upd_inv_input0_preserved)
                              apply (rule label_prop_inv(5))
                             apply (simp_all add: operator_state.defs os_inv(4))
                      unfolding label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def release_caps_def drop_caps_def add_caps_def
                      using label_prop_inv(7)
                      by (auto intro: wf_label_prop_updates_subset simp add: buffers_inv BULK_BENQ_def inputs_at_target_def operator_state.defs os_inv(4) input_tl_def release_caps_def drop_caps_def produces_def)
                     apply (simp add: input_tl_def)
                    apply (rule impI)
                    apply (rule label_prop_edge_batch_cc_of_all_edges[OF refl refl])
                    using os_inv(4) apply (simp add: operator_state.defs(3))
                    using os_inv(4) apply (simp add: operator_state.defs(3))
                    subgoal
                      apply (rule label_prop_upd_inv_input0_preserved)
                              apply (rule label_prop_inv(5))
                             apply (simp_all add: operator_state.defs os_inv(4))
                      unfolding label_prop_edge_record_update_def input_tl_def label_prop_edge_batch_def label_prop_neighbor_batch_def release_caps_def drop_caps_def add_caps_def
                      using label_prop_inv(7)
                      by (auto intro: wf_label_prop_updates_subset simp add: buffers_inv BULK_BENQ_def inputs_at_target_def operator_state.defs os_inv(4) input_tl_def release_caps_def drop_caps_def produces_def)
                        apply (simp add: input_tl_def)
                       apply assumption
                      apply simp
                     apply (erule sym)
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
                    done
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
                               (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t)))
                           (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t))
                         (map snd (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t)))
                       1)"])
                apply (rule exI[of _ "release_caps
                       (drop_caps
                         (produces
                           (add_caps (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l))
                             (map snd
                               (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t)))
                           (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t))
                         (map snd (label_prop_label_batch os_label_prop (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t)))
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
                        apply (subst (2) cfilter_False)
                        subgoal
                          unfolding label_prop_label_batch_def label_prop_neighbor_batch_def
                          by auto
                        subgoal
                          apply simp
                          apply (rule cimage_cong)
                          subgoal
                            unfolding input_tl_def
                            by (simp add: release_caps_def drop_caps_def produces_def add_caps_def)
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
                using os_inv(10) apply simp
                using buffers_inv(2) apply simp
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
                    apply (rule wf_label_prop_updates_subset[OF label_prop_inv(7)])
                    apply (fastforce simp add: buffers_inv BULK_BENQ_def inputs_at_target_def os_inv(4) operator_state.defs(3))
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
                  using label_prop_inv(7) apply (auto intro: wf_label_prop_updates_subset simp add:  buffers_inv BULK_BENQ_def inputs_at_target_def os_inv(4) operator_state.defs(3))
                  done
                subgoal
                  apply simp
                  apply (rule input_ocaps_inv_release_capsI)
                  apply (rule input_ocaps_inv_drop_produces_add_capsI)
                  apply (rule input_ocaps_inv_input_tlI)
                  using label_prop_inv(6) apply -
                  apply (simp add: os_inv(4) operator_state.defs)
                  done
                subgoal
                  apply (subst wf_label_prop_updates_Un[where S=\<open>set (tl (input (os 1) 1)) \<union> set (cbufs (1, 1)) \<union> set (outpu (os 2) 1) \<union> set (map (\<lambda>(d, t). (d, t -+- MyPair 0 1)) (chns (2, 1)))\<close>
                        and S'=\<open>set (map (\<lambda>(d, cap :: (2, (nat, nat) myprod) capability). (d, capability.time cap + MyPair 0 1)) (label_prop_label_batch os_label_prop
                     (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v (min (min_label os_label_prop (myfst t) v) l)) (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t))\<close>])
                   apply (simp add: os_inv(4) operator_state.defs(3) buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def input_tl_def image_Un flip: set_filter)
                   apply (subst filter_True)
                    apply (simp add: label_prop_label_batch_def label_prop_neighbor_batch_def)
                   apply (simp add: image_image split_beta Un_assoc)
                  apply (rule conjI)
                   apply (rule wf_label_prop_updates_subset[where S=\<open>set (chns (1, 1) @ map (\<lambda>(d, t). (d, t -+- MyPair 0 1)) (chns (2, 1)))\<close>])
                    apply (rule wf_label_prop_updates_os_mono[OF label_prop_inv(7) _ _ _ refl])
                      apply simp
                     apply simp
                    apply (intro allI conjI)
                     apply simp
                    apply (simp add: produces_def)
                   apply (simp add: os_inv(4) operator_state.defs(3) buffers_inv BULK_BENQ_def inputs_at_target_def outputs_at_target_raw_summary subgraph_inv(1))
                   apply blast
                  apply (clarsimp simp add: wf_label_prop_updates_def)
                  subgoal for d' cap
                    apply (intro conjI allI)
                      apply (rule label_prop_label_batch_in_timestamps[of d' cap os_label_prop _ \<open>myfst t\<close> v \<open>(min (min_label os_label_prop (myfst t) v) l)\<close> t])
                      apply blast
                     apply (rule label_prop_label_batch_all_vertices[OF refl refl, of \<open>input_tl os_label_prop 1\<close> d' cap \<open>myfst t\<close> v _ \<open>(min (min_label os_label_prop (myfst t) v) l)\<close> t])
                          apply (simp add: os_inv(4) operator_state.defs(3))
                         apply (simp add: os_inv(4) operator_state.defs(3))
                    using label_prop_inv(5) apply (simp add: input_tl_def label_prop_upd_inv_def)
                       apply (simp add: label_prop_label_batch_def label_prop_neighbor_batch_def input_tl_def neighbors_def)
                      apply (rule refl)
                     apply simp
                    apply (rule impI)
                    apply (rule label_prop_label_batch_cc_of_all_edges[OF refl refl])
                    using os_inv(4) apply (simp add: operator_state.defs(3))
                    using os_inv(4) apply (simp add: operator_state.defs(3))
                          apply (rule label_prop_inv(5))
                         apply blast
                        apply assumption
                       apply simp
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
                        apply (rule wf_label_prop_updates_subset[OF label_prop_inv(7)])
                        apply (fastforce simp add: buffers_inv BULK_BENQ_def inputs_at_target_def os_inv(4) operator_state.defs(3))
                        done
                      done
                     apply (rule refl)
                    apply simp
                    apply (insert label_prop_inv(7))
                    apply (drule wf_label_prop_updates_subset[where S'=\<open>set (input os_label_prop 1)\<close>])
                     apply (force simp add: buffers_inv BULK_BENQ_def inputs_at_target_def os_inv(4) operator_state.defs(3))
                    apply (unfold wf_label_prop_updates_def)
                    apply (drule bspec[of _ _ \<open>(d, t)\<close>])
                     apply simp
                    apply (simp add: edge_vertices_all_edges[OF label_prop_inv(5)])
                    done
                  done
                done
              done
            done
          done
        subgoal
          apply (clarsimp split: list.splits)
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
          apply (rule exI[of _ \<open>os(1 := release_caps (os 1) 1)\<close>])
          apply (rule exI[of _ \<open>release_caps os_label_prop 1\<close>])
          apply (rule exI[of _ cbufs])
          apply (rule exI[of _ sg])
          apply (intro conjI)
                              apply (simp add: dataflow_tree_to_operator_def os_inv(1))
                              apply (simp add: csets_inv buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def release_caps_def drop_caps_def cimage_cUn)
                              apply (rule subgraph_inv(1))
                             apply (rule subgraph_inv(2))
          using os_inv(2) apply simp
          using os_inv(3) apply simp
          using os_inv(4) apply (simp add: release_caps_def drop_caps_def operator_state.defs)
          using os_inv(1,5) apply (simp add: release_caps_def drop_caps_def)
          using os_inv(6) apply simp
          using os_inv(7) apply (simp add: release_caps_def drop_caps_def)

          using os_inv(8) apply (simp add: input_ocaps_inv_def release_caps_def drop_caps_def)
          using os_inv(9) apply simp
          using os_inv(10) apply force
          using buffers_inv(2) apply simp
          subgoal
            apply (rule dataplane_tracker_inv_release_caps_update[where nid=1 and os'=\<open>os 1\<close> and p=1, OF D])
            using dataplane_inv apply simp
            using G subgraph_inv(2) apply simp
            apply (rule subgraph_inv(2))
            done


          using input_stream_inv apply simp
          using label_prop_inv(1) apply simp
          using label_prop_inv(2) apply (simp add: release_caps_def drop_caps_def)
          using label_prop_inv(3) apply simp
          using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def release_caps_def drop_caps_def)
          using label_prop_inv(5) apply simp
           apply simp
           apply (rule input_ocaps_inv_release_capsI)
          using label_prop_inv(6) os_inv(4) apply (simp add: operator_state.defs)
          using label_prop_inv(7) apply (simp add: buffers_inv image_Un Un_assoc BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def release_caps_def drop_caps_def)
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
        using os_inv(10) apply force
        using buffers_inv(2) apply simp
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
          apply (intro impI conjI; clarsimp?)
          subgoal 
            by (clarsimp dest!: num2_neq(2) simp add: filter_True filter_False comp_def)
          subgoal
            by (clarsimp simp add: filter_True filter_False)
          done
        using input_stream_inv apply simp
              apply (rule label_prop_inv(1))
        using label_prop_inv(2) apply simp
        using label_prop_inv(3) apply simp
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
          apply (rule label_prop_inv(5))
        using label_prop_inv(6) apply simp
        using label_prop_inv(7) apply (simp add: buffers_inv image_Un Un_assoc BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def filter_True split_beta)
        done
      subgoal for _ d t
        apply (simp add: ran_loop_wire cUNIV_def cin_def)
        apply hypsubst_thin
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
        apply (rule exI[of _ \<open>os(1 := consumes (os 1) 1 t d)\<close>])
        apply (rule exI[of _ \<open>consumes os_label_prop 1 t d\<close>])
        apply (rule exI[of _ \<open>BTL (1, 1) cbufs\<close>])
        apply (rule exI[of _ sg])
        apply (intro conjI)
                            apply (clarsimp simp add: dataflow_tree_to_operator_def
            intro!: arg_cong[where f=\<open>set_op _ _\<close>] arg_cong[where f=\<open>dataflow_op _\<close>]
            arg_cong[where f=\<open>map_op _ _\<close>])
                            apply (rule comp_op_buf_cong[OF refl])
        using os_inv(1) apply simp
                            apply (rule loop_op_buf_cong[OF refl])
                            apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
                            apply (rule comp_op_buf_cong[OF refl refl refl])
                            apply (simp add: ran_comp_wire BTL_def)
                            apply (simp add: ran_loop_wire BTL_def map_tl)
                            apply (simp add: BTL_def ran_def split: sum.splits)
                            apply (metis prod.exhaust sum.exhaust)
                            apply (simp add: csets_inv buffers_inv BULK_BENQ_def BENQ_def BTL_def)
                            apply (subgoal_tac \<open>timestamps (consumes os_label_prop 1 t d) = timestamps os_label_prop\<close>)
                            apply (simp add: cimage_cUn)
                            apply (simp add: consumes_def add_caps_def os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                            apply simp
                            apply (rule subgraph_inv(1))
                           apply (rule subgraph_inv(2))
        using os_inv(2) apply simp
        using os_inv(3) apply simp
        using os_inv(4) apply (simp add: consumes_def add_caps_def operator_state.defs(3))
        using os_inv(1,5) apply (simp add: ty1_check_def BTL_def)
        using os_inv(1,4-6)
                      apply (simp add: ty1_check_def label_prob_ty2_check_def operator_state.defs(3) BTL_def BHD_def)
                      apply (erule conjE)
                      apply (rotate_tac 5)
                      apply (drule spec[of _ 1])
                      apply (simp add: Ball_def)
                      apply (meson img_fst in_fst_imageE in_set_tlD)
        using os_inv(7) apply simp
        using os_inv(8) apply simp
        using os_inv(9) apply simp
        using os_inv(10) apply (simp add: BTL_def)
        using buffers_inv(2) apply (simp add: BTL_def)
                apply (rule dataplane_tracker_inv_consumes[OF dataplane_inv _ D G, where xs=\<open>tl (cbufs (1, 1))\<close>])
                apply (simp add: BHD_def)
        using input_stream_inv apply simp
        using label_prop_inv(1) apply (simp add: os_inv(4,7) operator_state.defs(3))
        using label_prop_inv(2) unfolding min_label_def apply (simp add: consumes_def all_edges_def all_vertices_def neighbors_def)
        subgoal
          using dataplane_inv unfolding dataplane_tracker_inv_def
          apply (simp add: label_prop_inv(3))
          apply (elim exE conjE)
          subgoal premises prems for caps
            using prems(1,6-8) prems(2)[symmetric] unfolding front_inv_def imp_front_inv_def chnls_imp_front_inv_def
            apply simp
            apply (rule contrapos_pp[OF _ frontier_less_equal_exit_scope, rotated, where t1=t])
             apply simp
            apply (drule spec2[of _ 1 1])
            apply (drule spec[of _ \<open>Loc 1 (Trg 1)\<close>])
            apply (drule spec2[of _ 1 1])
            apply (drule bspec[of _ _ \<open>(d, t)\<close>])
             apply (simp add: BULK_BENQ_def BHD_def)
             apply (rule disjI1)
             apply (metis list.set_sel(1))
            apply (rule frontier_less_equal_le_trans[rotated])
             apply (rule order.trans)
              apply assumption
             apply assumption
            apply simp
            done
          done
        using os_inv(7) label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def BENQ_def BTL_def raw_summary_def)
        subgoal
          apply (insert label_prop_inv(1,5))
          apply (unfold label_prop_upd_inv_def)
          apply (elim conjE)
          apply (intro conjI)
             apply (simp add: consumes_def)
            apply (simp add: consumes_def)
           apply (simp add: consumes_def)
          apply (simp add: consumes_def all_vertices_def)
          done
        using inputs_ocaps_inv_consumes[OF label_prop_inv(6)] apply simp
        using label_prop_inv(7) apply (simp add: buffers_inv flip: BULK_BENQ_assoc)
        done
      subgoal for d t xs
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
        apply (rule exI[of _ \<open>os(2 := (os 2)\<lparr>outpu := (outpu (os 2))(1 := xs)\<rparr>)\<close>])
        apply (rule exI[of _ os_label_prop])
        apply (rule exI[of _ \<open>BENQ (1, 1) (d, t) cbufs\<close>])
        apply (rule exI[of _ sg])
        apply (intro conjI)
                            apply (clarsimp simp add: dataflow_tree_to_operator_def
            intro!: arg_cong[where f=\<open>set_op _ _\<close>] arg_cong[where f=\<open>dataflow_op _\<close>]
            arg_cong[where f=\<open>map_op _ _\<close>])
                            apply (rule comp_op_buf_cong[OF refl])
                            apply (simp add: os_inv(1))
                            apply (rule loop_op_buf_cong[OF refl])
                            apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
                            apply (rule comp_op_buf_cong[OF refl refl refl])
                            apply (simp add: ran_comp_wire BENQ_def)
                            apply (simp add: ran_loop_wire)
                            apply (clarsimp simp add: BENQ_def ran_def split: sum.splits)
                            apply (metis obj_sumE prod.exhaust)
                            apply (simp add: csets_inv buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) BENQ_def cimage_cUn)
                            apply (rule subgraph_inv(1))
                           apply (rule subgraph_inv(2))
        using os_inv(2) apply simp
        using os_inv(3) apply simp
        using os_inv(4) apply force
        using os_inv(5) apply (simp add: os_inv(1) ty1_check_def BENQ_def)
        using os_inv(6,10) apply (simp add: label_prob_ty2_check_def BENQ_def)
        using os_inv(7) apply simp
        using os_inv(8) apply (simp add: input_ocaps_inv_def)
        using os_inv(9) apply simp
        using os_inv(6,10) apply (simp add: label_prob_ty2_check_def BENQ_def)
        using buffers_inv(2) apply (simp add: BENQ_def)
                apply (rule dataplane_tracker_inv_update_outputs[OF dataplane_inv _ _ _ _ G, where nid=2 and xs=\<open>[(d, t)]\<close> and ys=xs and p=1])
                   apply simp
                  apply (simp add: fun_eq_iff)
                 apply (simp add: BENQ_def)
                apply (simp add: subgraph_inv(1) raw_summary_def antichain_from_list_singleton)
        using input_stream_inv apply simp
              apply (rule label_prop_inv(1))
        using label_prop_inv(2) apply simp
        using label_prop_inv(3) apply simp
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def BENQ_def outputs_at_target_raw_summary subgraph_inv(1))
          apply (rule label_prop_inv(5))
        using label_prop_inv(6) apply simp
        using label_prop_inv(7) apply (simp add: buffers_inv BULK_BENQ_def BENQ_def outputs_at_target_raw_summary subgraph_inv(1) image_Un Un_assoc)
        done
      subgoal for _ os_incr'
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
        apply (intro exI conjI)
                            apply (simp add: dataflow_tree_to_operator_def os_inv(1))
                            apply (simp add: csets_inv BULK_BENQ_def buffers_inv outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def cimage_cUn)
        using subgraph_inv(1) apply simp
        using subgraph_inv(2) apply simp
        using os_inv(2) apply simp
        using os_inv(3) apply simp
        using os_inv(4) apply simp
        using os_inv(1,5) apply simp
                      apply (rule os_inv(6))
        using os_inv(7) apply (simp add: obtain_progress_def)
        using os_inv(8) apply (simp add: obtain_progress_def input_ocaps_inv_def)
        using os_inv(9) apply (simp add: obtain_progress_def)
        using os_inv(10) apply (simp add: obtain_progress_def)
        using buffers_inv(2) apply simp
                apply (subst dataplane_tracker_inv_clean[where f=\<open>\<lambda>_. True\<close>])
                  prefer 3
                  apply (rule dataplane_tracker_inv_progress[OF dataplane_inv D G, where nid=2])
                  apply simp
                 apply (simp add: obtain_progress_def)
                apply (simp add: obtain_progress_def)
        using input_stream_inv apply simp
              apply (rule label_prop_inv(1))
        using label_prop_inv(2) apply simp
        using label_prop_inv(3) apply simp
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def)
          apply (rule label_prop_inv(5))
        using label_prop_inv(6) apply simp
        using label_prop_inv(7) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def obtain_progress_def image_Un Un_assoc)
        done
      subgoal for _ os_label_prop'
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
        apply (rule exI[of _ \<open>os(1 := fst (obtain_progress (os 1)))\<close>])
        apply (rule exI[of _ os_label_prop'])
        apply (rule exI[of _ cbufs])
        apply (intro exI conjI)
                            apply (simp add: dataflow_tree_to_operator_def os_inv(1))
                            apply (simp add: csets_inv buffers_inv obtain_progress_def BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def cimage_cUn)
        using subgraph_inv(1) apply simp
        using subgraph_inv(2) apply simp
        using os_inv(2) apply simp
        using os_inv(3) apply simp
        using os_inv(4) apply (simp add: obtain_progress_def operator_state.defs(3))
        using os_inv(1,5) apply simp
        using os_inv(6) apply (simp add: obtain_progress_def label_prob_ty2_check_def)
        using os_inv(7) apply (simp add: obtain_progress_def)
        using os_inv(8) apply simp
        using os_inv(9) apply simp
        using os_inv(10) apply (simp add: obtain_progress_def)
        using buffers_inv(2) apply simp
                apply (subst dataplane_tracker_inv_clean[where f=\<open>\<lambda>_. True\<close>])
                  prefer 3
                  apply (rule dataplane_tracker_inv_progress[OF dataplane_inv D G, where nid=1])
                  apply simp
                 apply (simp add: obtain_progress_def os_inv(4) operator_state.defs(3))
                apply simp
        using input_stream_inv apply simp
        using label_prop_inv(1) apply (simp add: obtain_progress_def)
        using label_prop_inv(2) apply (simp add: obtain_progress_def)
        using label_prop_inv(3) apply (simp add: obtain_progress_def)
        using label_prop_inv(4) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def obtain_progress_def)
        using label_prop_inv(5) apply (simp add: obtain_progress_def)
        using label_prop_inv(6) apply (simp add: obtain_progress_def input_ocaps_inv_def)
        using label_prop_inv(7) apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) inputs_at_target_def obtain_progress_def image_Un Un_assoc)
        done
      subgoal
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
        apply (rule exI[of _ \<open>os(0 := fst (obtain_progress (os 0)))\<close>])
        apply (rule exI[of _ os_label_prop])
        apply (rule exI[of _ cbufs])
        apply (intro exI conjI)
                            apply (simp add: dataflow_tree_to_operator_def os_inv(1) operator_state.defs(3) obtain_progress_def)
                            apply (simp add: csets_inv buffers_inv)
        using subgraph_inv(1) apply simp
        using subgraph_inv(2) apply simp
        using os_inv(2) apply (simp add: obtain_progress_def)
        using os_inv(3) apply (simp add: obtain_progress_def)
        using os_inv(4) apply simp
        using os_inv(1,5) apply (simp add: obtain_progress_def ty1_check_def operator_state.defs(3))
                      apply (rule os_inv(6))
        using os_inv(7) apply (simp add: obtain_progress_def)
        using os_inv(8) apply simp
        using os_inv(9) apply simp
        using os_inv(10) apply simp
        using buffers_inv(2) apply simp
                apply (subst dataplane_tracker_inv_clean[where f=\<open>\<lambda>_. True\<close>])
                  prefer 3
                  apply (rule dataplane_tracker_inv_progress[OF dataplane_inv D G, where nid=0])
                  apply simp
                 apply (simp add: obtain_progress_def)
                apply simp
        using input_stream_inv apply (simp add: obtain_progress_def)
              apply (rule label_prop_inv(1))
        using label_prop_inv(2) apply simp
        using label_prop_inv(3) apply simp
        using label_prop_inv(4) apply (simp add: buffers_inv)
          apply (rule label_prop_inv(5))
        using label_prop_inv(6) apply simp
        using label_prop_inv(7) apply (simp add: buffers_inv)
        done
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
        using os_inv(10) apply simp
        using buffers_inv(2) apply simp
                apply (rule dataplane_tracker_inv_update_outputs_outside[OF dataplane_inv _ _ G])
                 apply (simp add: fun_upd_def)
                apply (simp add: subgraph_inv(1) raw_summary_def)
               apply (subgoal_tac \<open>outputs_at_target (summ sg) (os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(0 := xs)\<rparr>)) (1, 0) = outputs_at_target (summ sg) os (1, 0)\<close>)
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
        subgoal
          apply (subst wf_label_prop_updates_cong[where os'=os_label_prop])
          using label_prop_inv(7)
          by (simp_all add: buffers_inv image_Un Un_assoc BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1))
        done
      done
  qed
next
  case SIM2
  note subgraph_inv = SIM2(1,2)
    and os_inv = SIM2(3-12)
    and buffers_inv = SIM2(13,14)
    and dataplane_inv = SIM2(15)
    and csets_inv = SIM2(16,17)
    and input_stream_inv = SIM2(18)
    and label_prop_inv = SIM2(19-)

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
  obtain cap where dt_inv:
    \<open>Src_caps_inv cap os\<close>
    \<open>Trg_caps_inv cap (outputs_at_target (summ sg) os >> cbufs)\<close>
    \<open>c_pts_inv
      (change_multiplicities (summ sg)
        (extract_progress 0 (subgraph.nxt sg) (snd (obtain_progress (os 0))) @
         extract_progress 1 (subgraph.nxt sg) (snd (obtain_progress (os 1))) @
         extract_progress 2 (subgraph.nxt sg) (snd (obtain_progress (os 2))))
        (pt_tr sg)) cap\<close>
    \<open>front_inv os (pt_tr sg)\<close>
    \<open>imp_front_inv (summ sg) (pt_tr sg)\<close>
    \<open>chnls_imp_front_inv (summ sg) (pt_tr sg) (outputs_at_target (summ sg) os >> cbufs)\<close>
    \<open>change_deltas_inv os\<close>
    \<open>propagation_inv (summ sg) (pt_tr sg)\<close>
    \<open>extract_prog_changes_above_impl_inv (summ sg) (subgraph.nxt sg) (pt_tr sg) os\<close>
    \<open>produ_consu_inter_supported (subgraph.nxt sg) os (pt_tr sg)\<close>
    using dataplane_inv[unfolded dataplane_tracker_inv_def, simplified]
    by clarsimp
  obtain c' where first_propa:
    \<open>propagate_all (antichain_from_list \<circ>\<circ> raw_summary)
      (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary)
        (extract_progress 0 (graph_to_nxt (antichain_from_list \<circ>\<circ> raw_summary))
          (snd (obtain_progress os_input)))
        (pt_tr sg)) = Some c'\<close>
    \<open>\<forall>loc. frontier (c_imp c' loc) =
      ifrontier (antichain_from_list \<circ>\<circ> raw_summary) (-+-)
        (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary)
          (extract_progress 0 (graph_to_nxt (antichain_from_list \<circ>\<circ> raw_summary))
            (snd (obtain_progress os_input)))
          (pt_tr sg)) loc\<close>
    \<open>dataflow_topology_from_tree.inv_implications_nonneg c'\<close>
    \<open>dataflow_topology_from_tree.inv_imp_plus_work_nonneg c'\<close>
    \<open>dataflow_topology.inv_imps_work_sum (antichain_from_list \<circ>\<circ> raw_summary) (-+-) c'\<close>
    using propagate_all_frontier_change_multiplicities_c_imp_correctnessE
      [OF D, of \<open>pt_tr sg\<close>
        \<open>extract_progress 0 (graph_to_nxt (antichain_from_list \<circ>\<circ> raw_summary))
          (snd (obtain_progress os_input))\<close>,
        unfolded subgraph_inv(1), simplified]
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
      apply (clarsimp simp add: obtain_progress_def subgraph_inv(1,2) set_map_filter
          split_beta operator_state.defs os_inv(1) image_iff split: option.splits)
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
        apply (rule dt_inv(9)[unfolded extract_prog_changes_above_impl_inv_def
              changes_above_impl_inv_def, simplified, rule_format,
              where xs=Nil and x=\<open>(l, t, m)\<close> and nid=0, simplified])
        apply (clarsimp simp add: obtain_progress_def subgraph_inv(1,2) set_map_filter
            split_beta operator_state.defs os_inv(1) image_iff split: option.splits)
        done
      done
    apply (drule meta_mp)
    subgoal
      using raw_summary_no_self_loop by auto
    by clarsimp

(* ----------------------------- *)
(* STEPS 1: op 0 reports progress *)
  define os_progress where \<open>os_progress = os(0 := op_state_base (fst (obtain_progress os_input)))\<close>

  define sg_progress where \<open>sg_progress = sg\<lparr>upfro := (\<lambda>_. True),
    pt_tr := change_multiplicities (summ sg)
      (extract_progress 0 (subgraph.nxt sg) (snd (obtain_progress os_input)))
      (pt_tr sg)\<rparr>\<close>

  have dataplane_after_input_progress:
    \<open>dataplane_tracker_inv os_progress cbufs sg_progress\<close>
  proof -
    have base_progress:
      \<open>op_state_base (fst (obtain_progress os_input)) = fst (obtain_progress (os 0))\<close>
      using os_inv(1)
      by (simp add: obtain_progress_def op_state_base_def operator_state.defs)
    have progress_st:
      \<open>snd (obtain_progress os_input) = snd (obtain_progress (os 0))\<close>
      using os_inv(1)
      by (simp add: obtain_progress_def operator_state.defs)
    have inv_no_upfro:
      \<open>dataplane_tracker_inv os_progress cbufs
        (sg\<lparr>pt_tr := change_multiplicities (summ sg)
          (extract_progress 0 (subgraph.nxt sg) (snd (obtain_progress os_input)))
          (pt_tr sg)\<rparr>)\<close>
      using dataplane_tracker_inv_progress[OF dataplane_inv D G refl]
      by (simp add: os_progress_def base_progress progress_st)
    have clean_upfro:
      \<open>dataplane_tracker_inv os_progress cbufs sg_progress \<longleftrightarrow>
        dataplane_tracker_inv os_progress cbufs
          (sg\<lparr>pt_tr := change_multiplicities (summ sg)
            (extract_progress 0 (subgraph.nxt sg) (snd (obtain_progress os_input)))
            (pt_tr sg)\<rparr>)\<close>
      by (rule dataplane_tracker_inv_clean[where f=\<open>\<lambda>_. True\<close>])
        (simp_all add: sg_progress_def)
    show ?thesis
      using clean_upfro inv_no_upfro by simp
  qed

  define sg_first_propa where \<open>sg_first_propa = sg_progress\<lparr>pt_tr := c', upfro := (upfro sg_progress)(1 := False)\<rparr>\<close>

  define label_front_after_first_propa where
    \<open>label_front_after_first_propa = frontier \<circ> (\<lambda>p. c_imp (pt_tr sg_first_propa) (Loc (1 :: 3) (Trg p)))\<close>

  define os_first_propa where
    \<open>os_first_propa = os_progress(1 := op_state_base
      (os_label_prop\<lparr>front := label_front_after_first_propa, initia := True\<rparr>))\<close>

  have dataplane_after_first_propa:
    \<open>dataplane_tracker_inv os_first_propa cbufs sg_first_propa\<close>
  proof -
    have base_progress:
      \<open>op_state_base (fst (obtain_progress os_input)) = fst (obtain_progress (os 0))\<close>
      using os_inv(1)
      by (simp add: obtain_progress_def op_state_base_def operator_state.defs)
    have progress_st:
      \<open>snd (obtain_progress os_input) = snd (obtain_progress (os 0))\<close>
      using os_inv(1)
      by (simp add: obtain_progress_def operator_state.defs)
    have G_progress:
      \<open>graph_summar_nt (summ sg_progress) (nxt sg_progress) os_progress\<close>
    proof -
      have \<open>graph_summar_nt (summ sg) (nxt sg) os_progress =
        graph_summar_nt (summ sg) (nxt sg) os\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_progress_def os_inv(1) obtain_progress_def op_state_base_def operator_state.defs)
      then show ?thesis
        using G by (simp add: sg_progress_def)
    qed
    have D_progress: \<open>dataflow_topology (summ sg_progress) (-+-)\<close>
      using D by (simp add: sg_progress_def)
    have reachable_progress: \<open>reachable_locations (summ sg_progress) = UNIV\<close>
      using subgraph_inv(1) by (simp add: sg_progress_def)
    have propagate_progress: \<open>propagate_all (summ sg_progress) (pt_tr sg_progress) = Some c'\<close>
      using first_propa(1) subgraph_inv by (simp add: sg_progress_def)
    define front_c where \<open>front_c = frontier \<circ> (\<lambda>p. c_imp c' (Loc (1 :: 3) (Trg p)))\<close>

    have inv_front_no_upfro:
      \<open>dataplane_tracker_inv os_first_propa cbufs (sg_progress\<lparr>pt_tr := c'\<rparr>)\<close>
    proof -
      define os_front where \<open>os_front = map_entry (1 :: 3) (front_update (\<lambda>_. front_c)) os_progress\<close>

      have inv_map:
        \<open>dataplane_tracker_inv os_front cbufs (sg_progress\<lparr>pt_tr := c'\<rparr>)\<close>
        unfolding os_front_def front_c_def
        by (rule dataplane_tracker_inv_front_update
            [OF D_progress reachable_progress propagate_progress G_progress dataplane_after_input_progress,
              where nid = \<open>1 :: 3\<close>, simplified])

      have clean_initia:
        \<open>dataplane_tracker_inv os_first_propa cbufs (sg_progress\<lparr>pt_tr := c'\<rparr>) \<longleftrightarrow>
          dataplane_tracker_inv os_front cbufs (sg_progress\<lparr>pt_tr := c'\<rparr>)\<close>
        by (rule dataplane_tracker_inv_clean[where f=\<open>upfro (sg_progress\<lparr>pt_tr := c'\<rparr>)\<close>])
          (simp_all add: os_first_propa_def os_front_def os_progress_def
            label_front_after_first_propa_def sg_first_propa_def front_c_def
            os_inv(4) op_state_base_def operator_state.defs)
      show ?thesis
        using clean_initia inv_map by simp
    qed
    have clean_upfro:
      \<open>dataplane_tracker_inv os_first_propa cbufs sg_first_propa \<longleftrightarrow>
        dataplane_tracker_inv os_first_propa cbufs (sg_progress\<lparr>pt_tr := c'\<rparr>)\<close>
      by (rule dataplane_tracker_inv_clean[where f=\<open>(upfro sg_progress)(1 := False)\<close>])
        (simp_all add: sg_first_propa_def)
    show ?thesis
      using clean_upfro inv_front_no_upfro by simp
  qed

(* ----------------------------- *)
(* STEPS 2: op 1 reads the initial frontier from propagation *)
  define os_label_after_first_propa where
    \<open>os_label_after_first_propa = os_label_prop\<lparr>front := label_front_after_first_propa, initia := True\<rparr>\<close>

  have labels_after_first_propa:
    \<open>\<forall>t. labels_inv (all_edges os_label_after_first_propa t) (min_label os_label_after_first_propa t)\<close>
    using label_prop_inv(1)
    by (simp add: os_label_after_first_propa_def all_edges_def all_vertices_def min_label_def)

  define input_events where \<open>input_events = (\<lambda>n. ltaken n lxs)\<close>

  define input_data where
    \<open>input_data = (\<lambda>n. map (\<lambda>ev. case ev of Data t d \<Rightarrow> (Inl d :: _ + nat set set, t))
      (filter is_Data (input_events n)))\<close>

  define os_input_after_stream where
    \<open>os_input_after_stream = (\<lambda>n. (fst (obtain_progress os_input))\<lparr>
      es := (es (fst (obtain_progress os_input)))(0 := ldropn n lxs),
      ocaps := (ocaps (fst (obtain_progress os_input)))(0 :=
        ocaps_updates (ocaps (fst (obtain_progress os_input)) 0) (input_events n)),
      inter := inter (fst (obtain_progress os_input)) @
        map (\<lambda>ev. case ev of Drop t \<Rightarrow> (0, t, -1) | Mint t \<Rightarrow> (0, t, 1))
          (filter (Not \<circ> is_Data) (input_events n)),
      produ := produ (fst (obtain_progress os_input)) @
        map (\<lambda>ev. case ev of Data t d \<Rightarrow> (0, t, 1))
          (filter is_Data (input_events n)),
      outpu := (outpu (fst (obtain_progress os_input)))(0 :=
        outpu (fst (obtain_progress os_input)) 0 @ input_data n)\<rparr>)\<close>

  define os_after_input_stream where
    \<open>os_after_input_stream = (\<lambda>n. os_first_propa(0 := op_state_base (os_input_after_stream n)))\<close>

  have dataplane_after_input_stream:
    \<open>dataplane_tracker_inv (os_after_input_stream n) cbufs sg_first_propa\<close>
    for n
  proof -
    have D_first: \<open>dataflow_topology (summ sg_first_propa) (-+-)\<close>
      using D by (simp add: sg_first_propa_def sg_progress_def)
    have Nxt_first: \<open>nxt sg_first_propa = graph_to_nxt (summ sg_first_propa)\<close>
      using subgraph_inv(2) by (simp add: sg_first_propa_def sg_progress_def)
    have G_first: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) os_first_propa\<close>
    proof -
      have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) os_first_propa =
        graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) os\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_first_propa_def os_progress_def
            os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs)
      then show ?thesis
        using G by (simp add: sg_first_propa_def sg_progress_def)
    qed

(* ----------------------------- *)
(* STEPS 3: op 0 produces n elements from the input stream *)  
    define xs where \<open>xs = ltaken n lxs\<close>

    define mint_times where \<open>mint_times = map event.time (filter is_Mint xs)\<close>

    define drop_times where \<open>drop_times = map event.time (filter is_Drop xs)\<close>

    define produs where \<open>produs = map (\<lambda>ev. ((0 :: 2), event.time ev, 1 :: int)) (filter is_Data xs)\<close>

    define oputs where \<open>oputs = (\<lambda>_. [])((0 :: 2) := input_data n)\<close>

    define base where \<open>base = os_first_propa 0\<close>

    define os_minted where
      \<open>os_minted = os_first_propa(0 := base\<lparr>
        ocaps := (ocaps base)((0 :: 2) := ocaps base 0 @ mint_times),
        inter := inter base @ map (\<lambda>t. ((0 :: 2), t, 1 :: int)) mint_times\<rparr>)\<close>

    have OSB1[simp]: \<open>\<And> F I. op_state_base (os_label_prop\<lparr>front := F, initia := I\<rparr>) = os 1\<lparr>front := F, initia := I\<rparr>\<close>
      by (simp add: op_state_base_def os_inv(4) operator_state.defs)
    have OSB0[simp]: \<open>op_state_base (fst (obtain_progress os_input)) = fst (obtain_progress (os 0))\<close>
      by (simp add: op_state_base_def obtain_progress_def os_inv(1) operator_state.defs)
    have inv_minted: \<open>dataplane_tracker_inv os_minted cbufs sg_first_propa\<close>
      unfolding os_minted_def base_def
      apply (rule dataplane_tracker_inv_mints_many[OF D_first, simplified,
            where nid=0 and p=0 and xs=mint_times])
        apply (rule dataplane_after_first_propa)
       apply (rule G_first)
      unfolding mint_times_def xs_def
      apply clarsimp
      subgoal for e
        apply (cases e; clarsimp)
        subgoal for t
          apply (drule setltakenD)
          apply (drule Mint_in_Stream_le_Mint_in_C[rotated])
          using input_stream_inv[unfolded timely_input_stream_def] apply blast
          using os_inv(1)
          by (auto simp add: os_first_propa_def os_progress_def
              obtain_progress_def op_state_base_def operator_state.defs)
        done
      done

    have G_minted: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) os_minted\<close>
    proof -
      have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) os_minted =
        graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) os_first_propa\<close>
        by (rule graph_summar_nt_intsum_cong) (simp add: os_minted_def base_def)
      then show ?thesis
        using G_first by simp
    qed

    define drops where \<open>drops = (\<lambda>_. [])((0 :: 2) := drop_times)\<close>

    define canon_ocaps_port0 where \<open>canon_ocaps_port0 = list_diff (ocaps base 0 @ mint_times) drop_times\<close>

    define canon_ocaps where \<open>canon_ocaps = (ocaps base)((0 :: 2) := canon_ocaps_port0)\<close>

    define canon_output where \<open>canon_output = (outpu base)((0 :: 2) := outpu base 0 @ input_data n)\<close>

    define canon_inter where
      \<open>canon_inter = inter base @ map (\<lambda>t. ((0 :: 2), t, 1 :: int)) mint_times @
        map (\<lambda>t. ((0 :: 2), t, -1 :: int)) drop_times\<close>

    define canon0 where
      \<open>canon0 = base\<lparr>outpu := canon_output, ocaps := canon_ocaps, input := input base,
        produ := produ base @ produs, inter := canon_inter\<rparr>\<close>

    define os_canon where \<open>os_canon = os_first_propa(0 := canon0)\<close>

    have concat_drops:
      \<open>concat (map (\<lambda>p. map (\<lambda>t. (p, t, - 1 :: int)) (drops p)) Enum.enum) =
        map (\<lambda>t. ((0 :: 2), t, - 1 :: int)) drop_times\<close>
      using concat_map_empty_except_1[OF Enum.enum_distinct Enum.in_enum,
          where x=\<open>0 :: 2\<close> and f=\<open>\<lambda>p. map (\<lambda>t. (p, t, - 1 :: int)) (drops p)\<close>]
      by (auto simp: drops_def)
    have oputs_produs:
      \<open>\<forall>p. to_zmset (map snd (oputs p)) =
        zmset (map snd (filter (\<lambda>x. p = fst x) produs))\<close>
    proof
      fix p :: 2
      show \<open>to_zmset (map snd (oputs p)) =
        zmset (map snd (filter (\<lambda>x. p = fst x) produs))\<close>
      proof (cases \<open>p = 0\<close>)
        case True
        have data_time:
          \<open>map (\<lambda>x. snd (case x of Data t d \<Rightarrow> (Inl d, t))) (filter is_Data xs) =
            map event.time (filter is_Data xs)\<close>
          by (rule map_cong[OF refl]) (auto split: event.splits)
        have lhs_time:
          \<open>to_zmset (map snd (oputs (0 :: 2))) =
            to_zmset (map event.time (filter is_Data xs))\<close>
          apply (simp add: oputs_def input_data_def input_events_def xs_def[symmetric] comp_def)
          apply (rule arg_cong[where f=to_zmset])
          apply (rule data_time)
          done
        have rhs_time:
          \<open>zmset (map snd (filter (\<lambda>x. (0 :: 2) = fst x) produs)) =
            to_zmset (map event.time (filter is_Data xs))\<close>
          by (simp add: produs_def filter_True comp_def zmset_map_one)
        show ?thesis
          using True lhs_time rhs_time by simp
      next
        case False
        then show ?thesis
          by (simp add: oputs_def produs_def filter_False)
      qed
    qed

    have inv_canon_step:
      \<open>dataplane_tracker_inv
        (os_minted(0 := (os_minted 0)\<lparr>outpu := canon_output,
          ocaps := canon_ocaps, input := input base,
          produ := produ base @ produs, inter := canon_inter\<rparr>))
        cbufs sg_first_propa\<close>
      apply (rule dataplane_tracker_inv_produces_drops[OF D_first,
            where os = os_minted and nid = \<open>0 :: 3\<close>
              and oputs = oputs and produs = produs and drops = drops])
                 apply (rule ext; simp add: canon_output_def oputs_def os_minted_def)
                apply (rule ext; simp add: canon_ocaps_def canon_ocaps_port0_def
          drops_def os_minted_def fun_upd_def)
               apply (rule ext; simp add: drops_def os_minted_def base_def
          os_first_propa_def os_progress_def
          os_inv(1,2) obtain_progress_def op_state_base_def operator_state.defs)
              apply (simp add: os_minted_def)
             apply (simp add: canon_inter_def os_minted_def drops_def concat_drops)
      using timely_input_stream_drops_subseteq_C_mints[OF input_stream_inv, of n] os_inv(1)
            apply (auto simp add: drops_def os_minted_def base_def
          os_first_propa_def os_progress_def drop_times_def mint_times_def xs_def
          obtain_progress_def op_state_base_def operator_state.defs split: if_splits)[1]
           apply (clarsimp del: disjCI simp add: produs_def os_minted_def base_def
          os_first_propa_def os_progress_def
          image_iff)
      subgoal for ev
        apply (cases ev; clarsimp del: disjCI simp add: image_iff)
        subgoal for t d
          using timely_input_stream_Data_in_C_in[OF _ input_stream_inv, of _ _ n] os_inv(1)
          by (force simp add: xs_def mint_times_def
              obtain_progress_def op_state_base_def operator_state.defs)
        done
          apply (clarsimp del: disjCI simp add: oputs_def os_minted_def base_def
          os_first_propa_def os_progress_def
          input_data_def input_events_def image_iff split: if_splits)
      subgoal for t d
        using timely_input_stream_Data_in_C_in[OF _ input_stream_inv, of _ _ n] os_inv(1)
        by (auto simp add: mint_times_def xs_def
            obtain_progress_def op_state_base_def operator_state.defs split: event.splits)
         apply (rule oputs_produs)
        apply (rule G_minted)
       apply (rule Nxt_first)
      apply (rule inv_minted)
      done
    have inv_canon: \<open>dataplane_tracker_inv os_canon cbufs sg_first_propa\<close>
      using inv_canon_step
      by (simp add: os_canon_def canon0_def os_minted_def base_def fun_upd_def)

    define target0_canon_ocaps where
      \<open>target0_canon_ocaps = (os_after_input_stream n 0)\<lparr>ocaps :=
        (ocaps (os_after_input_stream n 0))((0 :: 2) := canon_ocaps_port0)\<rparr>\<close>


    define os_target_canon_ocaps where \<open>os_target_canon_ocaps = (os_after_input_stream n)(0 := target0_canon_ocaps)\<close>

    have inter_events_mset:
      \<open>mset (map (\<lambda>t. ((0 :: 2), t, 1 :: int)) (map event.time (filter is_Mint xs))) +
        mset (map (\<lambda>t. ((0 :: 2), t, -1 :: int)) (map event.time (filter is_Drop xs))) =
        mset (map (\<lambda>ev. case ev of Drop t \<Rightarrow> ((0 :: 2), t, -1 :: int) | Mint t \<Rightarrow> ((0 :: 2), t, 1 :: int))
          (filter (Not \<circ> is_Data) xs))\<close> for xs
      by (induct xs) (auto split: event.splits)
    have inter_mset:
      \<open>mset canon_inter = mset (inter (target0_canon_ocaps))\<close>
      using inter_events_mset[of xs]
      by (simp add: canon_inter_def target0_canon_ocaps_def
          os_after_input_stream_def os_input_after_stream_def
          os_first_propa_def os_progress_def base_def
          mint_times_def drop_times_def
          input_events_def xs_def
          obtain_progress_def op_state_base_def operator_state.defs mset_append
          split: event.splits)

    have fields_inter:
      \<open>\<forall>nid. intsum (os_canon nid) = intsum (os_target_canon_ocaps nid) \<and>
        ocaps (os_canon nid) = ocaps (os_target_canon_ocaps nid) \<and>
        consu (os_canon nid) = consu (os_target_canon_ocaps nid) \<and>
        mset (inter (os_canon nid)) = mset (inter (os_target_canon_ocaps nid)) \<and>
        produ (os_canon nid) = produ (os_target_canon_ocaps nid) \<and>
        outpu (os_canon nid) = outpu (os_target_canon_ocaps nid) \<and>
        front (os_canon nid) = front (os_target_canon_ocaps nid)\<close>
      using inter_mset os_inv(1)
      by (auto simp add: os_canon_def canon0_def base_def
          os_target_canon_ocaps_def target0_canon_ocaps_def
          os_after_input_stream_def os_input_after_stream_def
          os_first_propa_def os_progress_def
          canon_ocaps_def canon_output_def produs_def xs_def input_events_def
          obtain_progress_def op_state_base_def operator_state.defs split: event.splits)
    have inv_target_canon_ocaps:
      \<open>dataplane_tracker_inv os_target_canon_ocaps cbufs sg_first_propa\<close>
      using iffD1[OF dataplane_tracker_inv_clean_reorder_inter[OF fields_inter, of cbufs sg_first_propa]]
        inv_canon
      by blast

    have ocaps_mset:
      \<open>mset (ocaps (os_after_input_stream n 0) (0 :: 2)) = mset canon_ocaps_port0\<close>
      using mset_ocaps_updates[of xs \<open>ldropn n lxs\<close> \<open>ocaps (fst (obtain_progress os_input)) (0 :: 2)\<close>]
        input_stream_inv os_inv(1)
      by (simp add: os_after_input_stream_def os_input_after_stream_def
          canon_ocaps_port0_def base_def os_first_propa_def os_progress_def
          mint_times_def drop_times_def xs_def input_events_def
          obtain_progress_def op_state_base_def operator_state.defs mset_list_diff)
    show ?thesis
      apply (rule dataplane_tracker_inv_replace_ocaps
          [where os' = os_target_canon_ocaps and nid = \<open>0 :: 3\<close> and p = \<open>0 :: 2\<close> and C = canon_ocaps_port0])
        apply (rule inv_target_canon_ocaps)
       apply (rule ocaps_mset)
      apply (simp add: os_target_canon_ocaps_def target0_canon_ocaps_def)
      done
  qed

(* ----------------------------- *)
(* STEPS 4: op 0 flushes the outpu buffer *)
  define input0_msgs where \<open>input0_msgs = (\<lambda>n. cbufs (1, 0) @ outpu (os 0) 0 @ input_data n)\<close>
  define cbufs_after_input_output where \<open>cbufs_after_input_output = (\<lambda>n. cbufs((1, 0) := input0_msgs n))\<close>
  define os_input_after_output where
    \<open>os_input_after_output = (\<lambda>n. (os_input_after_stream n)\<lparr>outpu :=
      (outpu (os_input_after_stream n))(0 := [])\<rparr>)\<close>

  define os_after_input_output where
    \<open>os_after_input_output = (\<lambda>n. (os_after_input_stream n)(0 := op_state_base (os_input_after_output n)))\<close>

  have dataplane_after_input_output:
    \<open>dataplane_tracker_inv
      (os_after_input_output n) (cbufs_after_input_output n) sg_first_propa\<close>
    for n
  proof -
    have G_after_input_stream:
      \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_input_stream n)\<close>
    proof -
      have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_input_stream n) =
        graph_summar_nt (summ sg) (nxt sg) (os_after_input_stream n)\<close>
        by (simp add: sg_first_propa_def sg_progress_def)
      also have \<open>... = graph_summar_nt (summ sg) (nxt sg) os\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_input_stream_def os_input_after_stream_def
            os_first_propa_def os_progress_def
            os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs)

      then show ?thesis
        using G by (simp add: sg_first_propa_def sg_progress_def)
    qed

    have edge_input0_label0:
      \<open>summ sg_first_propa (Loc (0 :: 3) (Src (0 :: 2))) (Loc (1 :: 3) (Trg (0 :: 2))) \<noteq> {}\<^sub>A\<close>
      by (simp add: sg_first_propa_def sg_progress_def
          subgraph_inv(1) raw_summary_def antichain_from_list_singleton)
    show ?thesis
      apply (rule dataplane_tracker_inv_update_outputs
          [where os = \<open>os_after_input_stream n\<close> and cbufs = cbufs and sg = sg_first_propa
            and nid = \<open>0 :: 3\<close> and p = \<open>0 :: 2\<close>
            and xs = \<open>outpu (os_after_input_stream n 0) (0 :: 2)\<close> and ys = \<open>[]\<close>
            and os' = \<open>os_after_input_output n\<close> and cbufs' = \<open>cbufs_after_input_output n\<close>
            and nid' = \<open>1 :: 3\<close> and p' = \<open>0 :: 2\<close>])
           apply (rule dataplane_after_input_stream)
          apply simp
         apply (simp add: os_after_input_output_def os_input_after_output_def
          os_after_input_stream_def os_input_after_stream_def
          fun_upd_def op_state_base_def operator_state.defs)
        apply (simp add: cbufs_after_input_output_def input0_msgs_def
          os_after_input_stream_def os_input_after_stream_def
          fun_upd_def os_inv(1) obtain_progress_def op_state_base_def operator_state.defs)
       apply (rule edge_input0_label0)
      apply (rule G_after_input_stream)
      done
  qed

(* ----------------------------- *)
(* STEPS 5: op 1 consumes all the data in the channel *)
  define os_label_after_read_input0 where
    \<open>os_label_after_read_input0 = (\<lambda>n. CONSUMES 0 (input0_msgs n) os_label_after_first_propa)\<close>

  define cbufs_after_label_read_input0 where
    \<open>cbufs_after_label_read_input0 = (\<lambda>n. (cbufs_after_input_output n)((1, 0) := []))\<close>

  define os_after_label_read_input0 where
    \<open>os_after_label_read_input0 = (\<lambda>n. (os_after_input_output n)(1 := op_state_base (os_label_after_read_input0 n)))\<close>

  have dataplane_after_label_read_input0:
    \<open>dataplane_tracker_inv
      (os_after_label_read_input0 n) (cbufs_after_label_read_input0 n) sg_first_propa\<close>
    for n
  proof -
    have G_after_input_output:
      \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_input_output n)\<close>
    proof -
      have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_input_output n) =
        graph_summar_nt (summ sg) (nxt sg) (os_after_input_output n)\<close>
        by (simp add: sg_first_propa_def sg_progress_def)
      also have \<open>... = graph_summar_nt (summ sg) (nxt sg) os\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def
            os_first_propa_def os_progress_def
            os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs)

      then show ?thesis
        using G by (simp add: sg_first_propa_def sg_progress_def)
    qed

    show ?thesis
      apply (rule dataplane_tracker_inv_fold_consumes
          [where os = \<open>os_after_input_output n\<close> and cbufs = \<open>cbufs_after_input_output n\<close>
            and sg = sg_first_propa and nid = \<open>1 :: 3\<close> and p = \<open>0 :: 2\<close>
            and n = \<open>length (input0_msgs n)\<close>
            and buf' = \<open>cbufs_after_label_read_input0 n\<close>
            and os' = \<open>os_after_label_read_input0 n\<close>])
           apply (rule dataplane_after_input_output)
          apply (simp add: D sg_first_propa_def sg_progress_def)
         apply (rule G_after_input_output)
        apply (simp add: cbufs_after_input_output_def input0_msgs_def)
       apply (rule ext)
       apply (simp add: cbufs_after_label_read_input0_def cbufs_after_input_output_def
          input0_msgs_def split: prod.splits)
      apply (simp add: os_after_label_read_input0_def os_label_after_read_input0_def
          os_after_input_output_def os_input_after_output_def
          os_after_input_stream_def os_first_propa_def os_progress_def
          os_label_after_first_propa_def cbufs_after_input_output_def input0_msgs_def
          fun_upd_def op_state_base_CONSUMES)
      done
  qed

  have labels_after_label_read_input0:
    \<open>\<forall>t. labels_inv (all_edges (os_label_after_read_input0 n) t) (min_label (os_label_after_read_input0 n) t)\<close>
    for n
    using labels_after_first_propa
    by (simp add: os_label_after_read_input0_def input_CONSUMES all_vertices_def all_edges_def neighbors_def min_label_def)

(* ----------------------------- *)
(* STEPS 6: op 1 processes all the new edges in the input 0 *)
  define label_input0_msgs where \<open>label_input0_msgs = (\<lambda>n. input (os 1) 0 @ input0_msgs n)\<close>

  define os_label_after_input0 where
    \<open>os_label_after_input0 = (\<lambda>n. fst (label_prop_input0_batched
      (os_label_after_read_input0 n) (label_input0_msgs n)))\<close>

  define os_after_label_input0 where
    \<open>os_after_label_input0 = (\<lambda>n. (os_after_label_read_input0 n)(1 := op_state_base (os_label_after_input0 n)))\<close>

  have dataplane_after_label_input0:
    \<open>dataplane_tracker_inv
      (os_after_label_input0 n) (cbufs_after_label_read_input0 n) sg_first_propa\<close>
    for n
  proof -
    have G_after_label_read_input0:
      \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n)\<close>
    proof -
      have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n) =
        graph_summar_nt (summ sg) (nxt sg) (os_after_label_read_input0 n)\<close>
        by (simp add: sg_first_propa_def sg_progress_def)
      also have \<open>... = graph_summar_nt (summ sg) (nxt sg) os\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_label_read_input0_def os_label_after_read_input0_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def
            os_first_propa_def os_progress_def os_label_after_first_propa_def
            os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs
            input_CONSUMES)

      then show ?thesis
        using G by (simp add: sg_first_propa_def sg_progress_def)
    qed
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have IOC_label_read:
      \<open>input_ocaps_inv (os_label_after_read_input0 n)\<close>
      unfolding os_label_after_read_input0_def
      apply (rule input_ocaps_inv_CONSUMES)
      using label_prop_inv(6) os_inv(4)
      by (simp add: os_label_after_first_propa_def input_ocaps_inv_def operator_state.defs)
    have zero_label_read:
      \<open>0 \<in> set (intsum (os_label_after_read_input0 n) (0 :: 2) (1 :: 2))\<close>
      using os_inv(7) os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          intsum_consumes_fold raw_summary_def zero_myprod_def operator_state.defs)
    have inv_batch:
      \<open>dataplane_tracker_inv
        ((os_after_input_output n)(1 := op_state_base
          (fst (label_prop_input0_batched (os_label_after_read_input0 n)
            (input (os_label_after_read_input0 n) (0 :: 2))))))
        (cbufs_after_label_read_input0 n) sg_first_propa\<close>
      apply (rule dataplane_tracker_inv_label_prop_input0_batched
          [where os = \<open>os_after_input_output n\<close> and nid = \<open>1 :: 3\<close>
            and ls = \<open>os_label_after_read_input0 n\<close>])
           apply (simp add: D sg_first_propa_def sg_progress_def)
      using dataplane_after_label_read_input0[of n]
          apply (simp add: os_after_label_read_input0_def)
      using G_after_label_read_input0
         apply (simp add: os_after_label_read_input0_def)
        apply (simp add: sg_first_propa_def sg_progress_def subgraph_inv(2))
       apply (rule IOC_label_read)
      apply (rule zero_label_read)
      done
    show ?thesis
      using inv_batch input_label_read
      by (simp add: os_after_label_input0_def os_label_after_input0_def
          os_after_label_read_input0_def fun_upd_def)
  qed

  have labels_after_label_input0:
    \<open>\<forall>t. labels_inv (all_edges (os_label_after_input0 n) t) (min_label (os_label_after_input0 n) t)\<close>
    for n
  proof -
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have WF_read:
      \<open>wf_label_prop_updates (os_label_after_read_input0 n)
        (set (input (os_label_after_read_input0 n) (1 :: 2)))\<close>
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    show ?thesis
      unfolding os_label_after_input0_def
      by (rule labels_inv_fst_label_prop_input0_batched_input_allI
          [OF input_label_read labels_after_label_read_input0 INV_read WF_read])
  qed

(* ----------------------------- *)
(* STEPS 7: op 1 loops all the data, and processes everything until the labels converges *)
  define loop_res where
    \<open>loop_res = (\<lambda>n. loop_updates
      (cbufs_after_label_read_input0 n) (os_label_after_input0 n) (os_after_label_input0 n))\<close>

  define cbufs_after_loop_updates where \<open>cbufs_after_loop_updates = (\<lambda>n. fst (loop_res n))\<close>

  define os_label_after_loop_updates where \<open>os_label_after_loop_updates = (\<lambda>n. fst (snd (loop_res n)))\<close>

  define os_after_loop_updates where \<open>os_after_loop_updates = (\<lambda>n. snd (snd (loop_res n)))\<close>

  have dataplane_after_loop_updates:
    \<open>dataplane_tracker_inv
      ((os_after_loop_updates n)(1 := op_state_base (os_label_after_loop_updates n)))
      (cbufs_after_loop_updates n) sg_first_propa\<close>
    for n
  proof -
    have step:
      \<open>(cbufs_after_loop_updates n, os_label_after_loop_updates n, os_after_loop_updates n)
        = loop_updates (cbufs_after_label_read_input0 n) (os_label_after_input0 n) (os_after_label_input0 n)\<close>
      by (simp add: cbufs_after_loop_updates_def os_label_after_loop_updates_def
          os_after_loop_updates_def loop_res_def prod_eq_iff)

    have D_sg: \<open>dataflow_topology (summ sg_first_propa) (-+-)\<close>
      using D by (simp add: sg_first_propa_def sg_progress_def)
    have Nxt_sg: \<open>nxt sg_first_propa = graph_to_nxt (summ sg_first_propa)\<close>
      using subgraph_inv(2) by (simp add: sg_first_propa_def sg_progress_def)
    have Summ_sg: \<open>summ sg_first_propa = antichain_from_list \<circ>\<circ> raw_summary\<close>
      using subgraph_inv(1) by (simp add: sg_first_propa_def sg_progress_def)
    have IOC2: \<open>input_ocaps_inv ((os_after_label_input0 n) 2)\<close>
      using os_inv(8)
      by (simp add: os_after_label_input0_def os_after_label_read_input0_def
          os_after_input_output_def os_after_input_stream_def
          os_first_propa_def os_progress_def)
    have Inv_step:
      \<open>dataplane_tracker_inv
        ((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n)))
        (cbufs_after_label_read_input0 n) sg_first_propa\<close>
      using dataplane_after_label_input0[of n]
      by (simp add: os_after_label_input0_def fun_upd_def)
    have G_after_label_read_input0:
      \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n)\<close>
    proof -
      have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n) =
        graph_summar_nt (summ sg) (nxt sg) (os_after_label_read_input0 n)\<close>
        by (simp add: sg_first_propa_def sg_progress_def)
      also have \<open>... = graph_summar_nt (summ sg) (nxt sg) os\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_label_read_input0_def os_label_after_read_input0_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def
            os_first_propa_def os_progress_def os_label_after_first_propa_def
            os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs
            input_CONSUMES)
      then show ?thesis
        using G by (simp add: sg_first_propa_def sg_progress_def)
    qed
    have GR: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
        ((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n)))\<close>
    proof -
      have eq: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
          ((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n))) =
        graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n)\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_label_input0_def os_after_label_read_input0_def
            os_label_after_input0_def intsum_fst_label_prop_input0_batched
            op_state_base_def operator_state.defs fun_upd_def)

      show ?thesis
        using eq G_after_label_read_input0 by simp
    qed
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have IOC_label_read:
      \<open>input_ocaps_inv (os_label_after_read_input0 n)\<close>
      unfolding os_label_after_read_input0_def
      apply (rule input_ocaps_inv_CONSUMES)
      using label_prop_inv(6) os_inv(4)
      by (simp add: os_label_after_first_propa_def input_ocaps_inv_def operator_state.defs)
    have lpe:
      \<open>os_label_after_input0 n = operator_state.extend (op_state_base (os_label_after_input0 n))
        \<lparr>en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr,
          timestamps = timestamps (os_label_after_input0 n),
          graph = graph (os_label_after_input0 n),
          vertices = vertices (os_label_after_input0 n),
          label = label (os_label_after_input0 n)\<rparr>\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def op_state_base_def operator_state.defs os_inv(4)
          input_CONSUMES en1_fst_label_prop_input0_batched de1_fst_label_prop_input0_batched
          is_en1_fst_label_prop_input0_batched en2_fst_label_prop_input0_batched
          de2_fst_label_prop_input0_batched is_en2_fst_label_prop_input0_batched)



    have Intsum:
      \<open>\<forall>m. intsum (((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n))) m) =
        (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
      using os_inv(7)
      by (simp add: os_after_label_input0_def os_label_after_input0_def
          os_after_label_read_input0_def os_label_after_read_input0_def
          os_after_input_output_def os_input_after_output_def
          os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
          os_label_after_first_propa_def intsum_fst_label_prop_input0_batched intsum_consumes_fold
          op_state_base_def operator_state.defs os_inv(1) obtain_progress_def os_inv(4))

    have IOC1: \<open>input_ocaps_inv (os_label_after_input0 n)\<close>
    proof -
      have aux:
        \<open>msgs = input ls (0 :: 2) \<Longrightarrow> input_ocaps_inv ls \<Longrightarrow>
          input_ocaps_inv (fst (label_prop_input0_batched ls msgs))\<close>
        for ls :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close> and msgs
      proof (induct msgs arbitrary: ls)
        case Nil
        then show ?case by simp
      next
        case (Cons msg msgs)
        obtain d t where msg_eq: \<open>msg = (d, t)\<close>
          by (cases msg)
        have input_eq: \<open>input ls (0 :: 2) = (d, t) # msgs\<close>
          using Cons.prems(1) msg_eq by simp
        define ls' where \<open>ls' = label_prop_input0_step_state ls d t\<close>

        have step_inv: \<open>input_ocaps_inv ls'\<close>
          unfolding ls'_def
          by (rule input_ocaps_inv_label_prop_input0_step_stateI[OF Cons.prems(2)])
        have input_step: \<open>msgs = input ls' (0 :: 2)\<close>
          using input_eq
          by (simp add: ls'_def input_label_prop_input0_step_state)
        have rec: \<open>input_ocaps_inv (fst (label_prop_input0_batched ls' msgs))\<close>
          by (rule Cons.hyps[OF input_step step_inv])
        then show ?case
          using msg_eq
          by (cases \<open>label_prop_input0_batched ls' msgs\<close>) (simp add: ls'_def)

      qed
      show ?thesis
        unfolding os_label_after_input0_def
        by (rule aux[OF input_label_read[symmetric] IOC_label_read])

    qed
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)


    have INV: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)




    have LABELS:
      \<open>\<forall>t. labels_inv (all_edges (os_label_after_input0 n) t) (min_label (os_label_after_input0 n) t)\<close>
      unfolding os_label_after_input0_def
      apply (intro allI)
      apply (rule labels_inv_fst_label_prop_input0_batched_inputI[where msgs="label_input0_msgs n"])
         apply (rule input_label_read)
      using label_prop_inv(1)
        apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          input_CONSUMES all_vertices_def all_edges_def neighbors_def min_label_def)
       apply (rule INV_read)
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)

    show ?thesis
      apply (rule loop_updates_preserves_dataplane_tracker_inv
          [where cbufs="cbufs_after_label_read_input0 n"
            and os_label_prop="os_label_after_input0 n"
            and os="os_after_label_input0 n"
            and sg="sg_first_propa"
            and T="timestamps (os_label_after_input0 n)"
            and G="graph (os_label_after_input0 n)"
            and V="vertices (os_label_after_input0 n)"
            and L="label (os_label_after_input0 n)"])
                  apply (rule step)
                 apply (rule D_sg)
                apply (rule GR)
               apply (rule Nxt_sg)
              apply (rule Inv_step)
             apply (rule lpe)
            apply (rule Summ_sg)
           apply (rule Intsum)
          apply (rule IOC1)
         apply (rule IOC2)
        apply (rule INV)
       apply (rule LABELS)
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
       apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
             apply (simp add: input_label_read)
            apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
           apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
          apply (rule INV_read)
      subgoal
        using label_prop_inv(1)
        by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            input_CONSUMES all_vertices_def all_edges_def neighbors_def min_label_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done

  qed

  have input_0_after_loop_updates_empty:
    \<open>input (os_label_after_loop_updates n) (0 :: 2) = []\<close>
    for n
  proof -
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have input0_after_input0:
      \<open>input (os_label_after_input0 n) (0 :: 2) = []\<close>
      unfolding os_label_after_input0_def
      by (rule input_0_fst_label_prop_input0_batched_empty[OF input_label_read[symmetric]])
    have loop_input0:
      \<open>input (fst (snd (loop_updates (cbufs_after_label_read_input0 n)
        (os_label_after_input0 n) (os_after_label_input0 n)))) (0 :: 2) =
        input (os_label_after_input0 n) (0 :: 2)\<close>
      by (rule input_0_fst_snd_loop_updates)
    show ?thesis
      using input0_after_input0 loop_input0
      by (simp add: os_label_after_loop_updates_def loop_res_def)
  qed

  have input_1_after_loop_updates_empty:
    \<open>input (os_label_after_loop_updates n) (1 :: 2) = []\<close>
    for n
  proof -
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have INV0: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    have WF0:
      \<open>wf_label_prop_updates (os_label_after_input0 n)
        (set (input (os_label_after_input0 n) (1 :: 2)) \<union>
         set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
              outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
              map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
                 cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
                 outpu (os_label_after_input0 n) (1 :: 2))))\<close>
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
       apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
             apply (simp add: input_label_read)
            apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
           apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
          apply (rule INV_read)
      subgoal
        using labels_after_label_read_input0[of n]
        by simp
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done
    have EN0: \<open>en1 (os_label_after_input0 n) = Inl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          en1_fst_label_prop_input0_batched operator_state.defs)
    have DE0: \<open>de1 (os_label_after_input0 n) = projl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          de1_fst_label_prop_input0_batched operator_state.defs)
    have loop_input1:
      \<open>input (fst (snd (loop_updates (cbufs_after_label_read_input0 n)
        (os_label_after_input0 n) (os_after_label_input0 n)))) (1 :: 2) = []\<close>
      by (rule input_1_fst_snd_loop_updates_empty
          [where cbufs=\<open>cbufs_after_label_read_input0 n\<close>
            and os_label_prop=\<open>os_label_after_input0 n\<close>
            and os=\<open>os_after_label_input0 n\<close>,
            OF INV0 labels_after_label_input0[of n] WF0 EN0 DE0])
    show ?thesis
      using loop_input1
      by (simp add: os_label_after_loop_updates_def loop_res_def)
  qed

  have labels_after_loop_updates:
    \<open>\<forall>t. labels_inv (all_edges (os_label_after_loop_updates n) t) (min_label (os_label_after_loop_updates n) t)\<close>
    for n
  proof -
    have step:
      \<open>(cbufs_after_loop_updates n, os_label_after_loop_updates n, os_after_loop_updates n) =
        loop_updates (cbufs_after_label_read_input0 n) (os_label_after_input0 n) (os_after_label_input0 n)\<close>
      by (simp add: cbufs_after_loop_updates_def os_label_after_loop_updates_def
          os_after_loop_updates_def loop_res_def prod_eq_iff)
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have INV0: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    have WF0:
      \<open>wf_label_prop_updates (os_label_after_input0 n)
        (set (input (os_label_after_input0 n) (1 :: 2)) \<union>
         set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
              outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
              map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
                 cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
                 outpu (os_label_after_input0 n) (1 :: 2))))\<close>
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
       apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
             apply (simp add: input_label_read)
            apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
           apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
          apply (rule INV_read)
      subgoal
        using labels_after_label_read_input0[of n]
        by simp
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done
    have EN0: \<open>en1 (os_label_after_input0 n) = Inl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          en1_fst_label_prop_input0_batched operator_state.defs)
    have DE0: \<open>de1 (os_label_after_input0 n) = projl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          de1_fst_label_prop_input0_batched operator_state.defs)
    show ?thesis
      by (rule labels_inv_loop_updates_allI[OF step INV0 labels_after_label_input0 WF0 EN0 DE0])
  qed

  have label_prop_upd_inv_after_loop_updates:
    \<open>label_prop_upd_inv (os_label_after_loop_updates n)\<close>
    for n
  proof -
    have step:
      \<open>(cbufs_after_loop_updates n, os_label_after_loop_updates n, os_after_loop_updates n) =
        loop_updates (cbufs_after_label_read_input0 n) (os_label_after_input0 n) (os_after_label_input0 n)\<close>
      by (simp add: cbufs_after_loop_updates_def os_label_after_loop_updates_def
          os_after_loop_updates_def loop_res_def prod_eq_iff)
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have INV0: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    have WF0:
      \<open>wf_label_prop_updates (os_label_after_input0 n)
        (set (input (os_label_after_input0 n) (1 :: 2)) \<union>
         set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
              outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
              map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
                 cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
                 outpu (os_label_after_input0 n) (1 :: 2))))\<close>
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
       apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
             apply (simp add: input_label_read)
            apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
           apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
          apply (rule INV_read)
      subgoal
        using labels_after_label_read_input0[of n]
        by simp
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done
    have EN0: \<open>en1 (os_label_after_input0 n) = Inl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          en1_fst_label_prop_input0_batched operator_state.defs)
    have DE0: \<open>de1 (os_label_after_input0 n) = projl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          de1_fst_label_prop_input0_batched operator_state.defs)
    show ?thesis
      by (rule label_prop_upd_inv_loop_updatesI[OF step INV0 labels_after_label_input0[of n] WF0 EN0 DE0])
  qed

(* ----------------------------- *)
(* STEPS 8: op 1 drop all capabilities that may be left *)

  define os_after_loop_base where
    \<open>os_after_loop_base = (\<lambda>n. (os_after_loop_updates n)(1 := op_state_base (os_label_after_loop_updates n)))\<close>

  define os_label_after_drop_caps where
    \<open>os_label_after_drop_caps = (\<lambda>n. drop_caps (os_label_after_loop_updates n)
      (map (\<lambda>t. Cap t (1 :: 2)) (ocaps (os_label_after_loop_updates n) (1 :: 2))))\<close>

  define os_after_drop_caps where
    \<open>os_after_drop_caps = (\<lambda>n. (os_after_loop_updates n)(1 := op_state_base (os_label_after_drop_caps n)))\<close>

  have dataplane_after_drop_caps:
    \<open>dataplane_tracker_inv
      (os_after_drop_caps n) (cbufs_after_loop_updates n) sg_first_propa\<close>
    for n
  proof -
    have D_drop: \<open>dataflow_topology (summ sg_first_propa) (-+-)\<close>
      using D by (simp add: sg_first_propa_def sg_progress_def)
    have Nxt_drop: \<open>nxt sg_first_propa = graph_to_nxt (summ sg_first_propa)\<close>
      using subgraph_inv(2) by (simp add: sg_first_propa_def sg_progress_def)
    have Intsum_after_label_input0_pre:
      \<open>\<forall>m. intsum (((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n))) m) =
        (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
      using os_inv(7)
      by (simp add: os_after_label_input0_def os_label_after_input0_def
          os_after_label_read_input0_def os_label_after_read_input0_def
          os_after_input_output_def os_input_after_output_def
          os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
          os_label_after_first_propa_def intsum_fst_label_prop_input0_batched intsum_consumes_fold
          op_state_base_def operator_state.defs os_inv(1) obtain_progress_def os_inv(4))
    have Intsum_base:
      \<open>\<forall>m. intsum ((os_after_loop_base n) m) =
        (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
    proof -
      have step:
        \<open>(cbufs_after_loop_updates n, os_label_after_loop_updates n, os_after_loop_updates n)
          = loop_updates (cbufs_after_label_read_input0 n) (os_label_after_input0 n) (os_after_label_input0 n)\<close>
        by (simp add: cbufs_after_loop_updates_def os_label_after_loop_updates_def
            os_after_loop_updates_def loop_res_def prod_eq_iff)
      show ?thesis
        using loop_updates_intsum_corrected[OF step] Intsum_after_label_input0_pre
        by (simp add: os_after_loop_base_def)
    qed
    have G_base:
      \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_base n)\<close>
    proof -
      have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_base n) =
        graph_summar_nt (summ sg) (nxt sg) (os_after_loop_base n)\<close>
        by (simp add: sg_first_propa_def sg_progress_def)
      also have \<open>... = graph_summar_nt (summ sg) (nxt sg) os\<close>
        by (rule graph_summar_nt_intsum_cong) (use Intsum_base os_inv(7) in simp)
      finally show ?thesis
        using G by simp
    qed
    have base_inv:
      \<open>dataplane_tracker_inv (os_after_loop_base n) (cbufs_after_loop_updates n) sg_first_propa\<close>
      using dataplane_after_loop_updates[of n]
      by (simp add: os_after_loop_base_def)
    have drop_eq:
      \<open>os_after_drop_caps n =
        (os_after_loop_base n)(1 := drop_caps (os_after_loop_base n (1 :: 3))
          (map (\<lambda>t. Cap t (1 :: 2)) (ocaps (os_after_loop_base n (1 :: 3)) (1 :: 2))))\<close>
      by (simp add: os_after_drop_caps_def os_after_loop_base_def os_label_after_drop_caps_def
          op_state_base_def drop_caps_def operator_state.defs fun_upd_def)
    show ?thesis
      by (rule dataplane_tracker_inv_drop_caps_all
          [where os=\<open>os_after_loop_base n\<close> and nid=\<open>1 :: 3\<close> and p=\<open>1 :: 2\<close>,
            OF D_drop G_base Nxt_drop base_inv drop_eq])
  qed

(* ----------------------------- *)
(* STEPS 9: op 0 reports progress again *)
  define os_after_loop_progress where
    \<open>os_after_loop_progress = os_after_drop_caps\<close>


  define sg_after_ooo_input_progress where
    \<open>sg_after_ooo_input_progress = (\<lambda>n. sg_first_propa\<lparr>upfro := (\<lambda>_. True),
      pt_tr := change_multiplicities (summ sg_first_propa)
        (extract_progress (0 :: 3) (nxt sg_first_propa)
          (snd (obtain_progress (os_after_loop_progress n 0))))
        (pt_tr sg_first_propa)\<rparr>)\<close>

  define os_after_ooo_input_progress where
    \<open>os_after_ooo_input_progress = (\<lambda>n. (os_after_loop_progress n)
      (0 := op_state_base (fst (obtain_progress (os_after_loop_progress n 0)))))\<close>

  have D_loop: \<open>dataflow_topology (summ sg_first_propa) (-+-)\<close>
    using D by (simp add: sg_first_propa_def sg_progress_def)
  have G_after_label_read_input0:
    \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n)\<close>
    for n
  proof -
    have \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n) =
      graph_summar_nt (summ sg) (nxt sg) (os_after_label_read_input0 n)\<close>
      by (simp add: sg_first_propa_def sg_progress_def)
    also have \<open>... = graph_summar_nt (summ sg) (nxt sg) os\<close>
      by (rule graph_summar_nt_intsum_cong)
        (simp add: os_after_label_read_input0_def os_label_after_read_input0_def
          os_after_input_output_def os_input_after_output_def
          os_after_input_stream_def os_input_after_stream_def
          os_first_propa_def os_progress_def os_label_after_first_propa_def
          os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs
          input_CONSUMES intsum_consumes_fold)
    then show ?thesis
      using G by (simp add: sg_first_propa_def sg_progress_def)
  qed
  have G_after_label_input0:
    \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
      ((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n)))\<close>
    for n
  proof -
    have eq: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
        ((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n))) =
      graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_label_read_input0 n)\<close>
      by (rule graph_summar_nt_intsum_cong)
        (simp add: os_after_label_input0_def os_label_after_input0_def
          os_after_label_read_input0_def os_label_after_read_input0_def
          intsum_fst_label_prop_input0_batched op_state_base_def operator_state.defs fun_upd_def)

    show ?thesis
      using eq G_after_label_read_input0 by simp
  qed
  have Intsum_after_label_input0:
    \<open>\<forall>m. intsum (((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n))) m) =
      (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
    for n
    using os_inv(7)
    by (simp add: os_after_label_input0_def os_label_after_input0_def
        os_after_label_read_input0_def os_label_after_read_input0_def
        os_after_input_output_def os_input_after_output_def
        os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
        os_label_after_first_propa_def intsum_fst_label_prop_input0_batched intsum_consumes_fold
        op_state_base_def operator_state.defs os_inv(1) obtain_progress_def os_inv(4))
  have step_loop:
    \<open>(cbufs_after_loop_updates n, os_label_after_loop_updates n, os_after_loop_updates n)
      = loop_updates (cbufs_after_label_read_input0 n) (os_label_after_input0 n) (os_after_label_input0 n)\<close>
    for n
    by (simp add: cbufs_after_loop_updates_def os_label_after_loop_updates_def
        os_after_loop_updates_def loop_res_def prod_eq_iff)
  have ocaps_1_os2_after_loop_updates_empty:
    \<open>ocaps ((os_after_loop_updates n) 2) (1 :: 2) = []\<close>
    for n
  proof -
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have INV0: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    have WF0:
      \<open>wf_label_prop_updates (os_label_after_input0 n)
        (set (input (os_label_after_input0 n) (1 :: 2)) \<union>
         set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
              outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
              map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
                 cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
                 outpu (os_label_after_input0 n) (1 :: 2))))\<close>
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
       apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
             apply (simp add: input_label_read)
            apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
           apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
          apply (rule INV_read)
      subgoal
        using labels_after_label_read_input0[of n]
        by simp
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done
    have EN0: \<open>en1 (os_label_after_input0 n) = Inl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          en1_fst_label_prop_input0_batched operator_state.defs)
    have DE0: \<open>de1 (os_label_after_input0 n) = projl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          de1_fst_label_prop_input0_batched operator_state.defs)
    have loop_empty:
      \<open>ocaps ((snd (snd (loop_updates (cbufs_after_label_read_input0 n)
        (os_label_after_input0 n) (os_after_label_input0 n)))) 2) (1 :: 2) = []\<close>
      by (rule ocaps_1_snd_snd_loop_updates_empty
          [where cbufs=\<open>cbufs_after_label_read_input0 n\<close>
            and os_label_prop=\<open>os_label_after_input0 n\<close>
            and os=\<open>os_after_label_input0 n\<close>,
            OF Intsum_after_label_input0[of n] INV0 labels_after_label_input0[of n] WF0 EN0 DE0])
    then show ?thesis
      by (simp add: os_after_loop_updates_def loop_res_def)
  qed

  have outpu_1_after_loop_updates_empty:
    \<open>outpu (os_label_after_loop_updates n) (1 :: 2) = []\<close>
    \<open>outpu ((os_after_loop_updates n) 2) (1 :: 2) = []\<close>
    \<open>input ((os_after_loop_updates n) 2) (1 :: 2) = []\<close>
    \<open>input_ocaps_inv ((os_after_loop_updates n) 2)\<close>
    for n
  proof -
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have INV0: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    have WF0:
      \<open>wf_label_prop_updates (os_label_after_input0 n)
        (set (input (os_label_after_input0 n) (1 :: 2)) \<union>
         set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
              outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
              map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
                 cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
                 outpu (os_label_after_input0 n) (1 :: 2))))\<close>
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
       apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
             apply (simp add: input_label_read)
            apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
           apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
          apply (rule INV_read)
      subgoal
        using labels_after_label_read_input0[of n]
        by simp
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done
    have EN0: \<open>en1 (os_label_after_input0 n) = Inl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          en1_fst_label_prop_input0_batched operator_state.defs)
    have DE0: \<open>de1 (os_label_after_input0 n) = projl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          de1_fst_label_prop_input0_batched operator_state.defs)
    have IOC0: \<open>input_ocaps_inv ((os_after_label_input0 n) 2)\<close>
      using os_inv(8)
      by (simp add: os_after_label_input0_def os_after_label_read_input0_def
          os_after_input_output_def os_after_input_stream_def
          os_first_propa_def os_progress_def)
    have label_out:
      \<open>outpu (fst (snd (loop_updates (cbufs_after_label_read_input0 n)
        (os_label_after_input0 n) (os_after_label_input0 n)))) (1 :: 2) = []\<close>
      by (rule outpu_1_fst_snd_loop_updates_empty
          [where cbufs=\<open>cbufs_after_label_read_input0 n\<close>
            and os_label_prop=\<open>os_label_after_input0 n\<close>
            and os=\<open>os_after_label_input0 n\<close>,
            OF INV0 labels_after_label_input0[of n] WF0 EN0 DE0])
    have os2_out:
      \<open>outpu ((snd (snd (loop_updates (cbufs_after_label_read_input0 n)
        (os_label_after_input0 n) (os_after_label_input0 n)))) 2) (1 :: 2) = []\<close>
      by (rule outpu_1_snd_snd_loop_updates_empty
          [where cbufs=\<open>cbufs_after_label_read_input0 n\<close>
            and os_label_prop=\<open>os_label_after_input0 n\<close>
            and os=\<open>os_after_label_input0 n\<close>,
            OF INV0 labels_after_label_input0[of n] WF0 EN0 DE0])
    have os2_input:
      \<open>input ((snd (snd (loop_updates (cbufs_after_label_read_input0 n)
        (os_label_after_input0 n) (os_after_label_input0 n)))) 2) (1 :: 2) = []\<close>
      by (rule input_1_snd_snd_loop_updates_empty
          [where cbufs=\<open>cbufs_after_label_read_input0 n\<close>
            and os_label_prop=\<open>os_label_after_input0 n\<close>
            and os=\<open>os_after_label_input0 n\<close>,
            OF INV0 labels_after_label_input0[of n] WF0 EN0 DE0])
    show \<open>outpu (os_label_after_loop_updates n) (1 :: 2) = []\<close>
      using label_out by (simp add: os_label_after_loop_updates_def loop_res_def)
    show \<open>outpu ((os_after_loop_updates n) 2) (1 :: 2) = []\<close>
      using os2_out by (simp add: os_after_loop_updates_def loop_res_def)
    show \<open>input ((os_after_loop_updates n) 2) (1 :: 2) = []\<close>
      using os2_input by (simp add: os_after_loop_updates_def loop_res_def)
    show \<open>input_ocaps_inv ((os_after_loop_updates n) 2)\<close>
      by (rule input_ocaps_inv_snd_snd_loop_updates2
          [OF step_loop[of n] IOC0 Intsum_after_label_input0[of n]
            EN0 DE0 INV0 labels_after_label_input0[of n] WF0])
  qed


  have wf_after_loop_updates_pending:
    \<open>wf_label_prop_updates (os_label_after_loop_updates n)
      (set (input (os_label_after_loop_updates n) (1 :: 2)) \<union>
       set (cbufs_after_loop_updates n ((1 :: 3), (1 :: 2)) @
            outpu ((os_after_loop_updates n) (2 :: 3)) (1 :: 2) @
            map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
              (input ((os_after_loop_updates n) (2 :: 3)) (1 :: 2) @
               cbufs_after_loop_updates n ((2 :: 3), (1 :: 2)) @
               outpu (os_label_after_loop_updates n) (1 :: 2))))\<close>
    for n
  proof -
    have input_label_read:
      \<open>input (os_label_after_read_input0 n) (0 :: 2) = label_input0_msgs n\<close>
      using os_inv(4)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          label_input0_msgs_def input_CONSUMES operator_state.defs)
    have INV_read: \<open>label_prop_upd_inv (os_label_after_read_input0 n)\<close>
      using label_prop_inv(5)
      by (simp add: os_label_after_read_input0_def os_label_after_first_propa_def input_CONSUMES)
    have INV0: \<open>label_prop_upd_inv (os_label_after_input0 n)\<close>
      unfolding os_label_after_input0_def
      apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI[OF input_label_read INV_read])
      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
      by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
          all_vertices_def all_edges_def neighbors_def)
    have WF0:
      \<open>wf_label_prop_updates (os_label_after_input0 n)
        (set (input (os_label_after_input0 n) (1 :: 2)) \<union>
         set (cbufs_after_label_read_input0 n ((1 :: 3), (1 :: 2)) @
              outpu (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
              map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                (input (os_after_label_input0 n (2 :: 3)) (1 :: 2) @
                 cbufs_after_label_read_input0 n ((2 :: 3), (1 :: 2)) @
                 outpu (os_label_after_input0 n) (1 :: 2))))\<close>
      unfolding os_label_after_input0_def
      apply (rule wf_label_prop_updates_subset)
       apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
          [where S=\<open>set (input os_label_prop (1 :: 2)) \<union>
          (set (cbufs ((1 :: 3), (1 :: 2))) \<union>
            (set (outpu (os (2 :: 3)) (1 :: 2)) \<union>
              ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (input (os (2 :: 3)) (1 :: 2)) \<union>
                ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (cbufs ((2 :: 3), (1 :: 2)))))))\<close>
            and rest=\<open>[]\<close>])
             apply (simp add: input_label_read)
            apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
           apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
          os_inv(4) operator_state.defs input_CONSUMES)
          apply (rule INV_read)
      subgoal
        using labels_after_label_read_input0[of n]
        by simp
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
            all_vertices_def all_edges_def neighbors_def)
      subgoal
        by (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
            os_after_label_input0_def os_after_label_read_input0_def
            cbufs_after_label_read_input0_def cbufs_after_input_output_def
            os_after_input_output_def os_input_after_output_def
            os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
            os_inv(1,4) operator_state.defs input_CONSUMES input_fst_label_prop_input0_batched
            fun_upd_def)
      done
    have EN0: \<open>en1 (os_label_after_input0 n) = Inl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          en1_fst_label_prop_input0_batched operator_state.defs)
    have DE0: \<open>de1 (os_label_after_input0 n) = projl\<close>
      by (simp add: os_label_after_input0_def os_label_after_read_input0_def
          os_label_after_first_propa_def os_inv(4) input_CONSUMES
          de1_fst_label_prop_input0_batched operator_state.defs)
    show ?thesis
      by (rule loop_updates_msgs_invI[OF step_loop[of n] EN0 DE0 INV0 labels_after_label_input0[of n] WF0])
  qed


  have Intsum_loop:
    \<open>\<forall>m. intsum ((os_after_loop_progress n) m) =
      (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
    for n
  proof
    fix m :: 3
    have base:
      \<open>intsum (((os_after_loop_updates n)(1 := op_state_base (os_label_after_loop_updates n))) m) =
        (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
      using loop_updates_intsum_corrected[OF step_loop[of n]] Intsum_after_label_input0[of n]
      by auto
    show \<open>intsum ((os_after_loop_progress n) m) =
        (\<lambda>p1 p2. raw_summary (Loc m (Trg p1)) (Loc m (Src p2)))\<close>
      using base
      by (cases \<open>m = (1 :: 3)\<close>)
        (simp_all add: os_after_loop_progress_def os_after_drop_caps_def
          os_label_after_drop_caps_def op_state_base_def drop_caps_def operator_state.defs fun_upd_def)
  qed

  have G_loop:
    \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_progress n)\<close>
    for n
  proof -
    have eq: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_progress n) =
      graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
        ((os_after_label_input0 n)(1 := op_state_base (os_label_after_input0 n)))\<close>
      by (rule graph_summar_nt_intsum_cong)
        (use Intsum_loop Intsum_after_label_input0 in simp)
    show ?thesis
      using eq G_after_label_input0 by simp
  qed

  have dataplane_after_ooo_input_progress:
    \<open>dataplane_tracker_inv
      (os_after_ooo_input_progress n) (cbufs_after_loop_updates n)
      (sg_after_ooo_input_progress n)\<close>
    for n
  proof -
    have inv_no_upfro:
      \<open>dataplane_tracker_inv
        ((os_after_loop_progress n)(0 := fst (obtain_progress (os_after_loop_progress n 0))))
        (cbufs_after_loop_updates n)
        (sg_first_propa\<lparr>pt_tr := change_multiplicities (summ sg_first_propa)
          (extract_progress (0 :: 3) (nxt sg_first_propa)
            (snd (obtain_progress (os_after_loop_progress n 0))))
          (pt_tr sg_first_propa)\<rparr>)\<close>
      apply (rule dataplane_tracker_inv_progress
          [where os="os_after_loop_progress n" and cbufs="cbufs_after_loop_updates n"
            and sg="sg_first_propa" and nid="0 :: 3"])
      using dataplane_after_drop_caps[of n]
         apply (simp add: os_after_loop_progress_def)
        apply (rule D_loop)
       apply (rule G_loop)
      apply (rule refl)
      done

    have clean_upfro:
      \<open>dataplane_tracker_inv
        (os_after_ooo_input_progress n) (cbufs_after_loop_updates n)
        (sg_after_ooo_input_progress n) \<longleftrightarrow>
       dataplane_tracker_inv
        ((os_after_loop_progress n)(0 := fst (obtain_progress (os_after_loop_progress n 0))))
        (cbufs_after_loop_updates n)
        (sg_first_propa\<lparr>pt_tr := change_multiplicities (summ sg_first_propa)
          (extract_progress (0 :: 3) (nxt sg_first_propa)
            (snd (obtain_progress (os_after_loop_progress n 0))))
          (pt_tr sg_first_propa)\<rparr>)\<close>
      by (rule dataplane_tracker_inv_clean[where f=\<open>\<lambda>_. True\<close>];
          (simp add: sg_after_ooo_input_progress_def os_after_ooo_input_progress_def
            os_after_loop_progress_def op_state_base_def operator_state.defs obtain_progress_def
            flip: map_append filter_append fold_append))
    show ?thesis
      using clean_upfro inv_no_upfro by simp
  qed

  have G_ooo:
    \<open>graph_summar_nt (summ (sg_after_ooo_input_progress n)) (nxt (sg_after_ooo_input_progress n))
      (os_after_ooo_input_progress n)\<close>
    for n
  proof -
    have eq0:
      \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
        (os_after_ooo_input_progress n) =
       graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_progress n)\<close>
      by (rule graph_summar_nt_intsum_cong)
        (simp add: os_after_ooo_input_progress_def os_after_loop_progress_def
          op_state_base_def operator_state.defs obtain_progress_def flip: map_append filter_append fold_append)
    show ?thesis
      using eq0 G_loop by (simp add: sg_after_ooo_input_progress_def)

  qed


(* ----------------------------- *)
(* STEPS 10: op 1 reports progress *)
  define os_label_after_label_progress where
    \<open>os_label_after_label_progress = (\<lambda>n. fst (obtain_progress (os_label_after_drop_caps n)))\<close>

  define sg_after_label_progress where
    \<open>sg_after_label_progress = (\<lambda>n. (sg_after_ooo_input_progress n)\<lparr>upfro := (\<lambda>_. True),
      pt_tr := change_multiplicities (summ (sg_after_ooo_input_progress n))
        (extract_progress (1 :: 3) (nxt (sg_after_ooo_input_progress n))
          (snd (obtain_progress (os_label_after_drop_caps n))))
        (pt_tr (sg_after_ooo_input_progress n))\<rparr>)\<close>

  define os_after_label_progress where
    \<open>os_after_label_progress = (\<lambda>n. (os_after_ooo_input_progress n)
      (1 := op_state_base (os_label_after_label_progress n)))\<close>

  have dataplane_after_label_progress:
    \<open>dataplane_tracker_inv
      (os_after_label_progress n) (cbufs_after_loop_updates n)
      (sg_after_label_progress n)\<close>
    for n
  proof -
    have D_ooo: \<open>dataflow_topology (summ (sg_after_ooo_input_progress n)) (-+-)\<close>
      using D by (simp add: sg_after_ooo_input_progress_def sg_first_propa_def sg_progress_def)
    have progress_st:
      \<open>snd (obtain_progress (os_label_after_drop_caps n)) =
        snd (obtain_progress (os_after_ooo_input_progress n 1))\<close>
      by (simp add: os_after_ooo_input_progress_def os_after_loop_progress_def
          os_after_drop_caps_def op_state_base_def operator_state.defs obtain_progress_def fun_upd_def)
    have base_progress:
      \<open>fst (obtain_progress (os_after_ooo_input_progress n 1)) =
        op_state_base (os_label_after_label_progress n)\<close>
      by (simp add: os_label_after_label_progress_def os_after_ooo_input_progress_def
          os_after_loop_progress_def os_after_drop_caps_def op_state_base_def
          operator_state.defs obtain_progress_def fun_upd_def)
    have inv_progress:
      \<open>dataplane_tracker_inv
        ((os_after_ooo_input_progress n)(1 := fst (obtain_progress (os_after_ooo_input_progress n 1))))
        (cbufs_after_loop_updates n)
        ((sg_after_ooo_input_progress n)\<lparr>pt_tr := change_multiplicities (summ (sg_after_ooo_input_progress n))
          (extract_progress (1 :: 3) (nxt (sg_after_ooo_input_progress n))
            (snd (obtain_progress (os_label_after_drop_caps n))))
          (pt_tr (sg_after_ooo_input_progress n))\<rparr>)\<close>
      apply (rule dataplane_tracker_inv_progress
          [where os="os_after_ooo_input_progress n"
            and cbufs="cbufs_after_loop_updates n"
            and sg="sg_after_ooo_input_progress n"
            and nid="1 :: 3"
            and st="snd (obtain_progress (os_label_after_drop_caps n))"])
         apply (rule dataplane_after_ooo_input_progress)
        apply (rule D_ooo)
       apply (rule G_ooo)
      apply (rule progress_st)
      done

    show ?thesis
      using inv_progress base_progress
      by (simp add: os_after_label_progress_def sg_after_label_progress_def sg_after_ooo_input_progress_def)

  qed

  have labels_after_label_progress:
    \<open>\<forall>t. labels_inv (all_edges (os_label_after_label_progress n) t) (min_label (os_label_after_label_progress n) t)\<close>
    for n
    using labels_after_loop_updates[of n]
    by (simp add: os_label_after_label_progress_def os_label_after_drop_caps_def
        obtain_progress_def op_state_base_def operator_state.defs all_edges_def all_vertices_def
        min_label_def drop_caps_def flip: map_append filter_append fold_append)

(* ----------------------------- *)
(* STEPS 11: op 2 reports progress *)
  define sg_after_increment_progress where
    \<open>sg_after_increment_progress = (\<lambda>n. (sg_after_label_progress n)\<lparr>upfro := (\<lambda>_. True),
      pt_tr := change_multiplicities (summ (sg_after_label_progress n))
        (extract_progress (2 :: 3) (nxt (sg_after_label_progress n))
          (snd (obtain_progress (os_after_label_progress n 2))))
        (pt_tr (sg_after_label_progress n))\<rparr>)\<close>

  define os_after_increment_progress where
    \<open>os_after_increment_progress = (\<lambda>n. (os_after_label_progress n)
      (2 := op_state_base (fst (obtain_progress (os_after_label_progress n 2)))))\<close>
  have dataplane_after_increment_progress:
    \<open>dataplane_tracker_inv
      (os_after_increment_progress n) (cbufs_after_loop_updates n)
      (sg_after_increment_progress n)\<close>
    for n
  proof -
    have D_label: \<open>dataflow_topology (summ (sg_after_label_progress n)) (-+-)\<close>
      using D by (simp add: sg_after_label_progress_def sg_after_ooo_input_progress_def
          sg_first_propa_def sg_progress_def)
    have G_label:
      \<open>graph_summar_nt (summ (sg_after_label_progress n)) (nxt (sg_after_label_progress n))
        (os_after_label_progress n)\<close>
    proof -
      have intsum_eq:
        \<open>\<And>nid. intsum (os_after_label_progress n nid) =
          intsum (os_after_ooo_input_progress n nid)\<close>
      proof -
        fix nid :: 3
        show \<open>intsum (os_after_label_progress n nid) =
          intsum (os_after_ooo_input_progress n nid)\<close>
        proof (cases \<open>nid = (1 :: 3)\<close>)
          case True
          then show ?thesis
            by (simp add: os_after_label_progress_def os_label_after_label_progress_def
                os_after_ooo_input_progress_def os_after_loop_progress_def os_after_drop_caps_def
                op_state_base_def operator_state.defs obtain_progress_def fun_upd_def)
        next
          case False
          then show ?thesis
            by (simp add: os_after_label_progress_def fun_upd_def)
        qed
      qed
      have eq0:
        \<open>graph_summar_nt (summ (sg_after_ooo_input_progress n)) (nxt (sg_after_ooo_input_progress n))
          (os_after_label_progress n) =
         graph_summar_nt (summ (sg_after_ooo_input_progress n)) (nxt (sg_after_ooo_input_progress n))
          (os_after_ooo_input_progress n)\<close>
        by (rule graph_summar_nt_intsum_cong) (rule intsum_eq)

      show ?thesis
        using eq0 G_ooo by (simp add: sg_after_label_progress_def)
    qed

    have base_progress:
      \<open>fst (obtain_progress (os_after_label_progress n 2)) =
        op_state_base (fst (obtain_progress (os_after_label_progress n 2)))\<close>
      by (simp add: op_state_base_def operator_state.defs)
    have inv_progress:
      \<open>dataplane_tracker_inv
        ((os_after_label_progress n)(2 := fst (obtain_progress (os_after_label_progress n 2))))
        (cbufs_after_loop_updates n)
        ((sg_after_label_progress n)\<lparr>pt_tr := change_multiplicities (summ (sg_after_label_progress n))
          (extract_progress (2 :: 3) (nxt (sg_after_label_progress n))
            (snd (obtain_progress (os_after_label_progress n 2))))
          (pt_tr (sg_after_label_progress n))\<rparr>)\<close>
      by (rule dataplane_tracker_inv_progress[OF dataplane_after_label_progress D_label G_label refl])
    have \<open>sg_after_label_progress n \<lparr>upfro := \<lambda>_. True\<rparr> = sg_after_label_progress n\<close>
      unfolding sg_after_label_progress_def sg_after_ooo_input_progress_def
      by simp
    then show ?thesis
      using inv_progress base_progress
      by (simp add: os_after_increment_progress_def sg_after_increment_progress_def)

  qed

  obtain caps' where dt_inv':
    \<open>Src_caps_inv (caps' n) (os_after_loop_progress n)\<close>
    \<open>Trg_caps_inv (caps' n) (outputs_at_target (summ sg_first_propa)
      (os_after_loop_progress n) >> (cbufs_after_loop_updates n))\<close>
    \<open>c_pts_inv
      (change_multiplicities (summ sg_first_propa)
        (extract_prog Enum.enum (nxt sg_first_propa) (os_after_loop_progress n))
        (pt_tr sg_first_propa)) (caps' n)\<close>
    \<open>front_inv (os_after_loop_progress n) (pt_tr sg_first_propa)\<close>
    \<open>imp_front_inv (summ sg_first_propa) (pt_tr sg_first_propa)\<close>
    \<open>chnls_imp_front_inv (summ sg_first_propa) (pt_tr sg_first_propa)
      (outputs_at_target (summ sg_first_propa)
        (os_after_loop_progress n) >> (cbufs_after_loop_updates n))\<close>
    \<open>change_deltas_inv (os_after_loop_progress n)\<close>
    \<open>propagation_inv (summ sg_first_propa) (pt_tr sg_first_propa)\<close>
    \<open>extract_prog_changes_above_impl_inv (summ sg_first_propa) (nxt sg_first_propa)
      (pt_tr sg_first_propa) (os_after_loop_progress n)\<close>
    \<open>produ_consu_inter_supported (nxt sg_first_propa)
      (os_after_loop_progress n) (pt_tr sg_first_propa)\<close>
  for n
  proof -
    have ex_caps:
      \<open>\<forall>n. \<exists>cap.
        Src_caps_inv cap (os_after_loop_progress n) \<and>
        Trg_caps_inv cap (outputs_at_target (summ sg_first_propa)
          (os_after_loop_progress n) >> (cbufs_after_loop_updates n)) \<and>
        c_pts_inv
          (change_multiplicities (summ sg_first_propa)
            (extract_prog Enum.enum (nxt sg_first_propa) (os_after_loop_progress n))
            (pt_tr sg_first_propa)) cap \<and>
        front_inv (os_after_loop_progress n) (pt_tr sg_first_propa) \<and>
        imp_front_inv (summ sg_first_propa) (pt_tr sg_first_propa) \<and>
        chnls_imp_front_inv (summ sg_first_propa) (pt_tr sg_first_propa)
          (outputs_at_target (summ sg_first_propa)
            (os_after_loop_progress n) >> (cbufs_after_loop_updates n)) \<and>
        change_deltas_inv (os_after_loop_progress n) \<and>
        propagation_inv (summ sg_first_propa) (pt_tr sg_first_propa) \<and>
        extract_prog_changes_above_impl_inv (summ sg_first_propa) (nxt sg_first_propa)
          (pt_tr sg_first_propa) (os_after_loop_progress n) \<and>
        produ_consu_inter_supported (nxt sg_first_propa)
          (os_after_loop_progress n) (pt_tr sg_first_propa)\<close>
    proof
      fix n
      show \<open>\<exists>cap.
        Src_caps_inv cap (os_after_loop_progress n) \<and>
        Trg_caps_inv cap (outputs_at_target (summ sg_first_propa)
          (os_after_loop_progress n) >> (cbufs_after_loop_updates n)) \<and>
        c_pts_inv
          (change_multiplicities (summ sg_first_propa)
            (extract_prog Enum.enum (nxt sg_first_propa) (os_after_loop_progress n))
            (pt_tr sg_first_propa)) cap \<and>
        front_inv (os_after_loop_progress n) (pt_tr sg_first_propa) \<and>
        imp_front_inv (summ sg_first_propa) (pt_tr sg_first_propa) \<and>
        chnls_imp_front_inv (summ sg_first_propa) (pt_tr sg_first_propa)
          (outputs_at_target (summ sg_first_propa)
            (os_after_loop_progress n) >> (cbufs_after_loop_updates n)) \<and>
        change_deltas_inv (os_after_loop_progress n) \<and>
        propagation_inv (summ sg_first_propa) (pt_tr sg_first_propa) \<and>
        extract_prog_changes_above_impl_inv (summ sg_first_propa) (nxt sg_first_propa)
          (pt_tr sg_first_propa) (os_after_loop_progress n) \<and>
        produ_consu_inter_supported (nxt sg_first_propa)
          (os_after_loop_progress n) (pt_tr sg_first_propa)\<close>
        using dataplane_after_drop_caps[of n, unfolded dataplane_tracker_inv_def]
        by (simp add: os_after_loop_progress_def)
    qed
    show ?thesis
      using choice[OF ex_caps] that by blast
  qed

  define second_progress where \<open>second_progress = (\<lambda>n.
    extract_progress (0 :: 3) (nxt sg_first_propa)
      (snd (obtain_progress (os_after_loop_progress n 0))) @
    extract_progress (1 :: 3) (nxt sg_first_propa)
      (snd (obtain_progress (os_label_after_drop_caps n))) @
    extract_progress (2 :: 3) (nxt sg_first_propa)
      (snd (obtain_progress (os_after_loop_progress n 2))))\<close>

  have c_pts_after_second_progress_caps':
    \<open>c_pts (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary)
      (second_progress n) c') l = caps' n l\<close>
    for n l
    using dt_inv'(3)[of n]
    by (simp add: c_pts_inv_def second_progress_def extract_prog_def
        sg_first_propa_def sg_progress_def os_after_loop_progress_def os_after_drop_caps_def
        subgraph_inv(1,2) op_state_base_def operator_state.defs obtain_progress_def
        flip: fold_append change_multiplicities_append_alt)

  obtain c'' where second_propa:
    \<open>propagate_all (summ sg_first_propa)
      (change_multiplicities (summ sg_first_propa) (second_progress n) (pt_tr sg_first_propa)) = Some (c'' n)\<close>
    \<open>\<forall>loc. frontier (c_imp (c'' n) loc) =
      ifrontier (summ sg_first_propa) (-+-)
        (change_multiplicities (summ sg_first_propa) (second_progress n) (pt_tr sg_first_propa)) loc\<close>
    \<open>dataflow_topology_from_tree.inv_implications_nonneg (c'' n)\<close>
    \<open>dataflow_topology_from_tree.inv_imp_plus_work_nonneg (c'' n)\<close>
    \<open>dataflow_topology.inv_imps_work_sum (summ sg_first_propa) (-+-) (c'' n)\<close>
  for n
  proof -
    have ex_c:
      \<open>\<forall>n. \<exists>c2.
        propagate_all (summ sg_first_propa)
          (change_multiplicities (summ sg_first_propa) (second_progress n) (pt_tr sg_first_propa)) = Some c2 \<and>
        (\<forall>loc. frontier (c_imp c2 loc) =
          ifrontier (summ sg_first_propa) (-+-)
            (change_multiplicities (summ sg_first_propa) (second_progress n) (pt_tr sg_first_propa)) loc) \<and>
        dataflow_topology_from_tree.inv_implications_nonneg c2 \<and>
        dataflow_topology_from_tree.inv_imp_plus_work_nonneg c2 \<and>
        dataflow_topology.inv_imps_work_sum (summ sg_first_propa) (-+-) c2\<close>
    proof
      fix n
      show \<open>\<exists>c2.
        propagate_all (summ sg_first_propa)
          (change_multiplicities (summ sg_first_propa) (second_progress n) (pt_tr sg_first_propa)) = Some c2 \<and>
        (\<forall>loc. frontier (c_imp c2 loc) =
          ifrontier (summ sg_first_propa) (-+-)
            (change_multiplicities (summ sg_first_propa) (second_progress n) (pt_tr sg_first_propa)) loc) \<and>
        dataflow_topology_from_tree.inv_implications_nonneg c2 \<and>
        dataflow_topology_from_tree.inv_imp_plus_work_nonneg c2 \<and>
        dataflow_topology.inv_imps_work_sum (summ sg_first_propa) (-+-) c2\<close>
        using propagate_all_frontier_change_multiplicities_c_imp_correctnessE
          [OF D, of \<open>pt_tr sg_first_propa\<close> \<open>second_progress n\<close>,
            unfolded subgraph_inv(1), simplified]
        apply -
        apply (drule meta_mp)
        subgoal
          using dt_inv'(8)[unfolded propagation_inv_def] subgraph_inv(1)
          by (simp add: sg_first_propa_def sg_progress_def)



        apply (drule meta_mp)
        subgoal
          using dt_inv'(8)[unfolded propagation_inv_def] subgraph_inv(1) by auto
        apply (drule meta_mp)
        subgoal
          using dt_inv'(8)[unfolded propagation_inv_def] subgraph_inv(1) by auto


        apply (drule meta_mp)
        subgoal
          apply (clarsimp simp flip: fold_append change_multiplicities_append_alt
              simp add: second_progress_def split_beta Misc.set_map_filter op_state_base_def
              extract_progress_def image_iff
              split: prod.splits option.splits event.splits)

          subgoal for l t
            apply (elim disjE exE; (clarsimp simp add: obtain_progress_def Misc.set_map_filter image_iff del: disjCI split: option.splits event.splits)?)
            subgoal for p
              using conjunct1[OF dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format,
                    of p t 0 0, simplified]]
              by (simp add: os_after_loop_progress_def)
            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format,
                  of p t 0 0, simplified]
              by (simp add: os_after_loop_progress_def)



            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format, of p t 0 0, simplified] apply -
              by (clarsimp simp add: os_after_loop_progress_def op_state_base_def obtain_progress_def Misc.set_map_filter image_iff del: disjCI split: option.splits event.splits)


            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format, of p t 0 1, simplified] apply -
              by (clarsimp simp add: os_after_loop_progress_def os_after_drop_caps_def
                  op_state_base_def obtain_progress_def Misc.set_map_filter image_iff
                  del: disjCI split: option.splits event.splits)
            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format, of p t 0 1, simplified] apply -
              by (clarsimp simp add: os_after_loop_progress_def os_after_drop_caps_def
                  op_state_base_def obtain_progress_def Misc.set_map_filter image_iff
                  del: disjCI split: option.splits event.splits)
            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format, of p t 0 1, simplified] apply -
              by (clarsimp simp add: os_after_loop_progress_def os_after_drop_caps_def
                  op_state_base_def obtain_progress_def Misc.set_map_filter image_iff
                  del: disjCI split: option.splits event.splits)
            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format, of p t 0 2, simplified] apply -
              by (clarsimp simp add: op_state_base_def obtain_progress_def Misc.set_map_filter image_iff del: disjCI split: option.splits event.splits)
            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format, of p t 0 2, simplified] apply -
              by (clarsimp simp add: op_state_base_def obtain_progress_def Misc.set_map_filter image_iff del: disjCI split: option.splits event.splits)
            subgoal for p
              using dt_inv'(7)[of n, unfolded change_deltas_inv_def, rule_format, of p t 0 2, simplified] apply -
              by (clarsimp simp add: op_state_base_def obtain_progress_def Misc.set_map_filter image_iff del: disjCI split: option.splits event.splits)
            done

          done
        apply (drule meta_mp)
        subgoal
          apply (clarsimp simp add: second_progress_def)

          subgoal for l t m
            apply (subst frontier_less_equal_iff2[symmetric])
            apply (rule frontier_less_equal_le_trans
                [of \<open>ifrontier (summ sg_first_propa) (+) (pt_tr sg_first_propa) l\<close>])
            subgoal
              apply (elim disjE)
              subgoal
                using dt_inv'(9)[of n, unfolded extract_prog_changes_above_impl_inv_def
                    changes_above_impl_inv_def, simplified, rule_format,
                    where xs=Nil and nid=0, simplified]
                apply (clarsimp simp add: os_after_loop_progress_def op_state_base_def obtain_progress_def subgraph_inv(1,2) set_map_filter
                    split_beta operator_state.defs os_inv(1) image_iff split: option.splits)

                done
              subgoal
                using dt_inv'(9)[of n, unfolded extract_prog_changes_above_impl_inv_def
                    changes_above_impl_inv_def, simplified, rule_format,
                    where xs=Nil and nid=1, simplified]
                apply (clarsimp simp add: os_after_loop_progress_def os_after_drop_caps_def
                    op_state_base_def obtain_progress_def subgraph_inv(1,2) set_map_filter
                    split_beta operator_state.defs os_inv(1) image_iff split: option.splits)
                done
              subgoal
                using dt_inv'(9)[of n, unfolded extract_prog_changes_above_impl_inv_def
                    changes_above_impl_inv_def, simplified, rule_format,
                    where xs=Nil and nid=2, simplified]
                apply (clarsimp simp add: op_state_base_def obtain_progress_def subgraph_inv(1,2) set_map_filter
                    split_beta operator_state.defs os_inv(1) image_iff split: option.splits)
                done
              done
            using dt_inv'(5)[unfolded imp_front_inv_def, rule_format, of l] by simp
          done
        apply (drule meta_mp)
        subgoal
          using raw_summary_no_self_loop by auto
        by (clarsimp simp flip: fold_append map_append
            simp add: sg_first_propa_def sg_progress_def subgraph_inv(1,2) CONSUMES_CONSUMES)

    qed
    show ?thesis
      using choice[OF ex_c] that by blast
  qed

(* STEPS 12: op 1 reads the final frontier from the propagation *)
  define label_front_after_second_propa where
    \<open>label_front_after_second_propa = (\<lambda>n. frontier \<circ> (\<lambda>p. c_imp (c'' n) (Loc (1 :: 3) (Trg p))))\<close>

  define os_label_after_second_propa where
    \<open>os_label_after_second_propa = (\<lambda>n. (os_label_after_label_progress n)\<lparr>
      front := label_front_after_second_propa n, initia := True\<rparr>)\<close>

  define sg_after_second_propa where
    \<open>sg_after_second_propa = (\<lambda>n. (sg_after_increment_progress n)\<lparr>
      pt_tr := c'' n, upfro := (upfro (sg_after_increment_progress n))(1 := False)\<rparr>)\<close>

  define os_after_second_propa where
    \<open>os_after_second_propa = (\<lambda>n. (os_after_increment_progress n)
      (1 := op_state_base (os_label_after_second_propa n)))\<close>

  have dataplane_after_second_propa: \<open>dataplane_tracker_inv
      (os_after_second_propa n) (cbufs_after_loop_updates n)
      (sg_after_second_propa n)\<close>
    for n
  proof -
    have D_increment: \<open>dataflow_topology (summ (sg_after_increment_progress n)) (-+-)\<close>
      using D by (simp add: sg_after_increment_progress_def sg_after_label_progress_def
          sg_after_ooo_input_progress_def sg_first_propa_def sg_progress_def)
    have reachable_increment: \<open>reachable_locations (summ (sg_after_increment_progress n)) = UNIV\<close>
      using subgraph_inv(1) by (simp add: sg_after_increment_progress_def sg_after_label_progress_def
          sg_after_ooo_input_progress_def sg_first_propa_def sg_progress_def)
    have propagate_increment:
      \<open>propagate_all (summ (sg_after_increment_progress n)) (pt_tr (sg_after_increment_progress n)) = Some (c'' n)\<close>
      using second_propa(1)[of n]
      by (simp add: sg_after_increment_progress_def sg_after_label_progress_def
          sg_after_ooo_input_progress_def os_after_label_progress_def os_after_ooo_input_progress_def
          os_after_loop_progress_def second_progress_def
          flip: fold_append change_multiplicities_append_alt)


    have G_increment:
      \<open>graph_summar_nt (summ (sg_after_increment_progress n)) (nxt (sg_after_increment_progress n))
        (os_after_increment_progress n)\<close>
    proof -
      have eq: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
          (os_after_increment_progress n) =
        graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_progress n)\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_increment_progress_def os_after_label_progress_def
            os_after_ooo_input_progress_def os_label_after_label_progress_def os_after_loop_progress_def
            os_after_drop_caps_def op_state_base_def operator_state.defs obtain_progress_def fun_upd_def)
      then show ?thesis
        using G_loop[of n]
        by (simp add: sg_after_increment_progress_def sg_after_label_progress_def
            sg_after_ooo_input_progress_def)
    qed
    define front_c where \<open>front_c = frontier \<circ> (\<lambda>p. c_imp (c'' n) (Loc (1 :: 3) (Trg p)))\<close>

    have inv_front_no_upfro: 
      \<open>dataplane_tracker_inv
        (os_after_second_propa n) (cbufs_after_loop_updates n)
        ((sg_after_increment_progress n)\<lparr>pt_tr := c'' n\<rparr>)\<close>
    proof -
      define os_front where \<open>os_front = map_entry (1 :: 3) (front_update (\<lambda>_. front_c)) (os_after_increment_progress n)\<close>

      have inv_map:
        \<open>dataplane_tracker_inv os_front (cbufs_after_loop_updates n)
          ((sg_after_increment_progress n)\<lparr>pt_tr := c'' n\<rparr>)\<close>
        unfolding os_front_def front_c_def
        by (rule dataplane_tracker_inv_front_update
            [OF D_increment reachable_increment propagate_increment G_increment dataplane_after_increment_progress,
              where nid = \<open>1 :: 3\<close>, simplified])

      have clean_initia:
        \<open>dataplane_tracker_inv
          (os_after_second_propa n) (cbufs_after_loop_updates n)
          ((sg_after_increment_progress n)\<lparr>pt_tr := c'' n\<rparr>) \<longleftrightarrow>
          dataplane_tracker_inv os_front (cbufs_after_loop_updates n)
          ((sg_after_increment_progress n)\<lparr>pt_tr := c'' n\<rparr>)\<close>
        by (rule dataplane_tracker_inv_clean
            [where f=\<open>upfro ((sg_after_increment_progress n)\<lparr>pt_tr := c'' n\<rparr>)\<close>])
          (simp_all add: os_after_second_propa_def os_front_def os_label_after_second_propa_def
            label_front_after_second_propa_def front_c_def os_after_increment_progress_def
            os_after_label_progress_def op_state_base_def operator_state.defs)
      show ?thesis
        using clean_initia inv_map by simp
    qed
    have clean_upfro:
      \<open>dataplane_tracker_inv
        (os_after_second_propa n) (cbufs_after_loop_updates n) (sg_after_second_propa n) \<longleftrightarrow>
        dataplane_tracker_inv
        (os_after_second_propa n) (cbufs_after_loop_updates n)
        ((sg_after_increment_progress n)\<lparr>pt_tr := c'' n\<rparr>)\<close>
      by (rule dataplane_tracker_inv_clean[where f=\<open>(upfro (sg_after_increment_progress n))(1 := False)\<close>])
        (simp_all add: sg_after_second_propa_def)
    show ?thesis
      using clean_upfro inv_front_no_upfro by simp
  qed

  have labels_after_second_propa:
    \<open>\<forall>t. labels_inv (all_edges (os_label_after_second_propa n) t) (min_label (os_label_after_second_propa n) t)\<close>
    for n
    using labels_after_label_progress[of n]
    by (simp add: os_label_after_second_propa_def all_edges_def all_vertices_def min_label_def)


(* ----------------------------- *)
(* STEPS 13: op 1 produces all the wcc components from the labels *)
  define label_produces_below_times where
    \<open>label_produces_below_times = (\<lambda>n.
      filter
        (\<lambda>t. \<not> frontier_less_equal
          (exit_scope myfst (front (os_label_after_second_propa n) 0 + front (os_label_after_second_propa n) 1))
          (myfst t) \<and> myfst t \<in> set (timestamps (os_label_after_second_propa n)))
        (ocaps (os_label_after_second_propa n) 0))\<close>

  define label_produces_batch where
    \<open>label_produces_batch = (\<lambda>n. label_prop_output_batch
      (os_label_after_second_propa n) (label_produces_below_times n) ::
      ((nat \<times> nat + nat set set) \<times> (2, (nat, nat) myprod) capability) list)\<close>

  define os_label_after_produces where
    \<open>os_label_after_produces = (\<lambda>n. drop_caps
      (produces (os_label_after_second_propa n) (label_produces_batch n))
      (map (\<lambda>t. Cap t (0 :: 2)) (label_produces_below_times n)))\<close>

  define os_after_label_produces where
    \<open>os_after_label_produces = (\<lambda>n. (os_after_second_propa n)
      (1 := op_state_base (os_label_after_produces n)))\<close>

  have dataplane_after_label_produces:
    \<open>dataplane_tracker_inv
      (os_after_label_produces n) (cbufs_after_loop_updates n)
      (sg_after_second_propa n)\<close>
    for n
  proof -
    have intsum_label_input0_10:
      \<open>intsum (os_label_after_input0 n) (1 :: 2) (0 :: 2) = []\<close>
      using Intsum_after_label_input0[of n, rule_format, of 1]
      by (simp add: os_after_label_input0_def op_state_base_def operator_state.defs raw_summary_def)
    have ocaps0_loop:
      \<open>ocaps (os_label_after_loop_updates n) (0 :: 2) = ocaps (os_label_after_input0 n) 0\<close>
      unfolding os_label_after_loop_updates_def loop_res_def
      by (subst ocaps_0_fst_snd_loop_updates) (rule intsum_label_input0_10, simp)

    have intsum_label_first_00:
      \<open>intsum os_label_after_first_propa (0 :: 2) (0 :: 2) = [MyPair 0 0]\<close>
      using os_inv(7)[rule_format, of 1]
      by (simp add: os_label_after_first_propa_def os_inv(4) operator_state.defs raw_summary_def)
    have ocaps0_first_mysnd:
      \<open>\<forall>t \<in> set (ocaps os_label_after_first_propa (0 :: 2)). mysnd t = 0\<close>
      using label_prop_inv(4)
      by (simp add: os_label_after_first_propa_def os_inv(4) operator_state.defs)
    have input0_msgs_mysnd:
      \<open>\<forall>t \<in> snd ` set (input0_msgs n). mysnd t = 0\<close>
      using label_prop_inv(4) buffers_inv input_stream_inv
      by (force simp add: input0_msgs_def input_data_def input_events_def
          buffers_inv outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def inputs_at_target_def
          os_inv(1) operator_state.defs split: event.splits dest!: setltakenD)


    have ocaps0_read_mysnd:
      \<open>\<forall>t \<in> set (ocaps (os_label_after_read_input0 n) (0 :: 2)). mysnd t = 0\<close>
      using ocaps0_first_mysnd input0_msgs_mysnd intsum_label_first_00
      by (auto simp add: os_label_after_read_input0_def fold_consumes zero_myprod_def split: prod.splits)
    have ocaps0_second_mysnd:
      \<open>\<forall>t \<in> set (ocaps (os_label_after_second_propa n) (0 :: 2)). mysnd t = 0\<close>
      using ocaps0_loop ocaps0_read_mysnd
      by (simp add: os_label_after_second_propa_def os_label_after_label_progress_def
          os_label_after_drop_caps_def os_label_after_input0_def drop_caps_def
          obtain_progress_def operator_state.defs)

    have D_second: \<open>dataflow_topology (summ (sg_after_second_propa n)) (-+-)\<close>
      using D by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
          sg_after_label_progress_def sg_after_ooo_input_progress_def sg_first_propa_def sg_progress_def)
    have Nxt_second: \<open>nxt (sg_after_second_propa n) = graph_to_nxt (summ (sg_after_second_propa n))\<close>
      using subgraph_inv(2) by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
          sg_after_label_progress_def sg_after_ooo_input_progress_def sg_first_propa_def sg_progress_def)
    have G_second:
      \<open>graph_summar_nt (summ (sg_after_second_propa n)) (nxt (sg_after_second_propa n))
        (os_after_second_propa n)\<close>
    proof -
      have eq: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
          (os_after_second_propa n) =
        graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_progress n)\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_second_propa_def os_label_after_second_propa_def
            os_after_increment_progress_def os_after_label_progress_def os_after_ooo_input_progress_def
            os_label_after_label_progress_def os_after_loop_progress_def os_after_drop_caps_def
            op_state_base_def operator_state.defs obtain_progress_def fun_upd_def)
      then show ?thesis
        using G_loop[of n]
        by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
            sg_after_label_progress_def sg_after_ooo_input_progress_def)
    qed
    have input0_loop_updates:
      \<open>input (fst (snd (loop_updates cb lp os'))) (0 :: 2) = input lp 0\<close>
      for cb lp os'
      by (induct cb lp os' rule: loop_updates.induct)
        (subst loop_updates.simps;
          clarsimp split: prod.splits;
          metis label_prop_input1_loop_updates_input_label_0)

    have input0_second_empty:
      \<open>input (os_after_second_propa n 1) (0 :: 2) = []\<close>
      using input_0_after_loop_updates_empty[of n]
      by (simp add: os_after_second_propa_def os_label_after_second_propa_def
          os_label_after_label_progress_def os_label_after_drop_caps_def drop_caps_def
          obtain_progress_def op_state_base_def operator_state.defs)
    have inv_produces: \<open>dataplane_tracker_inv
        ((os_after_second_propa n)(1 := drop_caps
          (produces (os_after_second_propa n 1) (label_produces_batch n))
          (map (\<lambda>t. Cap t (0 :: 2)) (label_produces_below_times n))))
        (cbufs_after_loop_updates n) (sg_after_second_propa n)\<close>
      apply (rule dataplane_tracker_inv_produces_drop
          [of \<open>os_after_second_propa n\<close> \<open>1 :: 3\<close> \<open>os_after_second_propa n 1\<close>
            \<open>cbufs_after_loop_updates n\<close> \<open>sg_after_second_propa n\<close>
            \<open>label_produces_batch n\<close>
            \<open>map (\<lambda>t. Cap t (0 :: 2)) (label_produces_below_times n)\<close>])
            apply (simp add: dataplane_after_second_propa)
           apply (rule D_second)
          apply (simp add: G_second)
         apply (rule Nxt_second)
      subgoal for x cap
        using ocaps0_second_mysnd
        apply (clarsimp simp add: label_produces_batch_def label_prop_output_batch_def
            label_produces_below_times_def os_after_second_propa_def os_label_after_second_propa_def
            op_state_base_def operator_state.defs)
        by (metis myprod.collapse)
      subgoal for p'
        apply (cases \<open>p' = (0 :: 2)\<close>)
        subgoal
          by (simp add: label_produces_below_times_def os_after_second_propa_def
              os_label_after_second_propa_def op_state_base_def operator_state.defs
              mset_filter filter_map comp_def)
        subgoal
          by (simp add: filter_False)
        done
      subgoal for p'
        by (cases \<open>p' = (0 :: 2)\<close>)
          (auto simp add: label_produces_below_times_def input0_second_empty filter_False)

      done


    show ?thesis
      using inv_produces
      by (simp add: os_after_label_produces_def os_label_after_produces_def
          os_after_second_propa_def os_label_after_second_propa_def
          op_state_base_def drop_caps_def produces_def)

  qed


  have labels_after_label_produces:
    \<open>\<forall>t. labels_inv (all_edges (os_label_after_produces n) t) (min_label (os_label_after_produces n) t)\<close>
    for n
    using labels_after_second_propa[of n]
    by (simp add: os_label_after_produces_def)


  let ?input_caps_after_prefix =
    "\<lambda>n. mset (ocaps (os 0) (0 :: 2)) +
      event.time `# filter_mset is_Mint (mset (ltaken n lxs)) -
      event.time `# filter_mset is_Drop (mset (ltaken n lxs))"
  let ?input_frontier_after_prefix =
    "\<lambda>n. frontier (zmset_of (?input_caps_after_prefix n))"

  have input_caps_in_lset:
    \<open>t \<in># mset (ocaps (os 0) (0 :: 2)) \<Longrightarrow> t \<in> event.time ` lset lxs\<close> for t
  proof -
    assume t_in: \<open>t \<in># mset (ocaps (os 0) (0 :: 2))\<close>
    obtain n where vacant: \<open>vacant t (?input_caps_after_prefix n)\<close>
      using input_stream_inv
      unfolding timely_input_stream_def timely_progress_def
      by auto
    let ?C = \<open>mset (ocaps (os 0) (0 :: 2))\<close>
    let ?M = \<open>event.time `# filter_mset is_Mint (mset (ltaken n lxs))\<close>
    let ?D = \<open>event.time `# filter_mset is_Drop (mset (ltaken n lxs))\<close>
    have vacant_t: \<open>count (?C + ?M - ?D) t = 0\<close>
      using vacant unfolding vacant_def by simp
    have live_before_drops: \<open>0 < count (?C + ?M) t\<close>
      using t_in by simp
    have drop_pos: \<open>0 < count ?D t\<close>
      using vacant_t live_before_drops
      by (cases \<open>count ?D t\<close>) auto
    then obtain e where e_in:
      \<open>e \<in># filter_mset is_Drop (mset (ltaken n lxs))\<close>
      and e_time: \<open>event.time e = t\<close>
      by auto
    then have \<open>e \<in> set (ltaken n lxs)\<close>
      by simp
    then have \<open>e \<in> lset lxs\<close>
      by (rule setltakenD)
    then show ?thesis
      using e_time by blast
  qed

  have input_cap_after_prefix_mysnd0:
    \<open>x \<in># ?input_caps_after_prefix n \<Longrightarrow> mysnd x = 0\<close> for n x
  proof -
    assume x_in: \<open>x \<in># ?input_caps_after_prefix n\<close>
    have x_live:
      \<open>x \<in># mset (ocaps (os 0) (0 :: 2)) \<or>
        x \<in># event.time `# filter_mset is_Mint (mset (ltaken n lxs))\<close>
      using in_diffD[OF x_in] by auto
    then have \<open>x \<in> event.time ` lset lxs\<close>
    proof
      assume \<open>x \<in># mset (ocaps (os 0) (0 :: 2))\<close>
      then show ?thesis
        by (rule input_caps_in_lset)
    next
      assume \<open>x \<in># event.time `# filter_mset is_Mint (mset (ltaken n lxs))\<close>
      then obtain e where \<open>e \<in># filter_mset is_Mint (mset (ltaken n lxs))\<close>
        and \<open>event.time e = x\<close>
        by auto
      then show ?thesis
        using setltakenD[of e n lxs] by auto
    qed
    then show ?thesis
      using label_prop_inv(4) by auto
  qed

  have input_frontier_mysnd0:
    \<open>x \<in>\<^sub>A ?input_frontier_after_prefix n \<Longrightarrow> mysnd x = 0\<close> for n x
  proof -
    assume x_in: \<open>x \<in>\<^sub>A ?input_frontier_after_prefix n\<close>
    have \<open>x \<in># ?input_caps_after_prefix n\<close>
      using x_in
      apply (subst count_greater_zero_iff[symmetric])
      apply (simp add: in_frontier_iff)
      done
    then show ?thesis
      by (rule input_cap_after_prefix_mysnd0)
  qed

  have input_frontier_exit_scopeD:
    \<open>frontier_less_equal (exit_scope myfst (?input_frontier_after_prefix n)) (myfst t) \<Longrightarrow>
      mysnd t = 0 \<Longrightarrow>
      frontier_less_equal (?input_frontier_after_prefix n) t\<close> for n t
  proof -
    assume projected:
      \<open>frontier_less_equal (exit_scope myfst (?input_frontier_after_prefix n)) (myfst t)\<close>
    assume t_zero: \<open>mysnd t = 0\<close>
    obtain y where y_in: \<open>y \<in>\<^sub>A exit_scope myfst (?input_frontier_after_prefix n)\<close>
      and y_le: \<open>y \<le> myfst t\<close>
      using projected unfolding frontier_less_equal_iff2 by blast
    from y_in obtain x where x_in: \<open>x \<in>\<^sub>A ?input_frontier_after_prefix n\<close>
      and x_fst: \<open>myfst x = y\<close>
      by (rule exit_scope_memberE)
    have x_zero: \<open>mysnd x = 0\<close>
      by (rule input_frontier_mysnd0[OF x_in])
    have \<open>x \<le> t\<close>
      using y_le x_fst x_zero t_zero
      by (cases x; cases t; simp)
    then show ?thesis
      using x_in unfolding frontier_less_equal_iff2 by blast
  qed

  have no_second_propa_output_frontier:
    \<open>\<not> frontier_less_equal
        (exit_scope myfst
          (frontier (c_imp (c'' n) (Loc 1 (Trg 0))) +
           frontier (c_imp (c'' n) (Loc 1 (Trg 1)))))
        (myfst t)\<close>
    if input_frontier_fresh:
      \<open>\<not> frontier_less_equal (?input_frontier_after_prefix n) t\<close>
      and t_live:
      \<open>t |\<in>| ts lxs \<or>
        cBex (cset_from_list (((outputs_at_target (summ sg) os >> cbufs) >> inputs_at_target os) (1, 0))) (\<lambda>x. t = snd x) \<or>
        cBex (cfilter (\<lambda>t. \<exists>x\<in>set (ocaps (os 1) 0). t = myfst x) (cset_from_list (timestamps os_label_prop))) (\<lambda>x. t = MyPair x 0)\<close>
    for n t


    unfolding second_propa(2)[rule_format, of n "Loc 1 (Trg 1)"]
      second_propa(2)[rule_format, of n "Loc 1 (Trg 0)"]

    apply safe
    apply (simp add: exit_scope_plus_distrib)
    apply (drule frontier_less_equal_pluss_le)
    subgoal
      apply (simp add: sg_first_propa_def sg_progress_def subgraph_inv(1))
      apply (rule exit_scope_ifrontier_L1T0_le_L1T1_empty_loop)
      subgoal
        using D by (simp add: sg_first_propa_def sg_progress_def subgraph_inv(1))
      subgoal
        using c_pts_after_second_progress_caps'[of n \<open>Loc (1 :: 3) (Src (1 :: 2))\<close>]
          dt_inv'(1)[of n]
        by (simp add: Src_caps_inv_def os_after_loop_progress_def
            os_after_drop_caps_def os_label_after_drop_caps_def
            op_state_base_def operator_state.defs ocaps_drop_caps_all)
      subgoal
        using c_pts_after_second_progress_caps'[of n \<open>Loc (2 :: 3) (Trg (1 :: 2))\<close>]
          dt_inv'(2)[of n] outpu_1_after_loop_updates_empty(1)[of n]
        by (simp add: Trg_caps_inv_def outputs_at_target_raw_summary subgraph_inv(1)
            sg_first_propa_def sg_progress_def cbufs_after_loop_updates_def loop_res_def
            os_after_loop_progress_def os_after_drop_caps_def os_label_after_drop_caps_def
            drop_caps_def op_state_base_def operator_state.defs)
      subgoal
        using c_pts_after_second_progress_caps'[of n \<open>Loc (2 :: 3) (Src (1 :: 2))\<close>]
          dt_inv'(1)[of n] ocaps_1_os2_after_loop_updates_empty[of n]
        by (simp add: Src_caps_inv_def os_after_loop_progress_def os_after_drop_caps_def)
      subgoal
        using c_pts_after_second_progress_caps'[of n \<open>Loc (1 :: 3) (Trg (1 :: 2))\<close>]
          dt_inv'(2)[of n] outpu_1_after_loop_updates_empty(2)[of n]
        by (simp add: Trg_caps_inv_def outputs_at_target_raw_summary subgraph_inv(1)
            sg_first_propa_def sg_progress_def cbufs_after_loop_updates_def loop_res_def
            os_after_loop_progress_def os_after_drop_caps_def
            op_state_base_def operator_state.defs)
      done
    subgoal
      apply (subgoal_tac "ifrontier (summ sg_first_propa) (-+-) (change_multiplicities (summ sg_first_propa) (second_progress n) (pt_tr sg_first_propa)) (Loc 1 (Trg 0)) =
                          frontier (zmset_of (mset (ocaps (os 0) 0) + event.time `# filter_mset is_Mint (mset (ltaken n lxs)) - event.time `# filter_mset is_Drop (mset (ltaken n lxs))))")
       defer
      subgoal premises auxx
        apply (simp add: sg_first_propa_def sg_progress_def)
        unfolding Propagate.dataflow_topology.implied_frontier_alt_def[OF D] UNIV_3_2
        apply (clarsimp simp add: split_beta subgraph_inv(1))
        subgoal premises self_path
          apply (subgoal_tac "c_pts (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c') (Loc (0 :: 3) (Trg (0 :: 2))) = {#}\<^sub>z")
           defer
          subgoal
            apply (subgoal_tac "c_pts (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c')
                 (Loc (0 :: 3) (Trg (0 :: 2))) = caps' n (Loc 0 (Trg 0))")
             defer
            subgoal
              using c_pts_after_second_progress_caps'[of n \<open>Loc (0 :: 3) (Trg (0 :: 2))\<close>]
              by simp
            apply (subgoal_tac "caps' n (Loc (0 :: 3) (Trg (0 :: 2))) = {#}\<^sub>z")
             defer
            subgoal
              using dt_inv'(2)[of n] buffers_inv(2)
              by (simp add: Trg_caps_inv_def outputs_at_target_raw_summary subgraph_inv(1)
                  sg_first_propa_def sg_progress_def
                  cbufs_after_loop_updates_def loop_res_def cbufs_after_label_read_input0_def
                  cbufs_after_input_output_def os_after_loop_progress_def os_after_drop_caps_def
                  os_after_loop_updates_def os_after_label_input0_def
                  os_after_label_read_input0_def os_after_input_output_def os_input_after_output_def
                  os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
                  input0_msgs_def BULK_BENQ_def os_inv(1,4) op_state_base_def
                  operator_state.defs obtain_progress_def)
            apply simp
            done
          apply (subgoal_tac "c_pts (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c') (Loc (1 :: 3) (Trg (0 :: 2))) = {#}\<^sub>z")
           defer
          subgoal
            apply (subgoal_tac "c_pts (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c')
                 (Loc (1 :: 3) (Trg (0 :: 2))) = caps' n (Loc 1 (Trg 0))")
             defer
            subgoal
              using c_pts_after_second_progress_caps'[of n \<open>Loc (1 :: 3) (Trg (0 :: 2))\<close>]
              by simp
            apply (subgoal_tac "caps' n (Loc (1 :: 3) (Trg (0 :: 2))) = {#}\<^sub>z")
             defer
            subgoal
              using dt_inv'(2)[of n]
              by (simp add: Trg_caps_inv_def outputs_at_target_raw_summary subgraph_inv(1)
                  sg_first_propa_def sg_progress_def
                  cbufs_after_loop_updates_def loop_res_def cbufs_after_label_read_input0_def
                  cbufs_after_input_output_def os_after_loop_progress_def os_after_drop_caps_def
                  os_after_loop_updates_def os_after_label_input0_def
                  os_after_label_read_input0_def os_after_input_output_def os_input_after_output_def
                  os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
                  input0_msgs_def BULK_BENQ_def os_inv(1,4) op_state_base_def
                  operator_state.defs obtain_progress_def)
            apply simp
            done
          apply (subgoal_tac "c_pts (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c') (Loc (0 :: 3) (Src (0 :: 2))) =
              zmset_of (mset (ocaps (os 0) 0) + event.time `# filter_mset is_Mint (mset (ltaken n lxs)) - event.time `# filter_mset is_Drop (mset (ltaken n lxs)))")
           defer
          subgoal
            apply (subgoal_tac "c_pts (change_multiplicities (antichain_from_list \<circ>\<circ> raw_summary) (second_progress n) c')
                 (Loc (0 :: 3) (Src (0 :: 2))) = caps' n (Loc 0 (Src 0))")
             defer
            subgoal
              using c_pts_after_second_progress_caps'[of n \<open>Loc (0 :: 3) (Src (0 :: 2))\<close>]
              by simp
            apply (subgoal_tac "caps' n (Loc (0 :: 3) (Src (0 :: 2))) =
                 zmset_of (mset (ocaps (os 0) 0) + event.time `# filter_mset is_Mint (mset (ltaken n lxs)) - event.time `# filter_mset is_Drop (mset (ltaken n lxs)))")
             defer
            subgoal
              using dt_inv'(1)[of n]
                mset_ocaps_updates[of "ltaken n lxs" "ldropn n lxs" "ocaps (fst (obtain_progress os_input)) (0 :: 2)"]
                input_stream_inv os_inv(1)
              apply (simp add: Src_caps_inv_def input_events_def
                  os_after_loop_progress_def os_after_drop_caps_def
                  os_after_loop_updates_def loop_res_def os_after_label_input0_def
                  os_after_label_read_input0_def os_after_input_output_def os_input_after_output_def
                  os_after_input_stream_def os_input_after_stream_def os_first_propa_def os_progress_def
                  os_inv(4) op_state_base_def operator_state.defs obtain_progress_def)
              apply (drule arg_cong[where f=zmset_of])
              apply (simp add: to_zmset_correct)
              done
            apply simp
            done
          apply simp
          done
        done
      subgoal
        apply simp
        apply (drule input_frontier_exit_scopeD[of n t])
        subgoal
          using t_live label_prop_inv(4)
          apply (clarsimp del: disjCI simp add: cimage_iff image_iff split_beta split: event.splits)
          apply (elim disjE)
          subgoal
            apply (clarsimp simp add: cin.rep_eq ts_def cset_of_llist.rep_eq split: event.splits)
            subgoal for a b
              by force
            done
          subgoal
            by (force simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1))
          subgoal
            by auto
          done
        using input_frontier_fresh
        by blast
      done
    done

(* ----------------------------- *)
(* STEPS 14: op 1 flushes outpu 0 buffer with all WCC  *)
  define os_label_after_final_output where
    \<open>os_label_after_final_output = (\<lambda>n. (os_label_after_produces n)\<lparr>outpu :=
      (outpu (os_label_after_produces n))(0 := [])\<rparr>)\<close>

  define os_after_final_output where
    \<open>os_after_final_output = (\<lambda>n. (os_after_label_produces n)
      (1 := op_state_base (os_label_after_final_output n)))\<close>


  have dataplane_after_final_output:
    \<open>dataplane_tracker_inv
      (os_after_final_output n) (cbufs_after_loop_updates n)
      (sg_after_second_propa n)\<close>
    for n
  proof -
    have G_second:
      \<open>graph_summar_nt (summ (sg_after_second_propa n)) (nxt (sg_after_second_propa n))
        (os_after_second_propa n)\<close>
    proof -
      have eq: \<open>graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa)
          (os_after_second_propa n) =
        graph_summar_nt (summ sg_first_propa) (nxt sg_first_propa) (os_after_loop_progress n)\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_second_propa_def os_label_after_second_propa_def
            os_after_increment_progress_def os_after_label_progress_def os_after_ooo_input_progress_def
            os_label_after_label_progress_def os_after_loop_progress_def os_after_drop_caps_def
            op_state_base_def operator_state.defs obtain_progress_def fun_upd_def)
      then show ?thesis
        using G_loop[of n]
        by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
            sg_after_label_progress_def sg_after_ooo_input_progress_def)
    qed
    have G_after_label_produces:
      \<open>graph_summar_nt (summ (sg_after_second_propa n)) (nxt (sg_after_second_propa n))
        (os_after_label_produces n)\<close>
    proof -
      have eq: \<open>graph_summar_nt (summ (sg_after_second_propa n)) (nxt (sg_after_second_propa n))
          (os_after_label_produces n) =
        graph_summar_nt (summ (sg_after_second_propa n)) (nxt (sg_after_second_propa n))
          (os_after_second_propa n)\<close>
        by (rule graph_summar_nt_intsum_cong)
          (simp add: os_after_label_produces_def os_label_after_produces_def
            os_after_second_propa_def op_state_base_def operator_state.defs drop_caps_def produces_def)
      then show ?thesis
        using G_second by simp
    qed
    have Summ_second:
      \<open>summ (sg_after_second_propa n) = antichain_from_list \<circ>\<circ> raw_summary\<close>
      using subgraph_inv(1)
      by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
          sg_after_label_progress_def sg_after_ooo_input_progress_def sg_first_propa_def sg_progress_def)
    show ?thesis
      apply (rule dataplane_tracker_inv_update_outputs_outside
          [OF dataplane_after_label_produces[of n], where nid=\<open>1 :: 3\<close> and p=\<open>0 :: 2\<close> and xs=Nil])
        apply (simp add: os_after_final_output_def os_label_after_final_output_def
          os_after_label_produces_def op_state_base_def operator_state.defs fun_eq_iff)
       apply (simp add: Summ_second raw_summary_def)
      apply (rule G_after_label_produces)
      done

  qed



  have labels_after_final_output:
    \<open>\<forall>t. labels_inv (all_edges (os_label_after_final_output n) t)
      (min_label (os_label_after_final_output n) t)\<close>
    for n
    using labels_after_label_produces[of n]
    by (simp add: os_label_after_final_output_def all_edges_def all_vertices_def min_label_def)

  have ocaps0_after_final_output_mysnd:
    \<open>\<forall>t \<in> set (ocaps (os_after_final_output n 1) (0 :: 2)). mysnd t = 0\<close>
    for n
  proof -
    have intsum_label_input0_10:
      \<open>intsum (os_label_after_input0 n) (1 :: 2) (0 :: 2) = []\<close>
      using Intsum_after_label_input0[of n, rule_format, of 1]
      by (simp add: os_after_label_input0_def op_state_base_def operator_state.defs raw_summary_def)
    have ocaps0_loop:
      \<open>ocaps (os_label_after_loop_updates n) (0 :: 2) = ocaps (os_label_after_input0 n) 0\<close>
      unfolding os_label_after_loop_updates_def loop_res_def
      by (subst ocaps_0_fst_snd_loop_updates) (rule intsum_label_input0_10, simp)
    have intsum_label_first_00:
      \<open>intsum os_label_after_first_propa (0 :: 2) (0 :: 2) = [MyPair 0 0]\<close>
      using os_inv(7)[rule_format, of 1]
      by (simp add: os_label_after_first_propa_def os_inv(4) operator_state.defs raw_summary_def)
    have ocaps0_first_mysnd:
      \<open>\<forall>t \<in> set (ocaps os_label_after_first_propa (0 :: 2)). mysnd t = 0\<close>
      using label_prop_inv(4)
      by (simp add: os_label_after_first_propa_def os_inv(4) operator_state.defs)
    have input0_msgs_mysnd:
      \<open>\<forall>t \<in> snd ` set (input0_msgs n). mysnd t = 0\<close>
      using label_prop_inv(4) buffers_inv input_stream_inv
      by (force simp add: input0_msgs_def input_data_def input_events_def
          buffers_inv outputs_at_target_raw_summary subgraph_inv(1) BULK_BENQ_def inputs_at_target_def
          os_inv(1) operator_state.defs split: event.splits dest!: setltakenD)
    have ocaps0_read_mysnd:
      \<open>\<forall>t \<in> set (ocaps (os_label_after_read_input0 n) (0 :: 2)). mysnd t = 0\<close>
      using ocaps0_first_mysnd input0_msgs_mysnd intsum_label_first_00
      by (auto simp add: os_label_after_read_input0_def fold_consumes zero_myprod_def split: prod.splits)
    have ocaps0_second_mysnd:
      \<open>\<forall>t \<in> set (ocaps (os_label_after_second_propa n) (0 :: 2)). mysnd t = 0\<close>
      using ocaps0_loop ocaps0_read_mysnd
      by (simp add: os_label_after_second_propa_def os_label_after_label_progress_def
          os_label_after_drop_caps_def os_label_after_input0_def drop_caps_def
          obtain_progress_def operator_state.defs)
    show ?thesis
      using ocaps0_second_mysnd
      by (auto simp add: os_after_final_output_def os_label_after_final_output_def
          os_after_label_produces_def os_label_after_produces_def
          os_after_second_propa_def os_label_after_second_propa_def
          os_label_after_label_progress_def os_label_after_drop_caps_def
          os_after_increment_progress_def os_after_label_progress_def
          os_after_ooo_input_progress_def os_after_loop_progress_def os_after_drop_caps_def
          op_state_base_def operator_state.defs drop_caps_def produces_def obtain_progress_def
          dest!: in_set_list_diffD)
  qed

  have outpu_0_after_final_output_empty:
    \<open>outpu (os_after_final_output n (0 :: 3)) (0 :: 2) = []\<close>
    for n
    by (simp add: os_after_final_output_def os_after_label_produces_def
        os_after_second_propa_def os_after_increment_progress_def
        os_after_label_progress_def os_after_ooo_input_progress_def
        os_after_loop_progress_def os_after_drop_caps_def os_after_loop_updates_def
        os_after_label_input0_def os_after_label_read_input0_def
        os_after_input_output_def os_input_after_output_def os_after_input_stream_def
        os_input_after_stream_def os_first_propa_def os_progress_def
        loop_res_def op_state_base_def operator_state.defs obtain_progress_def os_inv(1))


  define final_output where
    \<open>final_output = (\<lambda> n. label_prop_output_batch
                             (drop_caps
                               (fst (snd (loop_updates cbufs
                                           (fst (label_prop_input0_batched
                                                  (CONSUMES 0 (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))
                                                    (CONSUMES 0 (outpu (os 0) 0) (CONSUMES 0 (cbufs (1, 0)) (os_label_prop\<lparr>front := frontier \<circ> (\<lambda>p. c_imp c' (Loc 1 (Trg p))), initia := True\<rparr>))))
                                                  (input (os 1) 0 @ cbufs (1, 0) @ outpu (os 0) 0 @ map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))))
                                           os)))
                               (map (\<lambda>t. Cap t 1)
                                 (ocaps
                                   (fst (snd (loop_updates cbufs
                                               (fst (label_prop_input0_batched
                                                      (CONSUMES 0 (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))
                                                        (CONSUMES 0 (outpu (os 0) 0) (CONSUMES 0 (cbufs (1, 0)) (os_label_prop\<lparr>front := frontier \<circ> (\<lambda>p. c_imp c' (Loc 1 (Trg p))), initia := True\<rparr>))))
                                                      (input (os 1) 0 @ cbufs (1, 0) @ outpu (os 0) 0 @ map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))))
                                               os)))
                                   1))
                              \<lparr>consu := [], inter := [], produ := [], front := frontier \<circ> (\<lambda>p. c_imp (c'' n) (Loc 1 (Trg p))), initia := True\<rparr>)
                             (filter
                               (\<lambda>t. myfst t
                                     \<in> (\<lambda>(d, y). myfst y) `
                                        (set (input (os 1) 0) \<union> (set (cbufs (1, 0)) \<union> (set (outpu (os 0) 0) \<union> case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined) ` {x \<in> set (ltaken n lxs). is_Data x}))) \<or>
                                     myfst t \<in> set (timestamps os_label_prop))
                               (filter (\<lambda>t. \<not> frontier_less_equal (exit_scope myfst (frontier (c_imp (c'' n) (Loc 1 (Trg 0))) + frontier (c_imp (c'' n) (Loc 1 (Trg 1))))) (myfst t))
                                 (ocaps
                                   (drop_caps
                                     (fst (snd (loop_updates cbufs
                                                 (fst (label_prop_input0_batched
                                                        (CONSUMES 0 (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))
                                                          (CONSUMES 0 (outpu (os 0) 0) (CONSUMES 0 (cbufs (1, 0)) (os_label_prop\<lparr>front := frontier \<circ> (\<lambda>p. c_imp c' (Loc 1 (Trg p))), initia := True\<rparr>))))
                                                        (input (os 1) 0 @ cbufs (1, 0) @ outpu (os 0) 0 @ map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))))
                                                 os)))
                                     (map (\<lambda>t. Cap t 1)
                                       (ocaps
                                         (fst (snd (loop_updates cbufs
                                                     (fst (label_prop_input0_batched
                                                            (CONSUMES 0 (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))
                                                              (CONSUMES 0 (outpu (os 0) 0) (CONSUMES 0 (cbufs (1, 0)) (os_label_prop\<lparr>front := frontier \<circ> (\<lambda>p. c_imp c' (Loc 1 (Trg p))), initia := True\<rparr>))))
                                                            (input (os 1) 0 @ cbufs (1, 0) @ outpu (os 0) 0 @ map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))))
                                                     os)))
                                         1)))
                                   0))))\<close>


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
              by (simp  del: filter.simps add: image_iff subgraph_inv outputs_at_target_raw_summary csets_inv(2) label_prop_edge_batch_def label_prop_edge_record_update_def buffers_inv operator_state.defs os_inv(4) csets_inv(1))

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
          using os_inv(10) apply simp
          using buffers_inv(2) apply simp
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
          subgoal
            apply (subst wf_label_prop_updates_cong[where os'=os_label_prop])
            using label_prop_inv(7)
            by (simp_all add: buffers_inv image_Un Un_assoc BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1) os_inv(4) operator_state.defs(3))
          done
        subgoal premises prems
          using timely_input_stream_advances_frontier[OF input_stream_inv, of t] apply -
          apply clarsimp
          subgoal premises stream_move for n

            apply (intro exI conjI[rotated])
             apply (intro relcomppI)
               apply (rule bisim_refl)
              defer
              apply (rule wbisim_refl)
             apply (rule wstep_trans(1))
              apply (rule transitive_closurep_trans'(2))

(* ----------------------------- *)
(* STEPS 1: op 0 reports progress *)
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

(* ----------------------------- *)
(* STEPS 2: op 1 reads the initial frontier from propagation *)
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

(* ----------------------------- *)
(* STEPS 3: op 0 produces n elements from the input stream *)
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

(* ----------------------------- *)
(* STEPS 4: op 0 flushes the outpu buffer *)
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

(* ----------------------------- *)
(* STEPS 5: op 1 consumes all the data in the channel *)
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

(* ----------------------------- *)
(* STEPS 6: op 1 processes all the new edges in the input 0 *)
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

(* ----------------------------- *)
(* STEPS 7: op 1 loops all the data, and processes everything until the labels converges *)
               apply (rule transitive_closurep_trans'(2))
                apply (rule step_Taus_set_op)
                 apply (rule step_Taus_dataflow_op_Taus_intro)
                 apply (rule step_star_map_op)
                 apply (rule step_comp_op_R_Tau_start)
                 apply (rule step_tau_pow_loop_updates_alt)
                         apply simp
            subgoal
              unfolding op_state_base_def
              by (simp add: os_inv(7)[rule_format]  operator_state.defs os_inv(4))
            using os_inv(9) apply simp
            using os_inv(8) apply simp
            subgoal
              apply (simp only: CONSUMES_CONSUMES)
              apply (rule label_prop_upd_inv_fst_label_prop_input0_batched_inputI)
                apply (simp add: operator_state.defs os_inv(4) input_CONSUMES)
               apply (simp add:  label_prop_inv(5) input_CONSUMES)
              apply (simp add:  label_prop_inv(5) input_CONSUMES)
              using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified] 
              apply (auto del: disjCI simp add: input_CONSUMES os_inv(4) operator_state.defs wf_label_prop_updates_un)
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
                subgoal
                  apply (simp add:  label_prop_inv(5) input_CONSUMES)
                  using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified] 
                  apply (auto del: disjCI simp add: input_CONSUMES os_inv(4) operator_state.defs wf_label_prop_updates_un)
                  done

                done
              done
            subgoal
              apply (simp only: image_Un set_append set_map flip: Un_assoc)
              apply (rule wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI
                  [where rest=\<open>[]\<close>])
                    apply (simp add: os_inv(4) operator_state.defs input_CONSUMES)
                   apply (simp add: os_inv(4) operator_state.defs input_CONSUMES)
                  apply (simp add: os_inv(4) operator_state.defs input_CONSUMES)
              subgoal
                using label_prop_inv(5)  by simp
              subgoal
                using label_prop_inv(1)  by simp
              subgoal
                apply simp
                using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified] 
                by (simp add: input_CONSUMES os_inv(4) operator_state.defs wf_label_prop_updates_un)
              subgoal
                apply simp
                using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def  subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified] 
                apply (auto del: disjCI simp add: split_beta  wf_label_prop_updates_clean_image[unfolded split_beta]  image_iff input_CONSUMES os_inv(4) operator_state.defs wf_label_prop_updates_un split: capability.splits)
                done
              done
            subgoal
              by (simp add:  operator_state.defs os_inv(4))
            subgoal
              by (simp add:  operator_state.defs os_inv(4))
                apply (rule refl)+

(* ----------------------------- *)
(* STEPS 8: op 1 drop all capabilities that may be left *)
               apply (rule transitive_closurep_trans'(2))
                apply (rule step_Taus_set_op)
                 apply (rule step_Taus_dataflow_op_Taus_intro)
                 apply (rule step_star_map_op)
                 apply (rule step_comp_op_R_Tau_start)
                 apply (rule step_taus_loop_)
                 apply (rule step_star_map_op)
                 apply (rule step_comp_op_L_Tau_start)
                 apply (rule step_star_map_op)
                 apply (rule step_label_propagation_op_drop_caps)
            subgoal
              using input_0_after_loop_updates_empty[of n]
              by (simp add: os_label_after_loop_updates_def loop_res_def
                  cbufs_after_label_read_input0_def cbufs_after_input_output_def
                  os_label_after_input0_def os_label_after_read_input0_def label_input0_msgs_def
                  input0_msgs_def input_data_def input_events_def os_label_after_first_propa_def
                  label_front_after_first_propa_def sg_first_propa_def
                  os_after_label_input0_def os_after_label_read_input0_def
                  os_after_input_output_def os_after_input_stream_def os_first_propa_def os_progress_def
                  os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs input_CONSUMES)

            subgoal
              using input_1_after_loop_updates_empty[of n]
              by (simp add: os_label_after_loop_updates_def loop_res_def
                  cbufs_after_label_read_input0_def cbufs_after_input_output_def
                  os_label_after_input0_def os_label_after_read_input0_def label_input0_msgs_def
                  input0_msgs_def input_data_def input_events_def os_label_after_first_propa_def
                  label_front_after_first_propa_def sg_first_propa_def
                  os_after_label_input0_def os_after_label_read_input0_def
                  os_after_input_output_def os_after_input_stream_def os_first_propa_def os_progress_def
                  os_inv(1,4) obtain_progress_def op_state_base_def operator_state.defs input_CONSUMES)


                   apply (rule refl)+
            subgoal
              by simp
                 apply (rule refl)+

(* ----------------------------- *)
(* STEPS 9: op 0 reports progress again *)
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

(* ----------------------------- *)
(* STEPS 10: op 1 reports progress *)
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

(* ----------------------------- *)
(* STEPS 11: op 2 reports progress *)
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

(* ----------------------------- *)
(* STEPS 12: op 1 reads the new frontier from the propagation *)
               apply (rule converse_rtranclp_into_rtranclp) 
                apply (rule step_set_op_intro_Tau_2)
                  apply simp
                 apply (rule step_Tau_dataflow_op_Inp_Inl_intro[where ?conf'="c'' n"])
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
            subgoal
              using second_propa(1)[of n, simplified]
              by (simp add: input_data_def os_progress_def input_events_def input0_msgs_def label_input0_msgs_def os_first_propa_def os_input_after_stream_def os_input_after_output_def label_front_after_first_propa_def os_after_input_stream_def os_after_input_output_def os_label_after_first_propa_def os_label_after_read_input0_def os_label_after_input0_def cbufs_after_input_output_def os_after_label_read_input0_def os_after_label_input0_def cbufs_after_label_read_input0_def loop_res_def os_label_after_loop_updates_def sg_progress_def os_after_loop_updates_def os_after_loop_progress_def os_after_drop_caps_def os_label_after_drop_caps_def drop_caps_def second_progress_def sg_first_propa_def os_inv(1,4) op_state_base_def operator_state.defs obtain_progress_def CONSUMES_CONSUMES flip: fold_append change_multiplicities_append_alt)

                  apply (rule refl)+
               apply (simp add: flip: fold_append change_multiplicities_append_alt)

(* ----------------------------- *)
(* STEPS 13: op 1 produces all the wcc components from the labels *)
               apply (rule converse_rtranclp_into_rtranclp) 
                apply (rule step_set_op_intro_Tau_2)
                  apply simp
                 apply (rule step_Tau_dataflow_op_Tau_intro)
                 apply (rule step_map_op)
                  apply (rule step_comp_op_R_Tau)
                    apply (rule step_Tau_loop_op)
                     apply (rule step_map_op)
                      apply (rule step_comp_op_L_Tau)
                        apply (rule step_map_op)
                         apply (rule step_label_propagation_op_output)
                              apply (rule refl)+
                            apply (simp add: flip: fold_append change_multiplicities_append_alt)
            subgoal       
              unfolding label_prop_output_batch_def
              apply (clarsimp del: disjCI simp add: image_iff filter_empty_conv obtain_progress_def simp flip: fold_append change_multiplicities_append_alt)
              apply (subst ocaps_drop_caps_port_disjoint)
               apply auto
              apply (subst ocaps_0_fst_snd_loop_updates)
               apply simp

              subgoal
                using os_inv(7) by (simp add: operator_state.defs os_inv(4) raw_summary_def)
              subgoal
                apply (rule bexI[of _ t, rotated])
                subgoal
                  using prems(2) apply -
                  apply (clarsimp del: disjCI simp add:  outputs_at_target_raw_summary subgraph_inv inputs_at_target_def BULK_BENQ_def ts_def operator_state.defs os_inv(4) cimage_iff split: event.splits)
                    apply hypsubst_thin
                  subgoal for e
                    apply (cases e; simp)
                    apply (elim disjE; (clarsimp del: disjCI split: event.splits)?)

                    subgoal for v1 v2
                      using stream_move(3)[rule_format, of v1 v2] apply -
                      apply (drule meta_mp)
                      subgoal
                        by (metis cin_code)
                      subgoal
                        apply (rule disjI2)+
                        apply (intro exI[of _ e] impI allI conjI)
                           apply argo
                        using  os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] apply simp_all
                        done
                      done
                    done
                  subgoal
                    apply (clarsimp del: disjCI simp add:  outputs_at_target_raw_summary subgraph_inv inputs_at_target_def BULK_BENQ_def ts_def operator_state.defs os_inv(4) cimage_iff split: event.splits)
                    apply (elim disjE; (clarsimp del: disjCI split: event.splits)?)
                    subgoal
                      using label_prop_inv(6)
                        [unfolded input_ocaps_inv_def, rule_format, of _ 0 0 0, unfolded os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified], simplified, of t ] apply -
                      apply (drule meta_mp)
                      subgoal
                        by auto
                      apply (metis zero_myprod_def)
                      done
                    subgoal
                      by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                    subgoal
                      by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                    done
                  subgoal
                    apply (clarsimp del: disjCI)
                    apply (metis UnCI label_prop_inv(4) myprod.collapse)
                    done
                  done
                subgoal
                  apply (intro conjI)
                  subgoal
                    apply (rule no_second_propa_output_frontier[OF stream_move(2)])
                    using prems(2)
                    by (clarsimp del: disjCI simp add: cimage_iff image_iff split_beta split: event.splits)

                  subgoal
                    using prems(2) apply -
                    apply (clarsimp del: disjCI simp add: image_iff cimage_iff split_beta split: event.splits)
                    apply (elim disjE)
                    subgoal
                      apply (clarsimp del: disjCI simp add: ts_def operator_state.defs os_inv(4) split: event.splits) 
                      apply (rule disjI1)
                      subgoal for e
                        apply (cases e; simp)
                        subgoal for tt d
                          apply (cases d; simp)
                          subgoal for v1 v2
                            apply (rule exI[of _ e])
                            apply simp
                            using stream_move(3)[rule_format, of v1 v2] apply -
                            apply (drule meta_mp)
                            subgoal
                              by (meson cin_code)
                            subgoal
                              by simp
                            done
                          done
                        done
                      done
                    subgoal
                      apply (clarsimp del: disjCI simp add: outputs_at_target_raw_summary subgraph_inv inputs_at_target_def BULK_BENQ_def ts_def operator_state.defs os_inv(4) split: event.splits) 
                      subgoal for e
                        apply (cases e; simp)
                        subgoal for l
                          apply (cases l; cases t; simp)
                          apply (metis myprod.sel(1) snd_eqD)
                          done
                        subgoal
                          using os_inv(5)[unfolded ty1_check_def os_inv operator_state.defs, simplified]
                            os_inv(6)[unfolded label_prob_ty2_check_def os_inv operator_state.defs, simplified]
                          by (metis snd_eqD)
                        done
                      done
                    subgoal
                      by (force simp add: os_inv operator_state.defs)
                    done
                  done
                done
              done
                           apply (rule refl)+
                          apply simp
                         apply (rule refl)+
                        apply simp
                       apply (rule refl)+
                     apply simp
                    apply (rule refl)+
                 apply simp
                apply (rule refl)+
               apply (simp add: obtain_progress_def flip: filter_filter fold_append map_append filter_append change_multiplicities_append_alt)

(* ----------------------------- *)
(* STEPS 14: op 1 flushes outpu 0 buffer with all WCC  *)
               apply (rule relpowp_imp_rtranclp[
                  where n="length (outpu (os 1) 0) + length (final_output n)"]) 
               apply (rule step_set_op_steps_Out_intro[where xs="outpu (os 1) 0 @ map (\<lambda> (d, c). (d, time c)) (final_output n)"  and p="(1, 0)"])
                 apply (rule steps_Tau_dataflow_op_steps_Out_intro[where xs="outpu (os 1) 0 @ map (\<lambda> (d, c). (d, time c)) (final_output n)" and nid = 1 and p = 0])
                  apply (rule steps_map_op[where xs="map (\<lambda>x. Out (Inr (Inr (1, 0))) (Inr x)) (outpu (os 1) 0 @ map (\<lambda>(d, c). (d, capability.time c)) (final_output n))", rotated 2])
                    apply (rule steps_comp_op_R_Out[where xs="map Inr (outpu (os 1) 0 @ map (\<lambda>(d, c). (d, capability.time c)) (final_output n))" and p="Inr (1, 0)"])
                       apply (rule steps_Out_loop_op_intro[where xs="map Inr (outpu (os 1) 0 @ map (\<lambda>(d, c). (d, capability.time c)) (final_output n))" and p="Inr (1, 0)"])
                          apply (rule steps_map_op[where xs="map (\<lambda>x. Out (Inl (Inr (1, 0))) (Inr x)) (outpu (os 1) 0 @ map (\<lambda>(d, c). (d, capability.time c)) (final_output n))" , rotated 2])
                            apply (rule steps_comp_op_L_Out[where xs="map Inr (outpu (os 1) 0 @ map (\<lambda>(d, c). (d, capability.time c)) (final_output n))"])
                                apply (rule steps_map_op[where xs="map (\<lambda>x. Out (Some 0) (Inr x)) (outpu (os 1) 0 @ map (\<lambda>(d, c). (d, capability.time c)) (final_output n))", rotated 2])
                                apply (rule steps_label_propagation_op_Write_Some[where ys=Nil])
                                apply simp
                                apply (rule refl)+
                                apply (subst outpu_0_fst_snd_loop_updates)
            subgoal
              apply (subst (3) filter_True)
              subgoal
                by (auto simp add: label_prop_output_batch_def final_output_def split_beta comp_def os_inv(4) operator_state.defs)
              apply (rule map_cong)
              subgoal
                by (auto simp add: final_output_def split_beta comp_def os_inv(4) operator_state.defs)
              subgoal
                by simp
              done
                                apply (rule refl)+
                                apply force
                               apply fastforce
                              apply (rule refl)+
                            apply simp
                           apply (rule refl)+
                          apply simp
                         apply simp
                        apply (rule refl)+
                    apply simp
                   apply (rule refl)+
                  apply simp
                 apply simp
                apply simp
               apply (rule refl)+

(* ----------------------------- *)
(* STEPS 15: set_op picks the desired WCC  *)
              apply (rule rtranclp.intros(1))
             apply (rule step_set_op_intro_Out)
                apply (rule refl)+
            subgoal
              unfolding final_output_def
              using prems(2) apply -
              apply (clarsimp del: disjCI simp add: cimage_iff)
              apply hypsubst_thin
              apply (rule disjI2)
              apply (rule disjI1)
              apply (intro cBexI[of _ "(Inr (ccs (set (icoll (map (\<lambda>(x, t'). Data t' (projl x)) (((outputs_at_target (summ sg) os >> cbufs) >> inputs_at_target os) (1, 0)) @@- lxs) t) \<union> all_edges os_label_prop (myfst t))), Cap t 0)"])
               apply simp_all
              unfolding label_prop_output_batch_def
              apply (clarsimp del: disjCI simp add: image_iff filter_empty_conv obtain_progress_def simp flip: fold_append change_multiplicities_append_alt)

              apply (rule exI[of _ t])
              apply (intro conjI)
              subgoal
                apply (subst ocaps_drop_caps_port_disjoint)
                 apply auto
                  apply (subst ocaps_0_fst_snd_loop_updates)
                subgoal
                  using os_inv(7) by (simp add: operator_state.defs os_inv(4) raw_summary_def)
                using prems(2) apply -
                  apply (clarsimp del: disjCI simp add:  outputs_at_target_raw_summary subgraph_inv inputs_at_target_def BULK_BENQ_def ts_def operator_state.defs os_inv(4) cimage_iff split: event.splits)
                    apply hypsubst_thin
                subgoal for e
                  apply (cases e; simp)
                  apply (elim disjE; (clarsimp del: disjCI split: event.splits)?)

                  subgoal for v1 v2
                    using stream_move(3)[rule_format, of v1 v2] apply -
                    apply (drule meta_mp)
                    subgoal
                      by (metis cin_code)
                    subgoal
                      apply (rule disjI2)+
                      apply (intro exI[of _ e] impI allI conjI)
                         apply argo
                      using  os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] apply simp_all
                      done
                    done
                  subgoal for a b
                    using stream_move(3)[rule_format, of a b] apply -
                    apply (drule meta_mp)
                    subgoal
                      by (metis cin_code)
                    subgoal
                      apply (rule disjI2)+
                      apply (intro exI[of _ e] impI allI conjI)
                         apply argo
                      using  os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] apply simp_all
                      done
                    done
                  subgoal for a b
                    using stream_move(3)[rule_format, of a b] apply -
                    apply (drule meta_mp)
                    subgoal
                      by (metis cin_code)
                    subgoal
                      apply (rule disjI2)+
                      apply (intro exI[of _ e] impI allI conjI)
                         apply argo
                      using  os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] apply simp_all
                      done
                    done
                  subgoal for a b
                    using stream_move(3)[rule_format, of a b] apply -
                    apply (drule meta_mp)
                    subgoal
                      by (metis cin_code)
                    subgoal
                      apply (rule disjI2)+
                      apply (intro exI[of _ e] impI allI conjI)
                         apply argo
                      using  os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified] apply simp_all
                      done
                    done
                  done
                subgoal
                  apply (clarsimp del: disjCI simp add:  outputs_at_target_raw_summary subgraph_inv inputs_at_target_def BULK_BENQ_def ts_def operator_state.defs os_inv(4) cimage_iff split: event.splits)
                  apply (elim disjE; (clarsimp del: disjCI split: event.splits)?)
                  subgoal
                    using label_prop_inv(6)
                      [unfolded input_ocaps_inv_def, rule_format, of _ 0 0 0, unfolded os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified], simplified, of t ] apply -
                    apply (drule meta_mp)
                    subgoal
                      by auto
                    apply (metis zero_myprod_def)
                    done
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    using label_prop_inv(6)
                      [unfolded input_ocaps_inv_def, rule_format, of _ 0 0 0, unfolded os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified], simplified, of undefined] apply -
                    apply (drule meta_mp)
                    subgoal
                      by auto
                    apply (metis zero_myprod_def)
                    done
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    using label_prop_inv(6)
                      [unfolded input_ocaps_inv_def, rule_format, of _ 0 0 0, unfolded os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified], simplified, of undefined] apply -
                    apply (drule meta_mp)
                    subgoal
                      by auto
                    apply (metis zero_myprod_def)
                    done
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    using label_prop_inv(6)
                      [unfolded input_ocaps_inv_def, rule_format, of _ 0 0 0, unfolded os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified], simplified, of undefined] apply -
                    apply (drule meta_mp)
                    subgoal
                      by auto
                    apply (metis zero_myprod_def)
                    done
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  done
                subgoal
                  apply (clarsimp del: disjCI)
                  apply (metis UnCI label_prop_inv(4) myprod.collapse)
                  done
                subgoal
                  apply (subst ocaps_0_fst_snd_loop_updates)
                  subgoal
                    using os_inv(7) by (simp add: operator_state.defs os_inv(4) raw_summary_def)
                  apply (thin_tac "((nid, p), WCC, t) |\<in>| _")
                  apply (clarsimp del: disjCI simp add: outputs_at_target_raw_summary subgraph_inv inputs_at_target_def BULK_BENQ_def ts_def operator_state.defs os_inv(4) cimage_iff split: event.splits)
                  apply (elim disjE; (clarsimp del: disjCI split: event.splits)?)
                  subgoal
                    using label_prop_inv(6)
                      [unfolded input_ocaps_inv_def, rule_format, of _ 0 0 0, unfolded os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified], simplified, of t] apply -
                    apply (drule meta_mp)
                    subgoal
                      by auto
                    apply (metis zero_myprod_def)
                    done
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  subgoal
                    by (auto simp add: os_inv(7)[rule_format, of 1, unfolded raw_summary_def, simplified])
                  done
                subgoal
                  apply (subst ocaps_0_fst_snd_loop_updates)
                  subgoal
                    using os_inv(7) by (simp add: operator_state.defs os_inv(4) raw_summary_def)
                  apply (thin_tac "((nid, p), WCC, t) |\<in>| _")
                  apply (clarsimp del: disjCI)
                  apply (rule disjI1)
                  using label_prop_inv(4) os_inv(4)
                  apply (simp add: operator_state.defs)
                  apply (metis UnCI myprod.collapse)
                  done
                done
              subgoal
                by (rule no_second_propa_output_frontier[OF stream_move(2)])
              subgoal
                apply (clarsimp del: disjCI simp add: image_iff cimage_iff split_beta split: event.splits)
                apply (elim disjE)
                subgoal
                  apply (clarsimp del: disjCI simp add: ts_def operator_state.defs os_inv(4) split: event.splits)
                  apply (rule disjI1)
                  subgoal for e
                    apply (cases e; simp)
                    subgoal for tt d
                      apply (cases d; simp)
                      subgoal for v1 v2
                        using stream_move(3)[rule_format, of v1 v2] apply -
                        apply (drule meta_mp)
                        subgoal
                          by (meson cin_code)
                        subgoal
                          apply (rule bexI[of _ "(Inl (v1, v2), tt)"])
                           apply simp
                          apply (simp add: image_iff)
                          apply (rule disjI2)+
                          apply (rule exI[of _ "Data tt (v1, v2)"])
                          apply simp

                          done

                        done
                      done
                    done
                  done
                subgoal
                  apply (clarsimp del: disjCI simp add: outputs_at_target_raw_summary subgraph_inv inputs_at_target_def BULK_BENQ_def ts_def operator_state.defs os_inv(4) split: event.splits)
                  subgoal for e
                    apply (cases e; simp)
                    subgoal for l
                      apply (cases l; cases t; simp)
                      apply (rule disjI1)
                      apply (elim disjE)
                      subgoal for a b x1 x2
                        apply (rule bexI[of _ "(Inl (a, b), MyPair x1 x2)"])
                         apply simp
                        apply simp
                        done
                      subgoal for a b x1 x2
                        apply (rule bexI[of _ "(Inl (a, b), MyPair x1 x2)"])
                         apply simp
                        apply simp
                        done
                      subgoal for a b x1 x2
                        apply (rule bexI[of _ "(Inl (a, b), MyPair x1 x2)"])
                         apply simp
                        apply simp
                        done
                      done
                    subgoal
                      using os_inv(5)[unfolded ty1_check_def os_inv operator_state.defs, simplified]
                        os_inv(6)[unfolded label_prob_ty2_check_def os_inv operator_state.defs, simplified]
                      apply (elim disjE)
                      subgoal
                        apply (rule disjI1)
                        apply (rule bexI[of _ "(e, t)"])
                         apply simp
                        apply simp
                        done
                      subgoal
                        apply (rule disjI1)
                        apply (rule bexI[of _ "(e, t)"])
                         apply simp
                        apply simp
                        done
                      subgoal
                        apply (rule disjI1)
                        apply (rule bexI[of _ "(e, t)"])
                         apply simp
                        apply simp
                        done
                      done
                    done
                  done
                subgoal
                  by (force simp add: os_inv operator_state.defs)
                done
              subgoal
                apply (simp add: operator_state.defs os_inv(4))
                apply (subst Un_commute)
                apply (subst all_edges_fst_label_prop_input0_batched_input_eq)
                subgoal
                  by (simp add: input_CONSUMES)
                subgoal
                  using label_prop_inv(5)
                  apply (simp add: label_prop_upd_inv_def all_vertices_def all_edges_def neighbors_def operator_state.defs os_inv(4))
                  apply blast
                  done


                subgoal
                  apply (rule wf_label_prop_updates_subset[where
                    S="set (chns (1, 1) @ map (\<lambda>(d, t). (d, t -+- MyPair 0 1)) (chns (2, 1)))"])
                   apply (rule wf_label_prop_updates_os_mono[OF label_prop_inv(7) _ _ _ refl])
                      apply (simp add: os_inv(4) operator_state.defs)
                     apply (simp add: os_inv(4) operator_state.defs)
                    apply (simp add: os_inv(4) operator_state.defs)
                   apply (simp add: input_CONSUMES os_inv(4) operator_state.defs buffers_inv BULK_BENQ_def inputs_at_target_def outputs_at_target_raw_summary subgraph_inv(1))
                  done

                subgoal
                  apply (simp add: split_beta input_CONSUMES)
                  apply (rule sym)
                  apply (subgoal_tac
                      "ccs (all_edges \<lparr>intsum = intsum (os 1), consu = consu (os 1), inter = operator_state.inter (os 1),
                        produ = produ (os 1), input = input (os 1), outpu = outpu (os 1), front = front (os 1),
                        ocaps = ocaps (os 1), initia = initia (os 1), en1 = Inl, de1 = projl, is_en1 = isl,
                        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr> (myfst t) \<union>
                      set (icoll (map (\<lambda>(x, t'). Data t' (projl x))
                        (((outputs_at_target (summ sg) os >> cbufs) >> inputs_at_target os) (1, 0)) @@- lxs) t)) =
                     ccs (all_edges \<lparr>intsum = intsum (os 1), consu = consu (os 1), inter = operator_state.inter (os 1),
                        produ = produ (os 1), input = input (os 1), outpu = outpu (os 1),
                        front = frontier \<circ> (\<lambda>p. c_imp c' (Loc 1 (Trg p))), ocaps = ocaps (os 1), initia = True,
                        en1 = Inl, de1 = projl, is_en1 = isl, en2 = Inr, de2 = projr, is_en2 = isr,
                        timestamps = T, graph = G, vertices = V, label = L\<rparr> (myfst t) \<union>
                      (\<Union>x\<in>(set (input (os 1) 0) \<union>
                          (set (cbufs (1, 0)) \<union>
                            (set (outpu (os 0) 0) \<union>
                              case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined) `
                                {x \<in> set (ltaken n lxs). is_Data x}))) \<inter>
                          {x. myfst (snd x) \<le> myfst t}.
                          {projl (fst x), (snd (projl (fst x)), fst (projl (fst x)))}))")
                  subgoal
                    apply simp
                    apply (rule Wcc.components_from_labels_correct)
                    subgoal
                      using labels_after_loop_updates[of n, rule_format, of \<open>myfst t\<close>]
                      apply (simp add: os_label_after_loop_updates_def loop_res_def
                          os_label_after_input0_def)
                      apply (subst (asm) all_edges_fst_label_prop_input0_batched_input_eq)
                         apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
                            label_input0_msgs_def input_CONSUMES operator_state.defs os_inv(4))
                        apply (simp add: label_prop_inv(5) os_label_after_read_input0_def
                            os_label_after_first_propa_def input_CONSUMES)
                      using label_prop_inv(7)[unfolded inputs_at_target_def buffers_inv BULK_BENQ_def
                          subgraph_inv outputs_at_target_raw_summary operator_state.defs, simplified]
                       apply (auto simp add: os_label_after_read_input0_def os_label_after_first_propa_def
                          os_inv(4) operator_state.defs input_CONSUMES wf_label_prop_updates_def
                          all_vertices_def all_edges_def neighbors_def)[1]
                      apply (simp add: os_label_after_read_input0_def os_label_after_first_propa_def
                          label_front_after_first_propa_def
                          os_after_label_input0_def os_after_label_read_input0_def
                          os_after_input_output_def os_input_after_output_def
                          os_after_input_stream_def os_input_after_stream_def
                          os_first_propa_def os_progress_def sg_first_propa_def sg_progress_def
                          cbufs_after_label_read_input0_def cbufs_after_input_output_def
                          input0_msgs_def label_input0_msgs_def input_data_def input_events_def
                          input_CONSUMES os_inv(1,4) operator_state.defs obtain_progress_def
                          split_beta)
                      done
                    subgoal sorry
                    done

                  subgoal premises prems
                    apply (subst set_icoll_lshift)
                    subgoal
                      using input_stream_inv timely_input_stream_expires_le by blast
                    apply (subst (2) set_icoll_ltaken_if_no_ldropn_data_le[where n=n])
                    subgoal
                      using timely_input_stream_expires_le[OF timely_input_stream_ldrop[OF stream_move(1) input_stream_inv]] by blast
                    subgoal
                      using timely_input_stream_ldropn_no_data_le_if_not_frontier_less_equal[OF input_stream_inv stream_move(1) stream_move(2)] by blast
                    apply (simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary
                        subgraph_inv(1) inputs_at_target_def set_icoll_llist_of)
                    apply (simp add: all_edges_def all_vertices_def neighbors_def)
                    apply (rule label_prop_collected_edge_payloads_ccs_eq)
                    subgoal
                      using label_prop_inv(4)
                      by (force simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary
                          subgraph_inv(1) inputs_at_target_def)
                    subgoal
                      using label_prop_inv(4)
                      by (force dest!: setltakenD)
                    subgoal
                      using prems(1) label_prop_inv(4)
                      by (force simp add: cimage_iff cin.rep_eq ts_def cset_of_llist.rep_eq
                          buffers_inv BULK_BENQ_def outputs_at_target_raw_summary subgraph_inv(1)
                          inputs_at_target_def split: event.splits dest!: setltakenD)
                    done
                  done
                done
              subgoal
                apply (elim disjE)
                subgoal
                  apply (clarsimp simp add: cin.rep_eq ts_def cset_of_llist.rep_eq split: event.splits)
                  subgoal for a b
                    using label_prop_inv(4)
                    by (metis UnCI event.sel(1) imageI myprod.collapse)
                  done
                subgoal
                  apply (erule cBexE)
                  using label_prop_inv(4)
                  apply (clarsimp simp add: buffers_inv BULK_BENQ_def outputs_at_target_raw_summary
                      subgraph_inv(1) inputs_at_target_def)
                  apply (drule bspec[where x=t])
                   apply force
                  apply (cases t)
                  apply simp
                  done

                subgoal
                  by force
                done
              done
            subgoal 
              using prems(1) by assumption
             apply (rule refl)+


            subgoal
          apply (rule wb_upto_b_sym)
          apply (rule wb_upto_b_base)
          apply (unfold R_def[simplified])
          apply (rule exI[of _ "cUn (Pair (1, 0) |`| cset_from_list (outpu (os 1) 0 @ map  (\<lambda> (d, c). (d, time c)) (final_output n))) S"])
          apply (rule exI[of _ "cinsert ((nid, p), WCC, t) D"])
              apply (rule exI[of _ "ldropn n lxs"])
          apply (rule exI[of _ "os_after_final_output n"])
          apply (rule exI[of _ "os_label_after_final_output n"])
          apply (rule exI[of _ "cbufs((1, 0) := Nil, (1, 1) := Nil, (2, 1) := Nil)"])
          apply (rule exI[of _ "sg_after_second_propa n"])
              apply (intro conjI)
              subgoal
                apply (rule arg_cong3[where f=set_op])
                  apply (rule refl)
                 apply (rule refl)
                apply (rule arg_cong2[where f=dataflow_op])
                subgoal
                  by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
                      sg_after_label_progress_def sg_after_ooo_input_progress_def
                      sg_first_propa_def sg_progress_def)
                subgoal
                  apply (subst dataflow_tree_to_operator_def)
                  apply (simp only: dataflow_tree_to_operator_aux.simps Let_def prod.case
                      fst_conv snd_conv add_0 one_add_one diff_zero)
                  apply (rule arg_cong[where f=\<open>map_op (case_sum id id) (case_sum id id)\<close>])
                  apply (rule comp_op_buf_cong)
                  subgoal
                    by (auto simp add: fun_eq_iff split: sum.splits)
                  subgoal
                    apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
                    apply (rule arg_cong[where f=\<open>ooo_input_op _\<close>])
                    by (simp add: os_after_final_output_def os_after_label_produces_def
                        os_after_second_propa_def os_after_increment_progress_def
                        os_after_label_progress_def os_after_ooo_input_progress_def
                        os_after_loop_progress_def os_after_drop_caps_def os_after_loop_updates_def
                        os_after_label_input0_def os_after_label_read_input0_def
                        os_after_input_output_def os_input_after_output_def os_after_input_stream_def
                        os_input_after_stream_def os_first_propa_def os_progress_def input_events_def
                        input_data_def loop_res_def op_state_base_def operator_state.defs
                        obtain_progress_def os_inv(1,4))
                  subgoal
                    apply (rule loop_op_buf_cong)
                    subgoal
                      by (auto simp add: fun_eq_iff eq_diff_eq one_add_one split: sum.splits)
                    subgoal
                      apply (rule arg_cong[where f=\<open>map_op (case_sum id id) (case_sum id id)\<close>])
                      apply (rule comp_op_buf_cong)
                      subgoal
                        by (auto simp add: fun_eq_iff eq_diff_eq split: sum.splits)
                      subgoal
                        apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
                        apply (rule arg_cong[where f=label_propagation_op])
                        by (simp add: os_label_after_final_output_def
                            os_label_after_produces_def label_produces_batch_def
                            label_produces_below_times_def os_label_after_second_propa_def
                            label_front_after_second_propa_def os_label_after_label_progress_def
                            os_label_after_drop_caps_def os_label_after_loop_updates_def
                            loop_res_def os_label_after_input0_def label_input0_msgs_def
                            os_label_after_read_input0_def input0_msgs_def input_data_def
                            input_events_def os_label_after_first_propa_def
                            label_front_after_first_propa_def sg_first_propa_def
                            sg_progress_def cbufs_after_label_read_input0_def
                            cbufs_after_input_output_def os_after_label_input0_def
                            os_after_label_read_input0_def os_after_input_output_def
                            os_after_input_stream_def os_first_propa_def os_progress_def
                            obtain_progress_def CONSUMES_CONSUMES image_Un image_image
                            Un_ac disj_ac flip: fold_append)
                      subgoal
                        apply (rule arg_cong[where f=\<open>map_op _ _\<close>])
                        apply (rule arg_cong[where f=\<open>increment_op _ _ _\<close>])
                        apply (simp add: os_after_final_output_def os_after_label_produces_def
                            os_after_second_propa_def os_after_increment_progress_def
                            os_after_label_progress_def os_after_ooo_input_progress_def
                            os_after_loop_progress_def os_after_drop_caps_def
                            os_after_loop_updates_def loop_res_def)
                        apply (simp add: os_after_label_input0_def os_after_label_read_input0_def
                            os_after_input_output_def os_after_input_stream_def
                            os_first_propa_def os_progress_def
                            cbufs_after_label_read_input0_def cbufs_after_input_output_def
                            snd_snd_loop_updates_cbufs_irrelevant2)
                        apply (rule trans[of _ \<open>snd (snd (loop_updates cbufs
                            (os_label_after_input0 n) os)) 2
                            \<lparr>consu := [], inter := [], produ := []\<rparr>\<close>])
                        subgoal
                          by (rule operator_state_eqI)
                            (simp_all add: op_state_base_def obtain_progress_def)
                        apply (rule arg_cong[where
                              f=\<open>\<lambda>x. x\<lparr>consu := [], inter := [], produ := []\<rparr>\<close>])
                        apply (rule arg_cong[where
                              f=\<open>\<lambda>l. snd (snd (loop_updates cbufs l os)) 2\<close>])
                        apply (simp add: os_label_after_input0_def label_input0_msgs_def
                            os_label_after_read_input0_def input0_msgs_def input_data_def
                            input_events_def os_label_after_first_propa_def
                            label_front_after_first_propa_def sg_first_propa_def
                            sg_progress_def CONSUMES_CONSUMES flip: fold_append)
                        done
                      subgoal
                        apply (rule ballI)
                        apply (erule IntE)
                        apply (thin_tac \<open>p \<in> inputs X\<close> for p X)
                        apply (case_tac p)
                         apply simp
                        apply (clarsimp split: prod.splits if_splits)
                        apply (clarsimp simp add: ran_def)
                        apply (rename_tac x)
                        apply (case_tac x)
                         apply simp
                        apply (clarsimp split: prod.splits if_splits)
                        done
                      done
                    subgoal
                      apply (rule ballI)
                      apply (erule IntE)
                      apply (thin_tac \<open>p \<in> inputs X\<close> for p X)
                      apply (case_tac p)
                       apply simp
                      apply (clarsimp split: prod.splits if_splits)
                      apply (clarsimp simp add: ran_def)
                      apply (rename_tac x)
                      apply (case_tac x)
                       apply simp
                      apply (clarsimp split: prod.splits if_splits)
                      done
                    done
                  subgoal
                    apply (rule ballI)
                    apply (erule IntE)
                    apply (thin_tac \<open>p \<in> inputs X\<close> for p X)
                    apply (case_tac p)
                     apply simp
                    apply (clarsimp split: prod.splits if_splits)
                    apply (clarsimp simp add: ran_def)
                    apply (rename_tac x)
                    apply (case_tac x)
                     apply simp
                    apply (clarsimp split: prod.splits if_splits)
                    done
                  done
                done
              subgoal (* TIP 1: this reduces to cset equality. TIP 2: You probably want to do a case distinction if the given arbitrary t is frontier_less_equal (exit_scope myfst (front os 0 + front os 1)) (myfst t) or not *)
                apply (rule arg_cong2[where f=set_spec_op, OF _ refl])
                apply (subgoal_tac \<open>outpu (os_after_final_output n 1) (0 :: 2) = []\<close>)
                 prefer 2
                 subgoal
                   by (simp add: os_after_final_output_def os_label_after_final_output_def
                       op_state_base_def operator_state.defs)
                apply simp
                (* Remaining goal (after killing outpu-after and splitting the @):
                     cUn (cUn S OutOld) SPold
                   = cUn (cUn (Pair (1,0) |`| cUn OutOld' FinalImg) S) SPnew
                   where FinalImg = (\<lambda>(d,c). (d, time c)) |`| cset_from_list (final_output n).
                   Modulo cUn-AC this is:  SPold = cUn (Pair (1,0) |`| FinalImg) SPnew.
                   Proof plan (TIP 2): extensional via cset_eq_iff; for an element
                   x = ((1,0), Inr (ccs ...), t) case-distinguish on
                     frontier_less_equal (exit_scope myfst (front (os 1) 0 + front (os 1) 1)) (myfst t):
                   - \<not>fle (timestamp closed): x's payload is emitted in final_output n
                     (final_output_def filters \<not> frontier_less_equal of the c''-frontier;
                      use second_propa / label_prop_inv(2) labels_stable and
                      label_prop_collected_edge_payloads_ccs_eq as in the subgoal near the
                      BULK_BENQ/outputs_at_target_raw_summary proof above at ~line 14383).
                   - fle (timestamp live): x is in SPnew with the same ccs payload:
                     edges of (chns-after @@- ldropn n lxs) up to t plus
                     all_edges (os_label_after_final_output n) (myfst t)
                     equal edges of (chns @@- lxs) up to t plus all_edges os_label_prop (myfst t);
                     cf. labels_after_final_output and the timestamps/ocaps facts
                     ocaps0_after_final_output_mysnd, outpu_0_after_final_output_empty. *)
                apply (simp only: cset_eq_iff)
                apply (rule allI)
                subgoal for x
                  apply (case_tac \<open>frontier_less_equal
                      (exit_scope myfst (front (os 1) 0 + front (os 1) 1))
                      (myfst (snd (snd x)))\<close>)
                  subgoal (* live timestamp: x \<in> SPold \<longleftrightarrow> x \<in> SPnew (same ccs payload) *)
                    apply (clarsimp simp flip: cin.rep_eq simp add: image_iff)
                    apply (rule iffI)
                     apply (elim disjE)
                       apply simp
                    subgoal (* x \<in> OutOld \<Longrightarrow> x \<in> Pair(1,0)`(OutOld \<union> FinalImg) *)
                      by (force simp flip: cin.rep_eq
                          simp add: cset_from_list_def cset_of_llist.rep_eq image_iff)
                     subgoal (* HARD 1: x \<in> SPold \<Longrightarrow> x \<in> SPnew: same t (live), same ccs
                          payload; edges of the consumed prefix ltaken n lxs are now in
                          all_edges (os_label_after_final_output n) *)
                       apply (rule disjI2)+
                       apply (clarsimp simp flip: cin.rep_eq
                           simp add: image_iff cset_from_list_def cset_of_llist.rep_eq)
                       apply (subst cimage_iff)
                       apply (rule cBexI[where x=xa for xa])
                       subgoal (* payload equality at the witness timestamp xa:
                            ccs (edges of chns(1,0) @@- lxs up to xa \<union> all_edges os_label_prop)
                            = ccs (edges of chns-after @@- ldropn n lxs up to xa
                                   \<union> all_edges (os_label_after_final_output n));
                            use label_prop_collected_edge_payloads_ccs_eq as at ~14383 *)
                         sorry
                       subgoal (* xa in the new domain: live prefix/buffer timestamps land in
                            timestamps (os_label_after_final_output n) with surviving ocaps;
                            use in_lset_ltaken_ldropn, timely_input_stream_expires_le,
                            label_prop_inv(4) (mysnd = 0) *)
                         sorry
                       done
                    apply (elim disjE)
                      subgoal (* HARD 2: x \<in> Pair(1,0)`(OutOld \<union> FinalImg): OutOld case goes
                           to LHS disjunct 2 (force as above); FinalImg case contradicts fle
                           (final_output only emits closed timestamps) *)
                        sorry
                     apply simp
                    subgoal (* HARD 3: x \<in> SPnew \<Longrightarrow> x \<in> SPold: reverse of HARD 1 *)
                      sorry
                    done
                  subgoal (* closed timestamp: x \<in> SPold \<longleftrightarrow> x \<in> Pair (1,0) |`| FinalImg *)
                    sorry
                  done
                done
              subgoal
                using subgraph_inv(1)
                by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
                    sg_after_label_progress_def sg_after_ooo_input_progress_def sg_first_propa_def sg_progress_def)
              subgoal
                using subgraph_inv(2)
                by (simp add: sg_after_second_propa_def sg_after_increment_progress_def
                    sg_after_label_progress_def sg_after_ooo_input_progress_def sg_first_propa_def sg_progress_def)
              subgoal sorry
              subgoal sorry
              subgoal sorry
              subgoal sorry
              subgoal sorry
              subgoal
                apply (rule allI)
                subgoal for na
                  using Intsum_loop[of n, rule_format, of na]
                    Intsum_loop[of n, rule_format, of \<open>1 :: 3\<close>]
                  by (cases na rule: num3_cases)
                    (auto simp add: os_after_final_output_def os_after_label_produces_def
                      os_after_second_propa_def os_after_increment_progress_def
                      os_after_label_progress_def os_after_ooo_input_progress_def
                      os_after_loop_progress_def os_after_drop_caps_def
                      os_label_after_final_output_def os_label_after_produces_def
                      os_label_after_second_propa_def os_label_after_label_progress_def
                      os_label_after_drop_caps_def op_state_base_def operator_state.defs
                      obtain_progress_def drop_caps_def produces_def)
                done

              subgoal
                using outpu_1_after_loop_updates_empty(4)[of n]
                by (simp add: os_after_final_output_def os_after_label_produces_def
                    os_after_second_propa_def os_after_increment_progress_def
                    os_after_label_progress_def os_after_ooo_input_progress_def
                    os_after_loop_progress_def os_after_drop_caps_def
                    input_ocaps_inv_def input_ocaps_inv_op_state_base
                    op_state_base_def operator_state.defs obtain_progress_def)

              subgoal
                by (simp add: os_after_final_output_def os_after_label_produces_def
                    os_after_second_propa_def os_after_increment_progress_def
                    os_after_label_progress_def os_after_ooo_input_progress_def
                    os_after_loop_progress_def os_after_drop_caps_def os_after_loop_updates_def
                    os_after_label_input0_def os_after_label_read_input0_def
                    os_after_input_output_def os_input_after_output_def os_after_input_stream_def
                    os_input_after_stream_def os_first_propa_def os_progress_def
                    loop_res_def op_state_base_def operator_state.defs obtain_progress_def
                    drop_caps_def produces_def input_CONSUMES os_inv(9))

              subgoal
                by (simp add: os_after_final_output_def os_after_label_produces_def
                    os_after_second_propa_def os_after_increment_progress_def
                    os_after_label_progress_def os_after_ooo_input_progress_def
                    os_after_loop_progress_def os_after_drop_caps_def
                    op_state_base_def operator_state.defs obtain_progress_def
                    outpu_1_after_loop_updates_empty(2)[of n]
                    outpu_1_after_loop_updates_empty(3)[of n]
                    loop_updates_cbufs_cleared[OF step_loop[of n], of \<open>((2 :: 3), (1 :: 2))\<close>])

              subgoal
                using buffers_inv by simp

              subgoal (* Use the sequence of have STEPS to prove this one *)
                apply (subgoal_tac \<open>cbufs_after_loop_updates n =
                    cbufs((1, 0) := [], (1, 1) := [], (2, 1) := [])\<close>)
                 using dataplane_after_final_output[of n] apply simp
                apply (rule ext)
                apply (simp add: cbufs_after_loop_updates_def loop_res_def
                    cbufs_after_label_read_input0_def cbufs_after_input_output_def
                    loop_updates_cbufs_cleared[OF step_loop[of n], of \<open>((1 :: 3), (1 :: 2))\<close>]
                    loop_updates_cbufs_cleared[OF step_loop[of n], of \<open>((2 :: 3), (1 :: 2))\<close>])
                done



              subgoal
                apply (simp add: os_after_final_output_def os_after_label_produces_def
                    os_after_second_propa_def os_after_increment_progress_def
                    os_after_label_progress_def os_after_ooo_input_progress_def
                    os_after_loop_progress_def os_after_drop_caps_def os_after_loop_updates_def
                    os_after_label_input0_def os_after_label_read_input0_def
                    os_after_input_output_def os_input_after_output_def os_after_input_stream_def
                    os_input_after_stream_def os_first_propa_def os_progress_def input_events_def
                    loop_res_def op_state_base_def operator_state.defs obtain_progress_def os_inv(1,4))
                apply (subst mset_ocaps_updates[of "ltaken n lxs" "ldropn n lxs"
                    "ocaps (os (0 :: 3)) (0 :: 2)"])
                 apply (simp add: input_stream_inv)
                apply (rule timely_input_stream_ldrop[OF stream_move(1) input_stream_inv])
                done




              subgoal (* Use the sequence of have STEPS to prove this one *)
                by (rule labels_after_final_output)


              subgoal (* IGNORE THIS SUBGOAL SORRY *) sorry
              subgoal
                by (simp add: os_after_final_output_def os_label_after_final_output_def
                    os_label_after_produces_def os_label_after_second_propa_def
                    os_label_after_label_progress_def os_label_after_drop_caps_def
                    op_state_base_def operator_state.defs drop_caps_def produces_def obtain_progress_def
                    input_0_after_loop_updates_empty input_1_after_loop_updates_empty)



              subgoal
                apply (rule ballI)
                apply (erule UnE)
                subgoal
                  apply (erule UnE)
                  subgoal
                    using label_prop_inv(4)
                    by (metis (mono_tags, lifting) UnCI image_iff in_lset_ltaken_ldropn)

                  subgoal
                    using outpu_0_after_final_output_empty[of n]
                    by (simp add: outputs_at_target_raw_summary inputs_at_target_def BULK_BENQ_def
                        subgraph_inv(1) sg_after_second_propa_def sg_after_increment_progress_def
                        sg_after_label_progress_def sg_after_ooo_input_progress_def sg_first_propa_def
                        sg_progress_def os_after_final_output_def os_label_after_final_output_def
                        os_after_label_produces_def os_label_after_produces_def
                        os_after_second_propa_def os_label_after_second_propa_def
                        os_label_after_label_progress_def os_label_after_drop_caps_def
                        op_state_base_def operator_state.defs drop_caps_def produces_def obtain_progress_def
                        input_0_after_loop_updates_empty)

                  done
                subgoal
                  using ocaps0_after_final_output_mysnd[of n]
                  by simp
                done



              subgoal
                apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                    os_label_after_second_propa_def os_label_after_label_progress_def
                    os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def)
                apply (rule label_prop_upd_inv_after_loop_updates)
                done
              subgoal
                apply (simp add: os_after_final_output_def input_ocaps_inv_op_state_base)
                apply (rule input_ocaps_inv_empty_inputsI)
                apply (rule allI)
                subgoal for p
                  apply (cases \<open>p = (0 :: 2)\<close>)
                   apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                      os_label_after_second_propa_def os_label_after_label_progress_def
                      os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def
                      input_0_after_loop_updates_empty)
                  apply (subgoal_tac \<open>p = (1 :: 2)\<close>)
                   apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                      os_label_after_second_propa_def os_label_after_label_progress_def
                      os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def
                      input_1_after_loop_updates_empty)
                  by (rule num2_neq(1))
                done
              subgoal
                apply (subst wf_label_prop_updates_cong[
                    where os' = \<open>os_label_after_loop_updates n\<close>
                      and S' = \<open>set (input (os_label_after_loop_updates n) (1 :: 2)) \<union>
                        set (cbufs_after_loop_updates n ((1 :: 3), (1 :: 2)) @
                          outpu ((os_after_loop_updates n) (2 :: 3)) (1 :: 2) @
                          map (\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat))))
                            (input ((os_after_loop_updates n) (2 :: 3)) (1 :: 2) @
                             cbufs_after_loop_updates n ((2 :: 3), (1 :: 2)) @
                             outpu (os_label_after_loop_updates n) (1 :: 2)))\<close>])
                     apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                        os_label_after_second_propa_def os_label_after_label_progress_def
                        os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def)
                    apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                        os_label_after_second_propa_def os_label_after_label_progress_def
                        os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def)
                   apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                        os_label_after_second_propa_def os_label_after_label_progress_def
                        os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def)
                  apply (simp add: os_label_after_final_output_def os_label_after_produces_def
                        os_label_after_second_propa_def os_label_after_label_progress_def
                        os_label_after_drop_caps_def drop_caps_def produces_def obtain_progress_def)
                 apply (simp add: outputs_at_target_raw_summary subgraph_inv(1)
                    inputs_at_target_def BULK_BENQ_def
                    sg_after_second_propa_def sg_after_increment_progress_def
                    sg_after_label_progress_def sg_after_ooo_input_progress_def
                    sg_first_propa_def sg_progress_def
                    os_after_final_output_def os_label_after_final_output_def
                    os_after_label_produces_def os_label_after_produces_def
                    os_after_second_propa_def os_label_after_second_propa_def
                    os_after_increment_progress_def os_after_label_progress_def
                    os_label_after_label_progress_def os_after_ooo_input_progress_def
                    os_after_loop_progress_def os_after_drop_caps_def os_label_after_drop_caps_def
                    label_produces_batch_def label_prop_output_batch_def drop_caps_def produces_def
                    op_state_base_def operator_state.defs obtain_progress_def
                    input_1_after_loop_updates_empty outpu_1_after_loop_updates_empty
                    ocaps_1_os2_after_loop_updates_empty
                    loop_updates_cbufs_cleared[OF step_loop[of n], of \<open>((1 :: 3), (1 :: 2))\<close>]
                    loop_updates_cbufs_cleared[OF step_loop[of n], of \<open>((2 :: 3), (1 :: 2))\<close>])
                subgoal
                  by (auto simp add: image_Un image_iff)
                apply (rule wf_after_loop_updates_pending)
                done
            done
          done
        done
      done
    done
  qed
qed

end
