theory Lifted_Table_1

imports
  BNA_Operators
  "table_1/B1"
  "table_1/B2"
  "table_1/B3"
  "table_1/B4"
  "table_1/B5"
  "table_1/B6"
  "table_1/B7"
  "table_1/B8"
  "table_1/B9"
  "table_1/B10"
  "table_1/R1"
  "table_1/R2"
  "table_1/R3"
  "table_1/R4"
  "table_1/R5"
  "table_1/R6"
  "table_1/F1"
  "table_1/F2"
  Lifted
begin

no_notation wbisim (infix "\<approx>"40)
no_notation id_empty_op ("\<I>")
no_notation scomp_op (infixl "\<bullet>" 65)
no_notation pcomp_op (infixl "\<parallel>" 64)
no_notation feedback_op ( "_ \<up>" [66] 65)
no_notation transp_empty_op ("\<X>")

lemma B1:
  \<open>op1 \<parallel> (op2 \<parallel> op3) \<approx> map_operator reassoc reassoc ((op1 \<parallel> op2) \<parallel> op3)\<close>
  apply transfer
  apply (auto simp add: inj_eq split: if_splits  intro!: inj_onI B1 bisim_wbisim)
  done

lemma B2_1:
  \<open>(op \<parallel> (\<I> :: (0, 0, 'd) operator)) \<approx> map_operator Inl Inl op\<close>
  apply transfer
  apply (simp split: if_splits)
  apply (intro allI impI conjI)
    apply (rule bisim_wbisim)
    apply (rule B2_1)
   apply (auto simp add: inj_eq split: if_splits sum.splits intro!: inj_onI  bisim_wbisim)
  done

lemma B2_2:
  \<open>(\<I> :: (0, 0, 'd) operator) \<parallel> op \<approx> map_operator Inr Inr op\<close>
  apply transfer
  apply (simp split: if_splits)
  apply (intro allI impI conjI)
    apply (rule bisim_wbisim)
    apply (rule B2_2)
   apply (auto simp add: inj_eq split: if_splits sum.splits intro!: inj_onI  bisim_wbisim)
  done

lemma B3:
  "op1 \<bullet> op2 \<bullet> op3 \<approx> op1 \<bullet> (op2 \<bullet> op3)"
  apply transfer
  apply (rule bisim_wbisim)
  apply (rule B3.B3)
  done

lemma B4_1:
  "op \<bullet> \<I> \<approx> op"
  apply transfer
  using B4_1 apply (smt (verit, ccfv_threshold) B3.B3 bisim_wbisim wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans)
  done

lemma B4_2:
  "\<I> \<bullet> op \<approx> op"
  apply transfer
  using B4_2 apply (smt (verit, ccfv_threshold) B3.B3 bisim_wbisim wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans)
  done

lemma B5:
  \<open>(op1 \<parallel> op2) \<bullet> (op3 \<parallel> op4) \<approx> (op1 \<bullet> op3) \<parallel> (op2 \<bullet> op4)\<close>
  apply transfer
  apply (rule bisim_wbisim)
  apply (rule B5)
  done

lemma B6:
  \<open>\<I> \<parallel> \<I> \<approx> \<I>\<close>
  apply transfer
  apply (rule bisim_wbisim)
  apply (rule B6)
  done

lemma B7:
  \<open>\<X> \<bullet> \<X> \<approx> \<I>\<close>
  apply transfer
  apply (rule B7)
  done

lemma B8:
  \<open>(\<X> :: ('a :: {countable,defaults} + 0, 0 + 'a, 'd) operator) \<approx> map_operator id (case_sum Inr Inl) \<I>\<close>
  apply transfer
  apply (simp add: inj_eq split: if_splits)
  apply (intro impI conjI)
   apply (auto simp add: inj_eq split: if_splits sum.splits intro!: inj_onI B8 bisim_wbisim)[1]
  apply (auto split: sum.splits)
  subgoal for x
    by (cases x; simp)
  subgoal for x
    by (cases x; simp)
  done

lemma B9:
  "\<X> \<approx> map_operator reassoc reassoc (\<X> \<parallel> \<I>) \<bullet> map_operator id assoc (\<I> \<parallel> \<X>)"
  apply transfer
  apply (simp add: inj_eq split: if_splits)
  apply (rule B9)
      apply simp_all
  done

lemma B10:
  \<open>(op1 \<parallel> op2) \<bullet> \<X> \<approx> \<X> \<bullet> (op2 \<parallel> op1)\<close>
  apply transfer
  apply safe
  subgoal for op1 op2 op1' op2'
    apply (subgoal_tac "wbisim (scomp_op (pcomp_op op1 op2) transp_empty_op) (scomp_op (pcomp_op (\<stileturn>(\<stileturn>(op1'\<turnstile>))) (\<stileturn>(\<stileturn>(op2'\<turnstile>)))) transp_empty_op)")
     defer
    subgoal
      apply (rule wbisim_trans)
       apply (rule wbisim_scomp_op_cong)
        apply (rule wbisim_pcomp_op_cong)
         apply assumption+
       apply (rule wbisim_refl)+
      apply (rule wbisim_scomp_op_cong)
       apply (rule wbisim_pcomp_op_cong)
      using B4.B4_2 wbisim_sym apply blast
      using B4.B4_2 wbisim_sym apply blast
      apply (rule wbisim_refl)
      done
    apply (subgoal_tac "wbisim (scomp_op transp_empty_op (pcomp_op op2 op1)) (scomp_op transp_empty_op (pcomp_op (\<stileturn>(op2'\<turnstile>)) (\<stileturn>(op1'\<turnstile>))))")
     defer
    subgoal
      apply (rule wbisim_trans)
       apply (rule wbisim_scomp_op_cong)
        apply (rule wbisim_refl)
       apply (rule wbisim_pcomp_op_cong)
        apply assumption+
      apply (rule wbisim_refl)
      done
    apply (rule wbisim_trans)
     apply assumption
    apply (rule wbisim_trans[rotated])
     apply (rule wbisim_sym)
     apply assumption
    apply (rule wbisim_trans)
     apply (rule B10)
    apply (rule wbisim_scomp_op_cong)
     apply (rule wbisim_refl)
    apply (rule wbisim_pcomp_op_cong)
    using B4.B4_2 apply (smt (verit, ccfv_SIG) B3.B3 B4.B4_1 bisim_wbisim wbisim_scomp_op_cong wbisim_sym wbisim_trans)+
    done
  done

lemma R1:
  "op2 \<bullet> (op1\<up>) \<approx> ((op2 \<parallel> \<I>) \<bullet> op1)\<up>"
  apply transfer
  apply (rule R1)
  apply blast+
  done

lemma R2:
  fixes op1 :: "('b :: {countable,defaults} + 'm :: {defaults, countable}, 'c :: {countable,defaults} + 'm, 'd) operator"
    and op2 :: "('c, 'a :: {countable,defaults}, 'd) operator"
  shows  "(op1\<up>) \<bullet> op2 \<approx> (op1 \<bullet> (op2 \<parallel> \<I>))\<up>"
  apply transfer
  apply (rule R2)
   apply blast+
  done

lemma R3:
  fixes op1 :: "('b :: {countable,defaults} + 'a :: {countable,defaults}, 'c :: {countable,defaults} + 'd :: {countable,defaults}, 'e) operator"
    and op2 :: "('f  :: {countable,defaults} + 'm :: {countable,defaults}, 'g :: {countable,defaults} + 'm, 'e) operator"
  shows  "op1 \<parallel> (op2\<up>) \<approx> (map_operator assoc assoc (op1 \<parallel> op2))\<up>"
  apply transfer
  apply (simp add: inj_eq split: if_splits)
  apply (rule bisim_wbisim)
   apply (rule R3)
    apply blast
    apply blast
  done

lemma R4:
  fixes op1 :: "('k :: {countable,defaults} + 'm :: {countable,defaults}, 'l :: {countable,defaults} + 'n :: {countable,defaults}, 'd) operator"
    and op2 :: "('n, 'm, 'd) operator"
  shows  "(op1 \<bullet> (\<I> \<parallel> op2))\<up> \<approx> ((\<I> \<parallel> op2) \<bullet> op1)\<up>"
  apply transfer
  apply safe
  subgoal for op1 op2 op1' op2'
    apply (subgoal_tac " wbisim (feedback_op (scomp_op op1 (pcomp_op id_empty_op op2))) (feedback_op (scomp_op (\<stileturn>\<stileturn>(op1'\<turnstile>)) (pcomp_op id_empty_op (\<stileturn>(op2' \<turnstile>)))))")
     defer
    subgoal
      apply (rule wbisim_loop_op_cong)
      apply (rule wbisim_scomp_op_cong)
      using B4.B4_2 wbisim_sym wbisim_trans apply blast
      apply (rule wbisim_pcomp_op_cong)
       apply (rule wbisim_refl)
      apply assumption
      done
    apply (rule wbisim_trans)
     apply assumption
    apply (rule wbisim_trans)
     apply (rule R4)
        apply (metis wbisim_inputs wbisim_vdash_inputs_no_defaults)
       apply (metis wbisim_outputs wbisim_vdash_outputs_no_defaults)
      apply (auto simp add: scomp_op_def image_iff disjoint_iff op.set_map ran_def dest!: wbisim_inputs)[2]
    apply (rule wbisim_loop_op_cong)
    apply (rule wbisim_scomp_op_cong)
     apply (rule wbisim_pcomp_op_cong)
      apply (rule wbisim_refl)
    using wbisim_sym apply blast
    apply (subgoal_tac "wbisim ((\<stileturn>op1') \<turnstile> \<turnstile>) ((\<stileturn>op1') \<turnstile>)")
     apply (smt (verit, del_insts) B3.B3 bisim_wbisim scomp_op_id_id wbisim_scomp_op_cong wbisim_sym wbisim_trans)
    using B4.B4_1 apply blast
    done
  done

lemma R5:
  fixes op :: "('a :: {countable, defaults} + 0, 'b :: {countable, defaults} + 0, 'c) operator"
  shows "map_operator Inl Inl (op\<up>) \<approx> op"
  apply transfer
  apply (simp add: inj_eq split: if_splits)
  apply (intro impI conjI)
    apply (rule R5)
  apply force+
  done

lemma R6:
  fixes op :: "(('a :: {countable, defaults} + 'l) + 'k, ('b :: {countable, defaults} + 'l :: {countable, defaults}) + 'k :: {countable, defaults}, 'c) operator"
  shows  "(op\<up>)\<up> \<approx> (map_operator reassoc reassoc op)\<up>"
  apply transfer
  apply (simp add: inj_eq split: if_splits)
  apply (rule bisim_wbisim)
  apply (rule R6)
     apply blast
    apply blast
   apply (auto simp add: scomp_op_def image_iff disjoint_iff op.set_map ran_def dest!: wbisim_inputs)[1]
   apply (auto simp add: scomp_op_def image_iff disjoint_iff op.set_map ran_def dest!: wbisim_outputs)[1]
  done

end