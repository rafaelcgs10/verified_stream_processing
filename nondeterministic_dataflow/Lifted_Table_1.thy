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

(* map projs: B2 A3 A7 R5 B8 *)


lemma B2_1:
  \<open>(op \<parallel> (\<I> :: (0, 0, 'd) operator)) \<approx> map_operator Inl Inl op\<close>
  apply transfer
  apply (simp split: if_splits)
  apply (intro allI impI conjI)
      apply (rule bisim_wbisim)
      apply (rule B2_1)
     apply (auto simp add: inj_eq split: if_splits sum.splits intro!: inj_onI  bisim_wbisim)
  done

lemma B3:
  "op1 \<bullet> op2 \<bullet> op3 \<approx> op1 \<bullet> (op2 \<bullet> op3)"
  apply transfer
  apply (rule bisim_wbisim)
  apply (rule B3.B3)
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

lemma R1:
  "(op2 \<bullet> (op1\<up>)) \<approx> ((op2 \<parallel> \<I>) \<bullet> op1)\<up>"
  apply transfer
  apply (rule R1)
   apply blast+
  done

lemma R5:
  fixes op :: "('a :: {countable, defaults} + 0, 'b :: {countable, defaults} + 0, 'c) operator"
  shows "map_operator Inl Inl (op\<up>) \<approx> op"
  apply transfer
  apply (simp add: inj_eq split: if_splits)
  apply (intro impI conjI)
   apply (rule R5)
  using default_0 apply blast
  using default_0 apply blast
   apply (auto split: sum.splits)
  done

end