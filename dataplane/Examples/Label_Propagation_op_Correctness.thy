theory Label_Propagation_op_Correctness

imports
  Label_Propagation_op
  Ooo_Input_op
  Increment_op
begin

(* TODO move *)
lemma num2_cases:
  fixes n :: 2 obtains (0) \<open>n = 0\<close> | (1) \<open>n = 1\<close>
proof (cases n)
  case (of_int z)
  then consider \<open>z = 0\<close> | \<open>z = 1\<close> by fastforce
  thus ?thesis using of_int(1) 0 1 by fastforce
qed

lemma ooo_input_op_label_propagation_op_increment_op_source_op:
  defines \<open>invariant inc os1 buf1 os2 buf2 os3 buf3 \<equiv> initia os1 \<and> timely_input_stream (es os1 0) (mset (ocaps os1 0))
  \<and> (\<forall>x \<in> set (buf1 (Inr (1, 0))) \<union> set (buf2 (Inr (2, 0))) \<union> set (buf3 (Inr (1, 1))). is_Inr x)
  \<and> initia os2 \<and> summar os2 = default_internal_summary \<and> initia os3 \<and> summar os3 0 0 = [inc] \<and> ocaps os3 0 = map (\<lambda>(_, t). t + inc) (input os2 0) \<and> inc > 0\<close>
    and \<open>my_ooo_input_op os \<equiv> map_op
  (case_option (Inl (0 :: 3)) (\<lambda>(p :: 2). Inr (0 :: 3, p))) (case_option (Inl (0 :: 3)) (\<lambda>(p :: 2). Inr (0 :: 3, p)))
  (ooo_input_op {|0 :: 2|} os)\<close>
    and \<open>my_label_propagation_op os' \<equiv> map_op
  (case_option (Inl (1 :: 3)) (\<lambda>(p :: 2). Inr (1 :: 3, p))) (case_option (Inl (1 :: 3)) (\<lambda>(p :: 2). Inr (1 :: 3, p)))
  (label_propagation_op os')\<close>
    and \<open>my_increment_op inc os'' \<equiv> map_op
  (case_option (Inl (2 :: 3)) (\<lambda>(p :: 2). Inr (2 :: 3, p))) (case_option (Inl (2 :: 3)) (\<lambda>(p :: 2). Inr (2 :: 3, p)))
  (increment_op (0 :: 2) (0 :: 2) inc os'')\<close>
    and \<open>my_source_op inc os1 buf1 os2 buf2 os3 buf3 \<equiv> map_op (\<lambda>(p :: 2). (1 :: 3, p)) (\<lambda>(p :: 2). (1 :: 3, p))
    (source_op ((\<lambda>(p :: 2). undefined)))\<close>
  assumes \<open>invariant inc os1 buf1 os2 buf2 os3 buf3\<close>
  shows \<open>dataflow_op sg (map_op (case_sum id id) (case_sum id id)
  (comp_op [Inr (0, 0) \<mapsto> Inr (1, 0)] buf1
    (my_ooo_input_op os1)
    (loop_op [Inr (2, 0) \<mapsto> Inr (1, 1)] buf3 (map_op (case_sum id id) (case_sum id id)
      (comp_op [Inr (1, 1) \<mapsto> Inr (2, 0)] buf2
        (my_label_propagation_op os2)
        (my_increment_op inc os3))))))
  \<approx> my_source_op inc os1 buf1 os2 buf2 os3 buf3\<close>
  using assms(6)
proof (coinduction arbitrary: sg os1 buf1 os2 buf2 os3 rule: wbisim_coinduct_upto'')
  oops

end