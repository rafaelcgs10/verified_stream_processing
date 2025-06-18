theory T3A1

imports
  "../BNA_Operators"
  "../Wstep_Composition_Left_Right"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Proof against weak bisimulation\<close>

(* TODO move *)
simproc_setup num1_eq (\<open>x :: 1\<close>) =
  \<open>K (K (fn ct =>
    if Thm.term_of ct aconv @{term \<open>1 :: 1\<close>} then NONE
    else SOME (mk_meta_eq @{thm num1_eq1})))\<close>

lemma wstep_Inp_Inl_Inl:
  assumes \<open>wstep (Inp (Inl (Inl 1)) (Suc 0)) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (\<V> :: (1 + 1, 1, nat) op)) \<V>))) op\<close>
  obtains \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 1 (\<lambda>_. []))) \<V>) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
  apply atomize_elim
  using assms
  unfolding wstep_def
  apply simp
  apply (erule relcomppE)+
  apply (erule converse_rtranclpE)+
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L)[2]
   apply (erule converse_rtranclpE)
    apply fast
   apply (erule converse_rtranclpE)
  by (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp add: BENQ_diff_access)

lemma wstep_Inp_Inl_Inr1:
  assumes \<open>wstep (Inp (Inl (Inr 1)) 2) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 (Suc 0) (\<lambda>_. []))) (\<V> :: (1 + 1, 1, nat) op)) \<V>))) op\<close>
  obtains \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 1 (\<lambda>_. []))) (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 1 (\<lambda>_. []))) \<V>) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 1 (\<lambda>_. []))) \<V>) (merge_op (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))))))\<close>
    apply atomize_elim
  using assms
  unfolding wstep_def
  apply simp
  apply (erule relcomppE)+
  apply (erule converse_rtranclpE)+
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[3]
       apply (erule converse_rtranclpE)
        apply fast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (erule converse_rtranclpE)
        apply (metis case_sum_BENQ_L case_sum_BENQ_R surjective_sum)
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[6]
     apply (erule converse_rtranclpE)
      apply (smt (verit, ccfv_threshold) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L surjective_sum)
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
       apply (smt (verit, ccfv_threshold) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L surjective_sum)
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
     apply (erule converse_rtranclpE)
      apply (smt (verit) BENQ_diff_access BHD_BENQ_empty BTL_BENQ_empty Inr_Inl_False case_sum_BENQ_L case_sum_BENQ_R surjective_sum)
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
     apply (erule converse_rtranclpE)
      apply (smt (verit, best) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_L case_sum_BENQ_R sum.simps(6) surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inr_Inl_False)
     apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inr_Inl_False)
    apply (erule converse_rtranclpE)
     apply fast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (erule converse_rtranclpE)
     apply fast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (erule converse_rtranclpE)
     apply (metis case_sum_BENQ_L case_sum_BENQ_R surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
   apply (erule converse_rtranclpE)
    apply fast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (erule converse_rtranclpE)
     apply fast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
     apply (erule converse_rtranclpE)
      apply (smt (verit, best) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L surjective_sum)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
     apply (erule converse_rtranclpE)
      apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inr_Inl_False)
     apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inr_Inl_False)
    apply (erule converse_rtranclpE)
     apply fast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (erule converse_rtranclpE)
     apply (metis case_sum_BENQ_L case_sum_BENQ_R surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
   apply (erule converse_rtranclpE)
    apply fast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
   apply (erule converse_rtranclpE)
    apply fast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
   apply (erule converse_rtranclpE)
    apply fast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
  apply (erule converse_rtranclpE)+
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[2]
   apply (erule converse_rtranclpE)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[2]
  apply (erule converse_rtranclpE)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (erule converse_rtranclpE)
     apply fast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
     apply (erule converse_rtranclpE)
      apply (smt (verit, ccfv_threshold) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
     apply (erule converse_rtranclpE)
      apply (smt (z3) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L case_sum_BENQ_R case_sum_BTL_L surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inr_Inl_False)
     apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
    apply (erule converse_rtranclpE)
     apply fast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (erule converse_rtranclpE)
     apply (smt (verit, ccfv_SIG) case_sum_BENQ_L case_sum_BENQ_R surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
   apply (erule converse_rtranclpE)
    apply fast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
   apply (erule converse_rtranclpE)
    apply fast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
   apply (erule converse_rtranclpE)
    apply fast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[2]
  apply (erule converse_rtranclpE)+
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[2]
  apply (erule converse_rtranclpE)+
    apply hypsubst_thin
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; hypsubst_thin?; simp)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
   apply hypsubst_thin
   apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; hypsubst_thin?; simp)
   apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; hypsubst_thin?; simp)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; hypsubst_thin?; simp)
     apply (meson BENQ_diff_access sum.distinct(2))
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; hypsubst_thin?; simp)
   apply (meson BENQ_diff_access Inl_Inr_False)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; simp)
  done

lemma wstep_Inp_Inl_Inr2:
  assumes \<open>wstep (Inp (Inl (Inr 1)) 2) (map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 (Suc 0) (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (\<V> :: (1 + 1, 1, nat) op)) \<V>))) op\<close>
  obtains \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) \<V>))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))))))\<close>
  apply atomize_elim
  using assms
  unfolding wstep_def
  apply simp
  apply (erule relcomppE)+
  apply (erule converse_rtranclpE)+
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[3]
       apply (erule converse_rtranclpE)
        apply fast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
        apply (erule converse_rtranclpE)
         apply (smt (verit, best) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L surjective_sum)
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[7]
     apply (erule converse_rtranclpE)
      apply (smt (verit, ccfv_threshold) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (smt (verit, ccfv_threshold) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L surjective_sum)
     apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inr_Inl_False)
    apply (erule converse_rtranclpE)
     apply fast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (erule converse_rtranclpE)
     apply (metis case_sum_BENQ_L case_sum_BENQ_R surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
   apply (erule converse_rtranclpE)
    apply fast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
   apply (erule converse_rtranclpE)
    apply fast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
   apply (erule converse_rtranclpE)
    apply fast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
  apply (erule converse_rtranclpE)+
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[2]
  apply (erule converse_rtranclpE)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[2]
  apply (erule converse_rtranclpE)
   apply fast
  apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
  apply (erule converse_rtranclpE)
   apply fast
  by (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)

lemma wstep_Inp_Inl_Inr3:
  assumes \<open>wstep (Inp (Inl (Inr 1)) 2) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (\<V> :: (1 + 1, 1, nat) op)) (merge_op (case_sum (BENQ 1 (Suc 0) (\<lambda>_. [])) (\<lambda>_. [])))))) op\<close>
  obtains \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))))))\<close>
  apply atomize_elim
  using assms
  unfolding wstep_def
  apply simp
  apply (erule relcomppE)+
  apply (erule converse_rtranclpE)+
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[3]
   apply (erule converse_rtranclpE)
    apply fast
   apply (erule converse_rtranclpE)
  by (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim simp add: BENQ_diff_access)

lemma A1_not_wbisim:
  \<open>(\<V> \<parallel> (\<I> :: (1, 1, nat) op)) \<bullet> \<V> \<approx> map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>) \<Longrightarrow> False\<close>
  unfolding scomp_op_def pcomp_op_def
  apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inl (Inl 1)) 1\<close>])
   apply (rule wstep_converse_trans(2))
    apply (rule step_map_op)
     apply (rule step_comp_op_L_Inp)
       apply (rule step_comp_op_L_Inp)
         apply (rule step_merge_op_Read_L[of 1])
          apply (simp_all add: defaults_num1_def flip: case_sum_BENQ_L)
   apply (rule rtranclp.intros(2))
    apply (rule rtranclp.intros(2))
     apply (rule rtranclp.intros(1))
    apply (rule step_map_op)
     apply (rule step_Tau_comp_op_L)
        apply (rule step_comp_op_L_Out)
           apply (rule step_merge_op_Write_L[of 1])
              apply (simp_all add: defaults_num1_def)
   apply (rule step_map_op)
    apply (rule step_Tau_comp_op_R)
         apply (rule step_merge_op_Read_L[of 1])
          apply (simp_all add: defaults_num1_def)
  apply (erule wstep_Inp_Inl_Inl; clarsimp)
    apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inl (Inr 1)) 2\<close>])
     apply (rule wstep_converse_trans(2))
      apply (rule step_map_op)
       apply (rule step_comp_op_L_Inp)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_merge_op_Read_R[of 1])
            apply (simp_all add: defaults_num1_def)
     apply (rule rtranclp.intros(2))
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(1))
      apply (rule step_map_op)
       apply (rule step_Tau_comp_op_L)
          apply (rule step_comp_op_L_Out)
             apply (rule step_merge_op_Write_R[of 1])
                apply (simp_all add: defaults_num1_def)
     apply (rule step_map_op)
      apply (rule step_Tau_comp_op_R)
           apply (rule step_merge_op_Read_L[of 1])
            apply (simp_all add: defaults_num1_def)
    apply (erule wstep_Inp_Inl_Inr1; clarsimp; drule wbisim_sym)
            apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
             apply (rule wstep_trans(1))
              apply (rule rtranclp.intros(2))
               apply (rule rtranclp.intros(2))
                apply (rule rtranclp.intros(1))
               apply (rule step_map_op)
                apply (rule step_map_op)
                 apply (rule step_Tau_comp_op_L)
                    apply (rule step_comp_op_R_Out)
                      apply (rule step_merge_op_Write_L[of 1])
                      apply (simp_all add: defaults_num1_def)
              apply (rule step_map_op)
               apply (rule step_map_op)
                apply (rule step_Tau_comp_op_R)
                     apply (rule step_merge_op_Read_R[of 1])
                      apply (simp_all add: defaults_num1_def)
             apply (rule step_map_op)
              apply (rule step_map_op)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_merge_op_Write_R[of 1])
                    apply (simp_all add: defaults_num1_def)
             apply simp
            apply (unfold wstep_def)
            apply (erule relcomppE)+
            apply (erule converse_rtranclpE)
             apply (hypsubst_thin; simp)
             apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
             apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
            apply (simp add: BENQ_diff_access)
           apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
            apply (rule wstep_trans(1))
             apply (rule rtranclp.intros(2))
              apply (rule rtranclp.intros(1))
             apply (rule step_map_op)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_R)
                    apply (rule step_merge_op_Read_R[of 1])
                     apply (simp_all add: defaults_num1_def)
            apply (rule step_map_op)
             apply (rule step_map_op)
              apply (rule step_comp_op_R_Out)
                apply (rule step_merge_op_Write_R[of 1])
                   apply (simp_all add: defaults_num1_def)
            apply simp
           apply (unfold wstep_def)
           apply (erule relcomppE)+
           apply (erule converse_rtranclpE)
            apply (hypsubst_thin; simp)
            apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
            apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
           apply (simp add: BENQ_diff_access)
          apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
           apply (rule step_wstep)
           apply (rule step_map_op)
            apply (rule step_map_op)
             apply (rule step_comp_op_R_Out)
               apply (rule step_merge_op_Write_R[of 1])
                  apply (simp_all add: defaults_num1_def)
           apply simp
          apply (unfold wstep_def)
          apply (erule relcomppE)+
          apply (erule converse_rtranclpE)
           apply (hypsubst_thin; simp)
           apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
           apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
          apply (simp add: BENQ_diff_access)
         apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
          apply (rule wstep_trans(1))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(2))
             apply (rule rtranclp.intros(1))
            apply (rule step_map_op)
             apply (rule step_map_op)
              apply (rule step_Tau_comp_op_L)
                 apply (rule step_comp_op_R_Out)
                   apply (rule step_merge_op_Write_L[of 1])
                      apply (simp_all add: defaults_num1_def)
           apply (rule step_map_op)
            apply (rule step_map_op)
             apply (rule step_Tau_comp_op_R)
                  apply (rule step_merge_op_Read_R[of 1])
                   apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_R_Out)
              apply (rule step_merge_op_Write_R[of 1])
                 apply (simp_all add: defaults_num1_def)
          apply simp
         apply (unfold wstep_def)
         apply (erule relcomppE)+
         apply (erule converse_rtranclpE)
          apply (hypsubst_thin; simp)
          apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
          apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
         apply (simp add: BENQ_diff_access)
        apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
         apply (rule wstep_trans(1))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_R)
                 apply (rule step_merge_op_Read_R[of 1])
                  apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_R_Out)
             apply (rule step_merge_op_Write_R[of 1])
                apply (simp_all add: defaults_num1_def)
         apply simp
        apply (unfold wstep_def)
        apply (erule relcomppE)+
        apply (erule converse_rtranclpE)
         apply (hypsubst_thin; simp)
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
         apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
        apply (simp add: BENQ_diff_access)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Out)
            apply (rule step_merge_op_Write_R[of 1])
               apply (simp_all add: defaults_num1_def)
        apply simp
       apply (unfold wstep_def)
       apply (erule relcomppE)+
       apply (erule converse_rtranclpE)
        apply (hypsubst_thin; simp)
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
        apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
       apply (simp add: BENQ_diff_access)
      apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
       apply (rule wstep_trans(1))
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
         apply (rule step_map_op)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_L)
              apply (rule step_comp_op_R_Out)
                apply (rule step_merge_op_Write_L[of 1])
                   apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_map_op)
          apply (rule step_Tau_comp_op_R)
               apply (rule step_merge_op_Read_R[of 1])
                apply (simp_all add: defaults_num1_def)
       apply (rule step_map_op)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_merge_op_Write_R[of 1])
              apply (simp_all add: defaults_num1_def)
       apply simp
      apply (unfold wstep_def)
      apply (erule relcomppE)+
      apply (erule converse_rtranclpE)
       apply (hypsubst_thin; simp)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
       apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
      apply (simp add: BENQ_diff_access)
     apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
      apply (rule wstep_trans(1))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply (rule step_merge_op_Read_R[of 1])
               apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_map_op)
        apply (rule step_comp_op_R_Out)
          apply (rule step_merge_op_Write_R[of 1])
             apply (simp_all add: defaults_num1_def)
      apply simp
     apply (unfold wstep_def)
     apply (erule relcomppE)+
     apply (erule converse_rtranclpE)
      apply (hypsubst_thin; simp)
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
      apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
     apply (simp add: BENQ_diff_access)
    apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
     apply (rule step_wstep)
     apply (rule step_map_op)
      apply (rule step_map_op)
       apply (rule step_comp_op_R_Out)
         apply (rule step_merge_op_Write_R[of 1])
            apply (simp_all add: defaults_num1_def)
     apply simp
    apply (unfold wstep_def)
    apply (erule relcomppE)+
    apply (erule converse_rtranclpE)
     apply (hypsubst_thin; simp)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
     apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
    apply (simp add: BENQ_diff_access)
   apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inl (Inr 1)) 2\<close>])
    apply (rule wstep_converse_trans(2))
     apply (rule step_map_op)
      apply (rule step_comp_op_L_Inp)
        apply (rule step_comp_op_L_Inp)
          apply (rule step_merge_op_Read_R[of 1])
           apply (simp_all add: defaults_num1_def)
    apply (rule rtranclp.intros(2))
     apply (rule rtranclp.intros(2))
      apply (rule rtranclp.intros(1))
     apply (rule step_map_op)
      apply (rule step_Tau_comp_op_L)
         apply (rule step_comp_op_L_Out)
            apply (rule step_merge_op_Write_R[of 1])
               apply (simp_all add: defaults_num1_def)
    apply (rule step_map_op)
     apply (rule step_Tau_comp_op_R)
          apply (rule step_merge_op_Read_L[of 1])
           apply (simp_all add: defaults_num1_def)
   apply (erule wstep_Inp_Inl_Inr2; clarsimp; drule wbisim_sym)
        apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
         apply (rule wstep_trans(1))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_map_op)
             apply (rule step_Tau_comp_op_L)
                apply (rule step_comp_op_R_Out)
                  apply (rule step_merge_op_Write_L[of 1])
                     apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_R)
                 apply (rule step_merge_op_Read_R[of 1])
                  apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_R_Out)
             apply (rule step_merge_op_Write_R[of 1])
                apply (simp_all add: defaults_num1_def)
         apply simp
        apply (unfold wstep_def)
        apply (erule relcomppE)+
        apply (erule converse_rtranclpE)
         apply (hypsubst_thin; simp)
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
         apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
        apply (simp add: BENQ_diff_access)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
        apply (rule wstep_trans(1))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
         apply (rule step_map_op)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_merge_op_Read_R[of 1])
                 apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Out)
            apply (rule step_merge_op_Write_R[of 1])
               apply (simp_all add: defaults_num1_def)
        apply simp
       apply (unfold wstep_def)
       apply (erule relcomppE)+
       apply (erule converse_rtranclpE)
        apply (hypsubst_thin; simp)
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
        apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
       apply (simp add: BENQ_diff_access)
      apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
       apply (rule step_wstep)
       apply (rule step_map_op)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_merge_op_Write_R[of 1])
              apply (simp_all add: defaults_num1_def)
       apply simp
      apply (unfold wstep_def)
      apply (erule relcomppE)+
      apply (erule converse_rtranclpE)
       apply (hypsubst_thin; simp)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
       apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
      apply (simp add: BENQ_diff_access)
     apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
      apply (rule wstep_trans(1))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_map_op)
          apply (rule step_Tau_comp_op_L)
             apply (rule step_comp_op_R_Out)
               apply (rule step_merge_op_Write_L[of 1])
                  apply (simp_all add: defaults_num1_def)
       apply (rule step_map_op)
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply (rule step_merge_op_Read_R[of 1])
               apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_map_op)
        apply (rule step_comp_op_R_Out)
          apply (rule step_merge_op_Write_R[of 1])
             apply (simp_all add: defaults_num1_def)
      apply simp
     apply (unfold wstep_def)
     apply (erule relcomppE)+
     apply (erule converse_rtranclpE)
      apply (hypsubst_thin; simp)
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
      apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
     apply (simp add: BENQ_diff_access)
    apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
     apply (rule wstep_trans(1))
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(1))
      apply (rule step_map_op)
       apply (rule step_map_op)
        apply (rule step_Tau_comp_op_R)
             apply (rule step_merge_op_Read_R[of 1])
              apply (simp_all add: defaults_num1_def)
     apply (rule step_map_op)
      apply (rule step_map_op)
       apply (rule step_comp_op_R_Out)
         apply (rule step_merge_op_Write_R[of 1])
            apply (simp_all add: defaults_num1_def)
     apply simp
    apply (unfold wstep_def)
    apply (erule relcomppE)+
    apply (erule converse_rtranclpE)
     apply (hypsubst_thin; simp)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
     apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
    apply (simp add: BENQ_diff_access)
   apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
    apply (rule step_wstep)
    apply (rule step_map_op)
     apply (rule step_map_op)
      apply (rule step_comp_op_R_Out)
        apply (rule step_merge_op_Write_R[of 1])
           apply (simp_all add: defaults_num1_def)
    apply simp
   apply (unfold wstep_def)
   apply (erule relcomppE)+
   apply (erule converse_rtranclpE)
    apply (hypsubst_thin; simp)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
    apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
   apply (simp add: BENQ_diff_access)
  apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inl (Inr 1)) 2\<close>])
   apply (rule wstep_converse_trans(2))
    apply (rule step_map_op)
     apply (rule step_comp_op_L_Inp)
       apply (rule step_comp_op_L_Inp)
         apply (rule step_merge_op_Read_R[of 1])
          apply (simp_all add: defaults_num1_def)
   apply (rule rtranclp.intros(2))
    apply (rule rtranclp.intros(2))
     apply (rule rtranclp.intros(1))
    apply (rule step_map_op)
     apply (rule step_Tau_comp_op_L)
        apply (rule step_comp_op_L_Out)
           apply (rule step_merge_op_Write_R[of 1])
              apply (simp_all add: defaults_num1_def)
   apply (rule step_map_op)
    apply (rule step_Tau_comp_op_R)
         apply (rule step_merge_op_Read_L[of 1])
          apply (simp_all add: defaults_num1_def)
  apply (erule wstep_Inp_Inl_Inr3; clarsimp; drule wbisim_sym)
    apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
     apply (rule wstep_trans(1))
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_L)
            apply (rule step_comp_op_R_Out)
              apply (rule step_merge_op_Write_L[of 1])
                 apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_map_op)
        apply (rule step_Tau_comp_op_R)
             apply (rule step_merge_op_Read_R[of 1])
              apply (simp_all add: defaults_num1_def)
     apply (rule step_map_op)
      apply (rule step_map_op)
       apply (rule step_comp_op_R_Out)
         apply (rule step_merge_op_Write_R[of 1])
            apply (simp_all add: defaults_num1_def)
     apply simp
    apply (unfold wstep_def)
    apply (erule relcomppE)+
    apply (erule converse_rtranclpE)
     apply (hypsubst_thin; simp)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
     apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
  apply (simp add: BENQ_diff_access)
   apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
    apply (rule wstep_trans(1))
     apply (rule rtranclp.intros(2))
      apply (rule rtranclp.intros(1))
     apply (rule step_map_op)
      apply (rule step_map_op)
       apply (rule step_Tau_comp_op_R)
            apply (rule step_merge_op_Read_R[of 1])
             apply (simp_all add: defaults_num1_def)
    apply (rule step_map_op)
     apply (rule step_map_op)
      apply (rule step_comp_op_R_Out)
        apply (rule step_merge_op_Write_R[of 1])
           apply (simp_all add: defaults_num1_def)
    apply simp
   apply (unfold wstep_def)
   apply (erule relcomppE)+
   apply (erule converse_rtranclpE)
    apply (hypsubst_thin; simp)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
    apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
  apply (simp add: BENQ_diff_access)
  apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
   apply (rule step_wstep)
   apply (rule step_map_op)
    apply (rule step_map_op)
     apply (rule step_comp_op_R_Out)
       apply (rule step_merge_op_Write_R[of 1])
          apply (simp_all add: defaults_num1_def)
   apply simp
  apply (unfold wstep_def)
  apply (erule relcomppE)+
  apply (erule converse_rtranclpE)
   apply (hypsubst_thin; simp)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)[2]
   apply (smt (verit, best) BENQ_access BHD_BENQ_empty BHD_def One_nat_def Suc_1 append_self_conv2 hd_append2 list.simps(3) n_not_Suc_n num1_eq1)
  apply (simp add: BENQ_diff_access)
  done

section \<open>Branching bisimulation\<close>

definition \<open>brsim R op\<^sub>1 op\<^sub>2 =
  (\<forall>io op\<^sub>1'. step io op\<^sub>1 op\<^sub>1' \<longrightarrow>
    (\<exists>op\<^sub>2' op\<^sub>2'' op\<^sub>2'''. (step Tau)\<^sup>*\<^sup>* op\<^sub>2 op\<^sub>2' \<and> estep io op\<^sub>2' op\<^sub>2'' \<and> (step Tau)\<^sup>*\<^sup>* op\<^sub>2'' op\<^sub>2''' \<and>
    R op\<^sub>1 op\<^sub>2' \<and> R op\<^sub>1' op\<^sub>2'' \<and> R op\<^sub>1' op\<^sub>2'''))\<close>

lemma brsim_mono[mono]: \<open>R \<le> S \<Longrightarrow> brsim R \<le> brsim S\<close>
  by (force simp: brsim_def le_fun_def)

coinductive brbisim (infix \<open>\<approx>\<^sub>b\<close> 40) where
  \<open>brsim (\<approx>\<^sub>b) op\<^sub>1 op\<^sub>2 \<Longrightarrow> brsim (\<approx>\<^sub>b) op\<^sub>2 op\<^sub>1 \<Longrightarrow> op\<^sub>1 \<approx>\<^sub>b op\<^sub>2\<close>

lemma brsim_wsim:
  \<open>brsim R op\<^sub>1 op\<^sub>2 \<Longrightarrow> wsim R op\<^sub>1 op\<^sub>2\<close>
  unfolding brsim_def wsim_def wstep_def
  by (meson relcomppI)

lemma brbisim_wbisim:
  \<open>op\<^sub>1 \<approx>\<^sub>b op\<^sub>2 \<Longrightarrow> op\<^sub>1 \<approx> op\<^sub>2\<close>
  by (smt (verit, ccfv_threshold) brbisim.cases brsim_def brsim_wsim wbisim.coinduct)

lemma A1_not_brbisim:
  \<open>(\<V> \<parallel> (\<I> :: (1, 1, nat) op)) \<bullet> \<V> \<approx>\<^sub>b map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>) \<Longrightarrow> False\<close>
  using A1_not_wbisim brbisim_wbisim by blast

section \<open>Proof of trace equivalence\<close>

(* TODO move *)
lemma wstep_trans':
  \<open>(step Tau)\<^sup>*\<^sup>* op1 op1' \<Longrightarrow> wstep (Out p x) op1' op1'' \<Longrightarrow> wstep (Out p x) op1 op1''\<close>
  \<open>(step Tau)\<^sup>*\<^sup>* op2 op2' \<Longrightarrow> wstep (Inp p' x') op2' op2'' \<Longrightarrow> wstep (Inp p' x') op2 op2''\<close>
  unfolding wstep_def
  using rtranclp_trans by fastforce+

(* TODO move *)
lemma wstep_converse_trans':
  \<open>wstep (Out p x) op1 op1' \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* op1' op1'' \<Longrightarrow>  wstep (Out p x) op1 op1''\<close>
  \<open>wstep (Inp p' x') op2 op2' \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* op2' op2'' \<Longrightarrow> wstep (Inp p' x') op2 op2''\<close>
  unfolding wstep_def
  using rtranclp_trans by fastforce+

lemma wstep_Inp_Inl_Inl_Tau1:
  \<open>wstep (Inp (Inl (Inl p)) x)
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))
     op \<Longrightarrow>
  wstep Tau
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BENQ p x buf1) buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))
     op\<close>
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (rule wstep_map_op[of Tau])
  subgoal for io op
    apply (subst (asm) wstep_comp_op_L_R)
    apply (subst wstep_comp_op_L_R)
    apply (elim exE conjE)
    apply (cases io; simp)
    subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2' p'
      apply (cases p'; simp)
      apply hypsubst_thin
      apply (rule exI[of _ buf'])
      apply (rule exI[of _ buf\<^sub>1])
      apply (rule exI[of _ buf\<^sub>2])
      apply (rule exI[of _ op\<^sub>1'])
      apply (rule exI[of _ op\<^sub>2'])
      apply simp
      apply rotate_tac
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (induct \<open>Inp (Inl (Inl (Inl p))) x :: ((('a + 'a) + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO\<close> _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3)\<close> _ arbitrary: buf1 buf2 buf3 pred: wstep_comp_op_L)
          apply simp_all
      subgoal
        by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
      subgoal for _ _ _ _ _ _ _ buf1 buf2 buf3
        apply (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp; hypsubst_thin)
        subgoal for p'
          apply (drule meta_spec[of _ buf1])
          apply (drule meta_spec[of _ buf2])
          apply (drule meta_spec[of _ \<open>BTL p' buf3\<close>])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_R_Out)
               apply (rule step_id_op_Write)
          by simp_all
        subgoal for p'
          apply (drule meta_spec[of _ \<open>BTL p' buf1\<close>])
          apply (drule meta_spec[of _ buf2])
          apply (drule meta_spec[of _ buf3])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_L_Out)
               apply (rule step_merge_op_Write_L)
                   apply simp_all
            apply (smt (verit, best) BENQ_def BTL_def fun_upd_def fun_upd_twist fun_upd_upd tl_append2)
           apply (metis BENQ_access BENQ_diff_access Nil_is_append_conv)
          by (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
        subgoal for p'
          apply (drule meta_spec[of _ buf1])
          apply (drule meta_spec[of _ \<open>BTL p' buf2\<close>])
          apply (drule meta_spec[of _ buf3])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_L_Out)
               apply (rule step_merge_op_Write_R)
          by simp_all
        done
      subgoal
        by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
      done
    done
  subgoal
    by simp
  done

lemma wtraced_Inp_Inl_Inl1:
  \<open>wtraced
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))
    (LCons (VInp (Inl (Inl p)) x) lxs) \<Longrightarrow>
  wtraced
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BENQ p x buf1) buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))
    lxs\<close>
  apply (cases lxs; simp)
   apply (rule wtraced.Nil)
  subgoal for vio lxs
    apply (erule wtraced.cases; simp; hypsubst_thin)
    apply (erule wtraced.cases; simp; hypsubst_thin)
    subgoal for _ _ op op'
      apply (rule wtraced.Step[where ?op'=op'])
       apply (drule wstep_Inp_Inl_Inl_Tau1)
       apply (smt (verit, best) IO.exhaust io_of_vio_not_Tau(1) wstep_steps_Tau wstep_trans'(1,2))
      apply assumption
      done
    done
  done

lemma wstep_Inp_Inl_Inr_Tau1:
  \<open>wstep (Inp (Inl (Inr p)) x)
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))
     op \<Longrightarrow>
  wstep Tau
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 (BENQ p x buf2))) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))
     op\<close>
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (rule wstep_map_op[of Tau])
  subgoal for io op
    apply (subst (asm) wstep_comp_op_L_R)
    apply (subst wstep_comp_op_L_R)
    apply (elim exE conjE)
    apply (cases io; simp)
    subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2' p'
      apply (cases p'; simp)
      apply hypsubst_thin
      apply (rule exI[of _ buf'])
      apply (rule exI[of _ buf\<^sub>1])
      apply (rule exI[of _ buf\<^sub>2])
      apply (rule exI[of _ op\<^sub>1'])
      apply (rule exI[of _ op\<^sub>2'])
      apply simp
      apply rotate_tac
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (induct \<open>Inp (Inl (Inl (Inr p))) x :: ((('a + 'a) + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO\<close> _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3)\<close> _ arbitrary: buf1 buf2 buf3 pred: wstep_comp_op_L)
          apply simp_all
      subgoal
        by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
      subgoal for _ _ _ _ _ _ _ buf1 buf2 buf3
        apply (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp; hypsubst_thin)
        subgoal for p'
          apply (drule meta_spec[of _ buf1])
          apply (drule meta_spec[of _ buf2])
          apply (drule meta_spec[of _ \<open>BTL p' buf3\<close>])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_R_Out)
               apply (rule step_id_op_Write)
          by simp_all
        subgoal for p'
          apply (drule meta_spec[of _ \<open>BTL p' buf1\<close>])
          apply (drule meta_spec[of _ buf2])
          apply (drule meta_spec[of _ buf3])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_L_Out)
               apply (rule step_merge_op_Write_L)
          by simp_all
        subgoal for p'
          apply (drule meta_spec[of _ buf1])
          apply (drule meta_spec[of _ \<open>BTL p' buf2\<close>])
          apply (drule meta_spec[of _ buf3])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_L_Out)
               apply (rule step_merge_op_Write_R)
                   apply simp_all
            apply (smt (verit, best) BENQ_def BTL_def fun_upd_def fun_upd_twist fun_upd_upd tl_append2)
           apply (metis BENQ_access BENQ_diff_access Nil_is_append_conv)
          by (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
        done
      subgoal
        by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
      done
    done
  subgoal
    by simp
  done

lemma wtraced_Inp_Inl_Inr1:
  \<open>wtraced
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))
    (LCons (VInp (Inl (Inr p)) x) lxs) \<Longrightarrow>
  wtraced
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 (BENQ p x buf2))) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))
    lxs\<close>
  apply (cases lxs; simp)
   apply (rule wtraced.Nil)
  subgoal for vio lxs
    apply (erule wtraced.cases; simp; hypsubst_thin)
    apply (erule wtraced.cases; simp; hypsubst_thin)
    subgoal for _ _ op op'
      apply (rule wtraced.Step[where ?op'=op'])
       apply (drule wstep_Inp_Inl_Inr_Tau1)
       apply (smt (verit, best) IO.exhaust io_of_vio_not_Tau(1) wstep_steps_Tau wstep_trans'(1,2))
      apply assumption
      done
    done
  done

lemma wstep_Inp_Inr_Tau1:
  \<open>wstep (Inp (Inr p) x)
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))
     op \<Longrightarrow>
  wstep Tau
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op (BENQ p x buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))
     op\<close>
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (rule wstep_map_op[of Tau])
  subgoal for io op
    apply (subst (asm) wstep_comp_op_L_R)
    apply (subst wstep_comp_op_L_R)
    apply (elim exE conjE)
    apply (cases io; simp)
    subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2' p'
      apply (cases p'; simp)
      apply hypsubst_thin
      apply (rule exI[of _ buf'])
      apply (rule exI[of _ buf\<^sub>1])
      apply (rule exI[of _ buf\<^sub>2])
      apply (rule exI[of _ op\<^sub>1'])
      apply (rule exI[of _ op\<^sub>2'])
      apply simp
      apply rotate_tac
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (induct \<open>Inp (Inl (Inr p)) x :: ((('a + 'a) + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO\<close> _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3)\<close> _ arbitrary: buf1 buf2 buf3 pred: wstep_comp_op_L)
          apply simp_all
      subgoal
        by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
      subgoal for _ _ _ _ _ _ _ buf1 buf2 buf3
        apply (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp; hypsubst_thin)
        subgoal for p'
          apply (drule meta_spec[of _ buf1])
          apply (drule meta_spec[of _ buf2])
          apply (drule meta_spec[of _ \<open>BTL p' buf3\<close>])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_R_Out)
               apply (rule step_id_op_Write)
                  apply simp_all
            apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
           apply (metis BENQ_access BENQ_diff_access Nil_is_append_conv)
          by (smt (verit, best) BENQ_def BTL_def fun_upd_def fun_upd_twist fun_upd_upd tl_append2)
        subgoal for p'
          apply (drule meta_spec[of _ \<open>BTL p' buf1\<close>])
          apply (drule meta_spec[of _ buf2])
          apply (drule meta_spec[of _ buf3])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_L_Out)
               apply (rule step_merge_op_Write_L)
          by simp_all
        subgoal for p'
          apply (drule meta_spec[of _ buf1])
          apply (drule meta_spec[of _ \<open>BTL p' buf2\<close>])
          apply (drule meta_spec[of _ buf3])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_L_Out)
               apply (rule step_merge_op_Write_R)
          by simp_all
        done
      subgoal
        by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
      done
    done
  subgoal
    by simp
  done

lemma wtraced_Inp_Inr1:
  \<open>wtraced
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))
    (LCons (VInp (Inr p) x) lxs) \<Longrightarrow>
  wtraced
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op (BENQ p x buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))
    lxs\<close>
  apply (cases lxs; simp)
   apply (rule wtraced.Nil)
  subgoal for vio lxs
    apply (erule wtraced.cases; simp; hypsubst_thin)
    apply (erule wtraced.cases; simp; hypsubst_thin)
    subgoal for _ _ op op'
      apply (rule wtraced.Step[where ?op'=op'])
       apply (drule wstep_Inp_Inr_Tau1)
       apply (smt (verit, best) IO.exhaust io_of_vio_not_Tau(1) wstep_steps_Tau wstep_trans'(1,2))
      apply assumption
      done
    done
  done

lemma inputs_not_defaults1:
  \<open>p \<in> inputs (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))) \<Longrightarrow>
  p \<notin> defaults\<close>
proof -
  assume \<open>p \<in> inputs
          (map_op projl projr
            (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
              (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))\<close>
  hence \<open>p \<in> projl ` inputs (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))\<close>
    using op.set_map(1) by metis
  hence \<open>p \<in> inputs (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))\<close>
    using inputs_scomp_op_le_dest by (smt (verit, ccfv_threshold) imageE image_eqI sum.sel(1))
  hence \<open>p \<in> Inl ` inputs (merge_op (case_sum buf1 buf2)) \<or> p \<in> Inr ` inputs (id_op buf3)\<close>
    by blast
  hence \<open>p \<notin> defaults\<close>
    using defaults_sum_def inputs_merge_op inputs_id_op
    by blast
  thus ?thesis .
qed

lemma outputs_not_defaults1:
  \<open>p \<in> outputs (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))) \<Longrightarrow>
  p \<notin> defaults\<close>
proof -
  assume \<open>p \<in> outputs
          (map_op projl projr
            (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
              (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))\<close>
  hence \<open>p \<in> projr ` outputs (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))\<close>
    using op.set_map(2) by metis
  hence \<open>p \<in> outputs (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))\<close>
    using outputs_scomp_op_le_dest by (smt (verit, ccfv_threshold) imageE image_eqI sum.sel(2))
  hence \<open>p \<in> projr ` outputs (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))\<close>
    using op.set_map(2) by metis
  hence \<open>p \<in> outputs (id_op buf4)\<close>
    using outputs_scomp_op_le_dest by (smt (verit, best) imageE sum.sel(2))
  hence \<open>p \<notin> defaults\<close>
    using outputs_id_op by blast
  thus ?thesis .
qed

lemma wstep_Out_Tau1:
  assumes \<open>wstep (Out p x)
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))
    op\<close>
  obtains \<open>buf4 p \<noteq> []\<close> \<open>x = BHD p buf4\<close> \<open>wstep Tau (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op (BTL p buf4)))))) op\<close>
  | \<open>buf4 p = []\<close> \<open>buf1 p \<noteq> []\<close> \<open>x = BHD p buf1\<close> \<open>wstep Tau (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BTL p buf1) buf2)) (id_op buf3)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))) op\<close>
  | \<open>buf4 p = []\<close> \<open>buf2 p \<noteq> []\<close> \<open>x = BHD p buf2\<close> \<open>wstep Tau (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 (BTL p buf2))) (id_op buf3)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))) op\<close>
  | \<open>buf4 p = []\<close> \<open>buf3 p \<noteq> []\<close> \<open>x = BHD p buf3\<close> \<open>wstep Tau (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op (BTL p buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))) op\<close>
  apply atomize_elim
  using assms
  apply -
  apply (erule wstep_map_op_elim)
  apply (subst (asm) wstep_comp_op_L_R)
  apply (elim exE conjE)
  subgoal for io op' buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2'
    apply (cases io; simp)
    subgoal for p'
      apply (cases p'; simp; hypsubst_thin)
      sorry
    done
  done

lemma wtraced_Out1:
  assumes \<open>wtraced
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))
    (LCons (VOut p x) lxs)\<close>
  obtains \<open>p \<notin> defaults\<close> \<open>buf4 p \<noteq> []\<close> \<open>x = BHD p buf4\<close> \<open>wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op (BTL p buf4)))))) lxs\<close>
  | \<open>p \<notin> defaults\<close> \<open>buf4 p = []\<close> \<open>buf1 p \<noteq> []\<close> \<open>x = BHD p buf1\<close> \<open>wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BTL p buf1) buf2)) (id_op buf3)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))) lxs\<close>
  | \<open>p \<notin> defaults\<close> \<open>buf4 p = []\<close> \<open>buf2 p \<noteq> []\<close> \<open>x = BHD p buf2\<close> \<open>wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 (BTL p buf2))) (id_op buf3)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))) lxs\<close>
  | \<open>p \<notin> defaults\<close> \<open>buf4 p = []\<close> \<open>buf3 p \<noteq> []\<close> \<open>x = BHD p buf3\<close> \<open>wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op (BTL p buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))) lxs\<close>
  apply atomize_elim
  using assms
  apply -
  apply (erule wtraced.cases; simp; hypsubst_thin; simp)
  subgoal for op
    apply (erule wstep_Out_Tau1)
    using assms wtraced_outputs outputs_not_defaults1
  by (smt (verit, del_insts) VIO.set_intros(2) estep.elims io_of_vio_not_Tau(1) lset_intros(1) wstep_steps_Tau
    wstep_trans'(1,2) wtraced.simps)+
  done

lemma wstep_Inp_Inl_Inl_Tau2:
  \<open>wstep (Inp (Inl (Inl p)) x)
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))) op \<Longrightarrow>
  wstep Tau
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ p x buf1)) (merge_op (case_sum buf2 buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))) op\<close>
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (rule wstep_map_op[of Tau])
   apply (rule wstep_map_op[of Tau])
  subgoal for _ _ io op
    apply (subst (asm) wstep_comp_op_L_R)
    apply (subst wstep_comp_op_L_R)
    apply (elim exE conjE)
    apply (cases io; simp)
    subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2' p'
      apply (cases p'; simp)
      subgoal for p''
        apply (cases p''; simp)
         apply hypsubst_thin
         apply (rule exI[of _ buf'])
         apply (rule exI[of _ buf\<^sub>1])
         apply (rule exI[of _ buf\<^sub>2])
         apply (rule exI[of _ op\<^sub>1'])
         apply (rule exI[of _ op\<^sub>2'])
         apply simp
         apply rotate_tac
         apply (erule thin_rl)
         apply (erule thin_rl)
         apply (induct \<open>Inp (Inl (Inl p)) x :: (('a + 'a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO\<close> _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))\<close> _ arbitrary: buf1 buf2 buf3 pred: wstep_comp_op_L)
             apply simp_all
        subgoal
          by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
        subgoal for _ _ _ _ _ _ _ buf1 buf2 buf3
          apply (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp; hypsubst_thin)
          subgoal for p'
            apply (drule meta_spec[of _ buf1])
            apply (drule meta_spec[of _ \<open>BTL p' buf2\<close>])
            apply (drule meta_spec[of _ buf3])
            apply simp
            apply (rule wstep_comp_op_L.intros(4))
               apply (rule step_comp_op_R_Out)
                 apply (rule step_merge_op_Write_L)
            by simp_all
          subgoal for p'
            apply (drule meta_spec[of _ buf1])
            apply (drule meta_spec[of _ buf2])
            apply (drule meta_spec[of _ \<open>BTL p' buf3\<close>])
            apply simp
            apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_R_Out)
                 apply (rule step_merge_op_Write_R)
            by simp_all
          subgoal for p'
            apply (drule meta_spec[of _ \<open>BTL p' buf1\<close>])
            apply (drule meta_spec[of _ buf2])
            apply (drule meta_spec[of _ buf3])
            apply simp
            apply (rule wstep_comp_op_L.intros(4))
               apply (rule step_comp_op_L_Out)
                  apply (rule step_id_op_Write)
                     apply simp_all
              apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
             apply (metis BENQ_access BENQ_diff_access Nil_is_append_conv)
            by (smt (verit, best) BENQ_def BTL_def fun_upd_def fun_upd_twist fun_upd_upd tl_append2)
          done
        subgoal
          by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
        subgoal
          by (metis Inr_not_Inl sum.exhaust sum.simps(5,6))
        done
      done
    done
  subgoal
    by simp
  subgoal
    by simp
  done

lemma wtraced_Inp_Inl_Inl2:
  \<open>wtraced
     (map_op assoc id
       (map_op projl projr
         (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
           (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))))
     (LCons (VInp (Inl (Inl p)) x) lxs) \<Longrightarrow>
  wtraced
     (map_op assoc id
       (map_op projl projr
         (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ p x buf1)) (merge_op (case_sum buf2 buf3)))
           (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))))
     lxs\<close>
  apply (cases lxs; simp)
   apply (rule wtraced.Nil)
  subgoal for vio lxs
    apply (erule wtraced.cases; simp; hypsubst_thin)
    apply (erule wtraced.cases; simp; hypsubst_thin)
    subgoal for _ _ op op'
      apply (rule wtraced.Step[where ?op'=op'])
       apply (drule wstep_Inp_Inl_Inl_Tau2)
       apply (smt (verit, best) IO.exhaust io_of_vio_not_Tau(1) wstep_steps_Tau wstep_trans'(1,2))
      apply assumption
      done
    done
  done

lemma wstep_Inp_Inl_Inr_Tau2:
  \<open>wstep (Inp (Inl (Inr p)) x)
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))) op \<Longrightarrow>
  wstep Tau
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum (BENQ p x buf2) buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))) op\<close>
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (rule wstep_map_op[of Tau])
   apply (rule wstep_map_op[of Tau])
  subgoal for _ _ io op
    apply (subst (asm) wstep_comp_op_L_R)
    apply (subst wstep_comp_op_L_R)
    apply (elim exE conjE)
    apply (cases io; simp)
    subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2' p'
      apply (cases p'; simp)
      subgoal for p''
        apply (cases p''; simp)
        subgoal for p'''
          apply (cases p'''; simp)
          apply hypsubst_thin
          apply (rule exI[of _ buf'])
          apply (rule exI[of _ buf\<^sub>1])
          apply (rule exI[of _ buf\<^sub>2])
          apply (rule exI[of _ op\<^sub>1'])
          apply (rule exI[of _ op\<^sub>2'])
          apply simp
          apply rotate_tac
          apply (erule thin_rl)
          apply (erule thin_rl)
          apply (induct \<open>Inp (Inl (Inr (Inl p))) x :: (('a + 'a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO\<close> _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))\<close> _ arbitrary: buf1 buf2 buf3 pred: wstep_comp_op_L)
              apply simp_all
          subgoal
            by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
          subgoal for _ _ _ _ _ _ _ buf1 buf2 buf3
            apply (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp; hypsubst_thin)
            subgoal for p'
              apply (drule meta_spec[of _ buf1])
              apply (drule meta_spec[of _ \<open>BTL p' buf2\<close>])
              apply (drule meta_spec[of _ buf3])
              apply simp
              apply (rule wstep_comp_op_L.intros(4))
                 apply (rule step_comp_op_R_Out)
                 apply (rule step_merge_op_Write_L)
                      apply simp_all
                apply (smt (verit, best) BENQ_def BTL_def fun_upd_def fun_upd_twist fun_upd_upd tl_append2)
               apply (metis BENQ_access BENQ_diff_access Nil_is_append_conv)
              by (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
            subgoal for p'
              apply (drule meta_spec[of _ buf1])
              apply (drule meta_spec[of _ buf2])
              apply (drule meta_spec[of _ \<open>BTL p' buf3\<close>])
              apply simp
              apply (rule wstep_comp_op_L.intros(4))
                 apply (rule step_comp_op_R_Out)
                   apply (rule step_merge_op_Write_R)
              by simp_all
            subgoal for p'
              apply (drule meta_spec[of _ \<open>BTL p' buf1\<close>])
              apply (drule meta_spec[of _ buf2])
              apply (drule meta_spec[of _ buf3])
              apply simp
              apply (rule wstep_comp_op_L.intros(4))
                 apply (rule step_comp_op_L_Out)
                    apply (rule step_id_op_Write)
              by simp_all
            done
          subgoal
            by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
          done
        done
      done
    done
  subgoal
    by simp
  subgoal
    by simp
  done

lemma wtraced_Inp_Inl_Inr2:
  \<open>wtraced
     (map_op assoc id
       (map_op projl projr
         (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
           (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))))
     (LCons (VInp (Inl (Inr p)) x) lxs) \<Longrightarrow>
  wtraced
     (map_op assoc id
       (map_op projl projr
         (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum (BENQ p x buf2) buf3)))
           (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))))
     lxs\<close>
  apply (cases lxs; simp)
   apply (rule wtraced.Nil)
  subgoal for vio lxs
    apply (erule wtraced.cases; simp; hypsubst_thin)
    apply (erule wtraced.cases; simp; hypsubst_thin)
    subgoal for _ _ op op'
      apply (rule wtraced.Step[where ?op'=op'])
       apply (drule wstep_Inp_Inl_Inr_Tau2)
       apply (smt (verit, best) IO.exhaust io_of_vio_not_Tau(1) wstep_steps_Tau wstep_trans'(1,2))
      apply assumption
      done
    done
  done

lemma wstep_Inp_Inr_Tau2:
  \<open>wstep (Inp (Inr p) x)
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))) op \<Longrightarrow>
  wstep Tau
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 (BENQ p x buf3))))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))) op\<close>
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (rule wstep_map_op[of Tau])
   apply (rule wstep_map_op[of Tau])
  subgoal for _ _ io op
    apply (subst (asm) wstep_comp_op_L_R)
    apply (subst wstep_comp_op_L_R)
    apply (elim exE conjE)
    apply (cases io; simp)
    subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2' p'
      apply (cases p'; simp)
      subgoal for p''
        apply (cases p''; simp)
        subgoal for p'''
          apply (cases p'''; simp)
          apply hypsubst_thin
          apply (rule exI[of _ buf'])
          apply (rule exI[of _ buf\<^sub>1])
          apply (rule exI[of _ buf\<^sub>2])
          apply (rule exI[of _ op\<^sub>1'])
          apply (rule exI[of _ op\<^sub>2'])
          apply simp
          apply rotate_tac
          apply (erule thin_rl)
          apply (erule thin_rl)
          apply (induct \<open>Inp (Inl (Inr (Inr p))) x :: (('a + 'a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO\<close> _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))\<close> _ arbitrary: buf1 buf2 buf3 pred: wstep_comp_op_L)
              apply simp_all
          subgoal
            by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
          subgoal for _ _ _ _ _ _ _ buf1 buf2 buf3
            apply (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp; hypsubst_thin)
            subgoal for p'
              apply (drule meta_spec[of _ buf1])
              apply (drule meta_spec[of _ \<open>BTL p' buf2\<close>])
              apply (drule meta_spec[of _ buf3])
              apply simp
              apply (rule wstep_comp_op_L.intros(4))
                 apply (rule step_comp_op_R_Out)
                 apply (rule step_merge_op_Write_L)
              by simp_all
            subgoal for p'
              apply (drule meta_spec[of _ buf1])
              apply (drule meta_spec[of _ buf2])
              apply (drule meta_spec[of _ \<open>BTL p' buf3\<close>])
              apply simp
              apply (rule wstep_comp_op_L.intros(4))
                 apply (rule step_comp_op_R_Out)
                   apply (rule step_merge_op_Write_R)
                      apply simp_all
                apply (smt (verit, best) BENQ_def BTL_def fun_upd_def fun_upd_twist fun_upd_upd tl_append2)
               apply (metis BENQ_access BENQ_diff_access Nil_is_append_conv)
              by (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
            subgoal for p'
              apply (drule meta_spec[of _ \<open>BTL p' buf1\<close>])
              apply (drule meta_spec[of _ buf2])
              apply (drule meta_spec[of _ buf3])
              apply simp
              apply (rule wstep_comp_op_L.intros(4))
                 apply (rule step_comp_op_L_Out)
                    apply (rule step_id_op_Write)
              by simp_all
            done
          subgoal
            by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
          done
        done
      done
    done
  subgoal
    by simp
  subgoal
    by simp
  done

lemma wtraced_Inp_Inr2:
  \<open>wtraced
     (map_op assoc id
       (map_op projl projr
         (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
           (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))))
     (LCons (VInp (Inr p) x) lxs) \<Longrightarrow>
  wtraced
     (map_op assoc id
       (map_op projl projr
         (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 (BENQ p x buf3))))
           (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))))
     lxs\<close>
  apply (cases lxs; simp)
   apply (rule wtraced.Nil)
  subgoal for vio lxs
    apply (erule wtraced.cases; simp; hypsubst_thin)
    apply (erule wtraced.cases; simp; hypsubst_thin)
    subgoal for _ _ op op'
      apply (rule wtraced.Step[where ?op'=op'])
       apply (drule wstep_Inp_Inr_Tau2)
       apply (smt (verit, best) IO.exhaust io_of_vio_not_Tau(1) wstep_steps_Tau wstep_trans'(1,2))
      apply assumption
      done
    done
  done

lemma assoc_defaults:
  \<open>(p :: 'a :: {defaults} + 'b :: {defaults} + 'c :: {defaults}) \<in> defaults \<longleftrightarrow> assoc p \<in> defaults\<close>
  by (smt (verit, ccfv_threshold) Inl_in_defaults Inr_in_defaults assoc.simps(1,2,3) sum.exhaust_sel)

lemma inputs_not_defaults2:
  \<open>p \<in> inputs (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))) \<Longrightarrow>
  p \<notin> defaults\<close>
proof -
  assume \<open>p \<in> inputs
          (map_op assoc id
            (map_op projl projr
              (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
                (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))))\<close>
  hence \<open>p \<in> assoc ` inputs (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))\<close>
    using op.set_map(1) by metis
  hence \<open>p \<in> assoc ` projl` inputs (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))\<close>
    using op.set_map(1) by metis
  hence \<open>p \<in> assoc ` inputs (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))\<close>
    using inputs_scomp_op_le_dest by (smt (verit, ccfv_threshold) imageE image_eqI sum.sel(1))
  hence \<open>p \<in> assoc ` Inl ` inputs (id_op buf1) \<or> p \<in> assoc ` Inr ` inputs (merge_op (case_sum buf2 buf3))\<close>
    by (smt (verit, ccfv_threshold) image_iff inputs_pcomp_op_le_dest)
  hence \<open>p \<notin> defaults\<close>
    using assoc_defaults
    by (smt (verit) DiffE Inl_in_defaults Inr_in_defaults imageE inputs_id_op_alt inputs_sub_op_Read merge_op_reads)
  thus ?thesis .
qed

lemma outputs_not_defaults2:
  \<open>p \<in> outputs (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))) \<Longrightarrow>
  p \<notin> defaults\<close>
proof -
  assume \<open>p \<in> outputs
          (map_op assoc id
            (map_op projl projr
              (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
                (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))))\<close>
  hence \<open>p \<in> outputs (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))\<close>
    using op.set_map(2) id_apply image_id by metis
  hence \<open>p \<in> projr ` outputs (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))\<close>
    using op.set_map(2) by metis
  hence \<open>p \<in> outputs (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))\<close>
    using outputs_scomp_op_le_dest by (smt (verit, ccfv_threshold) imageE image_eqI sum.sel(2))
  hence \<open>p \<in> projr ` outputs (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))\<close>
    using op.set_map(2) by metis
  hence \<open>p \<in> outputs (id_op buf4)\<close>
    using outputs_scomp_op_le_dest by (smt (verit, best) imageE sum.sel(2))
  hence \<open>p \<notin> defaults\<close>
    using outputs_id_op by blast
  thus ?thesis .
qed

lemma wstep_Out_Tau2:
  assumes \<open>wstep (Out p x)
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))))
    op\<close>
  obtains \<open>buf4 p \<noteq> []\<close> \<open>x = BHD p buf4\<close> \<open>wstep Tau (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op (BTL p buf4))))))) op\<close>
  | \<open>buf4 p = []\<close> \<open>buf1 p \<noteq> []\<close> \<open>x = BHD p buf1\<close> \<open>wstep Tau (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL p buf1)) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))) op\<close>
  | \<open>buf4 p = []\<close> \<open>buf2 p \<noteq> []\<close> \<open>x = BHD p buf2\<close> \<open>wstep Tau (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum (BTL p buf2) buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))) op\<close>
  | \<open>buf4 p = []\<close> \<open>buf3 p \<noteq> []\<close> \<open>x = BHD p buf3\<close> \<open>wstep Tau (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 (BTL p buf3)))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))) op\<close>
  sorry

lemma wtraced_Out2:
  assumes \<open>wtraced
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))))
    (LCons (VOut p x) lxs)\<close>
  obtains \<open>p \<notin> defaults\<close> \<open>buf4 p \<noteq> []\<close> \<open>x = BHD p buf4\<close> \<open>wtraced (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op (BTL p buf4))))))) lxs\<close>
  | \<open>p \<notin> defaults\<close> \<open>buf4 p = []\<close> \<open>buf1 p \<noteq> []\<close> \<open>x = BHD p buf1\<close> \<open>wtraced (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL p buf1)) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))) lxs\<close>
  | \<open>p \<notin> defaults\<close> \<open>buf4 p = []\<close> \<open>buf2 p \<noteq> []\<close> \<open>x = BHD p buf2\<close> \<open>wtraced (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum (BTL p buf2) buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))) lxs\<close>
  | \<open>p \<notin> defaults\<close> \<open>buf4 p = []\<close> \<open>buf3 p \<noteq> []\<close> \<open>x = BHD p buf3\<close> \<open>wtraced (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 (BTL p buf3)))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))) lxs\<close>
 apply atomize_elim
  using assms
  apply -
  apply (erule wtraced.cases; simp; hypsubst_thin; simp)
  subgoal for op
    apply (erule wstep_Out_Tau2)
    using assms wtraced_outputs outputs_not_defaults2
  by (smt (verit, del_insts) VIO.set_intros(2) estep.elims io_of_vio_not_Tau(1) lset_intros(1) wstep_steps_Tau
    wstep_trans'(1,2) wtraced.simps)+
  done

lemma A1_trace_eq_gen:
  \<open>(merge_op (case_sum buf1 buf2) \<parallel> id_op buf3) \<bullet> (\<V> \<bullet> id_op buf4) \<equiv>\<^sub>t map_op assoc id ((id_op buf1 \<parallel> merge_op (case_sum buf2 buf3)) \<bullet> (\<V> \<bullet> id_op buf4))\<close>
  unfolding wtraces_def pcomp_op_def scomp_op_def
  apply (rule Collect_eqI)
  apply (rule iffI)
  subgoal for lxs
    apply (coinduction arbitrary: buf1 buf2 buf3 buf4 lxs pred: wtraced)
    subgoal for buf1 buf2 buf3 buf4 lxs
      apply (cases lxs; simp; hypsubst_thin)
      subgoal for vio lxs
        apply (cases vio; simp; hypsubst_thin)
        subgoal for p x
          apply (cases p; simp; hypsubst_thin)
          subgoal for p
            apply (cases p; simp; hypsubst_thin)
            subgoal for p
              apply (intro exI[of _ \<open>map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. [])
  (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ p x buf1)) (merge_op (case_sum buf2 buf3)))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))\<close>] conjI)
               apply (rule step_wstep)
               apply (rule step_map_op)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Inp)
                   apply (rule step_comp_op_L_Inp)
                     apply (rule step_id_op_Read)
                      apply simp_all
              using wtraced_inputs inputs_not_defaults1
                apply (metis Inl_in_defaults VIO.set_intros(1) lset_intros(1))
               apply fastforce
              using wtraced_Inp_Inl_Inl1
              by metis
            subgoal for p
              apply (intro exI[of _ \<open>map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. [])
  (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum (BENQ p x buf2) buf3)))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))\<close>] conjI)
               apply (rule step_wstep)
               apply (rule step_map_op)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Inp)
                   apply (rule step_comp_op_R_Inp)
                     apply (rule step_merge_op_Read_L)
                      apply simp_all
              using wtraced_inputs inputs_not_defaults1
                apply (metis Inl_in_defaults Inr_in_defaults VIO.set_intros(1) llist.set_intros(1))
               apply fastforce
              using wtraced_Inp_Inl_Inr1
              by metis
            done
          subgoal for p
            apply (intro exI[of _ \<open>map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. [])
  (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 (BENQ p x buf3))))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4)))))\<close>] conjI)
             apply (rule step_wstep)
             apply (rule step_map_op)
            apply (rule step_map_op)
               apply (rule step_comp_op_L_Inp)
                 apply (rule step_comp_op_R_Inp)
                    apply (rule step_merge_op_Read_R)
                     apply simp_all
            using wtraced_inputs inputs_not_defaults1
              apply (metis Inr_in_defaults VIO.set_intros(1) llist.set_intros(1))
             apply fastforce
            using wtraced_Inp_Inr1
            by metis
          done
        subgoal for p x
          apply (erule wtraced_Out1)
          apply (intro exI[of _ \<open>(map_op assoc id (map_op projl projr
               (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
  (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op (BTL p buf4)))))))\<close>] conjI)
              apply (rule step_wstep)
              apply (rule step_map_op)
               apply (rule step_map_op)
                apply (rule step_comp_op_R_Out)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Out)
                     apply (rule step_id_op_Write)
                        apply simp_all
              apply simp
             apply blast
          apply (intro exI[of _ \<open>(map_op assoc id (map_op projl projr
               (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL p buf1)) (merge_op (case_sum buf2 buf3)))
  (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))))\<close>] conjI)
             apply (rule wstep_trans(1))
              apply (rule rtranclp.intros(2))
               apply (rule rtranclp.intros(2))
                apply (rule rtranclp.intros(2))
                 apply (rule rtranclp.intros(2))
                  apply (rule rtranclp.intros(1))
                 apply (rule step_map_op)
                  apply (rule step_map_op)
                   apply (rule step_Tau_comp_op_L)
                      apply (rule step_comp_op_L_Out)
                         apply (rule step_id_op_Write)
                            apply simp_all
                apply (rule step_map_op)
                 apply (rule step_map_op)
                  apply (rule step_Tau_comp_op_R)
                       apply (rule step_map_op)
                        apply (rule step_comp_op_L_Inp)
                          apply (rule step_merge_op_Read_L[of p])
                           apply simp_all
                apply simp
               apply (rule step_map_op)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Tau)
                   apply (rule step_map_op)
                    apply (rule step_Tau_comp_op_L)
                       apply (rule step_merge_op_Write_L[of p])
                          apply simp_all
              apply (rule step_map_op)
               apply (rule step_map_op)
                apply (rule step_comp_op_R_Tau)
                  apply (rule step_map_op)
                   apply (rule step_Tau_comp_op_R)
                        apply (rule step_id_op_Read)
                         apply simp_all
              apply simp
             apply fastforce
            apply blast
           apply (intro exI[of _ \<open>(map_op assoc id (map_op projl projr
               (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum (BTL p buf2) buf3)))
  (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))))\<close>] conjI)
            apply (rule wstep_trans(1))
             apply (rule rtranclp.intros(2))
              apply (rule rtranclp.intros(2))
               apply (rule rtranclp.intros(2))
                apply (rule rtranclp.intros(2))
                 apply (rule rtranclp.intros(1))
                apply (rule step_map_op)
                 apply (rule step_map_op)
                  apply (rule step_Tau_comp_op_L)
                     apply (rule step_comp_op_R_Out)
                       apply (rule step_merge_op_Write_L)
                          apply simp_all
               apply (rule step_map_op)
                apply (rule step_map_op)
                 apply (rule step_Tau_comp_op_R)
                      apply (rule step_map_op)
                       apply (rule step_comp_op_L_Inp)
                         apply (rule step_merge_op_Read_R[of p])
                          apply simp_all
               apply simp
              apply (rule step_map_op)
               apply (rule step_map_op)
                apply (rule step_comp_op_R_Tau)
                  apply (rule step_map_op)
                   apply (rule step_Tau_comp_op_L)
                      apply (rule step_merge_op_Write_R[of p])
                         apply simp_all
             apply (rule step_map_op)
              apply (rule step_map_op)
               apply (rule step_comp_op_R_Tau)
                 apply (rule step_map_op)
                  apply (rule step_Tau_comp_op_R)
                       apply (rule step_id_op_Read)
                        apply simp_all
             apply simp
            apply fastforce
           apply blast
          apply (intro exI[of _ \<open>(map_op assoc id (map_op projl projr
               (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 (BTL p buf3))))
  (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))))\<close>] conjI)
           apply (rule wstep_trans(1))
            apply (rule rtranclp.intros(2))
             apply (rule rtranclp.intros(2))
              apply (rule rtranclp.intros(2))
               apply (rule rtranclp.intros(2))
                apply (rule rtranclp.intros(1))
               apply (rule step_map_op)
                apply (rule step_map_op)
                 apply (rule step_Tau_comp_op_L)
                    apply (rule step_comp_op_R_Out)
                      apply (rule step_merge_op_Write_R)
                         apply simp_all
              apply (rule step_map_op)
               apply (rule step_map_op)
                apply (rule step_Tau_comp_op_R)
                     apply (rule step_map_op)
                      apply (rule step_comp_op_L_Inp)
                        apply (rule step_merge_op_Read_R[of p])
                         apply simp_all
              apply simp
             apply (rule step_map_op)
              apply (rule step_map_op)
               apply (rule step_comp_op_R_Tau)
                 apply (rule step_map_op)
                  apply (rule step_Tau_comp_op_L)
                     apply (rule step_merge_op_Write_R[of p])
                        apply simp_all
            apply (rule step_map_op)
             apply (rule step_map_op)
              apply (rule step_comp_op_R_Tau)
                apply (rule step_map_op)
                 apply (rule step_Tau_comp_op_R)
                      apply (rule step_id_op_Read)
                       apply simp_all
            apply simp
           apply fastforce
          apply blast
          done
        done
      done
    done
  subgoal for lxs
    apply (coinduction arbitrary: buf1 buf2 buf3 buf4 lxs pred: wtraced)
    subgoal for buf1 buf2 buf3 buf4 lxs
      apply (cases lxs; simp; hypsubst_thin)
      subgoal for vio lxs
        apply (cases vio; simp; hypsubst_thin)
        subgoal for p x
          apply (cases p; simp; hypsubst_thin)
          subgoal for p
            apply (cases p; simp; hypsubst_thin)
            subgoal for p
              apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (\<lambda>_. [])
  (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BENQ p x buf1) buf2)) (id_op buf3))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))\<close>] conjI)
               apply (rule step_wstep)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Inp)
                  apply (rule step_comp_op_L_Inp)
                    apply (rule step_merge_op_Read_L)
                     apply simp_all
              using wtraced_inputs inputs_not_defaults2
               apply (metis Inl_in_defaults VIO.set_intros(1) lset_intros(1))
              using wtraced_Inp_Inl_Inl2
              by metis
            subgoal for p
              apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (\<lambda>_. [])
  (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 (BENQ p x buf2))) (id_op buf3))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))\<close>] conjI)
               apply (rule step_wstep)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Inp)
                  apply (rule step_comp_op_L_Inp)
                    apply (rule step_merge_op_Read_R)
                     apply simp_all
              using wtraced_inputs inputs_not_defaults2
               apply (metis Inl_in_defaults Inr_in_defaults VIO.set_intros(1) llist.set_intros(1))
              using wtraced_Inp_Inl_Inr2
              by metis
            done
          subgoal for p
            apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (\<lambda>_. [])
  (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op (BENQ p x buf3)))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (id_op buf4))))\<close>] conjI)
             apply (rule step_wstep)
             apply (rule step_map_op)
              apply (rule step_comp_op_L_Inp)
                apply (rule step_comp_op_R_Inp)
                   apply (rule step_id_op_Read)
                    apply simp_all
            using wtraced_inputs inputs_not_defaults2
             apply (metis Inr_in_defaults VIO.set_intros(1) llist.set_intros(1))
            using wtraced_Inp_Inr2
            by metis
          done
        subgoal for p x
          sorry
        done
      done
    done
  done

lemma A1_trace_eq:
  \<open>(\<V> \<parallel> \<I>) \<bullet> \<V>' \<equiv>\<^sub>t map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>')\<close>
  oops