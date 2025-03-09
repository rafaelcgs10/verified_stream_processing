theory A5

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A5: Acopy to acopy and identity\<close>

lemma A5_gen:
  \<open>map_op projl projr (comp_op Some (case_sum buf2 buf2')
    (acopy_op (case_sum buf1 buf1'))
    (acopy_op (case_sum buf3 buf3') \<parallel> id_op buf3''))
  ~ map_op id (case_sum Inr Inl) (map_op projl projr (comp_op Some (case_sum buf2' buf2)
    (acopy_op (case_sum buf1' buf1))
    (id_op buf3'' \<parallel> acopy_op (case_sum buf3 buf3'))))\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf2' buf3 buf3' buf3'' rule: bisim_coinduct_upto)
  case BISIM
  then show ?case
    unfolding sim_def pcomp_op_def
  proof (intro allI conjI impI)
    fix io :: "('a, ('a + 'a) + 'a, 'b) IO"
      and op1' :: "('a, ('a + 'a) + 'a, 'b) op"
    assume H: "step io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum buf3 buf3')) (id_op buf3'')))) op1'"
    show "\<exists>op2'. step io (map_op id (case_sum Inr Inl) (map_op projl projr (comp_op Some (case_sum buf2' buf2) (acopy_op (case_sum buf1' buf1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3'') (acopy_op (case_sum buf3 buf3')))))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf2 buf2' buf3 buf3' buf3''. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum buf3 buf3')) (id_op buf3''))) \<and> t = map_op id (case_sum Inr Inl) (map_op projl projr (comp_op Some (case_sum buf2' buf2) (acopy_op (case_sum buf1' buf1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3'') (acopy_op (case_sum buf3 buf3')))))) op1' op2'"
      using H by (auto elim !: step_map_op_elim step_comp_op_elim step_acopy_op_elim step_id_op_cases) (fastforce intro: bc_base)+
  next
    fix io :: "('a, ('a + 'a) + 'a, 'b) IO"
      and op1' :: "('a, ('a + 'a) + 'a, 'b) op"
    assume H: "step io (map_op id (case_sum Inr Inl) (map_op projl projr (comp_op Some (case_sum buf2' buf2) (acopy_op (case_sum buf1' buf1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3'') (acopy_op (case_sum buf3 buf3')))))) op1'"
    show "\<exists>op2'. step io (map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum buf3 buf3')) (id_op buf3'')))) op2' \<and> bisim_cong (\<lambda>s t. \<exists>buf1 buf1' buf2 buf2' buf3 buf3' buf3''. s = map_op projl projr (comp_op Some (case_sum buf2 buf2') (acopy_op (case_sum buf1 buf1')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (acopy_op (case_sum buf3 buf3')) (id_op buf3''))) \<and> t = map_op id (case_sum Inr Inl) (map_op projl projr (comp_op Some (case_sum buf2' buf2) (acopy_op (case_sum buf1' buf1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3'') (acopy_op (case_sum buf3 buf3')))))) op1' op2'"
      using H by (auto elim !: step_map_op_elim step_comp_op_elim step_acopy_op_elim step_id_op_cases) (fastforce intro: bc_sym[OF bc_base])+
  qed
qed

lemma A5:
  \<open>\<C> \<bullet> (\<C> \<parallel> \<I>) ~ map_op id (case_sum Inr Inl) (\<C> \<bullet> (\<I> \<parallel> \<C>))\<close>
  unfolding scomp_op_def
  using A5_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp


end