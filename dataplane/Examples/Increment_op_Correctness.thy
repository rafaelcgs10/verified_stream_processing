theory Increment_op_Correctness

imports
  Ooo_Input_op
  Increment_op
  "HOL-ex.Sketch_and_Explore"
begin

abbreviation inp_incr_edges where
  \<open>inp_incr_edges \<equiv> (\<lambda>l. if l = Loc (0 :: 2) (Src (1 :: 1)) then [Loc (1 :: 2) (Trg (1 :: 1))] else [])\<close>

abbreviation inp_incr_summary where
  \<open>inp_incr_summary inc \<equiv> (\<lambda>l1 l2.
  if l1 = Loc (0 :: 2) (Src (1 :: 1)) \<and> l2 = Loc (1 :: 2) (Trg (1 :: 1))
  then antichain {0}
  else if l1 = Loc 0 (Trg 1) \<and> l2 = Loc 0 (Src 1)
  then antichain {0}
  else if l1 = Loc 1 (Trg 1) \<and> l2 = Loc 1 (Src 1)
  then antichain {inc}
  else {}\<^sub>A)\<close>

(* Experiment with Eisbach. *)
method sim_cases uses defs elims =
  ((unfold defs)?, elim conjE elims, (auto; fail), fold defs; hypsubst_thin?)

lemma ooo_input_op_increment_op_source_op:
  defines \<open>invariant f os1 buf os2 \<equiv> initia os1 \<and> en1 os1 = f \<and> inj f \<and> timely_monotone (es os1 1) (mset (ocaps os1 1))
  \<and> initia os2 \<and> (\<forall>x \<in> set (buf (Inr (1, 1))). is_Inr x)\<close>
    and \<open>my_ooo_input_op os \<equiv> map_op
  (case_option (Inl (0 :: 2)) (\<lambda>(p :: 1). Inr (0 :: 2, 1))) (case_option (Inl (0 :: 2)) (\<lambda>(p :: 1). Inr (0 :: 2, 1)))
  (ooo_input_op {|1 :: 1|} os)\<close>
    and \<open>my_increment_op inc os \<equiv> map_op
  (case_option (Inl (1 :: 2)) (\<lambda>(p :: 1). Inr (1 :: 2, 1))) (case_option (Inl (1 :: 2)) (\<lambda>(p :: 1). Inr (1 :: 2, 1)))
  (increment_op (1 :: 1) (1 :: 1) inc os)\<close>
    and \<open>my_source_op f inc os1 buf os2 \<equiv> map_op (\<lambda>(p :: 1). (1, 1)) (\<lambda>(p :: 1). (1, 1))
    (source_op ((\<lambda>(p :: 1). outpu os2 1 @@- lmap (\<lambda>(d, t). (d, t + inc))
      ((input os2 1 @ map projr (buf (Inr (1, 1))) @ outpu os1 1) @@- lmap (\<lambda>x. case x of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os1 1))))))\<close>
  assumes \<open>invariant f os1 buf os2\<close>
  shows \<open>dataflow_op sg (map_op (case_sum id id) (case_sum id id)
  (comp_op [Inr (0 :: 2, 1 :: 1) \<mapsto> Inr (1 :: 2, 1 :: 1)] buf (my_ooo_input_op os1) (my_increment_op inc os2)))
  \<approx> my_source_op f inc os1 buf os2\<close>
  using assms(5)
proof (coinduction arbitrary: sg os1 buf os2 rule: wbisim_coinduct_upto'')
  case SIM1
  show ?case (is \<open>\<exists>_. _ \<and> wbisim_cong ?R _ _\<close>)
  proof -
    define R where \<open>R = ?R\<close>
    have invariant_initia: \<open>invariant f os1 buf os2 \<Longrightarrow> initia os1\<close> \<open>invariant f os1 buf os2 \<Longrightarrow> initia os2\<close>
      unfolding invariant_def by blast+
    show ?thesis
    proof -
      have "\<exists>op2'. wstep (Out (1, 1) (d, t)) (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc (os2\<lparr>outpu := (outpu os2)(1 := xs)\<rparr>))))) op2'"
      (is \<open>\<exists>_. _ \<and> wbisim_cong _ (dataflow_op _ (map_op _ _ (comp_op _ _ _ (my_increment_op _ ?os2')))) _\<close>)
        if "invariant f os1 buf os2"
          and "outpu os2 1 = (d, t) # xs"
        for d :: 'b
          and t :: 'c
          and xs :: "('b \<times> 'c) buf"
        term ?os2'
      proof -
        have \<open>step (Out 1 (d, t))
  (source_op ((\<lambda>(p :: 1). outpu os2 1 @@- lmap (\<lambda>(d, t). (d, t + inc))
      ((input os2 1 @ map projr (buf (Inr (1, 1))) @ outpu os1 1) @@- lmap (\<lambda>x. case x of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os1 1))))))
  (source_op ((\<lambda>(p :: 1). outpu ?os2' 1 @@- lmap (\<lambda>(d, t). (d, t + inc))
      ((input ?os2' 1 @ map projr (buf (Inr (1, 1))) @ outpu os1 1) @@- lmap (\<lambda>x. case x of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os1 1))))))\<close>
          using that(2) step_source_op_Out_intro defaults_num1_def by force
        hence \<open>wstep (Out (1, 1) (d, t)) (my_source_op f inc os1 buf os2) (my_source_op f inc os1 buf ?os2')\<close>
          using my_source_op_def by auto
        thus ?thesis using that(1) unfolding R_def invariant_def by (fastforce intro!: wbc_base)
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] (BENQ (Inr (1, 1)) (Inr (d, t)) buf)
    (my_ooo_input_op (os1\<lparr>outpu := (outpu os1)(1 := xs)\<rparr>)) (my_increment_op inc os2)))) op2'"
      (is \<open>\<exists>_. _ \<and> wbisim_cong _ (dataflow_op _ (map_op _ _ (comp_op _ ?buf' (my_ooo_input_op ?os1') _))) _\<close>)
        if "invariant f os1 buf os2"
          and "outpu os1 1 = (d, t) # xs"
        for d :: 'b
          and t :: 'c
          and xs :: "('b \<times> 'c) buf"
      proof -
        have \<open>my_source_op f inc os1 buf os2 = my_source_op f inc ?os1' ?buf' os2\<close>
          using that(2) unfolding my_source_op_def by simp
        thus ?thesis using that(1) unfolding R_def invariant_def by (fastforce intro!: wbc_base)
      qed
      moreover have False
        if "invariant f os1 buf os2"
          and "buf (Inr (1, 1)) \<noteq> []"
          and "is_Inl (BHD (Inr (1, 1)) buf)"
        using that sum.exhaust is_Inl.simps(2) is_Inr.simps(2) hd_in_set unfolding invariant_def BHD_def
        by (metis (no_types, opaque_lifting))
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] (BTL (Inr (1, 1)) buf)
    (my_ooo_input_op os1) (my_increment_op inc (consumes os2 1 t d))))) op2'"
        if "invariant f os1 buf os2"
          and "buf (Inr (1, 1)) \<noteq> []"
          and "Inr (d, t) = BHD (Inr (1, 1)) buf"
        for d :: 'b
          and t :: 'c
        using that sorry
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
  (my_ooo_input_op os1') (my_increment_op inc os2)))) op2'"
        if "invariant f os1 buf os2"
          and "ocaps os1 1 \<noteq> []"
          and "os1' |\<in>| ooo_input_op_logic {|1|} os1"
        for os1' :: "(1, 'b, 'a, 'c, 'd) input_state_scheme"
        using that sorry
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
  (my_ooo_input_op os1) (my_increment_op inc os2')))) op2'"
        if "invariant f os1 buf os2"
          and "ocaps os2 1 \<noteq> []"
          and "os2' |\<in>| increment_op_logic 1 1 inc os2"
        for os2' :: "(1, 'b, 'a, 'c, 'd) input_state_scheme"
        using that sorry
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op (sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 1 (edges sg) \<lparr>cons = consu os2, inte = inter os2, prod = produ os2\<rparr>) (pt_tr sg)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc (os2\<lparr>consu := [], inter := [], produ := []\<rparr>))))) op2'"
      (is \<open>_ (dataflow_op ?sg')\<close>)
        if "invariant f os1 buf os2"
          and "consu os2 \<noteq> [] \<or> inter os2 \<noteq> [] \<or> produ os2 \<noteq> []"
        using that unfolding R_def invariant_def my_source_op_def by (fastforce intro!: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op (sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 0 (edges sg) \<lparr>cons = consu os1, inte = inter os1, prod = produ os1\<rparr>) (pt_tr sg)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
  (my_ooo_input_op (os1\<lparr>consu := [], inter := [], produ := []\<rparr>)) (my_increment_op inc os2)))) op2'"
        if "invariant f os1 buf os2"
          and "consu os1 \<noteq> [] \<or> inter os1 \<noteq> [] \<or> produ os1 \<noteq> []"
      (is \<open>_ (dataflow_op ?sg')\<close>)
        using that unfolding R_def invariant_def my_source_op_def by (fastforce intro!: wbc_base)
      note * = calculation this
      show ?thesis
end
        using SIM1 unfolding R_def[symmetric]
        apply -
        apply (sim_cases defs: my_ooo_input_op_def ooo_input_op_def my_increment_op_def increment_op_def elims: step_dataflow_op_elim step_map_op_elim step_comp_op_elim step_builder_op_elim)
        using * apply (auto intro: invariant_initia simp flip: my_ooo_input_op_def)
        done
end
    subgoal
      apply (intro exI conjI)
       apply (rule step_wstep)
       apply (rule step_map_op)
        apply (rule step_source_op_Out_intro)
          apply (simp_all add: defaults_num1_def)
      apply (rule wbc_base)
      apply (intro exI conjI)
              apply (rule refl)
             apply (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op] simp add: fun_eq_iff)
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI)
      apply auto
      done
    subgoal
      using BHD_def is_Inl.simps(2) is_Inr.simps(2) list.set_sel(1) sumE
      by (metis (no_types, opaque_lifting))
    subgoal for d t
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (rule exI[of _ sg])
      apply (rule exI[of _ os1])
      apply (rule exI[of _ \<open>BTL (Inr (1, 0)) buf\<close>])
      apply (rule exI[of _ \<open>consumes os2 0 t d\<close>])
      apply (auto intro!: arg_cong[where f=\<open>map_op _ _ \<close>] arg_cong[where f=source_op] arg_cong[where f=\<open>lshift _\<close>] arg_cong[where f=\<open>lmap _\<close>] arg_cong[where f=\<open>\<lambda>x. lshift x _\<close>] simp add: produce_def BTL_def map_tl in_set_tlD fun_eq_iff)
      using hd_Cons_tl hd_map BHD_def list.inj_map_strong list.sel(2) list.simps(14) map_tl memb_imp_not_empty not_Cons_self sum.sel(2)
      apply (smt (verit, best))
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI)
      apply (auto elim: timely_monotone.cases simp add: list.map_ident_strong)
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI)
      apply (auto elim: timely_monotone.cases simp add: produce_def simp flip: snoc_shift)
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI)
      apply (auto elim: timely_monotone.cases)
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI)
      apply (auto elim: timely_monotone.cases)
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
              apply (rule refl)
             apply (auto simp add: produce_def fun_eq_iff split: list.splits)
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
              apply (rule refl)
             apply (auto simp add: fun_eq_iff)
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
              apply (rule refl)
             apply simp_all
      done
    subgoal
      apply (intro exI conjI[rotated, OF wbc_base])
       apply auto
      done
    subgoal
      apply (intro exI conjI[rotated, OF wbc_base])
       apply (auto simp add: fun_eq_iff)
      done
    done
next
  case SIM2
  then show ?case
    apply (elim step_map_op_elim step_source_op_elim conjE; simp; hypsubst_thin?; simp)
    subgoal for x
      apply (cases x; cases \<open>outpu os2 0\<close>; simp)
      subgoal for d t
        apply (cases \<open>input os2 0\<close>; simp)
        subgoal
          apply (cases \<open>buf (Inr (1, 1))\<close>; simp)
          subgoal
            apply (cases \<open>outpu os1 0\<close>; simp)
            subgoal
              apply (subst (asm) lmap_eq_LCons_conv)
              apply (elim exE conjE; hypsubst_thin)
              subgoal for x lxs
                apply (cases x; simp)
                subgoal for t'
                  apply (subgoal_tac \<open>ldropWhile (Not \<circ> is_Data) (es os1 0) = LCons (Data t' d) (ltl (ldropWhile (Not \<circ> is_Data) (es os1 0)))\<close>)
                   apply (subgoal_tac \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (es os1 0))\<close>)
                    apply (subgoal_tac \<open>initia (foldl
                   (\<lambda>os. case_event (\<lambda>a aa. undefined) (\<lambda>t. os\<lparr>inter := operator_state.inter os @ [(1, t, - 1)], ocaps := map_entry 1 (remove_last t) (ocaps os)\<rparr>)
                           (add_cap os 1))
                   (os1\<lparr>es := (es os1)(1 := ltl (ldropWhile (\<lambda>x. \<not> is_Data x) (es os1 1)))\<rparr>) (list_of (ltakeWhile (\<lambda>x. \<not> is_Data x) (es os1 1))))
               \<close>)
                     apply (subgoal_tac \<open>en1 (foldl
                   (\<lambda>os. case_event (\<lambda>a aa. undefined) (\<lambda>t. os\<lparr>inter := operator_state.inter os @ [(1, t, - 1)], ocaps := map_entry 1 (remove_last t) (ocaps os)\<rparr>)
                           (add_cap os 1))
                   (os1\<lparr>es := (es os1)(1 := ltl (ldropWhile (\<lambda>x. \<not> is_Data x) (es os1 1)))\<rparr>) (list_of (ltakeWhile (\<lambda>x. \<not> is_Data x) (es os1 1))))
               = id\<close>)
                  subgoal
                    apply (intro exI conjI)
                     apply (rule wstep_trans(1))
                      apply (rule step_Taus_dataflow_op_Taus_intro)
                      apply (rule rtranclp.intros(2))
                       apply (rule rtranclp.intros(2))
                        apply (rule rtranclp.intros(2))
                         apply (rule step_star_map_op)
                         apply (rule step_comp_op_L_Tau_start)
                         apply (rule step_star_map_op)
                         apply (rule step_Taus_ooo_input_op_Drop_Mint[where ops=\<open>{|1|}\<close>])
                                 apply simp_all
                         apply (unfold ooo_input_op_def ooo_input_op_logic_def)
                         apply simp
                        apply (rule step_map_op)
                         apply (rule step_Tau_comp_op_L)
                            apply (rule step_map_op)
                             apply (rule step_builder_op_Write_Some)
                                 apply (simp_all add: produce_def)
                         apply (drule outpu_foldl_ooo_input_os_Drop_Mint_es_update[where xs=\<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os1 0))\<close> and lxs=\<open>ltl (ldropWhile (Not \<circ> is_Data) (es os1 0))\<close>])
                    using set_list_of ltakeWhile_all comp_apply lset_ltakeWhileD ltakeWhile_cong zero_one
                           apply (smt (verit, best))
                          apply (rule refl)
                         apply simp
                         apply (subgoal_tac \<open>(ooo_input_os_Drop_Mint 1 :: (1, 'c, 'c, 'a, 'e) input_state_scheme \<Rightarrow> ('a, 'c) event \<Rightarrow> (1, 'c, 'c, 'a, 'e) input_state_scheme)
  = (\<lambda>os. case_event (\<lambda>a aa. undefined) (\<lambda>t. os\<lparr>inter := operator_state.inter os @ [(1, t, - 1)], ocaps := map_entry 1 (remove_last t) (ocaps os)\<rparr>) (add_cap os 1))\<close>)
                          apply simp
                    using event.case apply simp
                        apply simp
                       apply (rule step_map_op)
                        apply (rule step_Tau_comp_op_R)
                             apply (rule step_map_op)
                              apply (rule step_builder_op_Read_Some)
                                 apply auto[11]
                      apply (rule step_map_op)
                       apply (rule step_comp_op_R_Tau)
                         apply (rule step_map_op)
                          apply (rule step_builder_op_Silent)
                             apply auto[8]
                     apply (rule step_Out_dataflow_op_Out_Inr_intro)
                     apply (rule step_map_op)
                      apply (rule step_comp_op_R_Out)
                        apply (rule step_map_op)
                         apply (rule step_builder_op_Write_Some)
                             apply (simp_all add: produce_def)
                     apply simp
                    apply (rule wbc_base)
                    apply (subgoal_tac \<open>es (foldl
             (\<lambda>os. case_event (\<lambda>a aa. undefined) (\<lambda>t. os\<lparr>inter := operator_state.inter os @ [(1, t, - 1)], ocaps := map_entry 1 (remove_last t) (ocaps os)\<rparr>) (add_cap os 1))
             (os1\<lparr>es := (es os1)(1 := ltl (ldropWhile (\<lambda>x. \<not> is_Data x) (es os1 1)))\<rparr>) (list_of (ltakeWhile (\<lambda>x. \<not> is_Data x) (es os1 1))))
         1 = ltl (ldropWhile (\<lambda>x. \<not> is_Data x) (es os1 1))\<close>)
                     apply (intro exI conjI)
                             apply (rule refl)
                            apply (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op] arg_cong[where f=\<open>lmap _\<close>] simp add: fun_eq_iff)
                    using ltl_lfilter ext comp_apply ltl_lmap ltl_simps(2) apply (metis (lifting))
                     apply (rule monotone_ooo_input_os_Drop_Mint_es_update)
                        apply simp
                       apply simp
                      apply assumption
                     apply simp
                    apply (rule es_foldl_ooo_input_os_Drop_Mint[where os=\<open>(os1\<lparr>es := (es os1)(1 := ltl (ldropWhile (\<lambda>x. \<not> is_Data x) (es os1 1)))\<rparr>)\<close> and xs=\<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os1 0))\<close>])
                      apply simp
                    using set_list_of ltakeWhile_all comp_apply lset_ltakeWhileD ltakeWhile_cong zero_one
                     apply (smt (verit, best))
                    apply simp
                    done
                     apply (drule en1_foldl_ooo_input_os_Drop_Mint_es_update[where p=1 and xs=\<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os1 0))\<close> and lxs=\<open>ltl (ldropWhile (Not \<circ> is_Data) (es os1 1))\<close>])
                  using set_list_of ltakeWhile_all comp_apply lset_ltakeWhileD ltakeWhile_cong zero_one
                       apply (smt (verit, best))
                      apply (rule refl)
                     apply (subgoal_tac \<open>(ooo_input_os_Drop_Mint 1 :: (1, 'c, 'c, 'a, 'e) input_state_scheme \<Rightarrow> ('a, 'c) event \<Rightarrow> (1, 'c, 'c, 'a, 'e) input_state_scheme)
  = (\<lambda>os. case_event (\<lambda>a aa. undefined) (\<lambda>t. os\<lparr>inter := operator_state.inter os @ [(1, t, - 1)], ocaps := map_entry 1 (remove_last t) (ocaps os)\<rparr>) (add_cap os 1))\<close>)
                      apply simp
                  using event.case apply simp
                    apply (drule initia_foldl_ooo_input_os_Drop_Mint_es_update[where p=1 and xs=\<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os1 0))\<close> and lxs=\<open>ltl (ldropWhile (Not \<circ> is_Data) (es os1 1))\<close>])
                  using set_list_of ltakeWhile_all comp_apply lset_ltakeWhileD ltakeWhile_cong zero_one
                      apply (smt (verit, best))
                     apply (rule refl)
                    apply (subgoal_tac \<open>(ooo_input_os_Drop_Mint 1 :: (1, 'c, 'c, 'a, 'e) input_state_scheme \<Rightarrow> ('a, 'c) event \<Rightarrow> (1, 'c, 'c, 'a, 'e) input_state_scheme)
  = (\<lambda>os. case_event (\<lambda>a aa. undefined) (\<lambda>t. os\<lparr>inter := operator_state.inter os @ [(1, t, - 1)], ocaps := map_entry 1 (remove_last t) (ocaps os)\<rparr>) (add_cap os 1))\<close>)
                     apply simp
                  using event.case apply simp
                  using lfinite_ltakeWhile apply fastforce
                  using lfilter_eq_LCons event.case_eq_if event.collapse(1) lfilter_eq_LConsD lmap_eq_LCons_conv
                    ltl_simps(2) prod.sel(1,2) zero_one
                  apply (smt (verit, ccfv_threshold))
                  done
                done
              done
            subgoal for x'
              apply (erule conjE)
              apply (cases x'; simp)
              subgoal
                apply (intro exI conjI)
                 apply (rule wstep_trans(1))
                  apply (rule rtranclp.intros(2))
                   apply (rule rtranclp.intros(2))
                    apply (rule rtranclp.intros(2))
                     apply (rule rtranclp.intros(1))
                    apply (rule step_Tau_dataflow_op_Tau_intro)
                    apply (rule step_map_op)
                     apply (rule step_Tau_comp_op_L)
                        apply (rule step_map_op)
                         apply (rule step_builder_op_Write_Some)
                             apply auto[10]
                   apply (rule step_Tau_dataflow_op_Tau_intro)
                   apply (rule step_map_op)
                    apply (rule step_Tau_comp_op_R)
                         apply (rule step_map_op)
                          apply (rule step_builder_op_Read_Some)
                             apply auto[11]
                  apply (rule step_Tau_dataflow_op_Tau_intro)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Tau)
                     apply (rule step_map_op)
                      apply (rule step_builder_op_Silent)
                         apply auto[8]
                 apply (rule step_Out_dataflow_op_Out_Inr_intro)
                 apply (rule step_map_op)
                  apply (rule step_comp_op_R_Out)
                    apply (rule step_map_op)
                     apply (rule step_builder_op_Write_Some)
                         apply (simp_all add: produce_def)
                 apply simp
                apply (rule wbc_base)
                apply (intro exI conjI)
                        apply (rule refl)
                       apply (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op] simp add: fun_eq_iff)
                done
              done
            done
          subgoal for x'
            apply (cases x'; simp)
            subgoal for x'
              apply (cases x'; simp)
              subgoal
                apply (intro exI conjI)
                 apply (rule wstep_trans(1))
                  apply (rule rtranclp.intros(2))
                   apply (rule rtranclp.intros(2))
                    apply (rule rtranclp.intros(1))
                   apply (rule step_Tau_dataflow_op_Tau_intro)
                   apply (rule step_map_op)
                    apply (rule step_Tau_comp_op_R)
                         apply (rule step_map_op)
                          apply (rule step_builder_op_Read_Some)
                             apply (auto simp add: BHD_def)[11]
                  apply (rule step_Tau_dataflow_op_Tau_intro)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Tau)
                     apply (rule step_map_op)
                      apply (rule step_builder_op_Silent)
                         apply auto[8]
                 apply (rule step_Out_dataflow_op_Out_Inr_intro)
                 apply (rule step_map_op)
                  apply (rule step_comp_op_R_Out)
                    apply (rule step_map_op)
                     apply (rule step_builder_op_Write_Some)
                         apply (simp_all add: produce_def)
                 apply simp
                apply (rule wbc_base)
                apply (intro exI conjI)
                        apply (rule refl)
                       apply (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op] simp add: fun_eq_iff BTL_def)
                done
              done
            done
          done
        subgoal
          apply (intro exI conjI)
           apply (rule wstep_trans_base(1))
            apply (rule step_Tau_dataflow_op_Tau_intro)
            apply (rule step_map_op)
             apply (rule step_comp_op_R_Tau)
               apply (rule step_map_op)
                apply (rule step_builder_op_Silent)
                   apply auto[8]
           apply (rule step_Out_dataflow_op_Out_Inr_intro)
           apply (rule step_map_op)
            apply (rule step_comp_op_R_Out)
              apply (rule step_map_op)
               apply (rule step_builder_op_Write_Some)
                   apply (simp_all add: produce_def split: prod.splits)
          apply simp
          apply (rule wbc_base)
          apply (intro exI conjI)
                  apply (rule refl)
                 apply (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op] simp add: fun_eq_iff)
          done
        done
      subgoal
        apply (intro exI conjI)
         apply (rule step_wstep)
         apply (rule step_Out_dataflow_op_Out_Inr_intro)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Out)
            apply (rule step_map_op)
             apply (rule step_builder_op_Write_Some)
                 apply simp_all
         apply simp
        apply (rule wbc_base)
        apply (intro exI conjI)
                apply (rule refl)
               apply (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op] simp add: fun_eq_iff)
        done
      done
    done
qed

end