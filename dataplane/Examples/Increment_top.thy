theory Increment_top

imports
  Ooo_Input_top
  Dataplane.MyProduct_Instances
  Source_op
begin

corec increment_top where
  \<open>increment_top incr os = choice3
  (Choice (cimage (\<lambda>p. Read (Some p) (\<lambda>x. case x of
    Inr (d, t) \<Rightarrow> increment_top incr (produce (consume os p t 1) (Cap (t + incr p) p) [d])
  | _ \<Rightarrow> \<oslash>)) c\<UU>))
  (Choice (cimage (\<lambda>p. case outpu os p of
    x # xs \<Rightarrow> send_output (increment_top incr (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>)) p x)
    (cfilter (\<lambda>p. outpu os p \<noteq> []) c\<UU>)))
  (let (os', st) = obtain_progress os
  in send_progress (increment_top incr os') st)\<close>

lemma step_increment_top_elim:
  assumes \<open>step io (increment_top incr os) op\<close>
  obtains p d t where \<open>io = Inp (Some p) (Inr (d, t))\<close>
    \<open>op = increment_top incr (produce (consume os p t 1) (Cap (t + incr p) p) [d])\<close> \<open>p \<notin> defaults\<close>
  | p x where \<open>io = Inp (Some p) (Inl x)\<close> \<open>op = \<oslash>\<close> \<open>p \<notin> defaults\<close>
  | p x xs where \<open>io = Out (Some p) (Inr x)\<close> \<open>outpu os p = x # xs\<close>
    \<open>op = increment_top incr (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>)\<close> \<open>p \<notin> defaults\<close>
  | os' st where \<open>io = Out None (Inl (Inl st))\<close> \<open>obtain_progress os = (os', st)\<close> \<open>op = increment_top incr os'\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) increment_top.code)
  apply (cases io)
    apply (auto 0 5 split: sum.splits list.splits)
  done

lemma step_increment_top_Read_R[intro]:
  assumes \<open>op = increment_top incr (produce (consume os p t 1) (Cap (t + incr p) p) [d])\<close> \<open>p \<notin> defaults\<close>
  shows \<open>step (Inp (Some p) (Inr (d, t))) (increment_top incr os) op\<close>
proof -
  let ?f = \<open>\<lambda>x. case x of
      Inr (d, t) \<Rightarrow> increment_top incr (produce (consume os p t 1) (Cap (t + incr p) p) [d])
    | Inl _ \<Rightarrow> \<oslash>\<close>
  have \<open>Read (Some p) ?f |\<in>| choices (increment_top incr os)\<close>
    using assms(2) by (subst (2) increment_top.code) auto
  moreover have \<open>op = ?f (Inr (d, t))\<close>
    using assms(1) by simp
  ultimately show ?thesis
    by blast
qed

lemma step_increment_top_Write_Some[intro]:
  \<open>outpu os p = x # xs \<Longrightarrow> op = increment_top incr (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>) \<Longrightarrow> p \<notin> defaults \<Longrightarrow>
  step (Out (Some p) (Inr x)) (increment_top incr os) op\<close>
  by (subst increment_top.code) force

lemma step_increment_top_Write_None[intro]:
  \<open>(os', st) = obtain_progress os \<Longrightarrow> op = increment_top incr os' \<Longrightarrow>
  step (Out None (Inl (Inl st))) (increment_top incr os) op\<close>
  by (subst increment_top.code) auto

abbreviation inp_op where
  \<open>inp_op os caps ins \<equiv>
  map_op (case_option (Inl (0 :: 2)) (\<lambda>p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda>p. Inr (0, p)))
  (ooo_input_top os caps ins)\<close>

abbreviation incr_op where
  \<open>incr_op incr os \<equiv>
  map_op (case_option (Inl (1 :: 2)) (\<lambda>p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda>p. Inr (1, p)))
  (increment_top incr os)\<close>

abbreviation inp_incr_op where
  \<open>inp_incr_op os1 caps ins buf incr os2 \<equiv>
  map_op (case_sum id id) (case_sum id id)
  (comp_op [Inr (0 :: 2, 0 :: 1) \<mapsto> Inr (1 :: 2, 0 :: 1)] buf (inp_op os1 caps ins)
    (incr_op incr os2))\<close>

abbreviation inp_incr_edges where
  \<open>inp_incr_edges \<equiv> (\<lambda>l. if l = Loc (0 :: 2) (Src (0 :: 1)) then [Loc (1 :: 2) (Trg (0 :: 1))] else [])\<close>

abbreviation inp_incr_summary where
  \<open>inp_incr_summary \<equiv> (\<lambda>l1 l2.
  if l1 = Loc (0 :: 2) (Src (0 :: 1)) \<and> l2 = Loc (1 :: 2) (Trg (0 :: 1))
  then antichain {0}
  else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0)
  then antichain {0}
  else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
  then antichain {0}
  else {}\<^sub>A)\<close>

lemma
  \<open>summ sg = inp_incr_summary \<Longrightarrow>
  \<forall>x \<in> set (buf (Inr (1, 0))). is_Inr x \<Longrightarrow>
  dataflow_op sg (inp_incr_op os1 caps ins buf incr os2)
  \<approx> map_op (\<lambda>(p :: 1). (1, p)) (\<lambda>p. (1, p))
    (source_op ((\<lambda>p. outpu os2 p @@- lmap (\<lambda>(d, t). (d, t + incr p))
      ((map projr (buf (Inr (1, 0))) @ outpu os1 p) @@- lmap (\<lambda>x. case x of Data t d \<Rightarrow> (d, t)) (lfilter is_Data (ins p))))))\<close>
proof (coinduction arbitrary: sg os1 caps ins buf os2 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
    apply (elim step_dataflow_op_elim step_map_op_elim step_comp_op_elim step_ooo_input_top_elim step_increment_top_elim conjE; simp split: if_splits; hypsubst_thin?; simp)
    subgoal
      apply (intro exI conjI[rotated])
       apply (rule wbc_base)
       apply blast
      apply (rule step_wstep)
      apply (auto simp add: fun_eq_iff)
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI)
      apply auto
      done
    subgoal for d t
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (rule exI[of _ sg])
      apply (rule exI[of _ os1])
      apply (rule exI[of _ caps])
      apply (rule exI[of _ ins])
      apply (rule exI[of _ \<open>BTL (Inr (1, 0)) buf\<close>])
      apply (rule exI[of _ \<open>produce (consume os2 0 t 1) (Cap (t + incr 0) 0) [d]\<close>])
      apply (simp add: produce_def BTL_def map_tl in_set_tlD)
      apply (rule arg_cong[where f=\<open>map_op (Pair 1) (Pair 1)\<close>])
      apply (rule arg_cong[where f=source_op])
      apply (simp add: fun_eq_iff)
      apply (rule arg_cong[where f=\<open>\<lambda>x. outpu os2 1 @@- x\<close>])
      apply (simp add: lmap_eq_LCons_conv)
      apply (rule exI[of _ \<open>(tl (map projr (buf (Inr (1, 0)))) @ outpu os1 0) @@- lmap (\<lambda>x. case x of Data t d \<Rightarrow> (d, t)) (lfilter is_Data (ins 0))\<close>])
      apply simp
      apply (subst lshift.simps(2)[symmetric])
      apply (subst append_Cons[symmetric])
      apply (smt (verit, del_insts) BHD_def in_set_simps(3) list.exhaust_sel list.inj_map_strong list.map_sel(1)
          list.sel(2) map_tl not_Cons_self2 sum.sel(2))
      done
    subgoal
      using BHD_def list.set_sel(1) is_Inr.simps(2)
      apply (metis (no_types, opaque_lifting))
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI)
      apply (auto simp add: lnull_def produce_def simp flip: snoc_shift)
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI)
      apply (auto simp add: produce_def simp flip: append_assoc)
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
         apply (rule refl)
        apply auto
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
         apply (rule refl)
        apply auto
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
         apply (rule refl)
        apply auto
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
         apply (rule refl)
        apply auto
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI conjI)
         apply (rule refl)
        apply auto
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI)
      apply auto
      done
    subgoal
      apply (intro exI conjI)
       apply (rule rtranclp.intros(1))
      apply (rule wbc_base)
      apply (intro exI)
      apply auto
      done
    done
next
  case SIM2
  then show ?case
    apply (elim step_map_op_elim step_source_op_elim conjE; simp; hypsubst_thin?; simp)
    subgoal for x lxs
      apply (cases x; cases \<open>outpu os2 0\<close>; simp)
      subgoal for d t
        apply (cases \<open>buf (Inr (1, 1))\<close>; simp)
        subgoal
          apply (cases \<open>outpu os1 0\<close>; simp)
          subgoal
            apply (subst (asm) lmap_eq_LCons_conv)
            apply (elim exE conjE; hypsubst_thin)
            subgoal for x xs'
              apply (cases x; simp)
              subgoal for t'
                apply (intro exI conjI)
                 apply (rule wstep_trans(1))
                  apply (rule step_Taus_dataflow_op_Taus_intro)
                  apply (rule rtranclp.intros(2))
                   apply (rule rtranclp.intros(2))
                    apply (rule step_star_map_op)
                    apply (rule step_comp_op_L_Tau_start)
                    apply (rule step_star_map_op)
                    apply (rule step_Taus_ooo_input_top[where p=1])
                          apply (simp_all add: split_pairs snd_foldl)
                using lfinite_ltakeWhile apply fastforce
                    apply (subgoal_tac \<open>ldropWhile (Not \<circ> is_Data) (ins 0) = LCons (Data t' d) (ltl (ldropWhile (Not \<circ> is_Data) (ins 0)))\<close>)
                     apply fastforce
                using lfilter_eq_LCons event.case_eq_if event.collapse(1) lfilter_eq_LConsD lmap_eq_LCons_conv
                  ltl_simps(2) prod.sel(1,2)
                    apply (smt (verit, ccfv_threshold) zero_one)
                   apply (rule step_map_op)
                    apply (rule step_Tau_comp_op_L)
                       apply (rule step_map_op)
                        apply (rule step_ooo_input_top_Write_Some)
                          apply (simp_all add: produce_def)
                   apply (drule outpu_snd_foldl_ooo_input_os_caps_Watermark_Nil[where os=os1])
                   apply fastforce
                  apply (rule step_map_op)
                   apply (rule step_Tau_comp_op_R)
                        apply (rule step_map_op)
                         apply (rule step_increment_top_Read_R)
                          apply simp_all
                  apply simp
                 apply (rule step_Out_dataflow_op_Out_Inr_intro)
                 apply (rule step_map_op)
                  apply (rule step_comp_op_R_Out)
                    apply (rule step_map_op)
                     apply (rule step_increment_top_Write_Some)
                       apply (simp_all add: produce_def)
                apply (rule wbc_base)
                apply (intro exI conjI)
                   apply (auto intro!: arg_cong[where f=\<open>map_op (Pair 1) (Pair 1)\<close>] arg_cong[where f=source_op] arg_cong[where f=\<open>lmap (\<lambda>z. case z of (d, t) \<Rightarrow> (d, t -+- incr 1))\<close>] simp add: fun_eq_iff)
                using ltl_lfilter ext comp_apply ltl_lmap ltl_simps(2) apply (metis (lifting))
                done
              done
            done
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
                  apply (rule step_Tau_comp_op_L)
                     apply (rule step_map_op)
                      apply (rule step_ooo_input_top_Write_Some)
                        apply auto[8]
                apply (rule step_Tau_dataflow_op_Tau_intro)
                apply (rule step_map_op)
                 apply (rule step_Tau_comp_op_R)
                      apply (rule step_map_op)
                       apply (rule step_increment_top_Read_R)
                        apply simp_all
                apply simp
               apply (rule step_Out_dataflow_op_Out_Inr_intro)
               apply (rule step_map_op)
                apply (rule step_comp_op_R_Out)
                  apply (rule step_map_op)
                   apply (rule step_increment_top_Write_Some)
                     apply (simp_all add: produce_def)
              apply (rule wbc_base)
              apply (intro exI conjI)
                 apply (auto intro!: arg_cong[where f=\<open>map_op (Pair 1) (Pair 1)\<close>] arg_cong[where f=source_op])
              done
            done
          done
        subgoal for x' xs'
          apply (cases x'; simp)
          subgoal for x'
            apply (cases x'; simp)
            subgoal for t'
              apply (intro exI conjI)
               apply (rule wstep_trans_base(1))
                apply (rule step_Tau_dataflow_op_Tau_intro)
                apply (rule step_map_op)
                 apply (rule step_Tau_comp_op_R)
                      apply (rule step_map_op)
                       apply (rule step_increment_top_Read_R)
                        apply (simp_all add: BHD_def)
                apply simp
               apply (rule step_Out_dataflow_op_Out_Inr_intro)
               apply (rule step_map_op)
                apply (rule step_comp_op_R_Out)
                  apply (rule step_map_op)
                   apply (rule step_increment_top_Write_Some)
                     apply (simp_all add: produce_def)
              apply (rule wbc_base)
              apply (rule exI[of _ sg])
              apply (rule exI[of _ os1])
              apply (rule exI[of _ caps])
              apply (rule exI[of _ ins])
              apply (rule exI[of _ \<open>BTL (Inr (1, 1)) buf\<close>])
              apply (rule exI[of _ \<open>os2\<lparr>consu := consu os2 @ [(1, t', 1)], produ := produ os2 @ [(1, t, 1)],
                          outpu := (outpu os2)(1 := [])\<rparr>\<close>])
              apply (auto intro!: arg_cong[where f=\<open>map_op (Pair 1) (Pair 1)\<close>] arg_cong[where f=source_op] simp add: BTL_def)
              done
            done
          done
        done
      subgoal for xs'
        apply (intro exI conjI)
         apply (rule step_wstep)
         apply (rule step_Out_dataflow_op_Out_Inr_intro)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Out)
            apply (rule step_map_op)
             apply (rule step_increment_top_Write_Some)
               apply simp_all
        apply (rule wbc_base)
        apply (intro exI conjI)
           apply (auto intro!: arg_cong[where f=\<open>map_op (Pair 1) (Pair 1)\<close>] arg_cong[where f=source_op])
        done
      done
    done
qed

end
