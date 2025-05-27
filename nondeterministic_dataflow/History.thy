theory History

imports
 "BNA_Operators"
begin

section \<open>History model\<close>

definition \<open>lproject f g vios p =
  lmap vdata (lfilter (\<lambda>vio. case vio of VInp q _ \<Rightarrow> f p q | VOut q _ \<Rightarrow> g p q) vios)\<close>

abbreviation \<open>extract_inputs \<equiv> lproject (=) \<bottom>\<close>
abbreviation \<open>extract_outputs \<equiv> lproject \<bottom> (=)\<close>

definition \<open>history op lxs lys =
  (\<exists>vios. wtraced op vios \<and>
  (\<forall>p. lprefix (extract_inputs vios p) (lxs p)) \<and> lys = extract_outputs vios)\<close>

abbreviation history_equiv (infix \<open>\<equiv>\<^sub>h\<close> 40) where
  \<open>op\<^sub>1 \<equiv>\<^sub>h op\<^sub>2 \<equiv> history op\<^sub>1 = history op\<^sub>2\<close>

lemma history_equiv_refl:
  \<open>op \<equiv>\<^sub>h op\<close>
  by simp

lemma history_equiv_sym:
  \<open>op\<^sub>1 \<equiv>\<^sub>h op\<^sub>2 \<longleftrightarrow> op\<^sub>2 \<equiv>\<^sub>h op\<^sub>1\<close>
  by auto

lemma history_equiv_trans:
  \<open>op\<^sub>1 \<equiv>\<^sub>h op\<^sub>2 \<Longrightarrow> op\<^sub>2 \<equiv>\<^sub>h op\<^sub>3 \<Longrightarrow> op\<^sub>1 \<equiv>\<^sub>h op\<^sub>3\<close>
  by auto

lemma wtrace_equiv_history_equiv:
  \<open>op\<^sub>1 \<equiv>\<^sub>t op\<^sub>2 \<Longrightarrow> op\<^sub>1 \<equiv>\<^sub>h op\<^sub>2\<close>
  unfolding wtraces_def history_def
  by blast

datatype (discs_sels) ('m, 'd) source_op_aux =
  source_Write_aux \<open>'m \<Rightarrow> 'd llist\<close> 'm 'd

abbreviation eval_source_op_aux where
  \<open>eval_source_op_aux c aux \<equiv> (case aux of
    source_Write_aux lxs q x \<Rightarrow> Write (c lxs) q x)\<close>

corec source_op :: \<open>('m :: {countable, defaults} \<Rightarrow> 'd llist) \<Rightarrow> (0, 'm, 'd) op\<close> where
  \<open>source_op lxs = Choice (cimage (eval_source_op_aux source_op)
    (cimage (\<lambda>p. source_Write_aux (lxs(p := ltl (lxs p))) p (lhd (lxs p)))
      (cfilter (\<lambda>p. lxs p \<noteq> LNil) c\<UU>)))\<close>

lemma source_op_code:
  \<open>source_op lxs = Choice
    (cimage (\<lambda>p. Write (source_op (lxs(p := ltl (lxs p)))) p (lhd (lxs p)))
      (cfilter (\<lambda>p. lxs p \<noteq> LNil) c\<UU>))\<close>
  by (subst source_op.code) (auto simp add: cset.map_comp)

lemma source_op_reads:
  \<open>sub_op (Read p f) (source_op lxs) n \<Longrightarrow> False\<close>
proof (induct p \<open>source_op lxs\<close> arbitrary: lxs rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case by (subst (asm) source_op_code, simp)
next
  case (Read2 p p' f x d g)
  then show ?case by (subst (asm) source_op_code, simp)
next
  case (Write p p' op' x d g)
  then show ?case by (subst (asm) source_op_code, simp)
next
  case (Silent p op' d)
  then show ?case by (subst (asm) source_op_code, simp)
next
  case (Choice p ops d g)
  then show ?case by (subst (asm) (2) source_op_code, simp; force)
qed

lemma source_op_writes:
  \<open>sub_op (Write op p x) (source_op lxs) n \<Longrightarrow> p \<in> UNIV - defaults\<close>
proof (induct p \<open>source_op lxs\<close> arbitrary: lxs rule: sub_op_Write_induct)
  case (Read p p' f x op2 y d)
  then show ?case by (subst (asm) source_op_code, simp)
next
  case (Write1 p p' op' x op2 y d)
  then show ?case by (subst (asm) source_op_code, simp)
next
  case (Silent p op' op2 y d)
  then show ?case by (subst (asm) source_op_code, simp)
next
  case (Choice p op2 y d ops)
  then show ?case by (subst (asm) (2) source_op_code, simp; force)
next
  case (Write2 p op' x)
  then show ?case by (subst (asm) source_op_code, simp)
qed

lemma inputs_source_op:
  \<open>inputs (source_op lxs) = {}\<close>
  using source_op_reads inputs_sub_op_Read
  by fast

lemma outputs_source_op:
  \<open>outputs (source_op lxs) \<subseteq> UNIV - defaults\<close>
  apply (intro subsetI)
  using source_op_writes by (metis outputs_sub_op_Write)
lemma outputs_source_op_alt:
  \<open>\<forall>x \<in> outputs (source_op lxs). x \<notin> defaults\<close>
  using outputs_source_op[unfolded subset_eq, simplified] by fast
lemma outputs_source_op_dest:
  \<open>x \<in> outputs (source_op lxs) \<Longrightarrow> x \<notin> defaults\<close>
  using outputs_source_op_alt by blast

lemma inputs_source_op_scomp_op:
  \<open>inputs (source_op lxs \<bullet> op) = {}\<close>
  unfolding scomp_op_def
  by (metis empty_iff equals0I image_is_empty inputs_scomp_op_le_dest inputs_source_op op.set_map(1))

lemma outputs_source_op_scomp_op:
  \<open>outputs (source_op lxs \<bullet> op) \<subseteq> outputs op\<close>
  unfolding scomp_op_def
  using outputs_scomp_op_le_dest
  by (smt (verit, ccfv_threshold) image_iff op.set_map(2) subsetI sum.sel(2))

lemma wtraced_source_op:
  \<open>wtraced op lxs \<Longrightarrow>
  \<exists>vios. wtraced (source_op (extract_inputs lxs) \<bullet> op) vios \<and> extract_outputs vios = extract_outputs lxs\<close>
  oops

lemma wtrace_equiv_source_op:
  \<open>op\<^sub>1 \<equiv>\<^sub>t op\<^sub>2 \<Longrightarrow> source_op lxs \<bullet> op\<^sub>1 \<equiv>\<^sub>t source_op lxs \<bullet> op\<^sub>2\<close>
  oops

definition \<open>history' op lxs =
  {lys. \<exists>vios. wtraced (source_op lxs \<bullet> op) vios \<and> lys = extract_outputs vios}\<close>

lemma wtrace_equiv_history'_equiv:
  \<open>op\<^sub>1 \<equiv>\<^sub>t op\<^sub>2 \<Longrightarrow> history' op\<^sub>1 = history' op\<^sub>2\<close>
  oops

lemma history_history':
  \<open>op\<^sub>1 \<equiv>\<^sub>h op\<^sub>2 \<longleftrightarrow> history' op\<^sub>1 = history' op\<^sub>2\<close>
  oops

section \<open>Time anomaly\<close>

corec suc_op :: \<open>(1, 1, nat) op\<close> where
  \<open>suc_op = Read 1 (\<lambda>x. Write suc_op 1 (Suc x))\<close>

lemma step_suc_op_elim:
  assumes \<open>step io suc_op op\<close>
  obtains x where \<open>io = Inp 1 x\<close> \<open>op = Write suc_op 1 (Suc x)\<close>
  apply atomize_elim
  using assms
  apply (rule step_choicesE)
    apply (subst (asm) suc_op.code, simp)+
  done

corec dup_op :: \<open>(1, 1, nat) op\<close> where
  \<open>dup_op = Read 1 (\<lambda>x. Write (Write dup_op 1 x) 1 x)\<close>

lemma step_dup_op_elim:
  assumes \<open>step io dup_op op\<close>
  obtains x where \<open>io = Inp 1 x\<close> \<open>op = Write (Write dup_op 1 x) 1 x\<close>
  apply atomize_elim
  using assms
  apply (rule step_choicesE)
    apply (subst (asm) dup_op.code, simp)+
  done

corec twobuf_op :: \<open>(1, 1, nat) op\<close> where
  \<open>twobuf_op = Read 1 (\<lambda>x. Read 1 (\<lambda>y. Write (Write twobuf_op 1 y) 1 x))\<close>

lemma step_twobuf_op_elim:
  assumes \<open>step io twobuf_op op\<close>
  obtains x where \<open>io = Inp 1 x\<close> \<open>op = Read 1 (\<lambda>y. Write (Write twobuf_op 1 y) 1 x)\<close>
  apply atomize_elim
  using assms
  apply (rule step_choicesE)
    apply (subst (asm) twobuf_op.code, simp)+
  done

abbreviation \<open>f_op \<equiv> (dup_op \<parallel> suc_op \<bullet> dup_op) \<bullet> \<V> \<bullet> twobuf_op \<bullet> \<C>\<close>
abbreviation \<open>f'_op \<equiv> (dup_op \<parallel> suc_op \<bullet> dup_op) \<bullet> \<V> \<bullet> \<I> \<bullet> \<C>\<close>

simproc_setup num1_eq (\<open>x :: 1\<close>) =
  \<open>K (K (fn ct =>
    if Thm.term_of ct aconv @{term \<open>1 :: 1\<close>} then NONE
    else SOME (mk_meta_eq @{thm num1_eq1})))\<close>

lemma history_equiv_f_f':
  \<open>f_op \<equiv>\<^sub>h f'_op\<close>
  unfolding history_def feedback_op_def pcomp_op_def scomp_op_def
  apply (simp add: fun_eq_iff)
  apply (intro allI)
  subgoal for lxs lys
    apply (rule iffI)
    subgoal
      apply (elim exE conjE)
      subgoal for vios
        apply (intro exI[of _ vios] conjI)
        subgoal premises prems
          using prems(1)
          apply coinduction
          apply (cases vios; hypsubst_thin)
          subgoal
            by blast
          subgoal for vio vios'
            sorry
          done
        subgoal
          by assumption
        subgoal
          by assumption
        done
      done
    subgoal
      sorry
    done
  sorry

lemma history_f'_11:
  \<open>history f'_op (case_sum (\<lambda>_. LCons 1 LNil) (\<lambda>_. LNil)) (case_sum (\<lambda>_. LCons 1 LNil) (\<lambda>_. LNil))\<close>
  unfolding history_def pcomp_op_def scomp_op_def
  apply (rule exI[of _ \<open>LCons (VInp (Inl 1) 1) (LCons (VOut (Inl 1) 1) LNil)\<close>])
  apply (intro conjI)
  subgoal
    apply (rule wtraced.Step)
     apply simp
     apply (rule step_wstep)
     apply (rule step_map_op)
      apply (rule step_comp_op_L_Inp)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Inp)
              apply (rule step_comp_op_L_Inp)
                apply (subst dup_op.code)
                apply blast
               apply simp_all
    apply (rule wtraced.Step)
     apply simp
     apply (rule wstep_trans(1))
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_comp_op_L_Tau)
                 apply (rule step_map_op)
                  apply (rule step_Tau_comp_op_L)
                     apply (rule step_comp_op_L_Out)
                        apply blast
                       apply simp_all
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_comp_op_L_Tau)
                apply (rule step_map_op)
                 apply (rule step_Tau_comp_op_R)
                      apply (rule step_merge_op_Read_L)
                       apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_comp_op_L_Tau)
            apply (rule step_map_op)
             apply (rule step_Tau_comp_op_L)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Out)
                   apply (rule step_merge_op_Write_L)
                      apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Tau)
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_R)
                 apply (rule step_id_op_Read)
                  apply (simp_all add: defaults_num1_def)
       apply (rule step_map_op)
        apply (rule step_Tau_comp_op_L)
           apply (rule step_map_op)
            apply (rule step_comp_op_R_Out)
              apply (rule step_id_op_Write)
                 apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_Tau_comp_op_R)
            apply (rule step_acopy_op_Read)
             apply (simp_all add: defaults_num1_def)
     apply (rule step_map_op)
      apply (rule step_comp_op_R_Out)
        apply (rule step_acopy_op_WriteL)
           apply (simp_all add: defaults_num1_def BENQ_diff_access BHD_def)
    apply (rule wtraced.Nil)
    done
  subgoal
    by (simp add: lproject_def)
  subgoal
    by (auto simp: lproject_def split: sum.splits)
  done

lemma no_history_f_feedback_12:
  \<open>history (f_op \<up>) (\<lambda>_. LCons 1 LNil) (\<lambda>_. LCons 1 (LCons 2 LNil)) \<Longrightarrow> False\<close>
  unfolding history_def feedback_op_def pcomp_op_def scomp_op_def
  apply (elim exE conjE)
  subgoal for vios
    apply (cases vios; hypsubst_thin)
    subgoal premises prems
      using prems(3) lproject_def
      by (metis lfilter_LNil llist.distinct(1) lmap_eq_LNil)
    subgoal for vio vios'
      apply (subgoal_tac \<open>vio = VInp 1 1\<close>; hypsubst_thin?)
      subgoal
        apply (cases vios'; hypsubst_thin)
        subgoal premises prems
          using prems(3)
          apply -
          apply (drule fun_cong[of _ _ 1])
          by (simp add: lproject_def)
        subgoal for vio' vios''
          apply (cases vio'; hypsubst_thin)
          subgoal premises prems
            using prems(2)
            apply -
            apply (drule spec[of _ 1])
            by (simp add: lproject_def)
          subgoal
            sorry
          done
        done
      subgoal
        apply (cases vio; hypsubst_thin)
        subgoal premises prems
          using prems(2)
          apply -
          apply (drule spec[of _ 1])
          by (simp add: lproject_def)
        subgoal premises prems for _ x
          using prems(1)
          apply -
          apply (rule FalseE)
          apply (erule wtraced.cases; hypsubst_thin)
          subgoal
            by blast
          subgoal
            apply simp
            apply (erule conjE)
            apply hypsubst_thin
            apply (unfold wstep_def)
            apply simp
            apply (erule relcomppE)+
            apply (erule converse_rtranclpE)
             apply hypsubst_thin
            subgoal premises prems'
              using prems'(2)
              by (auto elim!: step_map_op_elim step_loop_op_elim step_comp_op_elim step_dup_op_elim step_suc_op_elim step_merge_op_elim step_twobuf_op_elim step_acopy_op_elim)
            subgoal premises prems'
              using prems'(4)
              apply (auto elim!: step_map_op_elim step_loop_op_elim step_comp_op_elim step_dup_op_elim step_suc_op_elim step_merge_op_elim step_twobuf_op_elim step_acopy_op_elim)[1]
              by (smt (verit) Inr_Inl_False in_feedback_wire mem_Collect_eq num1_eq1 ran_def sum.case_eq_if)
            done
          done
        done
      done
    done
  done

lemma history_f'_feedback_12:
  \<open>history (f'_op \<up>) (\<lambda>_. LCons 1 LNil) (\<lambda>_. LCons 1 (LCons 2 LNil))\<close>
  unfolding history_def feedback_op_def pcomp_op_def scomp_op_def
  apply (rule exI[of _ \<open>LCons (VInp 1 1) (LCons (VOut 1 1) (LCons (VOut 1 2) LNil))\<close>])
  apply (intro conjI)
  subgoal
    apply (rule wtraced.Step)
     apply simp
     apply (rule step_wstep)
     apply (rule step_map_op)
      apply (rule step_Inp_loop_op)
       apply (rule step_map_op)
        apply (rule step_comp_op_L_Inp)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Inp)
             apply (rule step_map_op)
              apply (rule step_comp_op_L_Inp)
                apply (rule step_comp_op_L_Inp)
                  apply (subst dup_op.code)
                  apply blast
                 apply simp_all
     apply (simp add: ran_def sum.case_eq_if)
    apply (rule wtraced.Step)
     apply simp
     apply (rule wstep_trans(1))
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_Tau_loop_op)
             apply (rule step_map_op)
              apply (rule step_comp_op_L_Tau)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Tau)
                   apply (rule step_map_op)
                    apply (rule step_Tau_comp_op_L)
                       apply (rule step_comp_op_L_Out)
                        apply blast
                        apply simp_all
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Tau)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Tau)
                  apply (rule step_map_op)
                   apply (rule step_Tau_comp_op_R)
                        apply (rule step_merge_op_Read_L)
                        apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_L)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Out)
                     apply (rule step_merge_op_Write_L)
                        apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_Tau_comp_op_R)
                   apply (rule step_id_op_Read)
                    apply (simp_all add: defaults_num1_def)
       apply (rule step_map_op)
        apply (rule step_Tau_loop_op)
         apply (rule step_map_op)
          apply (rule step_Tau_comp_op_L)
             apply (rule step_map_op)
              apply (rule step_comp_op_R_Out)
                apply (rule step_id_op_Write)
                   apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_Tau_loop_op)
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply (rule step_acopy_op_Read)
               apply (simp_all add: defaults_num1_def)
     apply (rule step_map_op)
      apply (rule step_Out_loop_op)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_acopy_op_WriteL)
              apply (simp_all add: defaults_num1_def BENQ_diff_access BHD_def)
     apply simp
    apply (rule wtraced.Step)
     apply simp
     apply (rule wstep_trans(1))
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(2))
             apply (rule rtranclp.intros(2))
              apply (rule rtranclp.intros(2))
               apply (rule rtranclp.intros(2))
                apply (rule rtranclp.intros(1))
               apply (rule step_map_op)
                apply (rule step_Out_Tau_loop_op)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Out)
                     apply (rule step_acopy_op_WriteR)
                        apply (simp_all add: defaults_num1_def BENQ_diff_access BTL_def)
               apply simp
              apply (rule step_map_op)
               apply (rule step_Inp_Tau_loop_op)
                   apply (rule step_map_op)
                    apply (rule step_comp_op_L_Inp)
                      apply (rule step_map_op)
                       apply (rule step_comp_op_L_Inp)
                        apply (rule step_map_op)
                        apply (rule step_comp_op_L_Inp)
                        apply (rule step_comp_op_R_Inp)
                        apply (rule step_map_op)
                        apply (rule step_comp_op_L_Inp)
                        apply (subst suc_op.code)
                        apply blast
                        apply (simp_all add: defaults_num1_def)
               apply (meson sum.simps(6) ranI)
              apply simp
             apply (rule step_map_op)
              apply (rule step_Tau_loop_op)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Tau)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_L_Tau)
                     apply (rule step_map_op)
                      apply (rule step_comp_op_L_Tau)
                        apply (rule step_comp_op_R_Tau)
                        apply (rule step_map_op)
                        apply (rule step_Tau_comp_op_L)
                        apply blast
                        apply simp_all
            apply (rule step_map_op)
             apply (rule step_Tau_loop_op)
              apply (rule step_map_op)
               apply (rule step_comp_op_L_Tau)
                 apply (rule step_map_op)
                  apply (rule step_comp_op_L_Tau)
                    apply (rule step_map_op)
                     apply (rule step_comp_op_L_Tau)
                       apply (rule step_comp_op_R_Tau)
                        apply (rule step_map_op)
                        apply (rule step_Tau_comp_op_R)
                        apply (subst dup_op.code)
                        apply blast
                        apply simp_all
           apply (rule step_map_op)
            apply (rule step_Tau_loop_op)
             apply (rule step_map_op)
              apply (rule step_comp_op_L_Tau)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Tau)
                   apply (rule step_map_op)
                    apply (rule step_Tau_comp_op_L)
                       apply (rule step_comp_op_R_Out)
                        apply (rule step_map_op)
                        apply (rule step_comp_op_R_Out)
                        apply blast
                        apply simp_all
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Tau)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Tau)
                  apply (rule step_map_op)
                   apply (rule step_Tau_comp_op_R)
                        apply (rule step_merge_op_Read_R)
                        apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_L)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Out)
                     apply (rule step_merge_op_Write_R)
                        apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_Tau_comp_op_R)
                   apply (rule step_id_op_Read)
                    apply (simp_all add: defaults_num1_def)
       apply (rule step_map_op)
        apply (rule step_Tau_loop_op)
         apply (rule step_map_op)
          apply (rule step_Tau_comp_op_L)
             apply (rule step_map_op)
              apply (rule step_comp_op_R_Out)
                apply (rule step_id_op_Write)
                   apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_Tau_loop_op)
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply (rule step_acopy_op_Read)
               apply (simp_all add: defaults_num1_def)
     apply (rule step_map_op)
      apply (rule step_Out_loop_op)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_acopy_op_WriteL)
              apply (simp_all add: defaults_num1_def BENQ_diff_access BHD_def)
     apply simp
    apply (rule wtraced.Nil)
    done
  subgoal
    by (simp add: lproject_def)
  subgoal
    by (auto simp: lproject_def)
  done

(*
lemma history_f'_feedback_1223:
  \<open>history (f'_op \<up>) (\<lambda>_. LCons 1 LNil) (\<lambda>_. LCons 1 (LCons 2 (LCons 2 (LCons 3 LNil))))\<close>
  unfolding history_def feedback_op_def pcomp_op_def scomp_op_def
  apply (rule exI[of _ \<open>LCons (VInp 1 1) (LCons (VOut 1 1) (LCons (VOut 1 2) (LCons (VOut 1 2) (LCons (VOut 1 3) LNil))))\<close>])
  apply (intro conjI)
  subgoal
    apply (rule wtraced.Step)
     apply simp
     apply (rule step_wstep)
     apply (rule step_map_op)
      apply (rule step_Inp_loop_op)
       apply (rule step_map_op)
        apply (rule step_comp_op_L_Inp)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Inp)
             apply (rule step_map_op)
              apply (rule step_comp_op_L_Inp)
                apply (rule step_comp_op_L_Inp)
                  apply (subst dup_op.code)
                  apply blast
                 apply simp_all
     apply (simp add: ran_def sum.case_eq_if)
    apply (rule wtraced.Step)
     apply simp
     apply (rule wstep_trans(1))
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_Tau_loop_op)
             apply (rule step_map_op)
              apply (rule step_comp_op_L_Tau)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Tau)
                   apply (rule step_map_op)
                    apply (rule step_Tau_comp_op_L)
                       apply (rule step_comp_op_L_Out)
                        apply blast
                        apply simp_all
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Tau)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Tau)
                  apply (rule step_map_op)
                   apply (rule step_Tau_comp_op_R)
                        apply (rule step_merge_op_Read_L)
                        apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_L)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Out)
                     apply (rule step_merge_op_Write_L)
                        apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_Tau_comp_op_R)
                   apply (rule step_id_op_Read)
                    apply (simp_all add: defaults_num1_def)
       apply (rule step_map_op)
        apply (rule step_Tau_loop_op)
         apply (rule step_map_op)
          apply (rule step_Tau_comp_op_L)
             apply (rule step_map_op)
              apply (rule step_comp_op_R_Out)
                apply (rule step_id_op_Write)
                   apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_Tau_loop_op)
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply (rule step_acopy_op_Read)
               apply (simp_all add: defaults_num1_def)
     apply (rule step_map_op)
      apply (rule step_Out_loop_op)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_acopy_op_WriteL)
              apply (simp_all add: defaults_num1_def BENQ_diff_access BHD_def)
     apply simp
    apply (rule wtraced.Step)
     apply simp
     apply (rule wstep_trans(1))
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(2))
             apply (rule rtranclp.intros(2))
              apply (rule rtranclp.intros(2))
               apply (rule rtranclp.intros(2))
                apply (rule rtranclp.intros(1))
               apply (rule step_map_op)
                apply (rule step_Out_Tau_loop_op)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Out)
                     apply (rule step_acopy_op_WriteR)
                        apply (simp_all add: defaults_num1_def BENQ_diff_access BTL_def)
               apply simp
              apply (rule step_map_op)
               apply (rule step_Inp_Tau_loop_op)
                   apply (rule step_map_op)
                    apply (rule step_comp_op_L_Inp)
                      apply (rule step_map_op)
                       apply (rule step_comp_op_L_Inp)
                        apply (rule step_map_op)
                        apply (rule step_comp_op_L_Inp)
                        apply (rule step_comp_op_R_Inp)
                        apply (rule step_map_op)
                        apply (rule step_comp_op_L_Inp)
                        apply (subst suc_op.code)
                        apply blast
                        apply (simp_all add: defaults_num1_def)
               apply (meson sum.simps(6) ranI)
              apply simp
             apply (rule step_map_op)
              apply (rule step_Tau_loop_op)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Tau)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_L_Tau)
                     apply (rule step_map_op)
                      apply (rule step_comp_op_L_Tau)
                        apply (rule step_comp_op_R_Tau)
                        apply (rule step_map_op)
                        apply (rule step_Tau_comp_op_L)
                        apply blast
                        apply simp_all
            apply (rule step_map_op)
             apply (rule step_Tau_loop_op)
              apply (rule step_map_op)
               apply (rule step_comp_op_L_Tau)
                 apply (rule step_map_op)
                  apply (rule step_comp_op_L_Tau)
                    apply (rule step_map_op)
                     apply (rule step_comp_op_L_Tau)
                       apply (rule step_comp_op_R_Tau)
                        apply (rule step_map_op)
                        apply (rule step_Tau_comp_op_R)
                        apply (subst dup_op.code)
                        apply blast
                        apply simp_all
           apply (rule step_map_op)
            apply (rule step_Tau_loop_op)
             apply (rule step_map_op)
              apply (rule step_comp_op_L_Tau)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Tau)
                   apply (rule step_map_op)
                    apply (rule step_Tau_comp_op_L)
                       apply (rule step_comp_op_R_Out)
                        apply (rule step_map_op)
                        apply (rule step_comp_op_R_Out)
                        apply blast
                        apply simp_all
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Tau)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Tau)
                  apply (rule step_map_op)
                   apply (rule step_Tau_comp_op_R)
                        apply (rule step_merge_op_Read_R)
                        apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_L)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Out)
                     apply (rule step_merge_op_Write_R)
                        apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_Tau_comp_op_R)
                   apply (rule step_id_op_Read)
                    apply (simp_all add: defaults_num1_def)
       apply (rule step_map_op)
        apply (rule step_Tau_loop_op)
         apply (rule step_map_op)
          apply (rule step_Tau_comp_op_L)
             apply (rule step_map_op)
              apply (rule step_comp_op_R_Out)
                apply (rule step_id_op_Write)
                   apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_Tau_loop_op)
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply (rule step_acopy_op_Read)
               apply (simp_all add: defaults_num1_def)
     apply (rule step_map_op)
      apply (rule step_Out_loop_op)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_acopy_op_WriteL)
              apply (simp_all add: defaults_num1_def BENQ_diff_access BHD_def)
     apply simp
    apply (rule wtraced.Step)
     apply simp
     apply (rule wstep_trans(1))
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_Tau_loop_op)
             apply (rule step_map_op)
              apply (rule step_comp_op_L_Tau)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Tau)
                   apply (rule step_map_op)
                    apply (rule step_Tau_comp_op_L)
                       apply (rule step_comp_op_R_Out)
                        apply blast
                        apply simp_all
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Tau)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Tau)
                  apply (rule step_map_op)
                   apply (rule step_Tau_comp_op_R)
                        apply (rule step_merge_op_Read_R)
                        apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_L)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Out)
                     apply (rule step_merge_op_Write_R)
                        apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_Tau_comp_op_R)
                   apply (rule step_id_op_Read)
                    apply (simp_all add: defaults_num1_def)
       apply (rule step_map_op)
        apply (rule step_Tau_loop_op)
         apply (rule step_map_op)
          apply (rule step_Tau_comp_op_L)
             apply (rule step_map_op)
              apply (rule step_comp_op_R_Out)
                apply (rule step_id_op_Write)
                   apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_Tau_loop_op)
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply (rule step_acopy_op_Read)
               apply (simp_all add: defaults_num1_def)
     apply (rule step_map_op)
      apply (rule step_Out_loop_op)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_acopy_op_WriteL)
              apply (simp_all add: defaults_num1_def BENQ_diff_access BHD_def BTL_access)
     apply simp
    apply (rule wtraced.Step)
     apply simp
     apply (rule wstep_trans(1))
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(2))
             apply (rule rtranclp.intros(2))
              apply (rule rtranclp.intros(2))
               apply (rule rtranclp.intros(2))
                apply (rule rtranclp.intros(1))
               apply (rule step_map_op)
                apply (rule step_Out_Tau_loop_op)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Out)
                     apply (rule step_acopy_op_WriteR)
                        apply (simp_all add: defaults_num1_def BENQ_diff_access BTL_def)
               apply simp
              apply (rule step_map_op)
               apply (rule step_Inp_Tau_loop_op)
                   apply (rule step_map_op)
                    apply (rule step_comp_op_L_Inp)
                      apply (rule step_map_op)
                       apply (rule step_comp_op_L_Inp)
                        apply (rule step_map_op)
                        apply (rule step_comp_op_L_Inp)
                        apply (rule step_comp_op_R_Inp)
                        apply (rule step_map_op)
                        apply (rule step_comp_op_L_Inp)
                        apply (subst suc_op.code)
                        apply blast
                        apply (simp_all add: defaults_num1_def)
               apply (meson sum.simps(6) ranI)
              apply simp
             apply (rule step_map_op)
              apply (rule step_Tau_loop_op)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Tau)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_L_Tau)
                     apply (rule step_map_op)
                      apply (rule step_comp_op_L_Tau)
                        apply (rule step_comp_op_R_Tau)
                        apply (rule step_map_op)
                        apply (rule step_Tau_comp_op_L)
                        apply blast
                        apply simp_all
            apply (rule step_map_op)
             apply (rule step_Tau_loop_op)
              apply (rule step_map_op)
               apply (rule step_comp_op_L_Tau)
                 apply (rule step_map_op)
                  apply (rule step_comp_op_L_Tau)
                    apply (rule step_map_op)
                     apply (rule step_comp_op_L_Tau)
                       apply (rule step_comp_op_R_Tau)
                        apply (rule step_map_op)
                        apply (rule step_Tau_comp_op_R)
                        apply (subst dup_op.code)
                        apply blast
                        apply simp_all
           apply (rule step_map_op)
            apply (rule step_Tau_loop_op)
             apply (rule step_map_op)
              apply (rule step_comp_op_L_Tau)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Tau)
                   apply (rule step_map_op)
                    apply (rule step_Tau_comp_op_L)
                       apply (rule step_comp_op_R_Out)
                        apply (rule step_map_op)
                        apply (rule step_comp_op_R_Out)
                        apply blast
                        apply simp_all
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Tau)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Tau)
                  apply (rule step_map_op)
                   apply (rule step_Tau_comp_op_R)
                        apply (rule step_merge_op_Read_R)
                        apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_L)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Out)
                     apply (rule step_merge_op_Write_R)
                        apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_Tau_comp_op_R)
                   apply (rule step_id_op_Read)
                    apply (simp_all add: defaults_num1_def)
       apply (rule step_map_op)
        apply (rule step_Tau_loop_op)
         apply (rule step_map_op)
          apply (rule step_Tau_comp_op_L)
             apply (rule step_map_op)
              apply (rule step_comp_op_R_Out)
                apply (rule step_id_op_Write)
                   apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_Tau_loop_op)
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply (rule step_acopy_op_Read)
               apply (simp_all add: defaults_num1_def)
     apply (rule step_map_op)
      apply (rule step_Out_loop_op)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_acopy_op_WriteL)
              apply (simp_all add: defaults_num1_def BENQ_diff_access BHD_def)
     apply simp
    apply (rule wtraced.Nil)
    done
  subgoal
    by (simp add: lproject_def)
  subgoal
    by (auto simp: lproject_def)
  done
*)

lemma time_anomaly_Brock_Ackermann:
  \<open>f_op \<equiv>\<^sub>h f'_op\<close>
  \<open>f_op\<up> \<equiv>\<^sub>h f'_op\<up> \<Longrightarrow> False\<close>
  subgoal
    by (rule history_equiv_f_f')
  subgoal
    using no_history_f_feedback_12 history_f'_feedback_12
    by simp
  oops

end