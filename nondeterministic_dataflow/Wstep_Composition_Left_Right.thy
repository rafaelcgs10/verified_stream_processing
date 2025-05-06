theory Wstep_Composition_Left_Right

imports
  "BNA_Operators"
begin

lemma
  \<open>p \<notin> defaults \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> p' \<notin> defaults \<Longrightarrow> p \<in> ran wire \<Longrightarrow> wire p' = Some q \<Longrightarrow>
  step Tau (comp_op wire buf op\<^sub>1 op\<^sub>2) (comp_op wire (BTL p buf) op\<^sub>1 op\<^sub>2') \<Longrightarrow>
  step Tau (comp_op wire buf op\<^sub>1 op\<^sub>2') (comp_op wire (BENQ q x (BTL p buf)) op\<^sub>1' op\<^sub>2') \<Longrightarrow>
  step Tau (comp_op wire buf op\<^sub>1 op\<^sub>2) (comp_op wire (BENQ q x buf) op\<^sub>1' op\<^sub>2)
  \<and> step Tau (comp_op wire (BENQ q x buf) op\<^sub>1' op\<^sub>2) (comp_op wire (BTL p (BENQ q x buf)) op\<^sub>1' op\<^sub>2')\<close>
  apply (auto elim!: step_comp_op_elim)
  oops

lemma
  \<open>p \<notin> defaults \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> p' \<notin> defaults \<Longrightarrow> p \<in> ran wire \<Longrightarrow> wire p' = Some q \<Longrightarrow>
  step (Inp p (BHD p buf)) op\<^sub>2 op\<^sub>2' \<Longrightarrow> step (Out p' x) op\<^sub>1 op\<^sub>1' \<Longrightarrow>
  step Tau (comp_op wire buf op\<^sub>1 op\<^sub>2) (comp_op wire (BENQ q x buf) op\<^sub>1' op\<^sub>2)
  \<and> step Tau (comp_op wire (BENQ q x buf) op\<^sub>1' op\<^sub>2) (comp_op wire (BTL p (BENQ q x buf)) op\<^sub>1' op\<^sub>2')\<close>
  apply (auto elim!: step_comp_op_elim)
   apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
  by (metis BENQ_access BENQ_diff_access Nil_is_append_conv)

inductive wstep_comp_op_L :: \<open>('c \<Rightarrow> 'b option) \<Rightarrow> ('a + 'b, 'c + 'd, 'e) IO \<Rightarrow> ('b \<Rightarrow> 'e buf) \<Rightarrow>
  ('a, 'c, 'e) op \<Rightarrow> ('a, 'c, 'e) op \<Rightarrow> bool\<close> for wire where
  \<open>io = Tau \<Longrightarrow> buf = (\<lambda>_. []) \<Longrightarrow> op' = op \<Longrightarrow> wstep_comp_op_L wire io buf op op'\<close>
| \<open>io = Inp (Inl p) x \<Longrightarrow> step (Inp p x) op op' \<Longrightarrow> wstep_comp_op_L wire Tau buf op' op'' \<Longrightarrow>
  wstep_comp_op_L wire io buf op op''\<close>
| \<open>io = Out (Inl p) x \<Longrightarrow> step (Out p x) op op' \<Longrightarrow> wire p = None \<Longrightarrow>
  wstep_comp_op_L wire Tau buf op' op'' \<Longrightarrow> wstep_comp_op_L wire io buf op op''\<close>
| \<open>step (Out p x) op op' \<Longrightarrow> wire p = Some q \<Longrightarrow> wstep_comp_op_L wire io buf op' op'' \<Longrightarrow>
  buf' = buf(q := x # buf q) \<Longrightarrow> wstep_comp_op_L wire io buf' op op''\<close>
| \<open>step Tau op op' \<Longrightarrow> wstep_comp_op_L wire io buf op' op'' \<Longrightarrow> wstep_comp_op_L wire io buf op op''\<close>

inductive wstep_comp_op_R :: \<open>('c \<Rightarrow> 'b option) \<Rightarrow> ('a + 'b, 'c + 'd, 'e) IO \<Rightarrow> ('b \<Rightarrow> 'e buf) \<Rightarrow>
  ('b, 'd, 'e) op \<Rightarrow> ('b, 'd, 'e) op \<Rightarrow> bool\<close> for wire where
  \<open>io = Tau \<Longrightarrow> buf = (\<lambda>_. []) \<Longrightarrow> op' = op \<Longrightarrow> wstep_comp_op_R wire io buf op op'\<close>
| \<open>io = Inp (Inr p) x \<Longrightarrow> step (Inp p x) op op' \<Longrightarrow> p \<notin> ran wire \<Longrightarrow>
  wstep_comp_op_R wire Tau buf op' op'' \<Longrightarrow> wstep_comp_op_R wire io buf op op''\<close>
| \<open>step (Inp p x) op op' \<Longrightarrow> p \<in> ran wire \<Longrightarrow> wstep_comp_op_R wire io (BTL p buf) op' op'' \<Longrightarrow>
  buf p \<noteq> [] \<Longrightarrow> x = BHD p buf \<Longrightarrow> wstep_comp_op_R wire io buf op op''\<close>
| \<open>io = Out (Inr p) x \<Longrightarrow> step (Out p x) op op' \<Longrightarrow> wstep_comp_op_R wire Tau buf op' op'' \<Longrightarrow>
  wstep_comp_op_R wire io buf op op''\<close>
| \<open>step Tau op op' \<Longrightarrow> wstep_comp_op_R wire io buf op' op'' \<Longrightarrow> wstep_comp_op_R wire io buf op op''\<close>

lemma
  \<open>wstep io (comp_op wire buf op\<^sub>1 op\<^sub>2) op' \<longleftrightarrow>
  (\<exists>buf' buf1 buf2 op\<^sub>1' op\<^sub>2'. op' = comp_op wire buf' op\<^sub>1' op\<^sub>2'
  \<and> wstep_comp_op_L wire (case io of Inp (Inl _) _ \<Rightarrow> io | Out (Inl _) _ \<Rightarrow> io | _ \<Rightarrow> Tau) buf1 op\<^sub>1 op\<^sub>1'
  \<and> wstep_comp_op_R wire (case io of Inp (Inr _) _ \<Rightarrow> io | Out (Inr _) _ \<Rightarrow> io | _ \<Rightarrow> Tau) buf2 op\<^sub>2 op\<^sub>2'
  \<and> (\<forall>p. \<exists>n \<le> length (buf p @ buf1 p). buf' p = drop n (buf p @ buf1 p) \<and> buf2 p = take n (buf p @ buf1 p)
    \<and> (p \<notin> ran wire \<longrightarrow> n = 0))
  \<and> (case io of Out (Inl p) _ \<Rightarrow> wire p = None | Inp (Inr p) _ \<Rightarrow> p \<notin> ran wire | _ \<Rightarrow> True))\<close>
  apply (intro iffI)
  subgoal
    sorry
  subgoal
    apply (elim exE conjE)
    subgoal for buf' buf1 buf2 op\<^sub>1' op\<^sub>2'
      apply hypsubst_thin
      apply (induct \<open>case io of Inp (Inl _) _ \<Rightarrow> io | Out (Inl _) _ \<Rightarrow> io | _ \<Rightarrow> Tau\<close> buf1 op\<^sub>1 op\<^sub>1' arbitrary: io buf pred: wstep_comp_op_L)
          apply (auto split: sum.splits IO.splits)
      subgoal for op\<^sub>1 buf x p
        apply (rotate_tac 2)
        apply (induct \<open>Inp (Inr p) x :: ('a + 'b, 'c + 'd, 'e) IO\<close> buf2 op\<^sub>2 op\<^sub>2' arbitrary: buf pred: wstep_comp_op_R)
            apply auto
        subgoal for op\<^sub>2 op\<^sub>2' buf2 op\<^sub>2'' buf
          apply (rule wstep_converse_trans(2))
           apply blast
          apply (erule thin_rl)
          apply (erule thin_rl)
          apply (induct \<open>Tau :: ('a + 'b, 'c + 'd, 'e) IO\<close> buf2 op\<^sub>2' op\<^sub>2'' arbitrary: buf pred: wstep_comp_op_R)
              apply auto
          subgoal
            by (metis drop0 ext le_0_eq list.size(3) rtranclp.rtrancl_refl)
          subgoal for p op\<^sub>2 op\<^sub>2' buf2 op\<^sub>2'' buf
            apply (drule meta_spec[of _ \<open>BTL p buf\<close>])
            apply (drule meta_mp)
            apply (rule allI)
            subgoal for p'
              apply (cases \<open>p' = p\<close>; simp?)
              subgoal
                apply (drule spec[of _ p])
                by (metis BTL_access Suc_diff_1 diff_le_mono drop_Suc le_0_eq length_tl linorder_not_le take_0 tl_take)
              subgoal
                by (simp add: BTL_diff_access)
              done
            subgoal
              by (metis BHD_def append_take_drop_id hd_append2 step_Tau_comp_op_R take_eq_Nil2 wstep_steps_Tau
                  wstep_trans_tau_1)
            done
          subgoal
            by (meson converse_rtranclp_into_rtranclp step_comp_op_R_Tau)
          done
        subgoal for p' op\<^sub>2 op\<^sub>2' buf2 op\<^sub>2'' buf
          apply (drule meta_spec[of _ \<open>BTL p' buf\<close>])
          apply (drule meta_mp)
           apply (rule allI)
          subgoal for p''
            apply (cases \<open>p'' = p'\<close>; simp?)
            subgoal
              apply (drule spec[of _ p'])
              by (metis (no_types, lifting) BTL_access One_nat_def Suc_diff_1 bot_nat_0.extremum_uniqueI diff_le_mono drop0 drop_Suc length_drop
                  not_le take_eq_Nil2 tl_take)
            subgoal
              by (simp add: BTL_diff_access)
            done
          subgoal
            by (metis BHD_def append_take_drop_id hd_append2 step_Tau_comp_op_R take_Nil wstep_trans_tau_1)
          done
        done
      subgoal for op\<^sub>1 buf x p
        apply rotate_tac
        apply (induct \<open>Out (Inr p) x :: ('a + 'b, 'c + 'd, 'e) IO\<close> buf2 op\<^sub>2 op\<^sub>2' arbitrary: buf pred: wstep_comp_op_R)
            apply auto
        subgoal for p' op\<^sub>2 op\<^sub>2' buf2 op\<^sub>2'' buf
          apply (drule meta_spec[of _ \<open>BTL p' buf\<close>])
          apply (drule meta_mp)
           apply (rule allI)
          subgoal for p''
            apply (cases \<open>p'' = p'\<close>; simp?)
            subgoal
              apply (drule spec[of _ p'])
              by (metis (no_types, lifting) BTL_access One_nat_def Suc_diff_1 bot_nat_0.extremum_uniqueI diff_le_mono drop0 drop_Suc length_drop
                  not_le take_eq_Nil2 tl_take)
            subgoal
              by (simp add: BTL_diff_access)
            done
          subgoal
            by (metis BHD_def append_take_drop_id hd_append2 step_Tau_comp_op_R take_Nil wstep_trans_tau_1)
          done
        subgoal for op\<^sub>2 op\<^sub>2' buf2 op\<^sub>2'' buf
          apply (rule wstep_converse_trans(1))
           apply blast
          apply (erule thin_rl)
          apply (induct \<open>Tau :: ('a + 'b, 'c + 'd, 'e) IO\<close> buf2 op\<^sub>2' op\<^sub>2'' arbitrary: buf pred: wstep_comp_op_R)
              apply auto
          subgoal
            by (metis drop0 ext le_0_eq list.size(3) rtranclp.rtrancl_refl)
          subgoal for p op\<^sub>2 op\<^sub>2' buf2 op\<^sub>2'' buf
            apply (drule meta_spec[of _ \<open>BTL p buf\<close>])
            apply (drule meta_mp)
            apply (rule allI)
            subgoal for p'
              apply (cases \<open>p' = p\<close>; simp?)
              subgoal
                apply (drule spec[of _ p])
                by (metis BTL_access Suc_diff_1 diff_le_mono drop_Suc le_0_eq length_tl linorder_not_le take_0 tl_take)
              subgoal
                by (simp add: BTL_diff_access)
              done
            subgoal
              by (metis BHD_def append_take_drop_id hd_append2 step_Tau_comp_op_R take_eq_Nil2 wstep_steps_Tau
                  wstep_trans_tau_1)
            done
          subgoal
            by (meson converse_rtranclp_into_rtranclp step_comp_op_R_Tau)
          done
        done
      subgoal for op\<^sub>1 buf
        apply (induct \<open>Tau :: ('a + 'b, 'c + 'd, 'e) IO\<close> buf2 op\<^sub>2 op\<^sub>2' arbitrary: buf pred: wstep_comp_op_R)
            apply auto
        subgoal
          by (metis drop0 ext le_0_eq list.size(3) rtranclp.rtrancl_refl)
        subgoal for p op\<^sub>2 op\<^sub>2' buf2 op\<^sub>2'' buf
          apply (drule meta_spec[of _ \<open>BTL p buf\<close>])
          apply (drule meta_mp)
          apply (rule allI)
          subgoal for p'
            apply (cases \<open>p' = p\<close>; simp?)
            subgoal
              apply (drule spec[of _ p])
              by (metis BTL_access Suc_diff_1 diff_le_mono drop_Suc le_0_eq length_tl linorder_not_le take_0 tl_take)
            subgoal
              by (simp add: BTL_diff_access)
            done
          subgoal
            by (metis BHD_def append_take_drop_id hd_append2 step_Tau_comp_op_R take_eq_Nil2 wstep_steps_Tau
                  wstep_trans_tau_1)
          done
        subgoal
          by (meson converse_rtranclp_into_rtranclp step_comp_op_R_Tau)
        done
      subgoal for p x op\<^sub>1 op\<^sub>1' buf1 op\<^sub>1'' buf
        apply (drule meta_spec[of _ Tau])
        apply (drule meta_spec[of _ buf])
        apply (drule meta_mp)
         apply simp_all
        by (meson step_comp_op_L_Inp wstep_converse_trans(2))
      subgoal for p x op\<^sub>1 op\<^sub>1' buf1 op\<^sub>1'' buf
        apply (drule meta_spec[of _ Tau])
        apply (drule meta_spec[of _ buf])
        apply (drule meta_mp)
         apply simp_all
        apply (rule wstep_converse_trans(1))
         apply blast
        apply assumption
        done
      subgoal for p x op\<^sub>1 op\<^sub>1' q buf1 op\<^sub>1'' buf x' p'
        apply (drule meta_spec[of _ \<open>Inp (Inl p') x'\<close>])
        apply (drule meta_spec[of _ \<open>BENQ q x buf\<close>])
        apply (drule meta_mp)
         apply simp_all
        apply (drule meta_mp)
         apply (rule allI)
        subgoal for p''
          apply (cases \<open>p'' = q\<close>; simp?)
          subgoal
            apply (drule spec[of _ q])
            apply simp
            by (smt (verit, del_insts) Cons_eq_appendI append.assoc drop_append length_append_singleton self_append_conv2 take_append)
          subgoal
            by (smt (verit, ccfv_SIG) BENQ_diff_access)
          done
        subgoal
          by blast
        done
      subgoal for p x op\<^sub>1 op\<^sub>1' q buf1 op\<^sub>1'' buf x' p'
        apply (drule meta_spec[of _ \<open>Inp (Inr p') x'\<close>])
        apply (drule meta_spec[of _ \<open>BENQ q x buf\<close>])
        apply (drule meta_mp)
         apply simp_all
        apply (drule meta_mp)
         apply (rule allI)
        subgoal for p''
          apply (cases \<open>p'' = q\<close>; simp?)
          subgoal
            apply (drule spec[of _ q])
            apply simp
            by (smt (verit, del_insts) Cons_eq_appendI append.assoc drop_append length_append_singleton self_append_conv2 take_append)
          subgoal
            by (smt (verit, ccfv_SIG) BENQ_diff_access)
          done
        subgoal
          by blast
        done
      subgoal for p x op\<^sub>1 op\<^sub>1' q buf1 op\<^sub>1'' buf x' p'
        apply (drule meta_spec[of _ \<open>Out (Inl p') x'\<close>])
        apply (drule meta_spec[of _ \<open>BENQ q x buf\<close>])
        apply (drule meta_mp)
         apply simp_all
        apply (drule meta_mp)
         apply (rule allI)
        subgoal for p''
          apply (cases \<open>p'' = q\<close>; simp?)
          subgoal
            apply (drule spec[of _ q])
            apply simp
            by (smt (verit, del_insts) Cons_eq_appendI append.assoc drop_append length_append_singleton self_append_conv2 take_append)
          subgoal
            by (smt (verit, ccfv_SIG) BENQ_diff_access)
          done
        subgoal
          by blast
        done
      subgoal for p x op\<^sub>1 op\<^sub>1' q buf1 op\<^sub>1'' buf x' p'
        apply (drule meta_spec[of _ \<open>Out (Inr p') x'\<close>])
        apply (drule meta_spec[of _ \<open>BENQ q x buf\<close>])
        apply (drule meta_mp)
         apply simp_all
        apply (drule meta_mp)
         apply (rule allI)
        subgoal for p''
          apply (cases \<open>p'' = q\<close>; simp?)
          subgoal
            apply (drule spec[of _ q])
            apply simp
            by (smt (verit, del_insts) Cons_eq_appendI append.assoc drop_append length_append_singleton self_append_conv2 take_append)
          subgoal
            by (smt (verit, ccfv_SIG) BENQ_diff_access)
          done
        subgoal
          by blast
        done
      subgoal for p x op\<^sub>1 op\<^sub>1' q buf1 op\<^sub>1'' buf
        apply (drule meta_spec[of _ Tau])
        apply (drule meta_spec[of _ \<open>BENQ q x buf\<close>])
        apply (drule meta_mp)
         apply simp_all
        apply (drule meta_mp)
         apply (rule allI)
        subgoal for p''
          apply (cases \<open>p'' = q\<close>; simp?)
          subgoal
            apply (drule spec[of _ q])
            apply simp
            by (smt (verit, del_insts) Cons_eq_appendI append.assoc drop_append length_append_singleton self_append_conv2 take_append)
          subgoal
            by (smt (verit, ccfv_SIG) BENQ_diff_access)
          done
        subgoal
          by (metis step_Tau_comp_op_L wstep_steps_Tau wstep_trans_tau_1)
        done
      subgoal for op\<^sub>1 op\<^sub>1' buf1 op\<^sub>1'' buf
        apply (drule meta_spec[of _ Tau])
        apply (drule meta_spec[of _ buf])
        by (metis IO.simps(11) step_comp_op_L_Tau wstep_steps_Tau wstep_trans_tau_1)
      done
    done
  oops

lemma
  \<open>wstep io (comp_op (\<lambda>_. None) (\<lambda>_. []) op\<^sub>1 op\<^sub>2) op' \<longleftrightarrow>
  (\<exists>op\<^sub>1' op\<^sub>2'. op' = comp_op (\<lambda>_. None) (\<lambda>_. []) op\<^sub>1' op\<^sub>2'
  \<and> wstep_comp_op_L (\<lambda>_. None) (case io of Inp (Inl _) _ \<Rightarrow> io | Out (Inl _) _ \<Rightarrow> io | _ \<Rightarrow> Tau) (\<lambda>_. []) op\<^sub>1 op\<^sub>1'
  \<and> wstep_comp_op_R (\<lambda>_. None) (case io of Inp (Inr _) _ \<Rightarrow> io | Out (Inr _) _ \<Rightarrow> io | _ \<Rightarrow> Tau) (\<lambda>_. []) op\<^sub>2 op\<^sub>2')\<close>
  apply (intro iffI)
  subgoal
    apply (unfold wstep_def)
    apply (erule relcomppE)+
    apply (auto split: sum.splits IO.splits)
    sorry
  subgoal
    apply (elim exE conjE)
    subgoal for op\<^sub>1' op\<^sub>2'
      apply hypsubst_thin
      apply (induct \<open>case io of Inp (Inl _) _ \<Rightarrow> io | Out (Inl _) _ \<Rightarrow> io | _ \<Rightarrow> Tau\<close> \<open>(\<lambda>_. []) :: 'b \<Rightarrow> 'e buf\<close> op\<^sub>1 op\<^sub>1' arbitrary: io pred: wstep_comp_op_L)
          apply (auto split: sum.splits IO.splits)
      subgoal
        apply (induct _ \<open>(\<lambda>_. []) :: 'b \<Rightarrow> 'e buf\<close> op\<^sub>2 op\<^sub>2' pred: wstep_comp_op_R)
            apply auto
         apply (metis empty_iff ran_empty step_comp_op_R_Inp wstep_converse_trans(2))
        by (meson step_comp_op_R_Out wstep_converse_trans(1))
      subgoal
        apply (induct _ \<open>(\<lambda>_. []) :: 'b \<Rightarrow> 'e buf\<close> op\<^sub>2 op\<^sub>2' pred: wstep_comp_op_R)
            apply auto
         apply (metis empty_iff ran_empty step_comp_op_R_Inp wstep_converse_trans(2))
        by (meson step_comp_op_R_Out wstep_converse_trans(1))
      subgoal
        apply (induct \<open>Tau :: ('a + 'b, 'c + 'd, 'e) IO\<close> \<open>(\<lambda>_. []) :: 'b \<Rightarrow> 'e buf\<close> op\<^sub>2 op\<^sub>2' pred: wstep_comp_op_R)
            apply auto
        by (meson rtranclp_trans step_Tau_closure_single step_comp_op_R_Tau_start)
      subgoal
        apply (drule meta_spec[of _ Tau])
        apply simp
        by (meson step_comp_op_L_Inp wstep_converse_trans(2))
      subgoal
        apply (drule meta_spec[of _ Tau])
        apply simp
        by (metis domIff step_comp_op_L_Out wstep_converse_trans(1))
      subgoal
        apply (drule meta_spec[of _ Tau])
        apply simp
        by (meson rtranclp_trans step_Tau_closure_single step_comp_op_L_Tau_start)
      done
    done
  oops

end