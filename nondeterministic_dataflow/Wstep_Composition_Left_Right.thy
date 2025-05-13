theory Wstep_Composition_Left_Right

imports
  "BNA_Operators"
begin

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

lemma wstep_comp_op_L_BENQ:
  \<open>wstep_comp_op_L wire io buf op op' \<Longrightarrow> step (Out p x) op' op'' \<Longrightarrow> wire p = Some q \<Longrightarrow>
  wstep_comp_op_L wire io (BENQ q x buf) op op''\<close>
  by (induct _ buf op op' pred: wstep_comp_op_L)
    (auto intro: wstep_comp_op_L.intros simp: BENQ_def fun_upd_twist)

lemma wstep_comp_op_L_Tau:
  \<open>wstep_comp_op_L wire io buf op op' \<Longrightarrow> step Tau op' op'' \<Longrightarrow> wstep_comp_op_L wire io buf op op''\<close>
  by (induct _ buf op op' pred: wstep_comp_op_L) (auto intro: wstep_comp_op_L.intros)

lemma wstep_comp_op_R_BENQ:
  \<open>wstep_comp_op_R wire io buf op op' \<Longrightarrow> step (Inp p x) op' op'' \<Longrightarrow> p \<in> ran wire \<Longrightarrow>
  wstep_comp_op_R wire io (BENQ p x buf) op op''\<close>
  apply (induct _ buf op op' pred: wstep_comp_op_R)
      apply (auto intro: wstep_comp_op_R.intros)
   apply (rule wstep_comp_op_R.intros(3))
       apply simp_all
    apply (rule wstep_comp_op_R.intros(1))
      apply simp_all
  apply (rule wstep_comp_op_R.intros(3))
      apply assumption
     apply (simp_all add: BENQ_def BTL_def BHD_def)
   apply (smt (verit, best) fun_upd_twist fun_upd_upd tl_append2)
  apply force
  done

lemma wstep_comp_op_R_Tau:
  \<open>wstep_comp_op_R wire io buf op op' \<Longrightarrow> step Tau op' op'' \<Longrightarrow> wstep_comp_op_R wire io buf op op''\<close>
  by (induct _ buf op op' pred: wstep_comp_op_R) (auto intro: wstep_comp_op_R.intros)

lemma wstep_comp_op_L_R:
  \<open>wstep io (comp_op wire buf op\<^sub>1 op\<^sub>2) op \<longleftrightarrow>
  (\<exists>buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2'. op = comp_op wire buf' op\<^sub>1' op\<^sub>2'
  \<and> wstep_comp_op_L wire (case io of Inp (Inl _) _ \<Rightarrow> io | Out (Inl _) _ \<Rightarrow> io | _ \<Rightarrow> Tau) buf\<^sub>1 op\<^sub>1 op\<^sub>1'
  \<and> wstep_comp_op_R wire (case io of Inp (Inr _) _ \<Rightarrow> io | Out (Inr _) _ \<Rightarrow> io | _ \<Rightarrow> Tau) buf\<^sub>2 op\<^sub>2 op\<^sub>2'
  \<and> (\<forall>p. \<exists>n \<le> length (buf p @ buf\<^sub>1 p). buf' p = drop n (buf p @ buf\<^sub>1 p) \<and> buf\<^sub>2 p = take n (buf p @ buf\<^sub>1 p)
    \<and> (p \<notin> ran wire \<longrightarrow> n = 0))
  \<and> (case io of Out (Inl p) _ \<Rightarrow> wire p = None | Inp (Inr p) _ \<Rightarrow> p \<notin> ran wire | _ \<Rightarrow> True))\<close>
  apply (rule iffI)
  subgoal
    apply (unfold wstep_def)
    apply (erule relcomppE)
    subgoal
      apply (induct \<open>comp_op wire buf op\<^sub>1 op\<^sub>2\<close> arbitrary: buf op\<^sub>1 op\<^sub>2 rule: converse_rtranclp_induct)
      subgoal for buf op\<^sub>1 op\<^sub>2
        apply (erule relcomppE)
        apply hypsubst_thin
        apply rotate_tac
        subgoal
          apply (induct op rule: rtranclp_induct)
          subgoal
            apply (auto split: IO.splits sum.splits elim!: step_comp_op_elim)
            subgoal for _ _ op\<^sub>1'
              apply (rule exI[of _ buf])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ op\<^sub>1'])
              apply (rule exI[of _ op\<^sub>2])
              apply (auto intro: wstep_comp_op_L.intros wstep_comp_op_R.intros)
              done
            subgoal for _ _ op\<^sub>2'
              apply (rule exI[of _ buf])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ op\<^sub>1])
              apply (rule exI[of _ op\<^sub>2'])
              apply (auto intro: wstep_comp_op_L.intros wstep_comp_op_R.intros)
              done
            subgoal for _ _ op\<^sub>1'
              apply (rule exI[of _ buf])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ op\<^sub>1'])
              apply (rule exI[of _ op\<^sub>2])
              apply (auto intro: wstep_comp_op_L.intros wstep_comp_op_R.intros)
              done
            subgoal for _ _ op\<^sub>2'
              apply (rule exI[of _ buf])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ op\<^sub>1])
              apply (rule exI[of _ op\<^sub>2'])
              apply (auto intro: wstep_comp_op_L.intros wstep_comp_op_R.intros)
              done
            subgoal for _ x op\<^sub>1' q
              apply (rule exI[of _ \<open>BENQ q x buf\<close>])
              apply (rule exI[of _ \<open>BENQ q x (\<lambda>_. [])\<close>])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ op\<^sub>1'])
              apply (rule exI[of _ op\<^sub>2])
              apply (intro conjI)
                 apply (simp_all add: wstep_comp_op_R.intros(1))
               apply (metis wstep_comp_op_L.intros(1) wstep_comp_op_L_BENQ)
              apply (metis BENQ_access BENQ_diff_access append.left_neutral append_Nil2 diff_0_eq_0
                  drop0 le0)
              done
            subgoal for p op\<^sub>2'
              apply (rule exI[of _ \<open>BTL p buf\<close>])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ \<open>BENQ p (BHD p buf) (\<lambda>_. [])\<close>])
              apply (rule exI[of _ op\<^sub>1])
              apply (rule exI[of _ op\<^sub>2'])
              apply (intro conjI)
                 apply (simp_all add: wstep_comp_op_L.intros(1))
               apply (metis wstep_comp_op_R.intros(1) wstep_comp_op_R_BENQ)
              apply (metis (no_types, lifting) BENQ_access BENQ_diff_access BHD_def BTL_access
                  BTL_diff_access bot_nat_0.extremum drop0 drop_Suc drop_all length_greater_0_conv
                  not_less_eq_eq take0 take_hd_drop)
              done
            subgoal for op\<^sub>1'
              apply (rule exI[of _ buf])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ op\<^sub>1'])
              apply (rule exI[of _ op\<^sub>2])
              apply (auto intro: wstep_comp_op_L.intros wstep_comp_op_R.intros)
              done
            subgoal for op\<^sub>2'
              apply (rule exI[of _ buf])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ op\<^sub>1])
              apply (rule exI[of _ op\<^sub>2'])
              apply (auto intro: wstep_comp_op_L.intros wstep_comp_op_R.intros)
              done
            subgoal
              apply (rule exI[of _ buf])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
              apply (rule exI[of _ op\<^sub>1])
              apply (rule exI[of _ op\<^sub>2])
              apply (auto intro: wstep_comp_op_L.intros wstep_comp_op_R.intros)
              done
            done
          subgoal
            apply simp
            apply (elim exE conjE)
            subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2'
              apply hypsubst_thin
              apply (erule step_comp_op_elim; simp)
              subgoal for _ x op\<^sub>1'' q
                apply (rule exI[of _ \<open>BENQ q x buf'\<close>])
                apply (rule exI[of _ \<open>BENQ q x buf\<^sub>1\<close>])
                apply (rule exI[of _ buf\<^sub>2])
                apply (rule exI[of _ op\<^sub>1''])
                apply (rule exI[of _ op\<^sub>2'])
                apply (intro conjI)
                   apply (simp_all add: BENQ_def)
                 apply (metis (lifting) wstep_comp_op_L_BENQ BENQ_def)
                apply (metis append.assoc append_Nil2 diff_is_0_eq drop0 le_SucI take0)
                done
              subgoal for p x op\<^sub>2''
                apply (rule exI[of _ \<open>BTL p buf'\<close>])
                apply (rule exI[of _ buf\<^sub>1])
                apply (rule exI[of _ \<open>BENQ p x buf\<^sub>2\<close>])
                apply (rule exI[of _ op\<^sub>1'])
                apply (rule exI[of _ op\<^sub>2''])
                apply (intro conjI)
                   apply simp_all
                 apply (metis wstep_comp_op_R_BENQ)
                apply (simp add: BTL_def BENQ_def)
                apply (drule spec[of _ p])
                apply (erule exE)
                subgoal for n
                  apply (rule exI[of _ \<open>Suc n\<close>])
                  apply (intro conjI)
                    apply (metis drop_append drop_eq_Nil2 length_append not_less_eq_eq)
                   apply (metis drop_Suc drop_append tl_drop)
                  apply (metis BHD_def antisym_conv1 drop_append drop_eq_Nil2 length_append
                      take_append take_hd_drop)
                  done
                done
              subgoal for op\<^sub>1''
                apply (rule exI[of _ buf'])
                apply (rule exI[of _ buf\<^sub>1])
                apply (rule exI[of _ buf\<^sub>2])
                apply (rule exI[of _ op\<^sub>1''])
                apply (rule exI[of _ op\<^sub>2'])
                apply (simp_all add: wstep_comp_op_L_Tau)
                done
              subgoal for op\<^sub>2''
                apply (rule exI[of _ buf'])
                apply (rule exI[of _ buf\<^sub>1])
                apply (rule exI[of _ buf\<^sub>2])
                apply (rule exI[of _ op\<^sub>1'])
                apply (rule exI[of _ op\<^sub>2''])
                apply (simp_all add: wstep_comp_op_R_Tau)
                done
              done
            done
          done
        done
      subgoal for _ buf op\<^sub>1 op\<^sub>2
        apply (erule step_comp_op_elim; simp)
        subgoal for _ x op\<^sub>1' q
          apply (drule meta_spec[of _ \<open>BENQ q x buf\<close>])
          apply (drule meta_spec[of _ op\<^sub>1'])
          apply (drule meta_spec[of _ op\<^sub>2])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1'' op\<^sub>2'
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ \<open>buf\<^sub>1(q := x # buf\<^sub>1 q)\<close>])
            apply (rule exI[of _ buf\<^sub>2])
            apply (rule exI[of _ op\<^sub>1''])
            apply (rule exI[of _ op\<^sub>2'])
            apply (intro conjI)
            apply assumption
               apply (rule wstep_comp_op_L.intros(4))
                  apply simp_all
            apply (rule allI)
            subgoal for p
              apply (drule spec[of _ p])
              apply (intro conjI impI)
               apply (metis (no_types, opaque_lifting) BENQ_def Cons_eq_appendI add.commute
                  append_Nil append_assoc drop_append fun_upd_def length_append_singleton
                  nat_arith.suc1 take_append)
              apply (simp add: BENQ_diff_access)
              done
            done
          done
        subgoal for p x op\<^sub>2'
          apply (drule meta_spec[of _ \<open>BTL p buf\<close>])
          apply (drule meta_spec[of _ op\<^sub>1])
          apply (drule meta_spec[of _ op\<^sub>2'])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2''
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf\<^sub>1])
            apply (rule exI[of _ \<open>buf\<^sub>2(p := x # buf\<^sub>2 p)\<close>])
            apply (rule exI[of _ op\<^sub>1'])
            apply (rule exI[of _ op\<^sub>2''])
            apply (intro conjI)
                apply assumption
               apply assumption
              apply (rule wstep_comp_op_R.intros(3))
                  apply assumption
                 apply (simp_all add: BTL_def BHD_def)
            apply (rule allI)
            subgoal for p'
              apply (drule spec[of _ p'])
              apply (intro conjI impI)
               apply (erule exE)
              subgoal for n
                apply (rule exI[of _ \<open>Suc n\<close>])
                apply (smt (verit, best) Suc_le_mono add_Suc append_Cons diff_Suc_Suc drop_Suc
                    length_Cons list.collapse take_Suc)
                done
              apply (simp add: BENQ_diff_access)
              done
            done
          done
        subgoal for op\<^sub>1'
          apply (drule meta_spec[of _ buf])
          apply (drule meta_spec[of _ op\<^sub>1'])
          apply (drule meta_spec[of _ op\<^sub>2])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1'' op\<^sub>2'
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf\<^sub>1])
            apply (rule exI[of _ buf\<^sub>2])
            apply (rule exI[of _ op\<^sub>1''])
            apply (rule exI[of _ op\<^sub>2'])
            apply (auto intro: wstep_comp_op_L.intros(5))
            done
          done
        subgoal for op\<^sub>2'
          apply hypsubst_thin
          apply (drule meta_spec[of _ buf])
          apply (drule meta_spec[of _ op\<^sub>1])
          apply (drule meta_spec[of _ op\<^sub>2'])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2''
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf\<^sub>1])
            apply (rule exI[of _ buf\<^sub>2])
            apply (rule exI[of _ op\<^sub>1'])
            apply (rule exI[of _ op\<^sub>2''])
            apply (auto intro: wstep_comp_op_R.intros(5))
            done
          done
        done
      done
    done
  subgoal
    apply (elim exE conjE)
    subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2'
      apply hypsubst_thin
      apply (induct \<open>case io of Inp (Inl _) _ \<Rightarrow> io | Out (Inl _) _ \<Rightarrow> io | _ \<Rightarrow> Tau\<close> buf\<^sub>1 op\<^sub>1 op\<^sub>1' arbitrary: io buf pred: wstep_comp_op_L)
          apply (auto split: sum.splits IO.splits)
      subgoal for _ buf x p
        apply (rotate_tac 2)
        apply (induct \<open>Inp (Inr p) x :: ('a + 'b, 'c + 'd, 'e) IO\<close> buf\<^sub>2 op\<^sub>2 op\<^sub>2' arbitrary: buf pred: wstep_comp_op_R)
            apply auto
        subgoal for _ op\<^sub>2 buf\<^sub>2 op\<^sub>2' buf
          apply (rule wstep_converse_trans(2))
           apply blast
          apply (erule thin_rl)
          apply (erule thin_rl)
          apply (induct \<open>Tau :: ('a + 'b, 'c + 'd, 'e) IO\<close> buf\<^sub>2 op\<^sub>2 op\<^sub>2' arbitrary: buf pred: wstep_comp_op_R)
              apply auto
          subgoal
            by (metis drop0 ext le_0_eq list.size(3) rtranclp.rtrancl_refl)
          subgoal for p _ _ _ _ buf
            apply (drule meta_spec[of _ \<open>BTL p buf\<close>])
            apply (drule meta_mp)
            apply (rule allI)
            subgoal for p'
              apply (cases \<open>p' = p\<close>)
               apply (drule spec[of _ p])
               apply (metis BTL_access Suc_diff_1 diff_le_mono drop_Suc le_0_eq length_tl
                  linorder_not_le take_0 tl_take)
              apply (simp add: BTL_diff_access)
              done
            apply (metis BHD_def append_take_drop_id hd_append2 step_Tau_comp_op_R take_eq_Nil2
                wstep_steps_Tau wstep_trans_tau_1)
            done
          subgoal
            by (meson converse_rtranclp_into_rtranclp step_comp_op_R_Tau)
          done
        subgoal for p _ _ _ _ buf
          apply (drule meta_spec[of _ \<open>BTL p buf\<close>])
          apply (drule meta_mp)
           apply (rule allI)
          subgoal for p'
            apply (cases \<open>p' = p\<close>)
             apply (drule spec[of _ p])
             apply (metis (no_types, lifting) BTL_access One_nat_def Suc_diff_1
                bot_nat_0.extremum_uniqueI diff_le_mono drop0 drop_Suc length_drop not_le
                take_eq_Nil2 tl_take)
            apply (simp add: BTL_diff_access)
            done
          apply (metis BHD_def append_take_drop_id hd_append2 step_Tau_comp_op_R take_Nil
              wstep_trans_tau_1)
          done
        done
      subgoal for _ buf x p
        apply rotate_tac
        apply (induct \<open>Out (Inr p) x :: ('a + 'b, 'c + 'd, 'e) IO\<close> buf\<^sub>2 op\<^sub>2 op\<^sub>2' arbitrary: buf pred: wstep_comp_op_R)
            apply auto
        subgoal for p _ _ _ _ buf
          apply (drule meta_spec[of _ \<open>BTL p buf\<close>])
          apply (drule meta_mp)
           apply (rule allI)
          subgoal for p'
            apply (cases \<open>p' = p\<close>)
             apply (drule spec[of _ p])
             apply (metis (no_types, lifting) BTL_access One_nat_def Suc_diff_1
                bot_nat_0.extremum_uniqueI diff_le_mono drop0 drop_Suc length_drop not_le
                take_eq_Nil2 tl_take)
            apply (simp add: BTL_diff_access)
            done
          apply (metis BHD_def append_take_drop_id hd_append2 step_Tau_comp_op_R take_Nil
                wstep_trans_tau_1)
          done
        subgoal for _ op\<^sub>2 buf\<^sub>2 op\<^sub>2' buf
          apply (rule wstep_converse_trans(1))
           apply blast
          apply (erule thin_rl)
          apply (induct \<open>Tau :: ('a + 'b, 'c + 'd, 'e) IO\<close> buf\<^sub>2 op\<^sub>2 op\<^sub>2' arbitrary: buf pred: wstep_comp_op_R)
              apply auto
          subgoal
            by (metis drop0 ext le_0_eq list.size(3) rtranclp.rtrancl_refl)
          subgoal for p _ _ _ _ buf
            apply (drule meta_spec[of _ \<open>BTL p buf\<close>])
            apply (drule meta_mp)
            apply (rule allI)
            subgoal for p'
              apply (cases \<open>p' = p\<close>)
               apply (drule spec[of _ p])
               apply (metis BTL_access Suc_diff_1 diff_le_mono drop_Suc le_0_eq length_tl
                  linorder_not_le take_0 tl_take)
              apply (simp add: BTL_diff_access)
              done
            subgoal
              by (metis BHD_def append_take_drop_id hd_append2 step_Tau_comp_op_R take_eq_Nil2
                  wstep_steps_Tau wstep_trans_tau_1)
            done
          subgoal
            by (meson converse_rtranclp_into_rtranclp step_comp_op_R_Tau)
          done
        done
      subgoal for _ buf
        apply (induct \<open>Tau :: ('a + 'b, 'c + 'd, 'e) IO\<close> buf\<^sub>2 op\<^sub>2 op\<^sub>2' arbitrary: buf pred: wstep_comp_op_R)
            apply auto
        subgoal
          by (metis drop0 ext le_0_eq list.size(3) rtranclp.rtrancl_refl)
        subgoal for p _ _ _ _ buf
          apply (drule meta_spec[of _ \<open>BTL p buf\<close>])
          apply (drule meta_mp)
          apply (rule allI)
          subgoal for p'
            apply (cases \<open>p' = p\<close>)
             apply (drule spec[of _ p])
             apply (metis BTL_access Suc_diff_1 diff_le_mono drop_Suc le_0_eq length_tl
                linorder_not_le take_0 tl_take)
            apply (simp add: BTL_diff_access)
            done
          apply (metis BHD_def append_take_drop_id hd_append2 step_Tau_comp_op_R take_eq_Nil2
              wstep_steps_Tau wstep_trans_tau_1)
          done
        subgoal
          by (meson converse_rtranclp_into_rtranclp step_comp_op_R_Tau)
        done
      subgoal for _ _ _ _ _ _ buf
        apply (drule meta_spec[of _ Tau])
        apply (drule meta_spec[of _ buf])
        apply (drule meta_mp)
         apply simp_all
        apply (meson step_comp_op_L_Inp wstep_converse_trans(2))
        done
      subgoal for _ _ _ _ _ _ buf
        apply (drule meta_spec[of _ Tau])
        apply (drule meta_spec[of _ buf])
        apply (drule meta_mp)
         apply simp_all
        apply (rule wstep_converse_trans(1))
         apply blast
        apply assumption
        done
      subgoal for _ x _ _ q _ _ buf x' p
        apply (drule meta_spec[of _ \<open>Inp (Inl p) x'\<close>])
        apply (drule meta_spec[of _ \<open>BENQ q x buf\<close>])
        apply (drule meta_mp)
         apply simp_all
        apply (drule meta_mp)
         apply (rule allI)
        subgoal for p'
          apply (cases \<open>p' = q\<close>)
           apply (drule spec[of _ q])
           apply simp
           apply (smt (verit, del_insts) Cons_eq_appendI append.assoc drop_append
              length_append_singleton self_append_conv2 take_append)
          apply (smt (verit, ccfv_SIG) BENQ_diff_access)
          done
        apply blast
        done
      subgoal for _ x _ _ q _ _ buf x' p
        apply (drule meta_spec[of _ \<open>Inp (Inr p) x'\<close>])
        apply (drule meta_spec[of _ \<open>BENQ q x buf\<close>])
        apply (drule meta_mp)
         apply simp_all
        apply (drule meta_mp)
         apply (rule allI)
        subgoal for p'
          apply (cases \<open>p' = q\<close>)
            apply (drule spec[of _ q])
            apply simp
           apply (smt (verit, del_insts) Cons_eq_appendI append.assoc drop_append
              length_append_singleton self_append_conv2 take_append)
          apply (smt (verit, ccfv_SIG) BENQ_diff_access)
          done
        apply blast
        done
      subgoal for _ x _ _ q _ _ buf x' p
        apply (drule meta_spec[of _ \<open>Out (Inl p) x'\<close>])
        apply (drule meta_spec[of _ \<open>BENQ q x buf\<close>])
        apply (drule meta_mp)
         apply simp_all
        apply (drule meta_mp)
         apply (rule allI)
        subgoal for p'
          apply (cases \<open>p' = q\<close>)
           apply (drule spec[of _ q])
           apply simp
           apply (smt (verit, del_insts) Cons_eq_appendI append.assoc drop_append
              length_append_singleton self_append_conv2 take_append)
          apply (smt (verit, ccfv_SIG) BENQ_diff_access)
          done
        apply blast
        done
      subgoal for _ x _ _ q _ _ buf x' p
        apply (drule meta_spec[of _ \<open>Out (Inr p) x'\<close>])
        apply (drule meta_spec[of _ \<open>BENQ q x buf\<close>])
        apply (drule meta_mp)
         apply simp_all
        apply (drule meta_mp)
         apply (rule allI)
        subgoal for p'
          apply (cases \<open>p' = q\<close>)
           apply (drule spec[of _ q])
           apply simp
           apply (smt (verit, del_insts) Cons_eq_appendI append.assoc drop_append
              length_append_singleton self_append_conv2 take_append)
          apply (smt (verit, ccfv_SIG) BENQ_diff_access)
          done
        apply blast
        done
      subgoal for _ x _ _ q _ _ buf
        apply (drule meta_spec[of _ Tau])
        apply (drule meta_spec[of _ \<open>BENQ q x buf\<close>])
        apply (drule meta_mp)
         apply simp_all
        apply (drule meta_mp)
         apply (rule allI)
        subgoal for p
          apply (cases \<open>p = q\<close>)
           apply (drule spec[of _ q])
           apply simp
          apply (smt (verit, del_insts) Cons_eq_appendI append.assoc drop_append
              length_append_singleton self_append_conv2 take_append)
          apply (smt (verit, ccfv_SIG) BENQ_diff_access)
          done
        apply (metis step_Tau_comp_op_L wstep_steps_Tau wstep_trans_tau_1)
        done
      subgoal for _ _ _ _ buf
        apply (drule meta_spec[of _ Tau])
        apply (drule meta_spec[of _ buf])
        apply (metis IO.simps(11) step_comp_op_L_Tau wstep_steps_Tau wstep_trans_tau_1)
        done
      done
    done
  done

lemma wstep_pcomp_op_L_R:
  \<open>wstep io (comp_op (\<lambda>_. None) (\<lambda>_. []) op\<^sub>1 op\<^sub>2) op \<longleftrightarrow>
  (\<exists>op\<^sub>1' op\<^sub>2'. op = comp_op (\<lambda>_. None) (\<lambda>_. []) op\<^sub>1' op\<^sub>2'
  \<and> wstep_comp_op_L (\<lambda>_. None) (case io of Inp (Inl _) _ \<Rightarrow> io | Out (Inl _) _ \<Rightarrow> io | _ \<Rightarrow> Tau) (\<lambda>_. []) op\<^sub>1 op\<^sub>1'
  \<and> wstep_comp_op_R (\<lambda>_. None) (case io of Inp (Inr _) _ \<Rightarrow> io | Out (Inr _) _ \<Rightarrow> io | _ \<Rightarrow> Tau) (\<lambda>_. []) op\<^sub>2 op\<^sub>2')\<close>
  apply (subst wstep_comp_op_L_R[of io \<open>\<lambda>_. None\<close> \<open>\<lambda>_. []\<close> op\<^sub>1 op\<^sub>2 op])
  apply (rule iffI)
  subgoal
    apply (elim exE conjE)
    subgoal for _ buf\<^sub>1 _ op\<^sub>1' op\<^sub>2'
      apply (rule exI[of _ op\<^sub>1'])
      apply (rule exI[of _ op\<^sub>2'])
      apply (subgoal_tac \<open>buf\<^sub>1 = (\<lambda>_. [])\<close>)
       apply (metis (no_types, lifting) ext append_is_Nil_conv drop_Nil take_Nil)
      apply (erule thin_rl)
      apply (induct _ buf\<^sub>1 op\<^sub>1 op\<^sub>1' pred: wstep_comp_op_L)
          apply simp_all
      done
    done
  subgoal
    apply (elim exE conjE)
    subgoal for op\<^sub>1' op\<^sub>2'
      apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
      apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
      apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
      apply (rule exI[of _ op\<^sub>1'])
      apply (rule exI[of _ op\<^sub>2'])
      apply (simp add: IO.case_eq_if sum.case_eq_if)
      done
    done
  done

end