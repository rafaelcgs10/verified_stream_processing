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

lemma wstep_comp_op_L_Tau_BENQ:
  \<open>wstep_comp_op_L wire Tau buf op op' \<Longrightarrow> wire p = Some q \<Longrightarrow> step (Out p x) op' op'' \<Longrightarrow>
  wstep_comp_op_L wire Tau (BENQ q x buf) op op''\<close>
  apply (induct \<open>Tau :: ('c + 'b, 'a + 'd, 'e) IO\<close> buf op op' pred: wstep_comp_op_L)
      apply auto
  subgoal
    apply (rule wstep_comp_op_L.intros(4)[where ?buf=\<open>\<lambda>_. []\<close>])
       apply assumption+
     apply (rule wstep_comp_op_L.intros(1))
       apply (simp_all add: BENQ_def)
    done
  subgoal
    apply (rule wstep_comp_op_L.intros(4))
       apply assumption+
    apply (simp add: BENQ_def fun_upd_twist)
    done
  subgoal
    apply (rule wstep_comp_op_L.intros(5))
     apply assumption+
    done
  done

lemma wstep_comp_op_L_Tau_Tau:
  \<open>wstep_comp_op_L wire Tau buf op op' \<Longrightarrow> step Tau op' op'' \<Longrightarrow>
  wstep_comp_op_L wire Tau buf op op''\<close>
  apply (induct \<open>Tau :: ('c + 'b, 'a + 'd, 'e) IO\<close> buf op op' pred: wstep_comp_op_L)
      apply auto
  subgoal
    apply (rule wstep_comp_op_L.intros(5))
     apply assumption
    apply (rule wstep_comp_op_L.intros(1))
      apply simp_all
    done
  subgoal
    apply (rule wstep_comp_op_L.intros(4))
       apply assumption+
    apply (rule refl)
    done
  subgoal
    apply (rule wstep_comp_op_L.intros(5))
     apply assumption+
    done
  done

lemma wstep_comp_op_L_Inp_BENQ:
  \<open>wstep_comp_op_L wire (Inp (Inl p) x) buf op op' \<Longrightarrow> wire p' = Some q \<Longrightarrow> step (Out p' x') op' op'' \<Longrightarrow>
  wstep_comp_op_L wire (Inp (Inl p) x) (BENQ q x' buf) op op''\<close>
  apply (induct \<open>Inp (Inl p) x :: ('c + 'b, 'a + 'd, 'e) IO\<close> buf op op' pred: wstep_comp_op_L)
      apply auto
  subgoal
    apply (rule wstep_comp_op_L.intros(2))
      apply (rule refl)
     apply assumption
    apply (simp add: wstep_comp_op_L_Tau_BENQ)
    done
  subgoal
    apply (rule wstep_comp_op_L.intros(4))
       apply assumption+
    apply (simp add: BENQ_def fun_upd_twist)
    done
  subgoal
    apply (rule wstep_comp_op_L.intros(5))
     apply assumption+
    done
  done

lemma wstep_comp_op_L_Inp_Tau:
  \<open>wstep_comp_op_L wire (Inp (Inl p) x) buf op op' \<Longrightarrow> step Tau op' op'' \<Longrightarrow>
  wstep_comp_op_L wire (Inp (Inl p) x) buf op op''\<close>
  apply (induct \<open>Inp (Inl p) x :: ('c + 'b, 'a + 'd, 'e) IO\<close> buf op op' pred: wstep_comp_op_L)
      apply auto
  subgoal
    apply (rule wstep_comp_op_L.intros(2))
      apply (rule refl)
     apply assumption
    apply (simp add: wstep_comp_op_L_Tau_Tau)
    done
  subgoal
    apply (rule wstep_comp_op_L.intros(4))
       apply assumption+
    apply (rule refl)
    done
  subgoal
    apply (rule wstep_comp_op_L.intros(5))
     apply assumption+
    done
  done

lemma wstep_comp_op_R_Tau_BENQ:
  \<open>wstep_comp_op_R wire Tau buf op op' \<Longrightarrow> p \<in> ran wire \<Longrightarrow> step (Inp p x) op' op'' \<Longrightarrow>
  wstep_comp_op_R wire Tau (BENQ p x buf) op op''\<close>
  apply (induct \<open>Tau :: ('c + 'b, 'a + 'd, 'e) IO\<close> buf op op' pred: wstep_comp_op_R)
      apply auto
  subgoal
    apply (rule wstep_comp_op_R.intros(3))
        apply assumption
       apply assumption
      apply (rule wstep_comp_op_R.intros(1))
        apply simp_all
    done
  subgoal
    apply (rule wstep_comp_op_R.intros(3))
        apply assumption
       apply assumption
      apply (metis BAPPEND_BENQ BAPPEND_BTL BULK_BENQ_left_neutral)
     apply (metis BENQ_access BENQ_diff_access Nil_is_append_conv)
    apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
    done
  subgoal
    apply (rule wstep_comp_op_R.intros(5))
     apply assumption+
    done
  done

lemma wstep_comp_op_R_Tau_Tau:
  \<open>wstep_comp_op_R wire Tau buf op op' \<Longrightarrow> step Tau op' op'' \<Longrightarrow>
  wstep_comp_op_R wire Tau buf op op''\<close>
  apply (induct \<open>Tau :: ('c + 'b, 'a + 'd, 'e) IO\<close> buf op op' pred: wstep_comp_op_R)
      apply auto
  subgoal
    apply (rule wstep_comp_op_R.intros(5))
     apply assumption
    apply (rule wstep_comp_op_R.intros(1))
      apply simp_all
    done
  subgoal
    apply (rule wstep_comp_op_R.intros(3))
        apply assumption+
    apply (rule refl)
    done
  subgoal
    apply (rule wstep_comp_op_R.intros(5))
     apply assumption+
    done
  done

lemma wstep_comp_op_R_Out_BENQ:
  \<open>wstep_comp_op_R wire (Out (Inr p) x) buf op op' \<Longrightarrow> p' \<in> ran wire \<Longrightarrow> step (Inp p' x') op' op'' \<Longrightarrow>
  wstep_comp_op_R wire (Out (Inr p) x) (BENQ p' x' buf) op op''\<close>
  apply (induct \<open>Out (Inr p) x :: ('c + 'b, 'a + 'd, 'e) IO\<close> buf op op' pred: wstep_comp_op_R)
      apply auto
  subgoal
    apply (rule wstep_comp_op_R.intros(3))
        apply assumption+
      apply (smt (verit, best) BENQ_access BENQ_def BTL_access BTL_def fun_upd_other fun_upd_twist fun_upd_upd tl_append2)
     apply (metis BENQ_access BENQ_diff_access Nil_is_append_conv)
    by (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
  subgoal
    apply (rule wstep_comp_op_R.intros(4))
      apply (rule refl)
     apply assumption
    apply (simp add: wstep_comp_op_R_Tau_BENQ)
    done
  subgoal
    apply (rule wstep_comp_op_R.intros(5))
     apply assumption+
    done
  done

lemma wstep_comp_op_R_Out_Tau:
  \<open>wstep_comp_op_R wire (Out (Inr p) x) buf op op' \<Longrightarrow> step Tau op' op'' \<Longrightarrow>
  wstep_comp_op_R wire (Out (Inr p) x) buf op op''\<close>
  apply (induct \<open>Out (Inr p) x :: ('c + 'b, 'a + 'd, 'e) IO\<close> buf op op' pred: wstep_comp_op_R)
      apply auto
  subgoal
    apply (rule wstep_comp_op_R.intros(3))
        apply simp_all
    done
  subgoal
    apply (rule wstep_comp_op_R.intros(4))
    apply (rule refl)
     apply assumption
    apply (simp add: wstep_comp_op_R_Tau_Tau)
    done
  subgoal
    apply (rule wstep_comp_op_R.intros(5))
     apply assumption+
    done
  done

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
    apply (unfold wstep_def)
    apply (erule relcomppE)+
    apply (auto split: sum.splits IO.splits)
    subgoal for op'' op''' p x
      apply (induct \<open>comp_op wire buf op\<^sub>1 op\<^sub>2\<close> arbitrary: buf op\<^sub>1 op\<^sub>2 rule: converse_rtranclp_induct)
      subgoal for buf op\<^sub>1 op\<^sub>2
        apply hypsubst_thin
        apply rotate_tac
        apply (induct op' rule: rtranclp_induct)
        subgoal
          apply (auto elim!: step_comp_op_elim)
          subgoal for op\<^sub>1'
            apply (rule exI[of _ buf])
            apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
            apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
            apply (rule exI[of _ op\<^sub>1'])
            apply (rule exI[of _ op\<^sub>2])
            apply (auto intro: wstep_comp_op_L.intros wstep_comp_op_R.intros)
            done
          done
        subgoal
          apply simp
          apply (elim exE)
          subgoal for buf' buf1 buf2 op\<^sub>1' op\<^sub>2'
            apply (auto elim!: step_comp_op_elim)
            subgoal for p' x' op\<^sub>1'' q op\<^sub>1'''
              apply hypsubst_thin
              apply (rule exI[of _ \<open>BENQ q x' buf'\<close>])
              apply (rule exI[of _ \<open>BENQ q x' buf1\<close>])
              apply (rule exI[of _ buf2])
              apply (rule exI[of _ op\<^sub>1''])
              apply (rule exI[of _ op\<^sub>2'])
              apply (intro conjI)
              subgoal
                by (rule refl)
              subgoal
                by (simp add: wstep_comp_op_L_Inp_BENQ)
              subgoal
                by assumption
              subgoal
                apply (auto simp: BENQ_def)
                by (metis append_Nil2 append_assoc diff_is_0_eq' drop_0 le_SucI take_0)
              done
            subgoal for p' op\<^sub>2'' op\<^sub>1''
              apply hypsubst_thin
              apply (rule exI[of _ \<open>BTL p' buf'\<close>])
              apply (rule exI[of _ buf1])
              apply (rule exI[of _ \<open>BENQ p' (BHD p' buf') buf2\<close>])
              apply (rule exI[of _ op\<^sub>1'])
              apply (rule exI[of _ op\<^sub>2''])
              apply (intro conjI)
              subgoal
                by (rule refl)
              subgoal
                by assumption
              subgoal
                by (simp add: wstep_comp_op_R_Tau_BENQ)
              subgoal
                apply (auto simp: BTL_def BENQ_def)
                apply (drule spec[of _ p'])
                apply (elim exE)
                subgoal for n
                  apply (rule exI[of _ \<open>Suc n\<close>])
                  apply auto
                     apply (simp add: drop_Suc tl_drop)
                    apply (simp add: BHD_def take_hd_drop)
                   apply (metis drop_Suc drop_append drop_tl)
                  by (metis (no_types, lifting) BHD_def Nil_is_append_conv append.assoc drop_append drop_eq_Nil2 linorder_not_le take_append
                      take_hd_drop)
                done
              done
            subgoal for op\<^sub>1'' op\<^sub>1'''
              apply hypsubst_thin
              apply (rule exI[of _ buf'])
              apply (rule exI[of _ buf1])
              apply (rule exI[of _ buf2])
              apply (rule exI[of _ op\<^sub>1''])
              apply (rule exI[of _ op\<^sub>2'])
              apply (intro conjI)
              subgoal
                by (rule refl)
              subgoal
                by (simp add: wstep_comp_op_L_Inp_Tau)
              subgoal
                by assumption
              subgoal
                by assumption
              done
            subgoal for op\<^sub>2'' op\<^sub>1''
              apply hypsubst_thin
              apply (rule exI[of _ buf'])
              apply (rule exI[of _ buf1])
              apply (rule exI[of _ buf2])
              apply (rule exI[of _ op\<^sub>1'])
              apply (rule exI[of _ op\<^sub>2''])
              apply (intro conjI)
              subgoal
                by (rule refl)
              subgoal
                by assumption
              subgoal
                by (simp add: wstep_comp_op_R_Tau_Tau)
              subgoal
                by assumption
              done
            done
          done
        done
      subgoal for op'''' buf op\<^sub>1 op\<^sub>2
        apply (auto elim!: step_comp_op_elim)
        subgoal for p' x' op\<^sub>1' q
          apply hypsubst_thin
          apply (drule meta_spec[of _ \<open>BENQ q x' buf\<close>])
          apply (drule meta_spec[of _ op\<^sub>1'])
          apply (drule meta_spec[of _ op\<^sub>2])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1'' op\<^sub>2'
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ \<open>buf1(q := x' # buf1 q)\<close>])
            apply (rule exI[of _ buf2])
            apply (rule exI[of _ op\<^sub>1''])
            apply (rule exI[of _ op\<^sub>2'])
            apply (intro conjI)
            subgoal
              by assumption
            subgoal
              apply (rule wstep_comp_op_L.intros(4))
              by simp_all
            subgoal
              by assumption
            subgoal
              apply (rule allI)
              subgoal for p''
                apply (cases \<open>p'' = q\<close>; simp?)
                subgoal
                  apply (drule spec[of _ q])
                  by (metis BENQ_def Cons_eq_appendI add.commute append_Nil append_eq_append_conv2 drop_append fun_upd_same
                      length_append_singleton nat_arith.suc1 take_append)
                subgoal
                  by (metis BENQ_diff_access)
                done
              done
            done
          done
        subgoal for p' op\<^sub>2'
          apply hypsubst_thin
          apply (drule meta_spec[of _ \<open>BTL p' buf\<close>])
          apply (drule meta_spec[of _ op\<^sub>1])
          apply (drule meta_spec[of _ op\<^sub>2'])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1' op\<^sub>2''
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf1])
            apply (rule exI[of _ \<open>buf2(p' := BHD p' buf # buf2 p')\<close>])
            apply (rule exI[of _ op\<^sub>1'])
            apply (rule exI[of _ op\<^sub>2''])
            apply (intro conjI)
               apply assumption
              apply assumption
            subgoal
              apply (rule wstep_comp_op_R.intros(3))
                  apply assumption+
                apply (simp_all add: BTL_def BHD_def)
              done
            subgoal
              apply (rule allI)
              subgoal for p''
                apply (cases \<open>p'' = p'\<close>; simp?)
                subgoal
                  apply (drule spec[of _ p'])
                  apply (erule exE)
                  subgoal for n
                    apply (rule exI[of _ \<open>Suc n\<close>])
                    by (metis BHD_def BTL_access Cons_eq_appendI Nitpick.size_list_simp(2) add_le_cancel_left diff_Suc_Suc drop_Suc plus_1_eq_Suc
                        plus_nat.simps(2) take_Suc)
                  done
                subgoal
                  by (metis BTL_diff_access)
                done
              done
            done
          done
        subgoal for op\<^sub>1'
          apply hypsubst_thin
          apply (drule meta_spec[of _ buf])
          apply (drule meta_spec[of _ op\<^sub>1'])
          apply (drule meta_spec[of _ op\<^sub>2])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1'' op\<^sub>2'
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf1])
            apply (rule exI[of _ buf2])
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
          subgoal for buf' buf1 buf2 op\<^sub>1' op\<^sub>2''
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf1])
            apply (rule exI[of _ buf2])
            apply (rule exI[of _ op\<^sub>1'])
            apply (rule exI[of _ op\<^sub>2''])
            apply (auto intro: wstep_comp_op_R.intros(5))
            done
          done
        done
      done
    subgoal for op op'' p x
      sorry
    subgoal
      sorry
    subgoal
      apply (induct \<open>comp_op wire buf op\<^sub>1 op\<^sub>2\<close> arbitrary: buf op\<^sub>1 op\<^sub>2 rule: converse_rtranclp_induct)
      subgoal for buf op\<^sub>1 op\<^sub>2
        apply hypsubst_thin
        apply rotate_tac
        apply (induct op' rule: rtranclp_induct)
        subgoal
          apply (auto elim!: step_comp_op_elim)
          subgoal for op\<^sub>2'
            apply (rule exI[of _ buf])
            apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
            apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
            apply (rule exI[of _ op\<^sub>1])
            apply (rule exI[of _ op\<^sub>2'])
            apply (auto intro: wstep_comp_op_L.intros wstep_comp_op_R.intros)
            done
          done
        subgoal
          apply simp
          apply (elim exE)
          subgoal for buf' buf1 buf2 op\<^sub>1' op\<^sub>2'
            apply (auto elim!: step_comp_op_elim)
            subgoal for p' x' op\<^sub>1'' q op\<^sub>2''
              apply hypsubst_thin
              apply (rule exI[of _ \<open>BENQ q x' buf'\<close>])
              apply (rule exI[of _ \<open>BENQ q x' buf1\<close>])
              apply (rule exI[of _ buf2])
              apply (rule exI[of _ op\<^sub>1''])
              apply (rule exI[of _ op\<^sub>2'])
              apply (intro conjI)
              subgoal
                by (rule refl)
              subgoal
                by (simp add: wstep_comp_op_L_Tau_BENQ)
              subgoal
                by assumption
              subgoal
                apply (auto simp: BENQ_def)
                by (metis append_Nil2 append_assoc diff_is_0_eq' drop_0 le_SucI take_0)
              done
            subgoal for p' op\<^sub>2'' op\<^sub>2'''
              apply hypsubst_thin
              apply (rule exI[of _ \<open>BTL p' buf'\<close>])
              apply (rule exI[of _ buf1])
              apply (rule exI[of _ \<open>BENQ p' (BHD p' buf') buf2\<close>])
              apply (rule exI[of _ op\<^sub>1'])
              apply (rule exI[of _ op\<^sub>2''])
              apply (intro conjI)
              subgoal
                by (rule refl)
              subgoal
                by assumption
              subgoal
                by (simp add: wstep_comp_op_R_Out_BENQ)
              subgoal
                apply (auto simp: BTL_def BENQ_def)
                apply (drule spec[of _ p'])
                apply (elim exE)
                subgoal for n
                  apply (rule exI[of _ \<open>Suc n\<close>])
                  apply auto
                     apply (simp add: drop_Suc tl_drop)
                    apply (simp add: BHD_def take_hd_drop)
                   apply (metis drop_Suc drop_append drop_tl)
                  by (metis (no_types, lifting) BHD_def Nil_is_append_conv append.assoc drop_append drop_eq_Nil2 linorder_not_le take_append
                      take_hd_drop)
                done
              done
            subgoal for op\<^sub>1'' op\<^sub>2''
              apply hypsubst_thin
              apply (rule exI[of _ buf'])
              apply (rule exI[of _ buf1])
              apply (rule exI[of _ buf2])
              apply (rule exI[of _ op\<^sub>1''])
              apply (rule exI[of _ op\<^sub>2'])
              apply (intro conjI)
              subgoal
                by (rule refl)
              subgoal
                by (simp add: wstep_comp_op_L_Tau_Tau)
              subgoal
                by assumption
              subgoal
                by assumption
              done
            subgoal for op\<^sub>2'' op\<^sub>2'''
              apply hypsubst_thin
              apply (rule exI[of _ buf'])
              apply (rule exI[of _ buf1])
              apply (rule exI[of _ buf2])
              apply (rule exI[of _ op\<^sub>1'])
              apply (rule exI[of _ op\<^sub>2''])
              apply (intro conjI)
              subgoal
                by (rule refl)
              subgoal
                by assumption
              subgoal
                by (simp add: wstep_comp_op_R_Out_Tau)
              subgoal
                by assumption
              done
            done
          done
        done
      subgoal for op'''' buf op\<^sub>1 op\<^sub>2
        apply (auto elim!: step_comp_op_elim)
        subgoal for p' x' op\<^sub>1' q
          apply hypsubst_thin
          apply (drule meta_spec[of _ \<open>BENQ q x' buf\<close>])
          apply (drule meta_spec[of _ op\<^sub>1'])
          apply (drule meta_spec[of _ op\<^sub>2])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1'' op\<^sub>2'
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ \<open>buf1(q := x' # buf1 q)\<close>])
            apply (rule exI[of _ buf2])
            apply (rule exI[of _ op\<^sub>1''])
            apply (rule exI[of _ op\<^sub>2'])
            apply (intro conjI)
            subgoal
              by assumption
            subgoal
              apply (rule wstep_comp_op_L.intros(4))
              by simp_all
            subgoal
              by assumption
            subgoal
              apply (rule allI)
              subgoal for p''
                apply (cases \<open>p'' = q\<close>; simp?)
                subgoal
                  apply (drule spec[of _ q])
                  by (metis BENQ_def Cons_eq_appendI add.commute append_Nil append_eq_append_conv2 drop_append fun_upd_same
                      length_append_singleton nat_arith.suc1 take_append)
                subgoal
                  by (metis BENQ_diff_access)
                done
              done
            done
          done
        subgoal for p' op\<^sub>2'
          apply hypsubst_thin
          apply (drule meta_spec[of _ \<open>BTL p' buf\<close>])
          apply (drule meta_spec[of _ op\<^sub>1])
          apply (drule meta_spec[of _ op\<^sub>2'])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1' op\<^sub>2''
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf1])
            apply (rule exI[of _ \<open>buf2(p' := BHD p' buf # buf2 p')\<close>])
            apply (rule exI[of _ op\<^sub>1'])
            apply (rule exI[of _ op\<^sub>2''])
            apply (intro conjI)
               apply assumption
              apply assumption
            subgoal
              apply (rule wstep_comp_op_R.intros(3))
                  apply assumption+
                apply (simp_all add: BTL_def BHD_def)
              done
            subgoal
              apply (rule allI)
              subgoal for p''
                apply (cases \<open>p'' = p'\<close>; simp?)
                subgoal
                  apply (drule spec[of _ p'])
                  apply (erule exE)
                  subgoal for n
                    apply (rule exI[of _ \<open>Suc n\<close>])
                    by (metis BHD_def BTL_access Cons_eq_appendI Nitpick.size_list_simp(2) add_le_cancel_left diff_Suc_Suc drop_Suc plus_1_eq_Suc
                        plus_nat.simps(2) take_Suc)
                  done
                subgoal
                  by (metis BTL_diff_access)
                done
              done
            done
          done
        subgoal for op\<^sub>1'
          apply hypsubst_thin
          apply (drule meta_spec[of _ buf])
          apply (drule meta_spec[of _ op\<^sub>1'])
          apply (drule meta_spec[of _ op\<^sub>2])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1'' op\<^sub>2'
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf1])
            apply (rule exI[of _ buf2])
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
          subgoal for buf' buf1 buf2 op\<^sub>1' op\<^sub>2''
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf1])
            apply (rule exI[of _ buf2])
            apply (rule exI[of _ op\<^sub>1'])
            apply (rule exI[of _ op\<^sub>2''])
            apply (auto intro: wstep_comp_op_R.intros(5))
            done
          done
        done
      done
    subgoal for op'' op'''
      apply (induct \<open>comp_op wire buf op\<^sub>1 op\<^sub>2\<close> arbitrary: buf op\<^sub>1 op\<^sub>2 rule: converse_rtranclp_induct)
      subgoal for buf op\<^sub>1 op\<^sub>2
        apply hypsubst_thin
        apply (induct op' rule: rtranclp_induct)
        subgoal
          apply (auto elim!: step_comp_op_elim)
          subgoal for p x op\<^sub>1' q
            apply (rule exI[of _ \<open>BENQ q x buf\<close>])
            apply (rule exI[of _ \<open>(\<lambda>_. [])(q := [x])\<close>])
            apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
            apply (rule exI[of _ op\<^sub>1'])
            apply (rule exI[of _ op\<^sub>2])
            apply (intro conjI)
            subgoal
              by (rule refl)
            subgoal
              apply (rule wstep_comp_op_L.intros(4)[where ?buf=\<open>\<lambda>_. []\<close>])
                 apply assumption+
               apply (rule wstep_comp_op_L.intros(1))
                 apply simp_all
              done
            subgoal
               apply (rule wstep_comp_op_R.intros(1))
                apply simp_all
              done
            subgoal
              by (metis (no_types, lifting) BENQ_access BENQ_diff_access append_Nil2 bot_nat_0.extremum drop0 fun_upd_apply take0
                  zero_diff)
            done
          subgoal for p op\<^sub>2'
            apply (rule exI[of _ \<open>BTL p buf\<close>])
            apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
            apply (rule exI[of _ \<open>(\<lambda>_. [])(p := [BHD p buf])\<close>])
            apply (rule exI[of _ op\<^sub>1])
            apply (rule exI[of _ op\<^sub>2'])
            apply (intro conjI)
            subgoal
              by (rule refl)
            subgoal
              apply (rule wstep_comp_op_L.intros(1))
                apply simp_all
              done
            subgoal
              apply (rule wstep_comp_op_R.intros(3))
                  apply assumption+
                apply (rule wstep_comp_op_R.intros(1))
                  apply (simp_all add: BTL_def BHD_def)
              done
            subgoal
              by (metis (no_types, lifting) BHD_def BTL_def add.right_neutral append_Nil2 bot_nat_0.extremum drop0 drop_Nil drop_Suc
                  fun_upd_apply length_greater_0_conv less_eq_Suc_le list.size(3) take0 take_Nil take_Suc)
            done
          subgoal for op\<^sub>1'
            apply (rule exI[of _ buf])
            apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
            apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
            apply (rule exI[of _ op\<^sub>1'])
            apply (rule exI[of _ op\<^sub>2])
            apply (intro conjI)
            subgoal
              by (rule refl)
            subgoal
              apply (rule wstep_comp_op_L.intros(5))
               apply assumption
              apply (rule wstep_comp_op_L.intros(1))
                apply simp_all
              done
            subgoal
              apply (rule wstep_comp_op_R.intros(1))
                apply simp_all
              done
            subgoal
              by fastforce
            done
          subgoal for op\<^sub>2'
            apply (rule exI[of _ buf])
            apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
            apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
            apply (rule exI[of _ op\<^sub>1])
            apply (rule exI[of _ op\<^sub>2'])
            apply (intro conjI)
            subgoal
              by (rule refl)
            subgoal
              apply (rule wstep_comp_op_L.intros(1))
                apply simp_all
              done
            subgoal
              apply (rule wstep_comp_op_R.intros(5))
               apply assumption
              apply (rule wstep_comp_op_R.intros(1))
                apply simp_all
              done
            subgoal
              by fastforce
            done
          done
        subgoal for op op'
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1' op\<^sub>2'
            apply hypsubst_thin
            apply (erule step_comp_op_elim; simp)
            subgoal for p x op\<^sub>1'' q
              apply (rule exI[of _ \<open>BENQ q x buf'\<close>])
              apply (rule exI[of _ \<open>BENQ q x buf1\<close>])
              apply (rule exI[of _ buf2])
              apply (rule exI[of _ op\<^sub>1''])
              apply (rule exI[of _ op\<^sub>2'])
              apply (simp add: wstep_comp_op_L_Tau_BENQ)
              apply (rule allI)
              subgoal for p'
                apply (cases \<open>p' = q\<close>; simp?)
                subgoal
                  apply (drule spec[of _ q])
                  by fastforce
                subgoal
                  by (metis BENQ_diff_access)
                done
              done
            subgoal for p x op\<^sub>2''
              apply (rule exI[of _ \<open>BTL p buf'\<close>])
              apply (rule exI[of _ buf1])
              apply (rule exI[of _ \<open>BENQ p (BHD p buf') buf2\<close>])
              apply (rule exI[of _ op\<^sub>1'])
              apply (rule exI[of _ op\<^sub>2''])
              apply (simp add: wstep_comp_op_R_Tau_BENQ)
              apply (rule allI)
              subgoal for p'
                apply (cases \<open>p' = p\<close>; simp?)
                subgoal
                  apply (drule spec[of _ p])
                  apply (erule exE)
                  subgoal for n
                    apply (rule exI[of _ \<open>Suc n\<close>])
                    by (metis (no_types, lifting) BHD_def BTL_access drop_Suc drop_append drop_eq_Nil2 length_append linorder_not_le
                        not_less_eq_eq take_append take_hd_drop tl_drop)
                  done
                subgoal
                  by (simp add: BENQ_diff_access BTL_diff_access)
                done
              done
            subgoal for op\<^sub>1''
              apply (rule exI[of _ buf'])
              apply (rule exI[of _ buf1])
              apply (rule exI[of _ buf2])
              apply (rule exI[of _ op\<^sub>1''])
              apply (rule exI[of _ op\<^sub>2'])
              apply (simp add: wstep_comp_op_L_Tau_Tau)
              done
            subgoal for op\<^sub>2''
              apply (rule exI[of _ buf'])
              apply (rule exI[of _ buf1])
              apply (rule exI[of _ buf2])
              apply (rule exI[of _ op\<^sub>1'])
              apply (rule exI[of _ op\<^sub>2''])
              apply (simp add: wstep_comp_op_R_Tau_Tau)
              done
            done
          done
        done
      subgoal for op buf op\<^sub>1 op\<^sub>2
        apply (erule step_comp_op_elim; simp)
        subgoal for p x op\<^sub>1' q
          apply (drule meta_spec[of _ \<open>BENQ q x buf\<close>])
          apply (drule meta_spec[of _ op\<^sub>1'])
          apply (drule meta_spec[of _ op\<^sub>2])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1'' op\<^sub>2'
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ \<open>buf1(q := x # buf1 q)\<close>])
            apply (rule exI[of _ buf2])
            apply (rule exI[of _ op\<^sub>1''])
            apply (rule exI[of _ op\<^sub>2'])
            apply (simp add: wstep_comp_op_L.intros(4))
            apply (rule allI)
            subgoal for p'
              apply (intro conjI impI)
              apply (metis BENQ_def add_Suc_right append.assoc append_Cons append_Nil drop_append fun_upd_same length_Cons length_append
                  take_append)
              by (metis BENQ_diff_access)
            done
          done
        subgoal for p x op\<^sub>2'
          apply (drule meta_spec[of _ \<open>BTL p buf\<close>])
          apply (drule meta_spec[of _ op\<^sub>1])
          apply (drule meta_spec[of _ op\<^sub>2'])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1' op\<^sub>2''
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf1])
            apply (rule exI[of _ \<open>buf2(p := x # buf2 p)\<close>])
            apply (rule exI[of _ op\<^sub>1'])
            apply (rule exI[of _ op\<^sub>2''])
            apply simp
            apply (intro allI conjI impI)
              apply (rule wstep_comp_op_R.intros(3))
                  apply assumption+
                apply (simp_all add: BHD_def BTL_def)
            subgoal
              apply (drule spec[of _ p])
              apply simp
              by (metis One_nat_def Suc_diff_eq_diff_pred add_eq_if append_Cons drop_Suc_Cons length_greater_0_conv list.collapse
                  list.size(3) not_less_eq_eq take_Suc)
            subgoal
              by presburger
            done
          done
        subgoal for op\<^sub>1'
          apply (drule meta_spec[of _ buf])
          apply (drule meta_spec[of _ op\<^sub>1'])
          apply (drule meta_spec[of _ op\<^sub>2])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1'' op\<^sub>2'
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf1])
            apply (rule exI[of _ buf2])
            apply (rule exI[of _ op\<^sub>1''])
            apply (rule exI[of _ op\<^sub>2'])
            apply (simp add: wstep_comp_op_L.intros(5))
            done
          done
        subgoal for op\<^sub>2'
          apply (drule meta_spec[of _ buf])
          apply (drule meta_spec[of _ op\<^sub>1])
          apply (drule meta_spec[of _ op\<^sub>2'])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1' op\<^sub>2''
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf1])
            apply (rule exI[of _ buf2])
            apply (rule exI[of _ op\<^sub>1'])
            apply (rule exI[of _ op\<^sub>2''])
            apply (simp add: wstep_comp_op_R.intros(5))
            done
          done
        done
      done
    subgoal
      apply (induct \<open>comp_op wire buf op\<^sub>1 op\<^sub>2\<close> arbitrary: buf op\<^sub>1 op\<^sub>2 rule: converse_rtranclp_induct)
      subgoal for buf op\<^sub>1 op\<^sub>2
        apply hypsubst_thin
        apply (induct op' rule: rtranclp_induct)
        subgoal
          apply (rule exI[of _ buf])
          apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
          apply (rule exI[of _ \<open>\<lambda>_. []\<close>])
          apply (rule exI[of _ op\<^sub>1])
          apply (rule exI[of _ op\<^sub>2])
          apply (auto intro: wstep_comp_op_L.intros wstep_comp_op_R.intros)
          done
        subgoal for op op'
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1' op\<^sub>2'
            apply hypsubst_thin
            apply (erule step_comp_op_elim; simp)
            subgoal for p x op\<^sub>1'' q
              apply (rule exI[of _ \<open>BENQ q x buf'\<close>])
              apply (rule exI[of _ \<open>BENQ q x buf1\<close>])
              apply (rule exI[of _ buf2])
              apply (rule exI[of _ op\<^sub>1''])
              apply (rule exI[of _ op\<^sub>2'])
              apply (simp add: wstep_comp_op_L_Tau_BENQ)
              apply (rule allI)
              subgoal for p'
                apply (cases \<open>p' = q\<close>; simp?)
                subgoal
                  apply (drule spec[of _ q])
                  by fastforce
                subgoal
                  by (metis BENQ_diff_access)
                done
              done
            subgoal for p x op\<^sub>2''
              apply (rule exI[of _ \<open>BTL p buf'\<close>])
              apply (rule exI[of _ buf1])
              apply (rule exI[of _ \<open>BENQ p (BHD p buf') buf2\<close>])
              apply (rule exI[of _ op\<^sub>1'])
              apply (rule exI[of _ op\<^sub>2''])
              apply (simp add: wstep_comp_op_R_Tau_BENQ)
              apply (rule allI)
              subgoal for p'
                apply (cases \<open>p' = p\<close>; simp?)
                subgoal
                  apply (drule spec[of _ p])
                  apply (erule exE)
                  subgoal for n
                    apply (rule exI[of _ \<open>Suc n\<close>])
                    by (metis (no_types, lifting) BHD_def BTL_access drop_Suc drop_append drop_eq_Nil2 length_append linorder_not_le
                        not_less_eq_eq take_append take_hd_drop tl_drop)
                  done
                subgoal
                  by (simp add: BENQ_diff_access BTL_diff_access)
                done
              done
            subgoal for op\<^sub>1''
              apply (rule exI[of _ buf'])
              apply (rule exI[of _ buf1])
              apply (rule exI[of _ buf2])
              apply (rule exI[of _ op\<^sub>1''])
              apply (rule exI[of _ op\<^sub>2'])
              apply (simp add: wstep_comp_op_L_Tau_Tau)
              done
            subgoal for op\<^sub>2''
              apply (rule exI[of _ buf'])
              apply (rule exI[of _ buf1])
              apply (rule exI[of _ buf2])
              apply (rule exI[of _ op\<^sub>1'])
              apply (rule exI[of _ op\<^sub>2''])
              apply (simp add: wstep_comp_op_R_Tau_Tau)
              done
            done
          done
        done
      subgoal for op buf op\<^sub>1 op\<^sub>2
        apply (erule step_comp_op_elim; simp)
        subgoal for p x op\<^sub>1' q
          apply (drule meta_spec[of _ \<open>BENQ q x buf\<close>])
          apply (drule meta_spec[of _ op\<^sub>1'])
          apply (drule meta_spec[of _ op\<^sub>2])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1'' op\<^sub>2'
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ \<open>buf1(q := x # buf1 q)\<close>])
            apply (rule exI[of _ buf2])
            apply (rule exI[of _ op\<^sub>1''])
            apply (rule exI[of _ op\<^sub>2'])
            apply (simp add: wstep_comp_op_L.intros(4))
            apply (rule allI)
            subgoal for p'
              apply (intro conjI impI)
              apply (metis BENQ_def add_Suc_right append.assoc append_Cons append_Nil drop_append fun_upd_same length_Cons length_append
                  take_append)
              by (metis BENQ_diff_access)
            done
          done
        subgoal for p x op\<^sub>2'
          apply (drule meta_spec[of _ \<open>BTL p buf\<close>])
          apply (drule meta_spec[of _ op\<^sub>1])
          apply (drule meta_spec[of _ op\<^sub>2'])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1' op\<^sub>2''
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf1])
            apply (rule exI[of _ \<open>buf2(p := x # buf2 p)\<close>])
            apply (rule exI[of _ op\<^sub>1'])
            apply (rule exI[of _ op\<^sub>2''])
            apply simp
            apply (intro allI conjI impI)
              apply (rule wstep_comp_op_R.intros(3))
                  apply assumption+
                apply (simp_all add: BHD_def BTL_def)
            subgoal
              apply (drule spec[of _ p])
              apply simp
              by (metis One_nat_def Suc_diff_eq_diff_pred add_eq_if append_Cons drop_Suc_Cons length_greater_0_conv list.collapse
                  list.size(3) not_less_eq_eq take_Suc)
            subgoal
              by presburger
            done
          done
        subgoal for op\<^sub>1'
          apply (drule meta_spec[of _ buf])
          apply (drule meta_spec[of _ op\<^sub>1'])
          apply (drule meta_spec[of _ op\<^sub>2])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1'' op\<^sub>2'
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf1])
            apply (rule exI[of _ buf2])
            apply (rule exI[of _ op\<^sub>1''])
            apply (rule exI[of _ op\<^sub>2'])
            apply (simp add: wstep_comp_op_L.intros(5))
            done
          done
        subgoal for op\<^sub>2'
          apply (drule meta_spec[of _ buf])
          apply (drule meta_spec[of _ op\<^sub>1])
          apply (drule meta_spec[of _ op\<^sub>2'])
          apply simp
          apply (elim exE conjE)
          subgoal for buf' buf1 buf2 op\<^sub>1' op\<^sub>2''
            apply (rule exI[of _ buf'])
            apply (rule exI[of _ buf1])
            apply (rule exI[of _ buf2])
            apply (rule exI[of _ op\<^sub>1'])
            apply (rule exI[of _ op\<^sub>2''])
            apply (simp add: wstep_comp_op_R.intros(5))
            done
          done
        done
      done
    done
end
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