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
  buf' = BENQ q x buf \<Longrightarrow> wstep_comp_op_L wire io buf' op op''\<close>
| \<open>step Tau op op' \<Longrightarrow> wstep_comp_op_L wire io buf op' op'' \<Longrightarrow> wstep_comp_op_L wire io buf op op''\<close>

inductive wstep_comp_op_R :: \<open>('c \<Rightarrow> 'b option) \<Rightarrow> ('a + 'b, 'c + 'd, 'e) IO \<Rightarrow> ('b \<Rightarrow> 'e buf) \<Rightarrow>
  ('b, 'd, 'e) op \<Rightarrow> ('b, 'd, 'e) op \<Rightarrow> bool\<close> for wire where
  \<open>io = Tau \<Longrightarrow> op' = op \<Longrightarrow> wstep_comp_op_R wire io buf op op'\<close>
| \<open>io = Inp (Inr p) x \<Longrightarrow> step (Inp p x) op op' \<Longrightarrow> p \<notin> ran wire \<Longrightarrow>
  wstep_comp_op_R wire Tau buf op' op'' \<Longrightarrow> wstep_comp_op_R wire io buf op op''\<close>
| \<open>step (Inp p x) op op' \<Longrightarrow> p \<in> ran wire \<Longrightarrow> wstep_comp_op_R wire io buf op' op'' \<Longrightarrow>
  buf p \<noteq> [] \<Longrightarrow> x = BHD p buf \<Longrightarrow> buf' = BTL p buf \<Longrightarrow> wstep_comp_op_R wire io buf' op op''\<close>
| \<open>io = Out (Inr p) x \<Longrightarrow> step (Out p x) op op' \<Longrightarrow> wstep_comp_op_R wire Tau buf op' op'' \<Longrightarrow>
  wstep_comp_op_R wire io buf op op''\<close>
| \<open>step Tau op op' \<Longrightarrow> wstep_comp_op_R wire io buf op' op'' \<Longrightarrow> wstep_comp_op_R wire io buf op op''\<close>

lemma
  \<open>wstep io (comp_op wire buf op\<^sub>1 op\<^sub>2) op' \<longleftrightarrow>
  (\<exists>buf' buf'' buf''' op\<^sub>1' op\<^sub>2'. op' = comp_op wire buf' op\<^sub>1' op\<^sub>2'
  \<and> wstep_comp_op_L wire (case io of Inp (Inl _) _ \<Rightarrow> io | Out (Inl p) _ \<Rightarrow> if wire p = None then io else Tau | _ \<Rightarrow> Tau) buf'' op\<^sub>1 op\<^sub>1'
  \<and> wstep_comp_op_R wire (case io of Out (Inr _) _ \<Rightarrow> io | Inp (Inr p) _ \<Rightarrow> if p \<notin> ran wire then io else Tau | _ \<Rightarrow> Tau) buf''' op\<^sub>2 op\<^sub>2'
  \<and> (\<forall>p. \<exists>n \<le> length (buf p @ buf'' p). buf' p = drop n (buf p @ buf'' p) \<and> buf''' p = take n (buf p @ buf'' p)))\<close>
  apply (intro iffI)
  subgoal
    sorry
  subgoal
    apply (elim exE conjE)
    subgoal for buf' buf'' buf''' op\<^sub>1' op\<^sub>2'
      apply hypsubst_thin
      apply (induct \<open>case io of Inp (Inl _) _ \<Rightarrow> io | Out (Inl p) _ \<Rightarrow> if wire p = None then io else Tau | _ \<Rightarrow> Tau\<close> buf'' op\<^sub>1 op\<^sub>1' arbitrary: io pred: wstep_comp_op_L)
          apply (auto split: sum.splits IO.splits)
      subgoal for op\<^sub>1'' x p
        apply (cases \<open>p \<notin> ran wire\<close>; simp)
        subgoal
          apply rotate_tac
          apply (induct _ buf''' op\<^sub>2 op\<^sub>2' pred: wstep_comp_op_R)
              apply auto
          sorry
        subgoal
          apply rotate_tac
          apply (induct _ buf''' op\<^sub>2 op\<^sub>2' pred: wstep_comp_op_R)
              apply auto
          sorry
        done
      oops

lemma
  \<open>wstep io (comp_op (\<lambda>_. None) (\<lambda>_. []) op\<^sub>1 op\<^sub>2) op' \<longleftrightarrow>
  (\<exists>op\<^sub>1' op\<^sub>2'. op' = comp_op (\<lambda>_. None) (\<lambda>_. []) op\<^sub>1' op\<^sub>2'
  \<and> wstep_comp_op_L (\<lambda>_. None) (case io of Inp (Inl _) _ \<Rightarrow> io | Out (Inl _) _ \<Rightarrow> io | _ \<Rightarrow> Tau) (\<lambda>_. []) op\<^sub>1 op\<^sub>1'
  \<and> wstep_comp_op_R (\<lambda>_. None) (case io of Inp (Inr _) _ \<Rightarrow> io | Out (Inr _) _ \<Rightarrow> io | _ \<Rightarrow> Tau) (\<lambda>_. []) op\<^sub>2 op\<^sub>2')\<close>
  apply (intro iffI)
  subgoal
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