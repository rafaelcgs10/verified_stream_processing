theory Wstep_Composition

imports
  "BNA_Operators"
begin

inductive wstep_comp_op_L where
  \<open>io = Tau \<Longrightarrow> buf = (\<lambda>_. []) \<Longrightarrow> op' = op \<Longrightarrow> wstep_comp_op_L io wire buf op op'\<close>
| \<open>io = Inp (Inl p) x \<Longrightarrow> step (Inp p x) op op' \<Longrightarrow> wstep_comp_op_L Tau wire buf op' op'' \<Longrightarrow>
  wstep_comp_op_L io wire buf op op''\<close>
| \<open>io = Out (Inl p) x \<Longrightarrow> step (Out p x) op op' \<Longrightarrow> p \<notin> dom wire \<Longrightarrow>
  wstep_comp_op_L Tau wire buf op' op'' \<Longrightarrow> wstep_comp_op_L io wire buf op op''\<close>
| \<open>step (Out p x) op op' \<Longrightarrow> p \<in> dom wire \<Longrightarrow> wstep_comp_op_L io wire buf op' op'' \<Longrightarrow>
  buf' = BENQ p x buf \<Longrightarrow> wstep_comp_op_L io wire buf' op op''\<close>
| \<open>step Tau op op' \<Longrightarrow> wstep_comp_op_L io wire buf op' op'' \<Longrightarrow> wstep_comp_op_L io wire buf op op''\<close>

inductive wstep_comp_op_R where
  \<open>io = Tau \<Longrightarrow> op' = op \<Longrightarrow> wstep_comp_op_R io wire buf op op'\<close>
| \<open>io = Inp (Inr p) x \<Longrightarrow> step (Inp p x) op op' \<Longrightarrow> p \<notin> ran wire \<Longrightarrow>
  wstep_comp_op_R Tau wire buf op' op'' \<Longrightarrow> wstep_comp_op_R io wire buf op op''\<close>
| \<open>step (Inp p x) op op' \<Longrightarrow> p \<in> ran wire \<Longrightarrow> wstep_comp_op_R io wire buf op' op'' \<Longrightarrow>
  buf p \<noteq> [] \<Longrightarrow> x = BHD p buf \<Longrightarrow> buf' = BTL p buf \<Longrightarrow> wstep_comp_op_R io wire buf' op op''\<close>
| \<open>io = Out (Inr p) x \<Longrightarrow> step (Out p x) op op' \<Longrightarrow> wstep_comp_op_R Tau wire buf op' op'' \<Longrightarrow>
  wstep_comp_op_R io wire buf op op''\<close>
| \<open>step Tau op op' \<Longrightarrow> wstep_comp_op_R io wire buf op' op'' \<Longrightarrow> wstep_comp_op_R io wire buf op op''\<close>

lemma
  \<open>wstep io (comp_op wire buf op\<^sub>1 op\<^sub>2) op' \<longleftrightarrow>
  (\<exists>buf' buf'' buf''' op\<^sub>1' op\<^sub>2'. op' = comp_op wire buf' op\<^sub>1' op\<^sub>2'
  \<and> wstep_comp_op_L io wire buf'' op\<^sub>1 op\<^sub>1' \<and> wstep_comp_op_R io wire buf''' op\<^sub>2 op\<^sub>2'
  \<and> (\<forall>p. \<exists>n \<le> length (buf p @ buf'' p). buf' p = drop n (buf p @ buf'' p) \<and> buf''' p = take n (buf p @ buf'' p)))\<close>
  oops

lemma
  \<open>wstep io (comp_op (\<lambda>_. None) (\<lambda>_. []) op\<^sub>1 op\<^sub>2) op' \<longleftrightarrow>
  (\<exists>op\<^sub>1' op\<^sub>2'. op' = comp_op (\<lambda>_. None) (\<lambda>_. []) op\<^sub>1' op\<^sub>2'
  \<and> wstep_comp_op_L io (\<lambda>_. None) (\<lambda>_. []) op\<^sub>1 op\<^sub>1' \<and> wstep_comp_op_R io (\<lambda>_. None) (\<lambda>_. []) op\<^sub>2 op\<^sub>2')\<close>
  apply (intro iffI)
  subgoal
    sorry
  subgoal
    sorry
  oops

end