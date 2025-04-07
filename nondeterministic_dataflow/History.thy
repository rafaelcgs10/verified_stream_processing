theory History

imports
 "BNA_Operators"
begin

definition \<open>lproject f g vios p =
  lmap vdata (lfilter (\<lambda>vio. case vio of VInp q _ \<Rightarrow> f p q | VOut q _ \<Rightarrow> g p q) vios)\<close>

definition \<open>history op lxs lys =
  (\<exists>vios. wtraced op vios \<and>
  (\<forall>p. lprefix (lproject (=) \<bottom> vios p) (lxs p)) \<and> lys = lproject \<bottom> (=) vios)\<close>

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

corec suc_op :: \<open>(1, 1, nat) op\<close> where
  \<open>suc_op = Read 1 (\<lambda>x. Write suc_op 1 (Suc x))\<close>

corec dup_op :: \<open>(1, 1, nat) op\<close> where
  \<open>dup_op = Read 1 (\<lambda>x. Write (Write dup_op 1 x) 1 x)\<close>

corec twobuf_op :: \<open>(1, 1, nat) op\<close> where
  \<open>twobuf_op = Read 1 (\<lambda>x. Read 1 (\<lambda>y. Write (Write twobuf_op 1 y) 1 x))\<close>

abbreviation \<open>f_op \<equiv> (dup_op \<parallel> suc_op \<bullet> dup_op) \<bullet> \<V> \<bullet> twobuf_op \<bullet> \<C>\<close>

abbreviation \<open>f'_op \<equiv> (dup_op \<parallel> suc_op \<bullet> dup_op) \<bullet> \<V> \<bullet> \<I> \<bullet> \<C>\<close>

lemma
  \<open>f_op \<equiv>\<^sub>h f'_op\<close>
  oops

lemma time_anomaly:
  \<open>f_op\<up> \<equiv>\<^sub>h f'_op\<up> \<Longrightarrow> False\<close>
  oops

end