theory MyMisc

imports
  Progress_Tracking.Propagate
  Coinductive.Coinductive_List
  Nondeterministic_Dataflow.CSet_LList_Impl
  Nondeterministic_Dataflow.Coinductive_List_Auxiliary
  AntichainOrder
  "Automatic_Refinement.Misc"
begin

section \<open>Debugging Support\<close>

text \<open>A trace function that prints only when DEBUG is on.\<close>

definition "DEBUG = True"

definition "trace = (if DEBUG then Debug.tracing else (\<lambda> x y. y))"

lemma trace_simp[simp]:
  "trace x r = r"
  by (auto simp add: trace_def)

section \<open>Arithmetic and Sums\<close>

text \<open>Small facts about integer sums and inequalities.\<close>

lemma plus_minus_gt:
  "A + (B - C) > X \<Longrightarrow> C \<ge> (0 :: int) \<Longrightarrow>  A + B > X"
  by force
lemma lt_le_lt:
  "(x :: int) < a + b \<Longrightarrow> b \<le> c \<Longrightarrow> x < a + c"
  by simp
lemma int_sum_minus_cases:
  "(0 :: int) < V \<Longrightarrow> V = n + m - p \<Longrightarrow> 0 \<le> p \<Longrightarrow> 0 < n \<or> 0 < m"
  by auto
lemma sum_singleton:
  "sum f {t} = f t"
  by auto
lemma sum_eq_singleton:
  "finite A \<Longrightarrow> f a = b \<Longrightarrow> a \<in> A \<Longrightarrow> (\<forall> c \<in> A. c \<noteq> a \<longrightarrow> f c = 0) \<Longrightarrow> sum f A = b"
  by (metis Diff_iff sum_singleton empty_subsetI insert_iff insert_subset sum.mono_neutral_right)
lemma gt_0_plusD:
  "0 < a + b \<Longrightarrow> 0 < a \<or> 0 < (b :: int)"
  by auto

section \<open>Lazy Lists and Miscellanea\<close>

text \<open>Facts about ltaken, lshift, filtered lazy lists, and sums.\<close>

lemma in_lset_ltaken_ldropn:
  "x \<in> lset lxs \<longleftrightarrow> x \<in> set (ltaken n lxs) \<or> x \<in> lset (ldropn n lxs)"
  apply (induct n arbitrary: lxs)
  apply simp
  subgoal premises prems for n lxs
    apply (cases lxs)
    apply simp
    apply simp
    using prems apply blast
    done
  done

lemma ltaken_lshift_ldropn[simp]:
  "ltaken n lxs @@- ldropn n lxs = lxs"
  apply (induct n arbitrary: lxs)
  apply simp_all
  subgoal for n lxs
    apply (cases lxs)
    apply simp_all
    done
  done


lemma concat_map_empty_except_1:
  assumes \<open>distinct xs\<close> \<open>x \<in> set xs\<close> \<open>\<forall>y \<in> set xs - {x}. f y = []\<close>
  shows \<open>concat (map f xs) = f x\<close>
proof -
  obtain ys zs where ys_zs: \<open>xs = ys @ [x] @ zs\<close>
    using assms(1,2) Cons_eq_appendI append_Nil in_set_list_format by metis
  have \<open>x \<notin> set ys\<close> \<open>x \<notin> set zs\<close> using assms(1) ys_zs by simp_all
  hence \<open>concat (map f ys) = []\<close> \<open>concat (map f zs) = []\<close> \<open>concat (map f [x]) = f x\<close>
    using assms(3) ys_zs by simp_all
  thus ?thesis using ys_zs append.right_neutral append.simps(1) concat_append map_append by metis
qed


lemma lfinite_lfilter_mono:
  assumes finite: \<open>lfinite (lfilter Q xs)\<close>
    and mono: \<open>\<And>x. x \<in> lset xs \<Longrightarrow> P x \<Longrightarrow> Q x\<close>
  shows \<open>lfinite (lfilter P xs)\<close>
proof -
  have \<open>lfilter P xs = lfilter P (lfilter Q xs)\<close>
    apply (subst lfilter_lfilter)
    apply (rule lfilter_cong[OF refl])
    using mono by auto
  then show ?thesis
    using finite by simp
qed

lemma isl_projl_eq: "isl dd \<Longrightarrow> projl dd = p \<Longrightarrow> dd = Inl p"
  by (cases dd) auto
end