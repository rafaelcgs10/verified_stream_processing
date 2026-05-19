theory MyMisc

imports
  Progress_Tracking.Propagate
  Coinductive.Coinductive_List
  Nondeterministic_Dataflow.CSet_LList_Impl
  Nondeterministic_Dataflow.Coinductive_List_Auxiliary
begin

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


lemma path_weight_direct_0path:
  assumes G: "Graph.graph su"
  shows "(0 :: 't :: {canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) \<in>\<^sub>A su l1 l2 \<Longrightarrow>
   0 \<in>\<^sub>A graph.path_weight su l1 l2"
  apply (subst graph.path_weight_def[OF G])
  apply clarsimp
  apply (subst member_antichain.abs_eq)
   apply (clarsimp simp add: eq_onp_def)
   apply (rule graph.finite_minimal_antichain_path_weightp[OF G])
  unfolding minimal_antichain_def
  apply clarsimp
  apply (subst graph.path_weightp_def[OF G])
  apply clarsimp
  apply (rule exI[of _ "[(l1, 0, l2)]"])
  apply clarsimp
  apply (rule graph.path.intros(2)[where xs=Nil, simplified, OF G])
   apply (rule graph.path.intros(1)[OF G])
   apply auto
  done
lemma path_weight_antichain0:
  assumes G: "Graph.graph su"
  shows "(0 :: 't :: {canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) \<in>\<^sub>A su loc1 loc2 \<Longrightarrow>
        graph.path_weight su loc1 loc2 = antichain {0}"
  apply (subst ac_eq_iff)
  apply safe
  subgoal for x
    by (metis assms finite.emptyI finite_insert graph.path_weight_conv_path in_antichain_minimal_antichain minimal_antichain_singleton not_gr_zero path_weight_direct_0path singletonI)
  subgoal for x
    by (metis assms finite.emptyI finite_insert in_antichain_minimal_antichain minimal_antichain_singleton path_weight_direct_0path singleton_iff)
  done

end