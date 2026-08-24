theory Bots

imports
  MyProduct_Instances
  AntichainOrder
begin


class bots = order + bot +
  fixes bots :: "'a list"
  assumes minimal: "(set bots = {x. \<not>(\<exists>y. y < x)})"
  and complete: "\<exists> x \<in> set bots. x \<le> y"
begin

lemma incomparable_bots[simp]:
  "incomparable (set bots)"
  unfolding incomparable_def
  using bots_class.minimal by blast

lemma minimal_antichain_bots[simp]:
  "minimal_antichain (set bots) = set bots"
  unfolding minimal_antichain_def
  using bots_class.minimal by blast

end


instantiation nat :: bots
begin
definition bots_nat :: "nat list" where
  "bots_nat = [0]"
instance
  apply standard
   apply (auto simp add: bots_nat_def)
  done
end

fun myproduct :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a, 'b) myprod list" where
"myproduct [] _ = []" |
"myproduct (x#xs) ys = map (MyPair x) ys @ myproduct xs ys"

lemma from_prod_product:
  "map from_prod (List.product xs ys) = myproduct xs ys"
  by (induct xs arbitrary: ys)
   (simp_all add: from_prod_def)


instantiation myprod :: (bots, bots) bots
begin
definition bots_myprod :: "('a, 'b) myprod list" where
  "bots_myprod = myproduct bots bots"
instance
  apply standard
   apply (auto simp add: bots_myprod_def from_prod_def simp flip: from_prod_product split: prod.splits)
  subgoal for a b y
    apply (cases y)
    apply (simp add: bots_class.minimal less_myprod_def antisym_conv1)
    done
  subgoal for x
    apply (cases x)
    apply (clarsimp simp add: image_iff bots_class.minimal less_myprod_def)
    apply (metis MyPair_le basic_trans_rules(20) myprod.inject order_less_imp_le order_refl)
    done
  subgoal for y
    apply (cases y)
    apply (clarsimp simp add: image_iff bots_class.minimal less_eq_myprod_def)
    using bots_class.complete[unfolded bots_class.minimal]
    apply (metis mem_Collect_eq)
    done
  done
end

lemma set_bots_not_less[simp]:
  "{x \<in> set bots. \<forall>y\<in>set bots. \<not> y < x} = set bots"
  by (auto simp add: bots_class.minimal less_myprod_def antisym_conv1)

lemma set_antichain_antichain_set_bots[simp]:
  "set_antichain (antichain (set bots)) = set bots"
  apply (subst antichain.antichain_inverse)
  subgoal
    by simp
  apply simp
  done




definition exit_scope where
  "exit_scope f A = frontier ((zmset_of o mset_set) (f ` set_antichain A))"

lemma frontier_less_equal_exit_scope:
  "\<not> frontier_less_equal (exit_scope myfst A) (myfst t) \<Longrightarrow>
   \<not> frontier_less_equal A t"
proof
  assume not_projected: "\<not> frontier_less_equal (exit_scope myfst A) (myfst t)"
  assume "frontier_less_equal A t"
  then obtain t' where t'_in: "t' \<in>\<^sub>A A" and t'_le: "t' \<le> t"
    unfolding frontier_less_equal_iff by blast
  have zcount_pos: "0 < zcount (zmset_of (mset_set (myfst ` set_antichain A))) (myfst t')"
    using t'_in by (simp add: member_antichain.rep_eq)
  have "frontier_less_equal (exit_scope myfst A) (myfst t')"
    unfolding exit_scope_def o_def using zcount_pos by (rule frontier_less_equal_zcount_pos)
  then have "frontier_less_equal (exit_scope myfst A) (myfst t)"
    using myfst_mono[OF t'_le] by (rule frontier_less_equal_trans)
  then show False
    using not_projected by contradiction
qed

lemma frontier_less_equal_antichain_plusI1:
  assumes "frontier_less_equal A t"
  shows "frontier_less_equal (A + B) t"
proof -
  obtain a where a_in: "a \<in>\<^sub>A A" and a_le: "a \<le> t"
    using assms unfolding frontier_less_equal_iff by blast
  have fin: "finite (set_antichain A \<union> set_antichain B)"
    by simp
  have "a \<in> set_antichain A \<union> set_antichain B"
    using a_in unfolding member_antichain.rep_eq by simp
  then obtain a' where a'_in: "a' \<in> minimal_antichain (set_antichain A \<union> set_antichain B)" and a'_le: "a' \<le> a"
    using minimal_antichain_member[OF fin] by blast
  then have "a' \<in>\<^sub>A A + B"
    unfolding member_antichain.rep_eq plus_antichain.rep_eq by simp
  moreover have "a' \<le> t"
    using a'_le a_le by order
  ultimately show ?thesis
    unfolding frontier_less_equal_iff by blast
qed

lemma frontier_less_equal_antichain_plusI2:
  assumes "frontier_less_equal B t"
  shows "frontier_less_equal (A + B) t"
  using frontier_less_equal_antichain_plusI1[OF assms, of A]
  by (simp add: antichain_add_commute)

lemma exit_scope_memberE:
  assumes "y \<in>\<^sub>A exit_scope myfst A"
  obtains x where "x \<in>\<^sub>A A" and "myfst x = y"
proof -
  have y_front: "y \<in>\<^sub>A frontier (zmset_of (mset_set (myfst ` set_antichain A)))"
    using assms unfolding exit_scope_def o_def by simp
  have "0 < zcount (zmset_of (mset_set (myfst ` set_antichain A))) y"
    using y_front by (simp add: in_frontier_iff)
  then obtain x where "x \<in> set_antichain A" and "myfst x = y"
    by auto
  then show ?thesis
    using that unfolding member_antichain.rep_eq by blast
qed

lemma frontier_less_equal_exit_scope_myfst_le:
  assumes "frontier_less_equal A T"
    and "myfst T \<le> t"
  shows "frontier_less_equal (exit_scope myfst A) t"
proof -
  have "frontier_less_equal (exit_scope myfst A) (myfst T)"
    using frontier_less_equal_exit_scope assms(1) by blast
  then show ?thesis
    using assms(2) by (rule frontier_less_equal_trans)
qed

lemma frontier_less_equal_exit_scopeI:
  assumes "x \<in>\<^sub>A A"
  shows "frontier_less_equal (exit_scope myfst A) (myfst x)"
proof -
  have "0 < zcount (zmset_of (mset_set (myfst ` set_antichain A))) (myfst x)"
    using assms by (simp add: member_antichain.rep_eq)
  then show ?thesis
    unfolding exit_scope_def o_def by (rule frontier_less_equal_zcount_pos)
qed

lemma frontier_less_equal_exit_scope_plusI1:
  assumes "x \<in>\<^sub>A A"
  shows "frontier_less_equal (exit_scope myfst (A + B)) (myfst x)"
proof -
  have fin: "finite (set_antichain A \<union> set_antichain B)"
    by simp
  have "x \<in> set_antichain A \<union> set_antichain B"
    using assms unfolding member_antichain.rep_eq by simp
  then obtain x' where x'_in: "x' \<in> minimal_antichain (set_antichain A \<union> set_antichain B)" and x'_le: "x' \<le> x"
    using minimal_antichain_member[OF fin] by blast
  then have "x' \<in>\<^sub>A A + B"
    unfolding member_antichain.rep_eq plus_antichain.rep_eq by simp
  then have "frontier_less_equal (exit_scope myfst (A + B)) (myfst x')"
    by (rule frontier_less_equal_exit_scopeI)
  then show ?thesis
    using myfst_mono[OF x'_le] by (rule frontier_less_equal_trans)
qed

lemma frontier_less_equal_exit_scope_plusI2:
  assumes "x \<in>\<^sub>A B"
  shows "frontier_less_equal (exit_scope myfst (A + B)) (myfst x)"
  using frontier_less_equal_exit_scope_plusI1[OF assms, of A]
  by (simp add: antichain_add_commute)

lemma exit_scope_plus_distrib:
  "exit_scope myfst (A + B) = exit_scope myfst A + exit_scope myfst B"
proof (rule antisym)
  show "exit_scope myfst (A + B) \<le> exit_scope myfst A + exit_scope myfst B"
    unfolding less_eq_antichain_def
  proof safe
    fix y
    assume y_in: "y \<in>\<^sub>A exit_scope myfst A + exit_scope myfst B"
    have "y \<in> set_antichain (exit_scope myfst A) \<union> set_antichain (exit_scope myfst B)"
      using y_in minimal_antichain_subset
      unfolding member_antichain.rep_eq plus_antichain.rep_eq by blast
    then show "\<exists>x. x \<in>\<^sub>A exit_scope myfst (A + B) \<and> x \<le> y"
    proof
      assume "y \<in> set_antichain (exit_scope myfst A)"
      then obtain x where x_in: "x \<in>\<^sub>A A" and y_eq: "myfst x = y"
        using exit_scope_memberE unfolding member_antichain.rep_eq by blast
      show ?thesis
        using frontier_less_equal_exit_scope_plusI1[OF x_in, of B]
        unfolding frontier_less_equal_iff y_eq by blast
    next
      assume "y \<in> set_antichain (exit_scope myfst B)"
      then obtain x where x_in: "x \<in>\<^sub>A B" and y_eq: "myfst x = y"
        using exit_scope_memberE unfolding member_antichain.rep_eq by blast
      show ?thesis
        using frontier_less_equal_exit_scope_plusI2[OF x_in, of A]
        unfolding frontier_less_equal_iff y_eq by blast
    qed
  qed
next
  show "exit_scope myfst A + exit_scope myfst B \<le> exit_scope myfst (A + B)"
    unfolding less_eq_antichain_def
  proof safe
    fix y
    assume y_in: "y \<in>\<^sub>A exit_scope myfst (A + B)"
    then obtain x where x_in: "x \<in>\<^sub>A A + B" and y_eq: "myfst x = y"
      using exit_scope_memberE by blast
    have "x \<in> set_antichain A \<union> set_antichain B"
      using x_in minimal_antichain_subset
      unfolding member_antichain.rep_eq plus_antichain.rep_eq by blast
    then show "\<exists>x. x \<in>\<^sub>A exit_scope myfst A + exit_scope myfst B \<and> x \<le> y"
    proof
      assume "x \<in> set_antichain A"
      then have "x \<in>\<^sub>A A"
        unfolding member_antichain.rep_eq by simp
      then have "frontier_less_equal (exit_scope myfst A) y"
        using frontier_less_equal_exit_scopeI[of x A] y_eq by simp
      then show ?thesis
        using frontier_less_equal_antichain_plusI1[of "exit_scope myfst A" y "exit_scope myfst B"]
        unfolding frontier_less_equal_iff by blast
    next
      assume "x \<in> set_antichain B"
      then have "x \<in>\<^sub>A B"
        unfolding member_antichain.rep_eq by simp
      then have "frontier_less_equal (exit_scope myfst B) y"
        using frontier_less_equal_exit_scopeI[of x B] y_eq by simp
      then show ?thesis
        using frontier_less_equal_antichain_plusI2[of "exit_scope myfst B" y "exit_scope myfst A"]
        unfolding frontier_less_equal_iff by blast
    qed
  qed
qed
end
