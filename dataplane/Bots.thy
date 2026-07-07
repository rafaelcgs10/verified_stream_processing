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
    unfolding frontier_less_equal_iff2 by blast
  have zcount_pos: "0 < zcount (zmset_of (mset_set (myfst ` set_antichain A))) (myfst t')"
    using t'_in by (simp add: member_antichain.rep_eq)
  have "frontier_less_equal (exit_scope myfst A) (myfst t')"
    unfolding exit_scope_def o_def using zcount_pos by (rule frontier_less_equal_zcount_pos)
  then have "frontier_less_equal (exit_scope myfst A) (myfst t)"
    using myfst_mono[OF t'_le] by (rule frontier_less_equal_trans)
  then show False
    using not_projected by contradiction
qed
end
