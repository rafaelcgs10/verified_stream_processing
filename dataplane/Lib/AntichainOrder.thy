theory AntichainOrder

imports
  Progress_Tracking.Antichain
  Progress_Tracking.Propagate
  Executable
begin 

declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]


section \<open>Trivial Topologies\<close>

text \<open>Degenerate graph and dataflow topology instances.\<close>

lemma trivial_graph[simp]:
  "graph (\<lambda> (a :: unit) _. antichain ({} :: nat set))"
  apply standard
  apply (auto simp add: empty_antichain_def)
  done

lemma trivial_dataflow_topology[simp]:
  "dataflow_topology (\<lambda> (a :: unit) _. antichain ({} :: nat set)) (+)"
  apply standard
  apply (auto simp add: empty_antichain_def)
  subgoal for xs
    apply (rule FalseE)
    apply (induct xs rule: rev_induct)
     apply auto
    apply (metis empty_antichain_def graph.path_AppendE mem_antichain_nonempty trivial_graph)
    done
  done


global_interpretation trivial_dataflow_topology_interpretation:
   dataflow_topology "(\<lambda> (a :: unit) _. antichain ({} :: nat set))" "(+)"
  by simp

section \<open>Orders and Equality on Antichains\<close>

text \<open>The frontier_below_eq_frontier relation, order type class instances,
  emptiness, and executable equality of antichains.\<close>

definition
  "frontier_below_eq_frontier ft1 ft2 = ((\<forall> t2. t2 \<in>\<^sub>A ft2 \<longrightarrow> (\<exists> t1. t1 \<in>\<^sub>A ft1 \<and> t1 \<le> t2)))"

instantiation antichain :: (_) ord
begin

definition
  "less_eq_antichain ft1 ft2 = ((\<forall> t2. t2 \<in>\<^sub>A ft2 \<longrightarrow> (\<exists> t1. t1 \<in>\<^sub>A ft1 \<and> t1 \<le> t2)))"

definition less_antichain where
  "(x::'a antichain) < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

instance ..
end


instance antichain :: (order) preorder
proof
  fix x y z :: "'a antichain"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (rule less_antichain_def)
  show "x \<le> x"
    unfolding less_eq_antichain_def by auto
  assume "x \<le> y" and "y \<le> z" thus "x \<le> z"
    unfolding less_eq_antichain_def by force
qed

instance antichain :: (order) order
  apply standard
  unfolding less_eq_antichain_def
  unfolding frontier_below_eq_frontier_def member_antichain.rep_eq
  apply transfer
  unfolding incomparable_def
  apply clarsimp
  apply (smt (verit, best) basic_trans_rules(18,23,24) subsetI)
  done

lemma empty_antichain_top[simp]:
  "A \<le> {}\<^sub>A"
  unfolding less_eq_antichain_def
  using mem_antichain_nonempty by blast


lemma is_empty_antichain_plus:
  "is_empty_antichain B \<Longrightarrow>
   antichain A + B = antichain A"
  by (metis Set.is_empty_iff antichain_add_commute antichain_sum_empty_2 empty_antichain.abs_eq is_empty_antichain.rep_eq set_antichain_inverse)
lemma incomparable_singleton[simp]:
  "incomparable {a}"
  unfolding incomparable_def by auto
lemma is_empty_antichain_iff:
  "is_empty_antichain A \<longleftrightarrow> A = {}\<^sub>A"
  by (metis is_empty_antichain_plus antichain_sum_empty_2 empty_antichain.abs_eq empty_is_empty_antichain)

definition "antichain_equal A1 A2 = (is_empty_antichain (filter_antichain (\<lambda> x. x \<notin>\<^sub>A A2) A1) \<and> is_empty_antichain (filter_antichain (\<lambda> x. x \<notin>\<^sub>A A1) A2))"

lemma equal_antichain_equal:
  "antichain_equal A1 A2 \<longleftrightarrow> A1 = A2"
  unfolding antichain_equal_def
  by(auto simp add: Set.is_empty_iff ac_eq_iff filter_antichain.rep_eq is_empty_antichain.rep_eq member_antichain.rep_eq filter_antichain.rep_eq member_antichain.rep_eq)
instantiation antichain :: (order) equal
begin
definition
  "equal_antichain = antichain_equal"
instance
  apply standard
  subgoal for f1 f2
    unfolding equal_antichain_def
    apply (subst equal_antichain_equal)
    apply auto
    done
  done
end

lemma set_antichain_empty_if:
  "M = {}\<^sub>A \<Longrightarrow>
   set_antichain M = {}"
  by simp

lemma in_antichain_singleton[simp]:
  "x \<in>\<^sub>A antichain {x}"
  by (metis ID.set_finite in_antichain_minimal_antichain insertI1 minimal_antichain_singleton)


section \<open>The Frontier of a Signed Multiset\<close>

text \<open>How frontier interacts with addition, subtraction, and ordering of
  signed multisets.\<close>

lemma frontier_idempotent[simp]:
  "frontier (zmset_of (mset_set (set_antichain (frontier M)))) = frontier M"
  apply transfer
  apply simp
  done

lemma in_frontier_iff:
  "t \<in>\<^sub>A frontier M \<longleftrightarrow> ((\<forall> t'. zcount M t' > 0 \<longrightarrow> \<not> t' < t) \<and> zcount M t > 0)"
  by (metis trivial_dataflow_topology_interpretation.in_frontier_least trivial_dataflow_topology_interpretation.obtain_elem_frontier le_less member_frontier_pos_zmset)

lemma frontier_below_eq_frontier_plus_neg:
  "(\<forall> t. zcount M t \<le> 0) \<Longrightarrow>
   (frontier N) \<le> (frontier (N + M))"
  unfolding less_eq_antichain_def
  apply safe
  apply (meson trivial_dataflow_topology_interpretation.frontier_unionD trivial_dataflow_topology_interpretation.obtain_frontier_elem order.strict_iff_not)
  done

lemma frontier_below_eq_frontier_minus:
  "(\<forall> t. zcount M t \<ge> 0) \<Longrightarrow>
   (frontier N) \<le> (frontier (N - M))"
  unfolding less_eq_antichain_def
  apply safe
  apply (smt (verit, ccfv_SIG) dataflow_topology.obtain_elem_frontier member_frontier_pos_zmset trivial_dataflow_topology_interpretation.dataflow_topology_axioms zcount_diff)
  done
lemma in_frontier_minusD:
  "x \<in>\<^sub>A frontier (A - B) \<Longrightarrow> 
   (\<forall> y. zcount B y \<ge> 0) \<Longrightarrow>
   (\<exists> y. y \<in>\<^sub>A frontier A \<and> y \<le> x)"
  using frontier_below_eq_frontier_minus less_eq_antichain_def by blast





lemma frontier_below_eq_frontier_plus_pos:
  "(\<forall> t. zcount M t \<ge> 0) \<Longrightarrow>
   frontier (N + M) \<le> frontier N"
  unfolding less_eq_antichain_def
  by (metis add.commute less_add_same_cancel1 member_frontier_pos_zmset order_le_less_trans trivial_dataflow_topology_interpretation.obtain_frontier_elem zcount_union)


lemma frontier_le_add_singleton:
  "(\<forall>t'. zcount A t' > 0 \<longrightarrow> t' \<le> t) \<Longrightarrow>
   (zcount A t \<ge> 0) \<Longrightarrow>
   frontier (A + {#t#}\<^sub>z) \<le> antichain {t}"
  unfolding less_eq_antichain_def
  apply auto
  subgoal for t2
    apply (subgoal_tac "t2 = t")
    subgoal premises prems
      using prems(1,3-) apply -
      apply simp
      apply hypsubst_thin
      apply (cases "\<exists> t'. 0 < zcount A t'")
      subgoal
        by (metis add_pos_pos order.trans trivial_dataflow_topology_interpretation.obtain_frontier_elem zcount_add_zmset zero_less_one)
      subgoal
        by (metis add.commute add.right_neutral nless_le prems(2) trivial_dataflow_topology_interpretation.obtain_frontier_elem zcount_add_zmset zero_less_one)
      done
    subgoal
      by (metis finite.emptyI finite.insertI in_antichain_minimal_antichain minimal_antichain_singleton singleton_iff)
    done
  done


lemma frontier_le_add:
  "C \<le> frontier A \<Longrightarrow>
   C \<le> frontier B \<Longrightarrow>
   C \<le> frontier (A + B)"
  unfolding less_eq_antichain_def
  apply auto
  by (metis order.trans trivial_dataflow_topology_interpretation.frontier_unionD trivial_dataflow_topology_interpretation.obtain_elem_frontier)


lemma frontier_singleton:
  "frontier {#x#}\<^sub>z = antichain {x}"
  by (smt (verit, ccfv_threshold) add_0 finite.emptyI finite_insert frontier_le_add_singleton in_antichain_minimal_antichain less_eq_antichain_def member_frontier_pos_zmset minimal_antichain_singleton order_antisym_conv
      order_less_le singleton_iff zcount_empty zcount_single)

lemma frontier_le_singletonD:
  "frontier A \<le> frontier {#t#}\<^sub>z \<Longrightarrow>
   A \<noteq> {#}\<^sub>z \<and> (\<exists> x. zcount A x > 0 \<longrightarrow> x \<le> t)"
  unfolding less_eq_antichain_def
  apply auto
  apply (metis mem_antichain_nonempty trivial_dataflow_topology_interpretation.obtain_elem_frontier zcount_single zero_less_one)
  done

lemma frontier_le_singletons:
  "t \<le> t' \<Longrightarrow>
   frontier {#t#}\<^sub>z \<le> frontier {#t'#}\<^sub>z"
  by (metis (no_types, opaque_lifting) frontier_le_singletonD less_eq_antichain_def member_frontier_pos_zmset nless_le zcount_single)


lemma frontier_add_add_le:
  "frontier B \<le> frontier B' \<Longrightarrow>
   frontier A \<le> frontier A' \<Longrightarrow>
   (\<forall> t. zcount A t \<ge> 0) \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   frontier (A + B) \<le> frontier (A' + B')"
  unfolding less_eq_antichain_def
  apply auto
  apply (smt (z3) add.commute frontier_below_eq_frontier_plus_pos less_eq_antichain_def order_trans trivial_dataflow_topology_interpretation.frontier_unionD trivial_dataflow_topology_interpretation.obtain_elem_frontier)
  done

lemma add_empty_zmultiset[simp]:
  "A + {#}\<^sub>z = A"
  "{#}\<^sub>z + A = A"
   apply auto
  done

lemma in_frontier_addD:
  "t \<in>\<^sub>A frontier (M + N) \<Longrightarrow> (0 < zcount M t \<and> (\<exists> t'. t' \<in>\<^sub>A frontier M \<and> t' \<le> t)) \<or> 0 < zcount N t  \<and> (\<exists> t'. t' \<in>\<^sub>A frontier N \<and> t' \<le> t)"
  by (metis dataflow_topology.frontier_unionD dataflow_topology.obtain_frontier_elem trivial_dataflow_topology_interpretation.dataflow_topology_axioms)

lemma in_frontier_addD_alt:
  "t \<in>\<^sub>A frontier (M + N) \<Longrightarrow>
  (\<forall> x. zcount M x \<ge> 0) \<Longrightarrow>
  (\<forall> x. zcount N x \<ge> 0) \<Longrightarrow>
   (t \<in>\<^sub>A frontier M \<and> (\<forall> t'. zcount N t' > 0 \<longrightarrow> \<not> t' < t)) \<or> (t \<in>\<^sub>A frontier N \<and> (\<forall> t'. zcount M t' > 0 \<longrightarrow> \<not> t' < t))"
  apply transfer'
  apply (auto simp add: minimal_antichain_def)
  using add_strict_increasing add_strict_increasing2 apply blast+
  done

lemma in_frontier_in_frontier_add:
  "t \<in>\<^sub>A frontier A \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   \<exists>t'. t' \<in>\<^sub>A frontier (A + B) \<and> t' \<le> t"
  using frontier_below_eq_frontier_plus_pos less_eq_antichain_def by blast

lemma in_frontier_in_frontier_add_alt:
  "t' \<in>\<^sub>A frontier A \<Longrightarrow>
   t' \<le> t \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   \<exists>t'. t' \<in>\<^sub>A frontier (A + B) \<and> t' \<le> t"
  using in_frontier_in_frontier_add order_trans by blast


(* 
lemma froniter_minus_justified:
  "justified A B \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   frontier (A - B) \<le> frontier A"
  unfolding less_eq_antichain_def justified_def
  apply auto
  subgoal for t
    apply (cases "zcount B t > 0")
    subgoal
      using order_class.elem_order_zmset_exists_foundation[of t B] apply -
      apply (drule meta_mp)
       apply (meson pos_zcount_in_zmset)
      apply (elim conjE bexE)
      subgoal for s
        apply (drule spec[of _ s], drule mp)
         apply (metis nless_le zcount_ne_zero_iff)
        apply (elim disjE)
        subgoal
          unfolding supported_def in_frontier_iff
          apply auto
          subgoal for s
            by (metis nless_le zcount_ne_zero_iff)
          done
        subgoal
          apply (elim exE conjE)
          by (meson dual_order.strict_trans1 in_frontier_iff)
        subgoal
          by (smt (verit, ccfv_threshold) in_frontier_iff order_le_imp_less_or_eq zcount_diff)
        done
      done
    subgoal
      apply (subgoal_tac "zcount B t = 0")
      subgoal
        apply simp
        by (metis diff_add_cancel in_frontier_addD nless_le) 
      subgoal
        by (metis nless_le)
      done
    done
  done *)
(* 
lemma froniter_add_justified:
  "justified A B \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   frontier A \<le> frontier (A + B)"
  unfolding less_eq_antichain_def justified_def
  apply auto
  subgoal for t
    apply (drule in_frontier_addD)
    apply (elim conjE disjE exE)
    subgoal
      by blast
    subgoal for t'
      apply (cases "zcount B t' > 0")
      subgoal   
        using order_class.elem_order_zmset_exists_foundation[of t' "B"] apply -
        apply (drule meta_mp)
         apply (meson pos_zcount_in_zmset)
        apply (elim conjE bexE)
        unfolding supported_def in_frontier_iff
        apply auto
        apply (smt (verit) nless_le order.trans order_zmset_exists_foundation')
        done
      subgoal
        apply (subgoal_tac "zcount B t' = 0")
        subgoal
          by (simp add: in_frontier_iff)
        subgoal
          by (metis nless_le)
        done
      done
    done
  done *)


lemma frontier_le_remove_l:
  "frontier A \<le> frontier C \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   frontier (A + B) \<le> frontier C"
  unfolding less_eq_antichain_def
  using in_frontier_in_frontier_add_alt by blast


lemma zmset_of_mset_set_ge_zero[simp]:
  "zcount (zmset_of (mset_set (set_antichain (frontier A)))) t \<ge> 0"
  by (meson zcount_zmset_of_nonneg)


lemma frontier_le_remove_left:
  "frontier B \<le> frontier C \<Longrightarrow>
   (\<forall> x. zcount A x \<ge> 0) \<Longrightarrow>
   frontier (A + B) \<le> frontier C"
  unfolding less_eq_antichain_def
  by (metis add.commute in_frontier_in_frontier_add_alt)

section \<open>The frontier_less_equal Order\<close>

text \<open>A frontier is less-equal a timestamp when one of its elements lies
  at or below it.\<close>

definition
  "frontier_less_equal ft t = (\<not> is_empty_antichain (filter_antichain (\<lambda> f. f \<le> t) ft))"

lemma frontier_less_equal_empty_antichain[simp]:
  "\<not> frontier_less_equal {}\<^sub>A A"
  unfolding frontier_less_equal_def
  apply transfer
  unfolding Set.filter_eq Set.is_empty_iff
  apply simp
  done


lemma frontier_less_equal_iff2:
  "frontier_less_equal f t \<longleftrightarrow> f \<le> frontier {#t#}\<^sub>z"
  unfolding frontier_less_equal_def less_eq_antichain_def
  apply (auto simp add: in_frontier_iff)
  subgoal
    unfolding is_empty_antichain_def Set.is_empty_iff
    apply clarsimp
    apply (simp add: filter_antichain.rep_eq member_antichain.rep_eq)
    done
  subgoal
    unfolding is_empty_antichain_def Set.is_empty_iff
    apply clarsimp
    apply (simp add: filter_antichain.rep_eq member_antichain.rep_eq)
    done
  done

lemma frontier_less_equal_le_trans:
  "frontier_less_equal f1 t \<Longrightarrow>
   f2 \<le> f1 \<Longrightarrow> 
   frontier_less_equal f2 t"
  unfolding frontier_less_equal_iff2
  apply (rule Orderings.preorder_class.order_trans)
   apply assumption+
  done

lemma frontier_less_equal_trans:
  "frontier_less_equal A t' \<Longrightarrow>
   t' \<le> t \<Longrightarrow> 
   frontier_less_equal A t"
  unfolding frontier_less_equal_iff2
  by (meson frontier_le_singletons order_trans_rules(23))


lemma frontier_less_equal_iff:
  "frontier_less_equal f t \<longleftrightarrow> (\<exists> t'. t' \<in>\<^sub>A f \<and> t' \<le> t)"
  unfolding frontier_less_equal_def
  apply (auto simp add: in_frontier_iff)
  subgoal
    unfolding is_empty_antichain_def Set.is_empty_iff
    apply clarsimp
    apply (simp add: filter_antichain.rep_eq member_antichain.rep_eq)
    done
  subgoal
    unfolding is_empty_antichain_def Set.is_empty_iff
    apply clarsimp
    apply (simp add: filter_antichain.rep_eq member_antichain.rep_eq)
    done
  done

lemma frontier_less_equal_addI:
  "frontier_less_equal (frontier A) t \<or> frontier_less_equal (frontier B) t \<Longrightarrow>
   (\<forall> t. zcount A t \<ge> 0) \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   frontier_less_equal (frontier (A + B)) t"
  unfolding frontier_less_equal_iff2
  apply safe
  using frontier_le_remove_l apply blast
  using frontier_le_remove_left apply blast
  done

lemma frontier_less_equal_add_cases:
  "frontier_less_equal (frontier (A + B)) t \<Longrightarrow>
   frontier_less_equal (frontier A) t \<or> frontier_less_equal (frontier B) t"
  unfolding frontier_less_equal_iff
  using in_frontier_addD order_trans_rules(23) by blast

lemma frontier_less_equal_add_cases_stronger:
  "frontier_less_equal (frontier (A + B)) t \<Longrightarrow>
   (\<exists> t'. (zcount A t' > 0 \<and> frontier_less_equal (frontier A) t \<or> zcount B t' > 0 \<and> frontier_less_equal (frontier B) t) \<and> t' \<le> t \<and> zcount A t' + zcount B t' > 0 \<and> t' \<in>\<^sub>A frontier (A + B))"
  unfolding frontier_less_equal_iff in_frontier_iff
  apply (auto del: )
  by (smt (verit) order.trans order_zmset_exists_foundation')

lemma frontier_less_equal_zcount_pos:
  " 0 < zcount A x \<Longrightarrow>
    frontier_less_equal (frontier A) x"
  unfolding frontier_less_equal_iff2
  by (metis dual_order.irrefl less_eq_antichain_def member_frontier_pos_zmset trivial_dataflow_topology_interpretation.obtain_elem_frontier zcount_single)

lemma frontier_less_equal_sumI:
  "finite S \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (f l) t \<ge> 0) \<Longrightarrow>
   l \<in> S \<Longrightarrow>
   frontier_less_equal (frontier (f l)) t \<Longrightarrow>
   frontier_less_equal (frontier (\<Sum>loc\<in>S. f loc)) t"
  by (induct S rule: finite_induct)
   (auto simp add: frontier_less_equal_addI sum_nonneg zcount_sum)


lemma frontier_less_equal_sumE:
  "frontier_less_equal (frontier (\<Sum>loc\<in>S. f loc)) t \<Longrightarrow>
   finite S \<Longrightarrow>
   \<exists> l\<in>S. frontier_less_equal (frontier (f l)) t"
  apply rotate_tac
  apply (induct S rule: finite_induct)
  apply (auto simp add: frontier_less_equal_addI sum_nonneg zcount_sum)
  using frontier_less_equal_add_cases apply blast
  done


lemma in_frontierI:
  "zcount M t > 0 \<Longrightarrow>
   (\<forall> t'. zcount M t' > 0 \<longrightarrow> \<not> t > t') \<Longrightarrow>
   t \<in>\<^sub>A frontier M"
  apply transfer
  apply (auto simp add: minimal_antichain_def)
  done

lemma frontier_sum_le:
  "finite S \<Longrightarrow>
   (\<forall> loc\<in>S. frontier (f loc) \<le> frontier (f' loc)) \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (f l) t \<ge> 0) \<Longrightarrow>
   frontier (\<Sum>loc\<in>S. f loc) \<le> frontier (\<Sum>loc\<in>S. f' loc)"
  apply (induct S rule: finite_induct)
   apply simp_all
  apply clarsimp
  apply (simp add: frontier_add_add_le sum_nonneg zcount_sum)
  done







section \<open>Frontiers of Sums\<close>

text \<open>Membership and ordering in the frontier of a sum of signed multisets.\<close>

lemma int_sum_disj:
  "0 \<le> x \<Longrightarrow>
   0 \<le> y \<Longrightarrow>
   (0 :: int) < x + y \<longleftrightarrow> 0 < x \<or> 0 < y"
  by linarith

lemma in_frontier_sumI1[intro]:
  "x \<in>\<^sub>A frontier M \<Longrightarrow>
   (\<forall> y. zcount N y > 0 \<longrightarrow> \<not> y < x) \<Longrightarrow>
   (\<forall> x. zcount M x \<ge> 0) \<Longrightarrow>
   (\<forall> x. zcount N x \<ge> 0) \<Longrightarrow>
   x \<in>\<^sub>A frontier (M + N)"
  by (auto del: disjE simp add: int_sum_disj member_antichain.rep_eq minimal_antichain_def frontier.rep_eq)
lemma in_frontier_sumI2[intro]:
  "x \<in>\<^sub>A frontier N \<Longrightarrow>
   (\<forall> y. zcount M y > 0 \<longrightarrow> \<not> y < x) \<Longrightarrow>
   (\<forall> x. zcount M x \<ge> 0) \<Longrightarrow>
   (\<forall> x. zcount N x \<ge> 0) \<Longrightarrow>
   x \<in>\<^sub>A frontier (M + N)"
  by (auto del: disjE simp add: int_sum_disj member_antichain.rep_eq minimal_antichain_def frontier.rep_eq)

lemma frontier_sum_eq:
  "finite S \<Longrightarrow>
   (\<forall> loc\<in>S. frontier (f loc) = frontier (f' loc)) \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (f l) t \<ge> 0) \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (f' l) t \<ge> 0) \<Longrightarrow>
   frontier (\<Sum>loc\<in>S. f loc) = frontier (\<Sum>loc\<in>S. f' loc)"
  apply (induct S rule: finite_induct)
   apply simp_all
  apply auto
  subgoal for x F
    apply (auto simp add:  sum_nonneg zcount_sum ac_eq_iff)
    subgoal for xx
      apply (drule in_frontier_addD_alt)
      apply (simp_all add: sum_nonneg zcount_sum)
      apply auto
      subgoal
       apply (rule in_frontier_sumI1)
      apply (simp_all add: sum_nonneg zcount_sum)
        apply (metis in_frontier_iff order_le_less_trans trivial_dataflow_topology_interpretation.obtain_frontier_elem zcount_sum)
        done
      subgoal
       apply (rule in_frontier_sumI2)
      apply (simp_all add: sum_nonneg zcount_sum)
        apply (metis in_frontier_iff order_le_less_trans trivial_dataflow_topology_interpretation.obtain_frontier_elem)
        done
      done
    subgoal for xx
      apply (drule in_frontier_addD_alt)
      apply (simp_all add: sum_nonneg zcount_sum)
      apply auto
      subgoal
       apply (rule in_frontier_sumI1)
      apply (simp_all add: sum_nonneg zcount_sum)
        apply (metis in_frontier_iff order_le_less_trans trivial_dataflow_topology_interpretation.obtain_frontier_elem zcount_sum)
        done
      subgoal
       apply (rule in_frontier_sumI2)
      apply (simp_all add: sum_nonneg zcount_sum)
        apply (metis in_frontier_iff order_le_less_trans trivial_dataflow_topology_interpretation.obtain_frontier_elem)
        done
      done
    done
  done



lemma zcount_gt_0_in_frontierD:
  "0 < zcount M t \<Longrightarrow> \<exists>s\<le>t. s \<in>\<^sub>A frontier M"
  by (metis trivial_dataflow_topology_interpretation.obtain_elem_frontier)



lemma in_frontier_sumEx:
  "t \<in>\<^sub>A frontier (sum f A) \<Longrightarrow>
   finite A \<Longrightarrow>
   (\<forall>x \<in> A. \<forall> t. zcount (f x) t \<ge> 0) \<Longrightarrow>
   \<exists> x \<in> A. t \<in>\<^sub>A frontier (f x) \<and> (\<forall>a \<in> A. \<forall> t'. zcount (f a) t' > 0 \<longrightarrow> \<not> t' < t)"
  apply transfer'
  unfolding minimal_antichain_def
  apply (auto simp add: zcount_sum dest!: sum_pos_ex_elem_pos)
  apply (rule bexI)
  apply (intro conjI)
     apply assumption
    apply auto
  subgoal for t f A M y
    apply (drule spec[of _ y])
    apply (drule mp)
     apply (rule AntichainOrder.trivial_dataflow_topology_interpretation.sum_pos)
        apply auto
    done
  subgoal
    by (meson sum_pos2)
  done


lemma in_frontier_addEx:
  "x \<in>\<^sub>A frontier A \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   \<exists> y \<le> x. y \<in>\<^sub>A frontier (A + B)"
  apply transfer'
  unfolding minimal_antichain_def
  apply clarsimp
  apply (smt (verit, del_insts) order_zmset_exists_foundation zcount_union)
  done


lemma frontier_less_equal_frontier_sum_iff:
  "finite A \<Longrightarrow>
   (\<forall> a\<in>A. \<forall> t. zcount (f a) t \<ge> 0) \<Longrightarrow>
   frontier_less_equal (frontier (sum f A)) t \<longleftrightarrow> (\<exists>a\<in>A. frontier_less_equal (frontier (f a)) t)"
  apply (rule iffI)
  subgoal
    apply (induct A rule: finite_induct)
     apply simp_all
    using frontier_less_equal_add_cases apply blast
    done
  subgoal
    apply clarsimp
    subgoal for a
    apply (induct A rule: finite_induct)
     apply simp_all
      apply (auto simp add: frontier_less_equal_addI sum_nonneg zcount_sum)
      done
    done
  done




lemma frontier_less_equal_add_frontier_le_alt:
  "\<forall> t \<in>#\<^sub>z X. frontier_less_equal (frontier A) t \<Longrightarrow>
   frontier A \<le> frontier B \<Longrightarrow>
   frontier A \<le> frontier (B + X)"
  unfolding frontier_less_equal_def less_eq_antichain_def
  apply auto
  subgoal for t
    by (metis antisym_conv1 frontier_comparable_False frontier_less_equal_add_cases_stronger frontier_less_equal_def frontier_less_equal_iff order_trans rel_simps(70) zcount_ne_zero_iff)
  done


lemma set_antichain_frontier_add_update_zmultiset_le:
  "0 < zcount A t + m \<Longrightarrow>
   \<not> frontier_less_equal (frontier A) t \<Longrightarrow>
   set_antichain (frontier (A + update_zmultiset {#}\<^sub>z t m)) = {t' \<in> set_antichain (frontier A). \<not> t < t'} \<union> {t}"
  unfolding frontier_less_equal_iff
  apply transfer'
  subgoal for A t m
  apply (auto simp add: zcount_update_zmultiset minimal_antichain_def )
     apply (metis nless_le order_trans order_zmset_exists_foundation)
    done
  done

lemma frontier_add_update_zmultiset_not_le:
  "zcount A t + m \<le> 0 \<Longrightarrow>
   m \<ge> 0 \<Longrightarrow>
   frontier (A + update_zmultiset {#}\<^sub>z t m) = frontier A"
  by transfer'
   (force simp add: zcount_update_zmultiset minimal_antichain_def)

lemma frontier_zmset_of_add_minus:
  "frontier (zmset_of (A + B - C)) = frontier (zmset_of A + zmset_of B - zmset_of C)"
  apply transfer
  apply (auto simp add: minimal_antichain_def)
  done

lemma frontier_empty_if:
  "M = {#}\<^sub>z \<Longrightarrow>
   frontier M = {}\<^sub>A"
  by simp

lemma frontier_zmset_of_remove1_mset[simp]:
  "frontier (zmset_of (remove1_mset t C)) = frontier (zmset_of C - {# t #}\<^sub>z)"
  apply transfer'
  unfolding minimal_antichain_def
  apply auto
  done

lemma frontier_le_subset[simp]:
  "frontier A \<le> frontier (zmset_of (mset_set {t' \<in> set_antichain (frontier A). P t'}))"
  unfolding less_eq_antichain_def
  apply auto
  apply transfer'
  apply (auto simp add: minimal_antichain_def)
  done


section \<open>Antichains from Lists\<close>

text \<open>Building antichains from lists of pairwise incomparable elements.\<close>

lemma in_antichain_from_list[intro]:
  "\<forall>t'\<in>set xs. \<not> t' < t \<and> \<not> t < t' \<Longrightarrow>
   t \<in> set xs \<Longrightarrow>
   t \<in>\<^sub>A antichain_from_list xs"
  apply (induct xs)
  unfolding antichain_from_list_def
   apply clarsimp+
    apply (subst member_antichain.abs_eq)
    apply (auto simp add: eq_onp_def incomparable_def)
  done
lemma in_antichain_from_list_alt[intro]:
  "incomparable (set xs) \<Longrightarrow>
   t \<in> set xs \<Longrightarrow>
   t \<in>\<^sub>A antichain_from_list xs"
  apply (induct xs)
  unfolding antichain_from_list_def
   apply clarsimp+
    apply (subst member_antichain.abs_eq)
    apply (auto simp add: eq_onp_def incomparable_def)
  done

lemma antichain_from_list_empty[simp]:
  "antichain_from_list [] \<noteq> antichain {a}"
  by (metis antichain_from_list_singleton is_empty_antichain_empty_list is_empty_antichain_not_empty_list)

lemma antichain_from_list_all_eq:
  "(\<forall> x \<in> set xs. x = a) \<Longrightarrow>
   xs \<noteq> [] \<Longrightarrow>
   antichain_from_list xs = antichain {a}"
  apply (induct xs)
   apply auto
  unfolding antichain_from_list_def
  apply auto
  apply (smt (verit, best) Collect_cong insert_compr mem_Collect_eq set_diff_eq singleton_iff)
  done
lemma antichain_empty:
  "antichain {} = {}\<^sub>A"
  unfolding empty_antichain_def
  by auto

lemma antichain_from_list_empty_antichain[simp]:
  "antichain_from_list [] = {}\<^sub>A"
  by (simp add: Executable.antichain_from_list_empty antichain_empty)

lemma set_antichain_antichain_singleton[simp]:
  "set_antichain (antichain {a}) = {a}"
  apply (subst antichain_inverse)
  apply (auto simp: incomparable_def)
  done

lemma antichain_nonempty[simp]:
  "antichain {A} \<noteq> {}\<^sub>A"
  by (metis empty_antichain.rep_eq insert_not_empty set_antichain_antichain_singleton)

section \<open>Miscellaneous Frontier Facts\<close>

text \<open>Frontiers of negated multisets are empty, and other assorted facts.\<close>

lemma frontier_negs[simp]:
  "frontier (- {# a #}\<^sub>z ) = {}\<^sub>A"
  "frontier (- {# a, b #}\<^sub>z ) = {}\<^sub>A"
  "frontier (- {# a, b, c #}\<^sub>z ) = {}\<^sub>A"
  "frontier (- {# a, b, c, d #}\<^sub>z ) = {}\<^sub>A"
  "frontier (- {# a, b, c, d, e #}\<^sub>z ) = {}\<^sub>A"
  "frontier (- {# a  :: _ :: {equal,order}, b, c, d, e, f #}\<^sub>z ) = {}\<^sub>A"
  unfolding frontier_def minimal_antichain_def
  by (simp add: antichain_empty)+

lemma in_sum_antichainD:
  "t \<in>\<^sub>A A + B \<Longrightarrow> t \<in>\<^sub>A A \<or> t \<in>\<^sub>A B"
  apply transfer
  unfolding minimal_antichain_def incomparable_def
  apply auto
  done

lemma  frontier_less_equal_pluss_le:
  \<open>frontier_less_equal (A + B) t \<Longrightarrow> A \<le> B \<Longrightarrow> frontier_less_equal A t\<close>
  by (meson frontier_less_equal_iff frontier_less_equal_le_trans in_sum_antichainD)

lemma not_frontier_less_equal_sum:
  "\<not> frontier_less_equal (A + B) t \<Longrightarrow> \<not> frontier_less_equal A t \<and> \<not> frontier_less_equal B t"
  unfolding frontier_less_equal_iff
  apply clarsimp
  apply safe
  subgoal for t'
    apply transfer
    unfolding minimal_antichain_def incomparable_def
    apply clarsimp
    by (smt (verit) Un_iff dual_order.strict_iff_order order_less_le_trans)
  subgoal for t'
    apply transfer
    unfolding minimal_antichain_def incomparable_def
    apply clarsimp
    by (smt (verit) Un_iff dual_order.strict_iff_order order_less_le_trans)
  done


section \<open>Graph Path Weights\<close>

text \<open>Facts about path_weight in summary graphs, moved here from
  MyMisc so they sit beside the antichain machinery they use.\<close>

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

lemma singleton_eq_append_conv:
  "[e] = l1 @ e' # l2 \<longleftrightarrow> l1 = [] \<and> e' = e \<and> l2 = []"
  by (cases l1) auto

lemma  summary_in_path_weight:
  assumes G: "Graph.graph (\<lambda>x. antichain_from_list o su x)"
  shows 
    "t \<in> set (su l1 l2) \<Longrightarrow>
   (\<forall> l1 l2. incomparable (set (su l1 l2))) \<Longrightarrow>
   \<exists>t' \<le> t. (t' :: _ :: {canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) \<in>\<^sub>A graph.path_weight (\<lambda>x xa. antichain_from_list (su x xa)) l1 l2"
  apply (subst Graph.graph.path_weight_def)
  subgoal
    using G[unfolded comp_def] by auto
  subgoal
    apply simp
    apply (subst member_antichain.abs_eq)
     apply (clarsimp simp add: eq_onp_def)
     apply (rule graph.finite_minimal_antichain_path_weightp)
    using G[unfolded comp_def] apply assumption
    unfolding minimal_antichain_def Graph.graph.path_weightp_def[OF G, unfolded comp_def]
    apply clarsimp
    apply (subgoal_tac "graph.path (\<lambda>xa xaa. antichain_from_list (su xa xaa)) l1 l2 [(l1, t, l2)]")
    subgoal
      by (smt (verit) \<open>t \<in> set (su l1 l2) \<Longrightarrow> \<forall>l1 l2. incomparable (set (su l1 l2)) \<Longrightarrow> Graph.graph (\<lambda>x xa. antichain_from_list (su x xa))\<close> add_le_cancel_left graph.path.simps
          graph.path_path_weight graph.path_weight_conv_path graph.sum_path_weights_append_singleton graph.sum_weights_append singleton_eq_append_conv map_append
          not_Cons_self)
    subgoal
      apply (rule graph.path.intros(2)[where xs=Nil, simplified])
      using G[unfolded comp_def] apply assumption
       apply (rule graph.path.intros(1))
      using G[unfolded comp_def] apply assumption
       apply simp_all
      apply (rule in_antichain_from_list)
      unfolding incomparable_def apply fastforce
      apply assumption
      done
    done
  done


lemma in_empty_graph_False:
  "(s :: _ :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) \<in>\<^sub>A graph.path_weight (\<lambda>x xa. {}\<^sub>A) l1 l2 \<Longrightarrow>
    l1 \<noteq> l2 \<Longrightarrow> False"
  apply(subgoal_tac "Graph.graph (\<lambda>x xa. {}\<^sub>A)")
   apply (subst (asm) Graph.graph.path_weight_def)
  apply assumption
  subgoal
  apply clarsimp
  subgoal premises prems
    using prems(1) apply -
    unfolding Graph.graph.path_weightp_def[OF prems(3), unfolded comp_def]
    apply (subst (asm) in_antichain_minimal_antichain)
    subgoal
      apply (rule rev_finite_subset[where B="{}"])
       apply auto
       apply (erule graph.path.cases[OF prems(3)])
      using prems(2) mem_antichain_nonempty apply auto
      done
    subgoal
      unfolding minimal_antichain_def
      apply clarsimp
      apply (erule graph.path.cases[OF prems(3)])
      using prems(2) mem_antichain_nonempty apply auto
      done
    done
  done
  subgoal
    apply standard
      apply simp_all
    using add_mono apply blast
    done
  done

lemma path_ConsE:
  assumes G: "Graph.graph weights"
  shows "graph.path weights l1 l3 ((l2, s, l2') # xs) \<Longrightarrow> (l1 = l2 \<Longrightarrow> graph.path weights l2' l3 xs \<Longrightarrow> s \<in>\<^sub>A weights l2 l2' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct l1 l3 "((l2, s, l2') # xs)" arbitrary: xs rule: graph.path.induct[OF G, consumes 1])
    (auto simp: append_eq_Cons_conv elim!: graph.path0E[OF G] intro: graph.path.intros[OF G])

lemma mem_antichain_nonempty_alt[simp]: "s \<notin>\<^sub>A {}\<^sub>A"
  using mem_antichain_nonempty by auto

lemma path_ConsI[intro]:
  assumes G: "Graph.graph weights"
 shows "graph.path weights l2 l3 xs \<Longrightarrow> lbl \<in>\<^sub>A weights l1 l2 \<Longrightarrow> graph.path weights l1 l3 ((l1, lbl, l2) # xs)"
  apply (induct l2 l3 xs arbitrary: rule: graph.path.induct[OF G, consumes 1])
  subgoal for l1 l2
    apply hypsubst_thin
    apply (rule graph.path.intros(2)[OF G, where xs=Nil, simplified])
     apply (rule graph.path.intros(1)[OF G])
    apply simp_all
    done
  subgoal for l1a l2 xs lbla l3
    by (auto simp flip: append.simps intro: graph.path.intros[OF G])
  done

lemma path_weight_Trg_decompose:
  assumes G: "Graph.graph su"
  shows "(s :: 't :: {ordered_ab_semigroup_monoid_add_imp_le}) \<in>\<^sub>A graph.path_weight su (Loc nid (Trg p)) l \<Longrightarrow>
   l \<noteq> Loc nid (Trg p) \<Longrightarrow>
   (\<forall> nid1 nid2 p2 p1 . su (Loc nid1 (Trg p1)) (Loc nid2 (Trg p2)) = {}\<^sub>A) \<Longrightarrow>
   (\<forall> nid1 nid2 p2 p1 . nid1 \<noteq> nid2 \<longrightarrow> su (Loc nid1 (Trg p1)) (Loc nid2 (Src p2)) = {}\<^sub>A) \<Longrightarrow>
    \<exists>t p'.
       t \<in>\<^sub>A (su (Loc nid (Trg p)) (Loc nid (Src p'))) \<and>
       (\<exists>s'. s' \<in>\<^sub>A graph.path_weight su (Loc nid (Src p')) l \<and> s = t + s')"
  apply (drule graph.path_weight_conv_path[OF G])
  apply clarsimp
  subgoal for xs
    apply (rotate_tac 3)
    apply (cases xs; hypsubst_thin?)
    subgoal 
      apply (erule graph.path.cases[OF G])
       apply auto
      done
    subgoal for a xs
      apply (cases a; simp; hypsubst_thin)
      subgoal for l1 t' l2
        apply (erule path_ConsE[OF G])
        apply simp_all
        apply hypsubst_thin
        apply (cases l2; simp)
        subgoal for nid2 lp2
          apply (cases lp2; simp; hypsubst_thin)
          subgoal for p2
            apply (cases "nid = nid2")
            subgoal
              apply simp
              apply hypsubst_thin
              apply (rule exI[of _ t'])
              apply (rule exI[of _ p2])
              apply simp
              apply (subst graph.path_weight_def[OF G])
              apply simp
              apply (subst member_antichain.abs_eq)
               apply (simp add: eq_onp_def)
               apply (rule  Graph.graph.finite_minimal_antichain_path_weightp[OF G])
              unfolding minimal_antichain_def
              apply clarsimp
              apply (intro conjI exI)
               apply (subst graph.path_weightp_def[OF G])
               apply auto[1]
              apply safe
              subgoal for t''
                apply (subst (asm) graph.path_weightp_def[OF G])
                apply clarsimp
                subgoal for ys
                  apply (drule spec[of _ "(Loc nid2 (Trg p), t', Loc nid2 (Src p2)) # ys"])
                  apply (drule mp)
                  subgoal
                    apply (rule path_ConsI[OF G])
                     apply assumption+
                    done
                  apply auto
                  done
                done
              done
            subgoal
              by auto
            done
          done
        done
      done
    done
  done

lemma path_weight_end_of_road:
  assumes G: "Graph.graph su"
  shows  "s \<in>\<^sub>A graph.path_weight su loc1 loc2 \<Longrightarrow> loc2 \<noteq> loc1 \<Longrightarrow>
   (\<forall> loc2. loc2 \<noteq> loc1 \<longrightarrow> su loc1 loc2 = {}\<^sub>A) \<Longrightarrow>
   False"
  apply (drule graph.path_weight_conv_path[OF G])
  apply clarsimp
  subgoal premises prems for xs
    using prems(3,2,1) apply -
    apply (induct xs arbitrary: loc2 rule: rev_induct)
    subgoal
      apply (erule graph.path.cases[OF G])
       apply (auto simp add: )
      done
    subgoal
      apply (erule graph.path.cases[OF G])
       apply (clarsimp simp add: split: if_splits)+
      apply force
      done
    done
  done

end
