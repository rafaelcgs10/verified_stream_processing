theory AntichainOrder

imports
  Progress_Tracking.Antichain
  Progress_Tracking.Propagate
  "../propagation_extras/Executable"
begin 

declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]


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

lemma frontier_add:
  "(frontier N) \<le> (frontier M) \<Longrightarrow>
   (\<forall> t. t \<in>#\<^sub>z M \<longrightarrow> zcount M t > 0) \<Longrightarrow>
   frontier (M + N) = frontier N"
  unfolding less_eq_antichain_def member_antichain.rep_eq
  apply transfer
  apply auto
  unfolding incomparable_def minimal_antichain_def
  subgoal
    apply (auto 0 0)
    subgoal
      by (smt (verit, best) order_le_imp_less_or_eq order_less_le_trans order_zmset_exists_foundation zcount_eq_zero_iff)
    subgoal 
      by (metis add.right_neutral add_mono_thms_linordered_field(2) add_pos_pos not_in_iff_zmset)
    done
  subgoal
    apply (auto 0 0)
    subgoal
      by (smt (verit, best) order_le_imp_less_or_eq order_less_le_trans order_zmset_exists_foundation zcount_eq_zero_iff)
    subgoal 
      by (smt (verit, best) order_le_less_trans order_zmset_exists_foundation)
    done
  done

lemma frontier_add_alt:
  "(frontier M) \<le> (frontier N) \<Longrightarrow>
   (\<forall> t. t \<in>#\<^sub>z N \<longrightarrow> zcount N t > 0) \<Longrightarrow>
   frontier (M + N) = frontier M"
  unfolding less_eq_antichain_def member_antichain.rep_eq
  apply transfer
  apply auto
  unfolding incomparable_def minimal_antichain_def
  subgoal
    apply (auto 0 0)
    subgoal
      by (smt (verit, best) order_le_imp_less_or_eq order_less_le_trans order_zmset_exists_foundation zcount_eq_zero_iff)
    subgoal 
      by (metis add.right_neutral add_pos_pos not_in_iff_zmset)
    done
  subgoal
    apply (auto 0 0)
    subgoal
      by (smt (verit, best) order_le_imp_less_or_eq order_less_le_trans order_zmset_exists_foundation zcount_eq_zero_iff)
    subgoal 
      by (smt (verit, best) order_le_less_trans order_zmset_exists_foundation)
    done
  done

lemma frontier_idempotent[simp]:
  "frontier (zmset_of (mset_set (set_antichain (frontier M)))) = frontier M"
  apply transfer
  apply simp
  done

lemma in_frontier_iff:
  "t \<in>\<^sub>A frontier M \<longleftrightarrow> ((\<forall> t'. zcount M t' > 0 \<longrightarrow> \<not> t' < t) \<and> zcount M t > 0)"
  by (metis trivial_dataflow_topology_interpretation.in_frontier_least trivial_dataflow_topology_interpretation.obtain_elem_frontier le_less member_frontier_pos_zmset)

lemma frontier_below_eq_frontier_plus[simp]:
  "(frontier (zmset_of (mset_set (set_antichain (frontier M))) + zmset_of (mset_set (set_antichain (frontier N))))) 
  \<le>
  (frontier (N + M))"
  unfolding less_eq_antichain_def
  apply safe
  subgoal for tMN
    apply (cases "(\<exists> t. t \<le> tMN \<and> t \<in>\<^sub>A frontier M \<and> (\<forall> t'. t' \<in>\<^sub>A frontier N \<longrightarrow> \<not> t' < t)) \<or> (\<exists> t. t \<le> tMN \<and> t \<in>\<^sub>A frontier N \<and> (\<forall> t'. t' \<in>\<^sub>A frontier M \<longrightarrow> \<not> t' < t))")
    subgoal
      apply (elim disjE conjE exE)
      subgoal for t
        apply (rule exI[of _ t])
        apply (intro conjI)
        subgoal
          by (smt (verit, ccfv_threshold) trivial_dataflow_topology_interpretation.mem_zmset_frontier frontier_idempotent in_frontier_iff not_in_iff_zmset zcount_union)
        subgoal
          by order
        done
      subgoal for t
        apply (rule exI[of _ t])
        apply (intro conjI)
        subgoal
          by (smt (verit, ccfv_threshold) trivial_dataflow_topology_interpretation.mem_zmset_frontier frontier_idempotent in_frontier_iff not_in_iff_zmset zcount_union)
        subgoal
          by order
        done
      done
    subgoal
      apply (rule ccontr)
      apply auto
      apply (smt (verit, best) trivial_dataflow_topology_interpretation.frontier_unionD trivial_dataflow_topology_interpretation.obtain_frontier_elem dual_order.strict_trans1 frontier_comparable_False order_less_imp_le)
      done
    done
  done

lemma frontier_below_eq_frontier_plus_neg[simp]:
  "(\<forall> t. zcount M t \<le> 0) \<Longrightarrow>
   (frontier N) \<le> (frontier (N + M))"
  unfolding less_eq_antichain_def
  apply safe
  apply (meson trivial_dataflow_topology_interpretation.frontier_unionD trivial_dataflow_topology_interpretation.obtain_frontier_elem order.strict_iff_not)
  done

lemma frontier_below_eq_frontier_minus[simp]:
  "(\<forall> t. zcount M t \<ge> 0) \<Longrightarrow>
   (frontier N) \<le> (frontier (N - M))"
  unfolding less_eq_antichain_def
  apply safe
  apply (smt (verit, ccfv_SIG) dataflow_topology.obtain_elem_frontier member_frontier_pos_zmset trivial_dataflow_topology_interpretation.dataflow_topology_axioms zcount_diff)
  done

lemma frontier_below_eq_frontier_plus_neg_alt[simp]:
  "(\<forall> t. zcount N t \<le> 0) \<Longrightarrow>
   (frontier M) \<le> (frontier (N + M))"
  by (simp add: add.commute)

lemma frontier_below_eq_frontier_plus_frontier_below_eq_frontier_plus[simp]:
  "(frontier N) \<le> (frontier M) \<Longrightarrow>
   (frontier N) \<le> (frontier (N + M))"
  unfolding less_eq_antichain_def
  apply safe
  apply (metis trivial_dataflow_topology_interpretation.frontier_unionD trivial_dataflow_topology_interpretation.obtain_elem_frontier dual_order.trans)
  done

lemma frontier_below_eq_frontier_plus_frontier_below_eq_frontier_plus_gen[simp]:
  "(frontier N) \<le> (frontier M) \<Longrightarrow>
   (frontier C) \<le> (frontier N) \<Longrightarrow>
   frontier C \<le> frontier (N + M)"
  unfolding less_eq_antichain_def
  apply safe
  apply (metis trivial_dataflow_topology_interpretation.frontier_unionD trivial_dataflow_topology_interpretation.obtain_elem_frontier dual_order.trans)
  done


lemma frontier_below_eq_frontier_plus_pos[simp]:
  "(\<forall> t. zcount M t \<ge> 0) \<Longrightarrow>
   frontier (N + M) \<le> frontier N"
  unfolding less_eq_antichain_def
  by (metis add.commute less_add_same_cancel1 member_frontier_pos_zmset order_le_less_trans trivial_dataflow_topology_interpretation.obtain_frontier_elem zcount_union)

lemma frontier_add_zmset:
  "frontier M \<le> frontier N \<Longrightarrow>
   frontier (add_zmset x M) \<le> frontier N"
  using frontier_below_eq_frontier_plus_pos
  by (metis add_zmset_add_single dual_order.refl dual_order.trans zcount_single zero_less_one_class.zero_le_one)

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

lemma frontier_linorder:
  "frontier (A :: ('a :: linorder) zmultiset) = (if {t. zcount A t > 0} = {} then {}\<^sub>A else antichain {Min {t. zcount A t > 0}})"
  apply (auto split: if_splits simp add: empty_antichain_def minimal_antichain_def frontier.abs_eq)
  apply (rule arg_cong[where f=antichain])
  apply safe
    apply simp_all
  subgoal
    by (metis Min_eqI finite_zcount_pos mem_Collect_eq verit_comp_simplify1(3))
  subgoal
    using \<open>\<And>xa x. 0 < zcount A x \<Longrightarrow> 0 < zcount A xa \<Longrightarrow> \<forall>y. 0 < zcount A y \<longrightarrow> \<not> y < xa \<Longrightarrow> xa = Min {t. 0 < zcount A t}\<close> order_zmset_exists_foundation by blast
  subgoal
    by (metis Min_le finite_zcount_pos linorder_not_le mem_Collect_eq)
  done

lemma frontier_singleton:
  "frontier {#x#}\<^sub>z = antichain {x}"
  by (smt (verit, ccfv_threshold) add_0 finite.emptyI finite_insert frontier_le_add_singleton in_antichain_minimal_antichain less_eq_antichain_def member_frontier_pos_zmset minimal_antichain_singleton order_antisym_conv
      order_less_le singleton_iff zcount_empty zcount_single)

lemma frontier_le_zmset_of[simp]:
  "frontier {#t#}\<^sub>z \<le> frontier (zmset_of {#t. x \<in># mset xs#})"
  apply (induct xs)
  using frontier_le_add apply fastforce+
  done

lemma frontie_add_zmset_add:
  "frontier (add_zmset t A) \<le> frontier {#t#}\<^sub>z \<Longrightarrow>
   frontier (add_zmset t A) \<le> frontier (add_zmset t A + zmset_of {#t. x \<in># mset xs#})"
  apply (induct xs)
   apply auto
  using frontier_le_add apply fastforce
  done

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

lemma frontier_add_le:
  "frontier B \<le> frontier C \<Longrightarrow>
   frontier (A + B) \<le> frontier B \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   frontier (A + B) \<le> frontier (A + C)"
  unfolding less_eq_antichain_def
  apply auto
  apply (smt (verit, ccfv_threshold) order.trans trivial_dataflow_topology_interpretation.frontier_unionD trivial_dataflow_topology_interpretation.obtain_elem_frontier zcount_union)
  done

lemma frontier_add_le_gen:
  "frontier B \<le> frontier C \<Longrightarrow>
   frontier (A + B) \<le> frontier B \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   frontier A \<le> frontier A' \<Longrightarrow>
   frontier (A + B) \<le> frontier (A' + C)"
  unfolding less_eq_antichain_def
  apply auto
  apply (smt (verit, ccfv_threshold) dual_order.trans frontier_below_eq_frontier_plus_pos less_eq_antichain_def trivial_dataflow_topology_interpretation.frontier_unionD
      trivial_dataflow_topology_interpretation.obtain_frontier_elem)
  done

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

lemma frontier_le_minus_gen:
  "frontier A \<le> frontier B \<Longrightarrow>
   (\<forall> t. zcount C t \<ge> 0) \<Longrightarrow>
   frontier A \<le> frontier (B - C)"
  by (meson dual_order.trans frontier_below_eq_frontier_minus)

lemma frontier_add_le_alt:
  "frontier A \<le> frontier C \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   frontier B \<le> frontier C \<Longrightarrow>
   frontier (A + B) \<le> frontier C"
  using frontier_below_eq_frontier_plus_pos order_trans by blast

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


lemma frontier_add_le_alt2:
  "frontier (A + {#t#}\<^sub>z) \<le> frontier {#t#}\<^sub>z \<Longrightarrow>
   t \<le> t' \<Longrightarrow>
   zcount A t' \<ge> 0 \<Longrightarrow>
   frontier (A + {#t'#}\<^sub>z) \<le> frontier {#t'#}\<^sub>z"
  unfolding less_eq_antichain_def
  apply auto
  apply (metis dual_order.irrefl dual_order.strict_trans2 member_frontier_pos_zmset trivial_dataflow_topology_interpretation.obtain_elem_frontier zcount_add_zmset zcount_single zless_add1_eq)
  done

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

lemma frontier_add_le_alt3:
  "frontier B \<le> frontier C \<Longrightarrow>
   (\<forall> t. zcount A t \<ge> 0) \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   frontier (A + B) \<le> frontier (A + C)"
  unfolding less_eq_antichain_def
  apply auto
  apply (metis add.commute frontier_add_le frontier_below_eq_frontier_plus_pos less_eq_antichain_def)
  done

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

lemma fronteier_lt_add_ex:
  "t' \<in>\<^sub>A frontier A \<Longrightarrow> t' \<le> t \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   \<exists>t'. t' \<in>\<^sub>A frontier (A + B) \<and> t' \<le> t"
  using in_frontier_in_frontier_add_alt by blast


definition
  "frontier_less_equal ft t = (\<not> is_empty_antichain (filter_antichain (\<lambda> f. f \<le> t) ft))"

lemma frontier_less_equal_empty_antichain[simp]:
  "\<not> frontier_less_equal {}\<^sub>A A"
  unfolding frontier_less_equal_def
  apply transfer
  unfolding Set.filter_eq Set.is_empty_iff
  apply simp
  done


lemma frontier_less_equal_iff:
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
  unfolding frontier_less_equal_iff
  apply (rule Orderings.preorder_class.order_trans)
   apply assumption+
  done

lemma frontier_less_equal_trans:
  "frontier_less_equal A t' \<Longrightarrow>
   t' \<le> t \<Longrightarrow> 
   frontier_less_equal A t"
  unfolding frontier_less_equal_iff
  by (meson frontier_le_singletons order_trans_rules(23))


lemma frontier_less_equal_iff2:
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
  unfolding frontier_less_equal_iff
  apply safe
  using frontier_le_remove_l apply blast
  using frontier_le_remove_left apply blast
  done

lemma frontier_less_equal_addI1:
  "frontier_less_equal (frontier A) t \<Longrightarrow>
   (\<forall> t' \<le> t. zcount A t' > 0 \<longrightarrow> zcount A t' + zcount B t' > 0) \<Longrightarrow>
   frontier_less_equal (frontier (A + B)) t"
  unfolding frontier_less_equal_iff2
  apply clarsimp
  apply (metis (full_types) dual_order.trans in_frontier_iff trivial_dataflow_topology_interpretation.obtain_elem_frontier zcount_union)
  done

lemma frontier_less_equal_add_cases:
  "frontier_less_equal (frontier (A + B)) t \<Longrightarrow>
   frontier_less_equal (frontier A) t \<or> frontier_less_equal (frontier B) t"
  unfolding frontier_less_equal_iff2
  using in_frontier_addD order_trans_rules(23) by blast

lemma frontier_less_equal_add_cases_stronger:
  "frontier_less_equal (frontier (A + B)) t \<Longrightarrow>
   (\<exists> t'. (zcount A t' > 0 \<and> frontier_less_equal (frontier A) t \<or> zcount B t' > 0 \<and> frontier_less_equal (frontier B) t) \<and> t' \<le> t \<and> zcount A t' + zcount B t' > 0 \<and> t' \<in>\<^sub>A frontier (A + B))"
  unfolding frontier_less_equal_iff2 in_frontier_iff
  apply (auto del: )
  by (smt (verit) order.trans order_zmset_exists_foundation')

lemma frontier_less_equal_zcount_pos:
  " 0 < zcount A x \<Longrightarrow>
    frontier_less_equal (frontier A) x"
  unfolding frontier_less_equal_iff
  by (metis dual_order.irrefl less_eq_antichain_def member_frontier_pos_zmset trivial_dataflow_topology_interpretation.obtain_elem_frontier zcount_single)

term "dataflow_topology.implied_frontier_alt su (+) c l"

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

lemma frontier_less_equal_subset_sumI:
  "finite S \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (f l) t \<ge> 0) \<Longrightarrow>
   S' \<subseteq> S \<Longrightarrow>
   frontier_less_equal (frontier (\<Sum>loc\<in>S'. f loc)) t \<Longrightarrow>
   frontier_less_equal (frontier (\<Sum>loc\<in>S. f loc)) t"
  apply (induct S arbitrary:S' rule: finite_induct)
  apply (clarsimp simp add: frontier_less_equal_addI sum_nonneg zcount_sum)+
  apply (smt (verit, del_insts) Set.set_insert frontier_less_equal_addI frontier_less_equal_add_cases insert_subset rev_finite_subset subset_insert sum.insert_if sum_nonneg
      zcount_sum)
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

lemma frontier_lt_minus_add:
  "(\<forall> t. zcount A t \<ge> 0) \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   frontier A \<le> frontier (C - B) \<Longrightarrow> frontier (B + A) \<le> frontier C"
  unfolding less_eq_antichain_def
  apply auto
  apply transfer'
  unfolding incomparable_def minimal_antichain_def
  apply auto
  apply (smt (z3) dual_order.strict_trans2 in_frontier_iff nless_le trivial_dataflow_topology_interpretation.obtain_elem_frontier)
  done

lemma frontier_sum_le_alt:
  "finite S \<Longrightarrow>
   S' \<subseteq> S \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (f l) t \<ge> 0) \<Longrightarrow>
   frontier (\<Sum>loc\<in>S. f loc) \<le> frontier (\<Sum>loc\<in>S'. f loc)"
    apply (induct S arbitrary: S' rule: finite_induct)
   apply simp_all
  apply (clarsimp simp add: subset_insert_iff split: if_splits)
  subgoal for x F S'
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply assumption
    apply (subst (asm) sum_diff)
      apply simp_all
     apply (meson infinite_remove infinite_super)
    apply (rule frontier_lt_minus_add)
    apply (simp_all add: sum_nonneg zcount_sum)
    done
  subgoal for x F S'
    by (meson frontier_le_remove_left)
  done

lemma frontier_lt_subseq:
  "N \<subseteq>#\<^sub>z M \<Longrightarrow>
   frontier M \<le> frontier N"
  unfolding less_eq_antichain_def
  apply clarsimp
  apply transfer'
  unfolding incomparable_def minimal_antichain_def
  apply (metis (no_types, lifting) ext frontier.rep_eq in_frontier_iff member_antichain.rep_eq minimal_antichain_def order.strict_trans2 subseteq_zmset_def
      trivial_dataflow_topology_interpretation.obtain_elem_frontier)
  done



lemma frontier_sum_le_alt2:
  "finite S \<Longrightarrow>
   S' \<subseteq> S \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. f' l \<subseteq>#\<^sub>z f l) \<Longrightarrow>
   frontier (\<Sum>loc\<in>S. f loc) \<le> frontier (\<Sum>loc\<in>S. f' loc)"
    apply (induct S arbitrary: S' rule: finite_induct)
   apply simp_all
  apply (clarsimp simp add: subset_insert_iff split: if_splits)
  subgoal for x F S'
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply assumption
    using frontier_lt_subseq 
    apply (metis subset_zmset.add_mono trivial_dataflow_topology_interpretation.sum_mono_subseteq)
    done
  subgoal for x F S'
    by (simp add: frontier_lt_subseq subset_zmset.add_mono trivial_dataflow_topology_interpretation.sum_mono_subseteq)
  done

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

lemma in_frontier_SumD:
  "t \<in>\<^sub>A frontier (\<Sum>loc\<in>A. f loc) \<Longrightarrow>
   zcount (f a) t > 0 \<Longrightarrow>
   (\<forall> loc \<in> A. \<forall> y. zcount (f loc) y \<ge> 0) \<Longrightarrow>
   a \<in> A \<Longrightarrow>
   t \<in>\<^sub>A frontier (f a)"
    apply transfer
    unfolding minimal_antichain_def
    apply clarsimp
    apply (smt (verit, ccfv_SIG) sum.infinite sum_nonneg_leq_bound zcount_sum)
    done

lemma in_frontier_Sum_all_not_lt:
  "t \<in>\<^sub>A frontier (\<Sum>loc\<in>A. f loc) \<Longrightarrow>
   (\<forall> loc \<in> A. \<forall> y. zcount (f loc) y \<ge> 0) \<Longrightarrow>
   (\<forall> loc\<in>A. \<forall> t'. zcount (f loc) t' > 0 \<longrightarrow> \<not> t' < t)"
    apply transfer'
    unfolding minimal_antichain_def
    apply clarsimp
    apply (smt (verit, ccfv_SIG) sum.infinite sum_nonneg_leq_bound zcount_sum)
    done

lemma zcount_gt_0_in_frontierD:
  "0 < zcount M t \<Longrightarrow> \<exists>s\<le>t. s \<in>\<^sub>A frontier M"
  by (metis trivial_dataflow_topology_interpretation.obtain_elem_frontier)

lemma in_frontier_SumI:
  "finite A \<Longrightarrow>
   t \<in>\<^sub>A frontier (f a) \<Longrightarrow>
   a \<in> A \<Longrightarrow>
   (\<forall> x \<in> A. \<forall> t'. zcount (f x) t' \<ge> 0) \<Longrightarrow>
   (\<forall> x \<in> A. \<forall> t'. x \<noteq> a \<longrightarrow> zcount (f x) t' > 0 \<longrightarrow> \<not> t' < t) \<Longrightarrow>
   t \<in>\<^sub>A frontier (sum f A)"
  apply (induct A rule: finite_induct)
   apply simp_all
  apply (clarsimp simp add: sum_nonneg zcount_sum)
  subgoal 
    apply (elim disjE)
    subgoal
      apply hypsubst_thin
      apply (rule in_frontier_sumI1)
         apply auto
       apply (metis sum_pos_ex_elem_pos zcount_sum)
      apply (simp add: sum_nonneg zcount_sum)
      done
    subgoal
      apply (rule in_frontier_sumI2)
         apply auto
      apply (simp add: sum_nonneg zcount_sum)
      done
    done
  done


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


lemma frontier_less_equal_add_frontier_le:
  "\<forall> t \<in>#\<^sub>z X. frontier_less_equal (frontier A) t \<Longrightarrow>
   frontier A \<le> frontier (A + X)"
  unfolding frontier_less_equal_def less_eq_antichain_def
  apply auto
  subgoal for t
    by (metis frontier_less_equal_def frontier_less_equal_iff2 in_frontier_addD pos_zcount_in_zmset)
  done


lemma frontier_less_equal_add_frontier_le_alt:
  "\<forall> t \<in>#\<^sub>z X. frontier_less_equal (frontier A) t \<Longrightarrow>
   frontier A \<le> frontier B \<Longrightarrow>
   frontier A \<le> frontier (B + X)"
  unfolding frontier_less_equal_def less_eq_antichain_def
  apply auto
  subgoal for t
    by (metis antisym_conv1 frontier_comparable_False frontier_less_equal_add_cases_stronger frontier_less_equal_def frontier_less_equal_iff2 order_trans rel_simps(70) zcount_ne_zero_iff)
  done

lemma frontier_add_update_zmultiset_le:
  "zcount A t + m > 0 \<Longrightarrow>
   (frontier (A + update_zmultiset {#}\<^sub>z t m)) = frontier A + frontier {#t#}\<^sub>z"
  apply transfer'
  apply (auto simp add: zcount_update_zmultiset minimal_antichain_def)
  subgoal for A m x y
    by force
  subgoal
    by (metis basic_trans_rules(21) order_zmset_exists_foundation)
  done

lemma set_antichain_frontier_add_update_zmultiset_le:
  "0 < zcount A t + m \<Longrightarrow>
   \<not> frontier_less_equal (frontier A) t \<Longrightarrow>
   set_antichain (frontier (A + update_zmultiset {#}\<^sub>z t m)) = {t' \<in> set_antichain (frontier A). \<not> t < t'} \<union> {t}"
  unfolding frontier_less_equal_iff2
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

end