theory AntichainOrder

imports
  Progress_Tracking.Antichain
  Progress_Tracking.Propagate
begin 

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

end