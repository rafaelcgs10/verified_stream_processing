theory AntichainOrder

imports
  Progress_Tracking.Antichain
  Progress_Tracking.Propagate
  Progress_Tracking.Exchange
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


(*
\<forall>t. 0 < zcount (c_pts (pt_tr sg) (Loc 1 (Trg 1))) t + zcount (zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (lo_pt sg)))) t + zcount (zmset (map snd (produ os1))) t +
            zcount (zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (map (\<lambda>(p, t, m). (Loc 1 (Trg 1), t, - m)) (consu os2))))) t +
            (if n 1 = t then zcount {#}\<^sub>z t + 1 else zcount {#}\<^sub>z t) \<longrightarrow>
        t \<le> n 1 \<Longrightarrow>
    frontier
     (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (lo_pt sg))) +
      (zmset (map snd (produ os1)) + (zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (map (\<lambda>(p, t, m). (Loc 1 (Trg 1), t, - m)) (consu os2)))) + {#n 1#}\<^sub>z)))
    \<le> frontier (zmset_of {#n 1. x \<in># mset batch'#})
*)

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
  "frontier C \<le> frontier A \<Longrightarrow>
   frontier C \<le> frontier B \<Longrightarrow>
   frontier C \<le> frontier (A + B)"
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

(*
frontier
     (add_zmset (n 1)
       (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (lo_pt sg))) + zmset (map snd (produ os1)) +
        zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (map (\<lambda>(p, t, m). (Loc 1 (Trg 1), t, - m)) (consu os2))))))
    \<le> frontier {#n 1#}\<^sub>z \<Longrightarrow>
    frontier
     (add_zmset (n 1)
       (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (lo_pt sg))) + zmset (map snd (produ os1)) +
        zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (map (\<lambda>(p, t, m). (Loc 1 (Trg 1), t, - m)) (consu os2))))))
    \<le> frontier
        (add_zmset (n 1)
          (c_pts (pt_tr sg) (Loc 1 (Trg 1)) + zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (lo_pt sg))) +
           (zmset (map snd (produ os1)) + (zmset (map snd (filter (\<lambda>(l', t, d). Loc 1 (Trg 1) = l') (map (\<lambda>(p, t, m). (Loc 1 (Trg 1), t, - m)) (consu os2)))) + zmset_of {#n 1. x \<in># mset batch'#}))))

*)


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

lemma in_frontier_in_frontier_add:
  "t \<in>\<^sub>A frontier A \<Longrightarrow>
   (\<forall> t. zcount B t \<ge> 0) \<Longrightarrow>
   \<exists>t'. t' \<in>\<^sub>A frontier (A + B) \<and> t' \<le> t"
  using frontier_below_eq_frontier_plus_pos less_eq_antichain_def by blast



lemma frontier_add_le_alt2:
  "frontier (A + {#t#}\<^sub>z) \<le> frontier {#t#}\<^sub>z \<Longrightarrow>
   t \<le> t' \<Longrightarrow>
   zcount A t' \<ge> 0 \<Longrightarrow>
   frontier (A + {#t'#}\<^sub>z) \<le> frontier {#t'#}\<^sub>z"
  unfolding less_eq_antichain_def
  apply auto
  apply (metis dual_order.irrefl dual_order.strict_trans2 member_frontier_pos_zmset trivial_dataflow_topology_interpretation.obtain_elem_frontier zcount_add_zmset zcount_single zless_add1_eq)
  done


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
  done

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
  done

lemma
  assumes "justified C M1"
    and   "justified C M2"
    and   "\<forall>t. 0 \<le> zcount C t"
  shows   "justified C (M1+M2)"
 apply (rule justified_leastI)
  apply (intro allI impI)
  subgoal for t
    apply (cases "0 < zcount M1 t") (* symmetric cases *)
    subgoal
      apply (drule assms(1)[unfolded justified_alt supported_strong_def, rule_format])
      apply (elim disj3_split)
      subgoal
        apply (elim exE conjE)
        apply (drule order_zmset_exists_foundation_neg)
        apply (elim exE conjE)
        subgoal for s s' (* anything less than s' is 0 in M1 *)
          apply (cases "zcount (M1 + M2) s' < 0")
          subgoal
            apply (rule disjI1)
            apply (auto intro!: exI[of _ s'] simp: nonpos_upto_def supported_strong_def) []
            done
          subgoal
            apply (subst (asm) not_less)
            apply (cases "0 < zcount M2 s'")
             prefer 2
            subgoal by auto (* trivial contradiction *)
            subgoal
              apply (drule assms(2)[unfolded justified_alt supported_strong_def, rule_format])
              apply (elim disj3_split)
              subgoal
                apply (rule disjI1)
                apply (elim exE)
                subgoal for s''
                  by (auto intro!: exI[of _ s''] simp: nonpos_upto_def supported_strong_def add_nonpos_neg)
                done
              subgoal
                apply (rule disjI2, rule disjI1)
                apply (elim exE conjE)
                subgoal for s''
                  using assms(3) by (auto simp: add_nonneg_pos intro!: exI[of _ s''])
                done
              subgoal
                by (metis add.right_neutral add_strict_increasing2 assms(3) less_add_same_cancel1 order.strict_trans1 pos_add_strict zcount_union)
              done
            done
          done
        done
      subgoal
        by blast
      subgoal
        apply simp
        oops

        thm justified_add_msg_delta

end