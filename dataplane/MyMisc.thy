theory MyMisc

imports
  Progress_Tracking.Propagate
  Coinductive.Coinductive_List
  Nondeterministic_Dataflow.CSet_LList_Impl
  Nondeterministic_Dataflow.Coinductive_List_Auxiliary
  AntichainOrder
  "Automatic_Refinement.Misc"
begin

definition "DEBUG = False"

definition "trace = (if DEBUG then Debug.tracing else (\<lambda> x y. y))"

lemma trace_simp[simp]:
  "trace x r = r"
  by (auto simp add: trace_def)

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

lemma  summary_in_path_weight:
  assumes G: "Graph.graph (antichain_from_list oo su)"
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
          graph.path_path_weight graph.path_weight_conv_path graph.sum_path_weights_append_singleton graph.sum_weights_append list_e_eq_lel(1) map_append
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