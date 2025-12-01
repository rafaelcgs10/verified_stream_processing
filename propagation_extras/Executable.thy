theory Executable

imports 
   Progress_Tracking.Propagate
  "../dataplane/Locations"
begin
declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]  neg_filter_zmset_neg_zmset[simp del]


declare [[typedef_overloaded]]

datatype ('loc :: enum, 't) Step =
  CM 'loc 't int |
  PR

lift_definition zmultiset_of_antichain :: "'t :: order antichain \<Rightarrow> 't zmultiset" is
  "\<lambda>A. (mset_set A, {#})" .

declare [[code drop: mset_set]]
lemma mset_set_code[code]: "mset_set (set xs) = mset (remdups xs)"
  using mset_set_set by fastforce

(*
  Computes the difference of frontiers of two zmultisets.
*)
abbreviation frontier_change_code :: "'t :: order zmultiset
                                           \<Rightarrow> 't zmultiset
                                           \<Rightarrow> 't zmultiset" where
  "frontier_change_code M0 M1 \<equiv>
  zmultiset_of_antichain (frontier M1) - zmultiset_of_antichain (frontier M0)"

definition t_loc_pairs :: "('loc :: enum, 't) configuration \<Rightarrow> ('t \<times> 'loc) set" where
  "t_loc_pairs c = (\<Union>x \<in> set enum_class.enum. (Set.image (\<lambda>t. (t, x)) (set_zmset (c_work c x))))"

export_code t_loc_pairs in SML

lift_definition is_empty_antichain :: "'a :: order antichain \<Rightarrow> bool" is "Set.is_empty".

locale enum_dataflow_topology = dataflow_topology summary results_in 
  for summary :: "'loc \<Rightarrow> 'loc :: {linorder, enum} \<Rightarrow> 'sum :: {order, monoid_add} antichain" 
  and results_in :: "'t :: order \<Rightarrow> 'sum \<Rightarrow> 't"
begin

fun take_step :: "('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('loc :: {linorder, enum} , 't) Step
                   \<Rightarrow> ('loc, 't) configuration
                   \<Rightarrow> ('loc, 't) configuration" where
  "take_step _ (CM loc t delta) c =
  (let c_pointstamps_old = c_pts c loc;
       c_pointstamps_new = (c_pts c)(loc := (update_zmultiset (c_pts c loc) t delta)) in
   c \<lparr> c_pts := c_pointstamps_new,
       c_work := (c_work c) (loc := (c_work c loc) +
                     (frontier_change_code c_pointstamps_old (c_pointstamps_new loc)))
      \<rparr>)"
| "take_step t_less PR c =
      (let (t, loc) = mymin t_less (t_loc_pairs c);
      c_implications_old = c_imp c loc;
      c_implications_new = ((c_imp c)
                           (loc :=  c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}));
      c_worklist_removed_loc = ((c_work c) (loc := {#t' \<in>#\<^sub>z c_work c loc. t' \<noteq> t#}))
  in
  c \<lparr>  c_work := \<lambda> loc'. ((c_worklist_removed_loc loc') +
                              after_summary (frontier_change_code (c_implications_old) (c_implications_new loc)) (summary loc loc')),
       c_imp := c_implications_new \<rparr>)"

lemma zmset_of_lemma: "zmultiset_of_antichain (frontier A) = zmset_frontier A"
  apply (simp add: zmultiset_of_antichain_def zmset_of_def)
  done

lemma CM_next:
  assumes "delta \<noteq> 0"
    and "\<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t"
  shows "next_change_multiplicity' c (take_step linord (CM loc t delta) c) loc t delta"
  apply (cases c)
  apply (auto simp: next_change_multiplicity'_def Let_def)
  using assms(1) apply simp
  using assms(2) apply auto[1]
  apply(simp add: zmset_of_lemma)
  done

lemma PR_next:
  assumes "\<exists> t loc. t \<in>#\<^sub>z c_work c loc"
    "class.linorder (\<lambda>t u. less_t t u \<or> t = u) less_t"
    "\<And>t u. t < u \<Longrightarrow> less_t t u"
  shows "next_propagate
          (shd (c ## (take_step less_t PR c) ## s))
          (shd (stl (c ## (take_step less_t PR c) ## s)))"
  apply (cases c)
  apply (auto simp: next_propagate'_def Let_def split: prod.splits)
  apply (intro exI[of _ "snd (mymin less_t (t_loc_pairs c))"] impI conjI ext
      exI[of _ "fst (mymin less_t (t_loc_pairs c))"])
     apply auto
  subgoal for ws ps "is" t loc
    apply (simp add: t_loc_pairs_def Set.image_def)
    unfolding set_zmset_def
    apply (auto simp add: zcount_ne_zero_iff[of "c_work c loc" "t"])
  proof -
    interpret linorder "t_loc_linord less_t" "\<lambda>t u. t_loc_linord less_t t u \<and> t \<noteq> u"
      by (rule linorder_t_loc_linord[OF assms(2)])
    assume
      "c = \<lparr>c_work = ws, c_pts = ps,  c_imp = is\<rparr>"
      "mymin less_t (\<Union> {y. \<exists>x\<in>set enum_class.enum. y = {y. \<exists>xa\<in>#\<^sub>zws x. y = (xa, x)}}) = (t, loc)"
    with assms show "t \<in>#\<^sub>z ws loc"
      unfolding mymin_def
      apply (subst (asm) Min_eq_iff)
        apply auto []
       apply (auto simp: enum_UNIV) []
      apply auto
      done
  qed
  subgoal for ws ps "is" t loc t' loc'
    apply (simp add: t_loc_pairs_def Set.image_def)
    unfolding set_zmset_def
    apply (auto simp add: zcount_ne_zero_iff[of "c_work c loc" "t"])
  proof -
    interpret less_t: linorder "(\<lambda>t u. less_t t u \<or> t = u)" less_t
      by (rule assms)
    interpret linorder "t_loc_linord less_t" "\<lambda>t u. t_loc_linord less_t t u \<and> t \<noteq> u"
      by (rule linorder_t_loc_linord[OF assms(2)])
    assume
      "c = \<lparr>c_work = ws, c_pts = ps, c_imp = is\<rparr>"
      "mymin less_t (\<Union> {y. \<exists>x\<in>set enum_class.enum. y = {y. \<exists>xa\<in>#\<^sub>zws x. y = (xa, x)}}) = (t, loc)"
      "t' \<in>#\<^sub>z ws loc'" "t' < t"
    with assms(1,2) show False
      unfolding mymin_def
      apply (subst (asm) Min_eq_iff)
        apply auto []
       apply (auto simp: enum_UNIV) []
      apply (auto simp: enum_UNIV t_loc_linord_def)
      apply (drule spec)
      apply (drule mp)
       apply (rule exI[of _ loc'])
       apply (rule refl)
      apply simp
      apply (drule spec, drule mp, assumption)
      apply (auto simp add: assms(3) less_t.not_le)
      using assms(3) less_t.less_not_sym apply blast
      done
  qed
  subgoal for ws ps "is" t loc
    apply (simp add: t_loc_pairs_def Set.image_def)
    unfolding set_zmset_def
    apply (auto simp add: zcount_ne_zero_iff[of "c_work c loc" "t"])
    apply (simp add: summary_self)
    done
  subgoal  by (simp add: zmset_of_lemma)
  done


end

declare zmultiset_of_antichain_def[code]

lemma set_zmset_code[code]:
  "set_zmset (abs_zmultiset x) = (case x of (A, B) \<Rightarrow> set_mset (A - B) \<union> set_mset (B - A))"
  unfolding set_zmset_def
  by transfer (auto simp: set_mset_def)

lemma frontier_code[code]:
  "set_antichain (frontier x) = minimal_antichain {t \<in> set_zmset x. 0 < zcount x t}"
  by transfer' (auto intro!: arg_cong[of _ _ minimal_antichain] zcount_inI)

lemma frontier_empty_zmset: "frontier {#}\<^sub>z = {}\<^sub>A"
  by transfer' (auto simp: minimal_antichain_def)

(* lemma summary_self: "summary (op, p) (op, p) = {}\<^sub>A"
  by (cases op; cases p) (auto simp: summary_def frontier_empty_zmset)
 *)

lemma incomparable_set_list[simp]:
  "incomparable {x \<in> set (xs :: 'sum :: {order, monoid_add} list). list_all ((\<le>) x) xs}"
  apply (subst list_all_def set_filter)
  apply (simp add: basic_trans_rules(24) incomparable_def list.pred_set)
  done

lift_definition antichain_from_list :: "'sum :: {order, monoid_add} list \<Rightarrow> 'sum antichain" is
  "\<lambda>A. set (filter (\<lambda> x . (list_all ((\<le>) x) A)) A)"
  apply simp
  done

lemma antichain_from_list_antichain:
  "antichain_from_list xs = antichain {x \<in> set xs. list_all ((\<le>) x) xs}"
  unfolding antichain_from_list_def
  apply clarsimp
  done

declare zmultiset_of_antichain_def[code]

lemma antichain_sum_empty[simp]:
  "A + {}\<^sub>A = A"
  apply transfer
  apply simp
  apply (smt (verit, ccfv_threshold) in_minimal_antichain incomparable_def order_class.order_eq_iff order_less_imp_not_eq subset_iff)
  done

lift_definition zequal :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> bool" is
  "\<lambda> (M, N) (P, Q). (M-N) = (P-Q) \<and> (N-M) = (Q-P)"
  apply (auto simp: equiv_zmset_def)
  apply (metis (full_types) Multiset.diff_right_commute add_diff_cancel_right')
  apply (metis Multiset.diff_right_commute add_diff_cancel_left')
  apply (metis add_diff_cancel_right' cancel_ab_semigroup_add_class.diff_right_commute)
  by (metis Multiset.diff_right_commute add_diff_cancel_left')

lemma is_empty_antichain_simp[simp]:
  "is_empty_antichain {}\<^sub>A"
  apply transfer
  apply (auto simp add: Set.is_empty_def)
  done
lemma is_empty_antichain_empty_list[simp]:
  "is_empty_antichain (antichain_from_list [])"
  apply transfer
  apply (auto simp add: Set.is_empty_def)
  done
lemma is_empty_antichain_not_empty_list[simp]:
  "\<not> is_empty_antichain (antichain_from_list [a])"
  apply transfer
  apply (auto simp add: Set.is_empty_def)
  done

definition "reachable_locations summary \<equiv> { loc . \<exists> loc' .
     \<not> is_empty_antichain (summary loc loc') \<or> \<not> is_empty_antichain (summary loc' loc) }"

definition worklist_is_empty where
  "worklist_is_empty summary c = Set.Ball (reachable_locations summary) (\<lambda> loc. zequal (c_work c loc) {#}\<^sub>z)"

lift_definition Max_antichain :: "nat antichain \<Rightarrow> nat" is "\<lambda> x. if Set.is_empty x then 42 else Max x" .

lemma update_zmultiset_simps[simp]:
  "update_zmultiset A x 0 = A"
  "update_zmultiset A x (int (Suc n)) = {# x #}\<^sub>z + update_zmultiset A x (int n)"
  "update_zmultiset A x (- (int (Suc n))) = update_zmultiset A x (- (int n)) - {# x #}\<^sub>z"
  subgoal
    apply transfer
    apply (auto simp add: equiv_zmset_def)
    done
  subgoal
    apply transfer
    apply (clarsimp simp add: equiv_zmset_def split: if_splits)
    apply (metis nat_int of_nat_Suc replicate_mset_Suc)
    done
  subgoal
    apply transfer
    apply (clarsimp simp add: equiv_zmset_def split: if_splits)
    apply (metis Suc_as_int replicate_mset_Suc)
    done
  done

lemma update_zmultiset_simps_more[simp]:
  "update_zmultiset A x (int n) = A + zmset_of (replicate_mset n x)"
  "update_zmultiset A x (- (int n)) = A - zmset_of (replicate_mset n x)"
  subgoal
    apply (induct n)
    apply simp_all
    apply (metis Groups.add_ac(2) add_zmset_add_single int_ops(2,5) plus_1_eq_Suc update_zmultiset_simps(2))
    done
  subgoal
    apply (induct n)
    apply simp_all
    apply (metis ab_group_add_class.ab_diff_conv_add_uminus arith_simps(49) diff_add_eq_diff_diff_swap int_Suc union_add_left_zmset
        update_zmultiset_simps(3))
    done
  done

lemma update_zmultiset_replicate:
  "update_zmultiset A x (m :: int) =
  (if m < 0 then A - zmset_of (mset (replicate (nat (abs m)) x)) else A + zmset_of (mset (replicate (nat m) x)))"
  apply (cases m)
  apply clarsimp+
  apply (metis add_uminus_conv_diff int_Suc is_num_normalize(8) nat_int update_zmultiset_simps_more(2))
  done

lemma update_zmultiset_singleton:
  "update_zmultiset {#}\<^sub>z t (- 1) = - {# t #}\<^sub>z"
  "update_zmultiset {#}\<^sub>z t' (1) = {# t' #}\<^sub>z"
  by (simp add: update_zmultiset_replicate)+

lemma update_zmultiset_one:
  "update_zmultiset A t (- 1) = A - {# t #}\<^sub>z"
  "update_zmultiset A t' (1) = A + {# t' #}\<^sub>z"
  by (simp add: update_zmultiset_replicate)+

lemma update_zmultiset_comm:
  "update_zmultiset (update_zmultiset A x m) y n = update_zmultiset (update_zmultiset A y n) x m"
  apply (cases m; cases n)
  apply (clarsimp simp add: update_zmultiset_replicate)+
  apply (simp add: add.commute)
  done

lemma update_zmultiset_plus_pos:
  "A + update_zmultiset B x (int m) = B + update_zmultiset A x (int m)"
  by simp
lemma update_zmultiset_plus_neg:
  "A + update_zmultiset B x (- (int m)) = (A + B) - update_zmultiset {#}\<^sub>z x (int m)"
  apply simp
  using add_diff_eq apply blast
  done

lemma update_zmultiset_plus[simp]:
  "update_zmultiset (update_zmultiset A t n) t m = update_zmultiset A t (n + m)"
  apply transfer
  apply (clarsimp simp add:  nat_add_distrib replicate_mset_plus equiv_zmset_def split: if_splits)
  subgoal by (metis ab_group_add_class.ab_diff_conv_add_uminus diff_add_cancel less_imp_le nat_add_distrib neg_0_le_iff_le not_le replicate_mset_plus)
  subgoal by (smt (verit, del_insts) nat_add_distrib replicate_mset_plus)
  subgoal by (smt (verit, ccfv_threshold) add.commute add.left_commute nat_add_distrib replicate_mset_plus) 
  subgoal by (smt (verit, ccfv_threshold) nat_add_distrib replicate_mset_plus)
  subgoal by (smt (verit, best) nat_add_distrib replicate_mset_plus) 
  done


lemma antichain_not_empty:
  "finite A \<Longrightarrow> incomparable A \<Longrightarrow> antichain A = {}\<^sub>A \<longleftrightarrow> A = {}"
  unfolding empty_antichain_def
  apply safe
  apply (subst (asm) antichain.antichain_inject)
    apply auto
  done

lemma antichain_from_list_is_empty:
  "antichain_from_list (xs :: 'sum :: {order, monoid_add} list) = {}\<^sub>A \<longleftrightarrow> filter (\<lambda>x. list_all ((\<le>) x) xs) xs = []"
  unfolding antichain_from_list_def 
  apply (auto simp add: empty_antichain_def)
  apply (subst (asm) antichain_not_empty[unfolded empty_antichain_def])
    apply auto
  apply (rule ccontr)
  apply (cases xs)
  apply (auto split: if_splits)
  apply (smt (verit, best) empty_Collect_eq filter_empty_conv)
  done

lemma set_antichain_antichain_from_list[simp]:
  "set_antichain (antichain_from_list xs) = {x \<in> set xs. list_all ((\<le>) x) xs}"
  unfolding antichain_from_list_def 
  apply simp
    apply (subst antichain_inverse)
   apply auto
  done


lemma zequal_equal:
  "zequal A B \<longleftrightarrow> A = B"
  apply safe
  subgoal
    apply transfer
    apply (auto simp: equiv_zmset_def)
    subgoal for A B A' B'
      apply (simp add: multiset_eq_iff)
      apply (smt (verit, ccfv_threshold) add_diff_cancel_left diff_add_inverse diff_add_inverse2 diff_cancel2 diff_diff_cancel diff_diff_left diff_is_0_eq diff_le_self nat_le_linear ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
      done
    done
  subgoal
    apply transfer
    apply auto
    done
  done


end