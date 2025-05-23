

theory Executable

imports Complex_Main
  "HOL-Library.Linear_Temporal_Logic_on_Streams"
  "HOL-Library.Multiset"
  "HOL-Library.Product_Lexorder"
  "HOL.List"
   Progress_Tracking.Propagate
   Types
begin

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

definition t_loc_linord :: "('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('t \<times> 'loc :: linorder ) \<Rightarrow> ('t \<times> 'loc) \<Rightarrow> bool" where
  "t_loc_linord t_less p1 p2 = (case (p1, p2) of ((t1, l1), (t2, l2)) \<Rightarrow>
    (t_less t1 t2) \<or> (t1 = t2 \<and> l1 \<le> l2))"

lemma linorder_t_loc_linord:
  assumes H1: "class.linorder (\<lambda>t u. less_t t u \<or> t = u) less_t"
  shows "class.linorder (t_loc_linord less_t) (\<lambda>t u. t_loc_linord less_t t u \<and> t \<noteq> u)"
proof -
  from H1 interpret A: linorder "(\<lambda>t u. less_t t u \<or> t = u)" less_t by auto
  show ?thesis 
  apply unfold_locales
  subgoal  by (smt (z3) A.dual_order.asym Pair_inject case_prodE t_loc_linord_def verit_la_disequality)
  subgoal by (simp add: case_prodI2 t_loc_linord_def)
  subgoal by (smt (z3) A.order.strict_trans1 case_prodE order_trans prod.simps(2) t_loc_linord_def)
  subgoal using \<open>\<And>y x. (t_loc_linord less_t x y \<and> x \<noteq> y) = (t_loc_linord less_t x y \<and> \<not> t_loc_linord less_t y x)\<close> by blast
  subgoal by (smt (verit, best) A.antisym_conv3 case_prodI case_prodI2 nle_le t_loc_linord_def)
  done
qed

definition mymin :: "('t \<Rightarrow> 't \<Rightarrow> bool) => ('t \<times> 'loc :: linorder) set \<Rightarrow> ('t \<times> 'loc)"
  where "mymin t_less = linorder.Min (t_loc_linord t_less)"

lemma linorderMin:
  assumes "class.linorder (\<lambda>t u. less_t t u \<or> t = u) less_t"
  shows "mymin less_t (set (x # xs)) = fold (\<lambda>a b. if t_loc_linord less_t a b then a else b) xs x"
proof -
  interpret B: linorder "t_loc_linord less_t" "\<lambda>t u. t_loc_linord less_t t u \<and> t \<noteq> u"
    by (rule linorder_t_loc_linord[OF assms])
  have H2: "B.Min (insert x (set xs)) = fold B.min xs x" by (metis B.Min.set_eq_fold list.simps(15))
  have H3: "B.min = (\<lambda>a b. if t_loc_linord less_t a b then a else b)" using B.min_def by blast
  show ?thesis
    unfolding mymin_def
    by (auto simp: H2 H3)
qed

definition t_loc_pairs :: "('loc :: enum, 't) configuration \<Rightarrow> ('t \<times> 'loc) set" where
  "t_loc_pairs c = (\<Union>x \<in> set enum_class.enum. (Set.image (\<lambda>t. (t, x)) (set_zmset (c_work c x))))"

export_code t_loc_pairs in SML

definition is_empty_antichain :: "('sum::order) antichain \<Rightarrow> bool" where
  "is_empty_antichain A = Set.is_empty (set_antichain A)"

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


declare zmultiset_of_antichain_def[code]

lemma set_zmset_code[code]:
  "set_zmset (abs_zmultiset x) = (case x of (A, B) \<Rightarrow> set_mset (A - B) \<union> set_mset (B - A))"
  unfolding set_zmset_def
  by transfer (auto simp: set_mset_def)

lemma frontier_code[code]:
  "set_antichain (frontier x) = minimal_antichain {t \<in> set_zmset x. 0 < zcount x t}"
  by transfer' (auto intro!: arg_cong[of _ _ minimal_antichain] zcount_inI)

end

type_synonym t = "(nat \<times> nat)"
type_synonym sum = "(nat \<times> nat)"

definition followed_by :: "sum \<Rightarrow> sum \<Rightarrow> sum" where
  "followed_by \<equiv> plus"

definition results_in :: "sum \<Rightarrow> sum \<Rightarrow> sum" where
  "results_in \<equiv> plus"

lemma frontier_empty_zmset: "frontier {#}\<^sub>z = {}\<^sub>A"
  by transfer' (auto simp: minimal_antichain_def)

(* lemma summary_self: "summary (op, p) (op, p) = {}\<^sub>A"
  by (cases op; cases p) (auto simp: summary_def frontier_empty_zmset)
 *)


end