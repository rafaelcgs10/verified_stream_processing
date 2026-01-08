theory Termination

imports Complex_Main
    Progress_Tracking.Propagate
    "HOL-Library.Product_Lexorder"
begin

context dataflow_topology
begin

lemma configuration_iff: "c = c' \<longleftrightarrow> c_work c = c_work c' \<and>
    c_pts c = c_pts c' \<and> c_imp c = c_imp c' \<and> more c = more c'"
  by (cases c; cases c') auto

lemma next_propagate_always_greater_than_vacants:
  assumes  "next_propagate' c1 c2 loc t"
    and "t' < t"
  shows "worklists_vacant_to c1 t'"
  unfolding next_propagate'_def worklists_vacant_to_def
  by (metis assms(1) assms(2) flow.zero_le next_propagate'_def order_le_less_trans results_in_mono(2) results_in_zero)

lemma next_propagate'_worklist_aux: "next_propagate' c0 c1 loc t \<Longrightarrow> c_work c1 = (\<lambda>loc'.
                    if loc' = loc then {#t' \<in>#\<^sub>z c_work c0 loc'. t' \<noteq> t#}
                    else c_work c0 loc'
                           + after_summary
                               (frontier_changes (c_imp c0 loc + {#t' \<in>#\<^sub>z c_work c0 loc. t' = t#}) (c_imp c0 loc))
                               (summary loc loc'))"
  unfolding next_propagate'_def
  apply (simp add: configuration_iff)
  done

lemma next_propagate'_implications_aux: "next_propagate' c0 c1 loc t \<Longrightarrow> c_imp c1 = (c_imp c0)(loc := c_imp c0 loc + {#t' \<in>#\<^sub>z c_work c0 loc. t' = t#})" 
  unfolding next_propagate'_def
  apply (simp add: configuration_iff)
  done

lemma next_propagate'_worklist: "next_propagate' c1 c2 loc t \<Longrightarrow> c_work c2 loc = {#t' \<in>#\<^sub>z c_work c1 loc. t' \<noteq> t#}"
  apply (simp add: next_propagate'_worklist_aux)
  done

lemma next_propagate'_removes_from_loc: "next_propagate' c1 c2 loc t \<Longrightarrow> t \<in>#\<^sub>z c_work c1 loc"
  using next_propagate'_def by blast

lemma next_propagate'_removes_t_from_loc: "next_propagate' c1 c2 loc t \<Longrightarrow> t \<notin>#\<^sub>z c_work c2 loc"
  by (metis (mono_tags, lifting) next_propagate'_worklist count_filter_zmset zcount_ne_zero_iff)

lemma next_propagate'_implications_aux_2: "next_propagate' c1 c2 loc t  \<Longrightarrow> c_imp c2 loc = c_imp c1 loc + {#t' \<in>#\<^sub>z c_work c1 loc. t' = t#}"
  unfolding next_propagate'_def
  apply (simp add: configuration_iff)
  done

lemma frontier_changes_empty_if_eq: "frontier (c_imp c2 loc) = frontier (c_imp c1 loc) \<Longrightarrow> frontier_changes (c_imp c2 loc) (c_imp c1 loc) = {#}\<^sub>z"
  by simp

lemma next_propagate'_consecutives_diff_locations: "next_propagate' c1 c2 loc t \<Longrightarrow> next_propagate' c2 c3 loc' t \<Longrightarrow> loc \<noteq> loc'"
  using next_propagate'_def next_propagate'_removes_t_from_loc by blast

lemma next_propagate'_same_location_diff_configurations: "next_propagate' c1 c2 loc t \<Longrightarrow> next_propagate' c3 c4 loc t \<Longrightarrow> c2 \<noteq> c3"
  using next_propagate'_consecutives_diff_locations by blast

lemma alw_exists_t_in_some_worklist:
  assumes H1: "alw (relates (\<lambda> c1 c2 . \<exists> loc . next_propagate' c1 c2 loc t)) s"
  shows "alw (holds (\<lambda>c1. (\<exists> loc . t \<in>#\<^sub>z c_work c1 loc))) s"
  by (smt (verit, best) H1 alw_mono holds.elims(3) next_propagate'_removes_from_loc relatesD)
  
lemma alw_no_exists_t_in_some_worklist:
  assumes H1: "alw (relates (\<lambda> c1 c2 . \<exists> loc . next_propagate' c1 c2 loc t)) s"
  shows "alw (holds (\<lambda>c1. (\<exists> loc . t \<notin>#\<^sub>z c_work c1 loc))) (stl s)"
  using next_propagate'_removes_t_from_loc relatesD H1
  by (smt (verit, del_insts) alw_cong alw_inv holds.simps)

lemma some_other:
  assumes H1: "alw (relates (\<lambda> c1 c2 . \<exists> loc . next_propagate' c1 c2 loc t)) s"
  shows "\<exists> loc' . ev (relates (\<lambda> c1 c2 . next_propagate' c1 c2 loc' t)) (stl s)"
  by (smt (verit, del_insts) H1 alw_relates ev.simps relates_def)

lemma multiset_always_finite: "next_propagate' c1 c2 loc t \<Longrightarrow> finite (set_zmset (c_work c1 loc)) \<Longrightarrow> finite (set_zmset (c_work c2 loc))"
  by blast

lemma cartesian_product_locations_is_finite: "finite {(loc, loc') . (loc, loc') \<in> ((UNIV :: 'loc set) \<times> (UNIV :: 'loc set))}"
  by simp

lemma alw_next_propagate_at_least_two_locations:
  assumes H1: "alw (relates (\<lambda> c1 c2 . \<exists> loc . next_propagate' c1 c2 loc t)) s"
  shows "\<exists> loc loc' . loc \<noteq> loc' \<and> ev (relates (\<lambda> c1 c2 . next_propagate' c1 c2 loc t)) s \<and> ev (relates (\<lambda> c1 c2 . next_propagate' c1 c2 loc' t)) s"
proof -
  from H1 obtain loc1 where "next_propagate' (shd s) (shd (stl s)) loc1 t" by blast
  from this and H1 obtain loc2 where "next_propagate' (shd (stl s)) (shd (stl (stl s))) loc2 t" by blast
  then have "loc1 \<noteq> loc2" using \<open>next_propagate' (shd s) (shd (stl s)) loc1 t\<close> next_propagate'_same_location_diff_configurations by blast
  then show ?thesis by (meson \<open>next_propagate' (shd (stl s)) (shd (stl (stl s))) loc2 t\<close> \<open>next_propagate' (shd s) (shd (stl s)) loc1 t\<close> ev.base ev.step relates_def)
qed

lemma summary_self_never_empty: "summary loc loc = antichain {}"
  by (simp add: empty_antichain_def summary_self)

lemma dataflow_acyclic_if_remove_non_zero:"path loc loc xs \<Longrightarrow> (\<forall> loc loc'. summary loc loc' = antichain { 0 }) \<Longrightarrow> False"
proof(induction xs rule: path.induct)
  case (path0 l1 l2)
  then show ?case using summary_self_never_empty by (smt (verit, ccfv_threshold) antichain_inverse empty_antichain.rep_eq empty_not_insert finite.intros(1) finite.intros(2) incomparable_minimal_antichain mem_Collect_eq minimal_antichain_singleton summary_self)
next
  case (path l1 l2 xs lbl l3)
  then show ?case by auto
qed

lemma set_antichain_0: "set_antichain (antichain {0}) = {0}"
  by (metis antichain_inverse finite.emptyI finite.insertI incomparable_minimal_antichain mem_Collect_eq minimal_antichain_singleton)

lemma set_antichain_reverse: "t \<in>\<^sub>A (antichain A) \<Longrightarrow> t \<in> set_antichain (antichain A)"
  using set_antichain2 by blast

lemma after_summary_antichain_0: "t \<in>#\<^sub>z A \<Longrightarrow> t \<in>#\<^sub>z after_summary A (antichain {0})"
  unfolding after_summary_def
  apply (simp add: set_antichain_0 results_in_zero)
  done

lemma exists_next_config: 
  "t \<in>#\<^sub>z (c_work c1 loc) \<Longrightarrow> 
   (\<forall>t' loc'. t' \<in>#\<^sub>z c_work c1 loc' \<longrightarrow> \<not> t' < t) \<Longrightarrow> 
   \<exists> c2 . next_propagate' c1 c2 loc t"
  using next_propagate'_def by blast

section\<open>Termination\<close>
subsection\<open>Total work repro\<close>

definition c_work_pos :: "('loc, 't) configuration \<Rightarrow> 'loc \<Rightarrow> 't multiset" where
  "c_work_pos c loc = mset_pos (c_work c loc)"

definition c_work_neg :: "('loc, 't) configuration \<Rightarrow> 'loc \<Rightarrow> 't multiset" where
  "c_work_neg c loc = mset_neg (c_work c loc)"

definition work_repro :: "('loc, 't :: order) configuration \<Rightarrow> 'loc \<Rightarrow> 't \<Rightarrow> bool" where
"work_repro c loc t = (\<forall>i. i \<in>#\<^sub>z c_imp c loc \<longrightarrow> \<not> i \<le> t)"

definition work_n_repro :: "('loc, 't) configuration \<Rightarrow> 't \<Rightarrow> nat" where
"work_n_repro c t = (\<Sum> loc \<in> UNIV . if (work_repro c loc t) then 1 else 0)"

definition nr_work_repro :: "('loc, 't) configuration \<Rightarrow> nat \<Rightarrow> nat" where
"nr_work_repro c n = (\<Sum> loc \<in> UNIV . (\<Sum> work \<in> {work . work \<in># (c_work_pos c loc) \<and> work_n_repro c work \<ge> n} . count (c_work_pos c loc) work))"

lemma fin_nr_work_repro :
 "finite {t. 0 < nr_work_repro c t}"
proof -
  have G : "\<exists>n. \<forall>m>n. nr_work_repro c m = 0"
  proof (intro exI [where x = "card (UNIV :: 'loc set)"] allI impI)
    fix m :: nat
    assume G1: "card (UNIV :: 'loc set) < m"
    let ?Sum = "\<lambda> t. (\<Sum>loc \<in> UNIV. if work_repro c loc t then 1 else 0)"
    show "nr_work_repro c m = 0"
      unfolding nr_work_repro_def work_n_repro_def c_work_pos_def
    proof (subst sum_eq_0_iff ; (subst sum_eq_0_iff) ?)
      show "finite (UNIV::'loc set)"
        by auto
    next
      fix loc' :: 'loc
      show "finite {t. t \<in># mset_pos (c_work c loc') \<and> m \<le> ?Sum t}"
        by auto
    next
      show "\<forall>loc'\<in>UNIV. \<forall>t'\<in>{t. t \<in># mset_pos (c_work c loc') \<and> m \<le> ?Sum t}. count (mset_pos (c_work c loc')) t' = 0"
        unfolding Ball_def
      proof (safe)
        fix loc' :: 'loc
          and t' :: 't
        assume "t' \<in># mset_pos (c_work c loc')"
        assume G2: "m \<le> ?Sum t'"
        have H: "?Sum t' \<le> card (UNIV ::'loc set)"
          by(rule ord_le_eq_trans[where b = "(\<Sum>loc\<in>(UNIV ::'loc set). 1)"])
          (fastforce intro: sum_le_included)+
        from H and G2 and G1 show "count (mset_pos (c_work c loc')) t' = 0"
          by auto
      qed
    qed
  qed
  from G show ?thesis
    by (metis bot_nat_0.not_eq_extremum infinite_nat_iff_unbounded mem_Collect_eq)
qed

lemma fin_nr_work_repro' :
 "finite {x. n < nr_work_repro c x}"
  using fin_nr_work_repro
  by (metis finite_nat_set_iff_bounded less_nat_zero_code mem_Collect_eq neq0_conv)

context includes multiset.lifting begin
lift_definition total_work_repro :: "('loc, 't) configuration \<Rightarrow> nat multiset" is
"nr_work_repro"
  by (rule fin_nr_work_repro)
end

definition diff_order :: "nat multiset \<Rightarrow> nat multiset \<Rightarrow> nat \<Rightarrow> bool" where
  "diff_order M N n = (count M n > count N n \<and> (\<forall> m > n. count M m = count N m))"

definition diff_order' :: "('loc, 't) configuration \<Rightarrow> ('loc, 't) configuration \<Rightarrow> nat \<Rightarrow> bool" where
  "diff_order' c c' n = (nr_work_repro c n > nr_work_repro c' n \<and> (\<forall> m > n. nr_work_repro c m = nr_work_repro c' m))"

(*Helper theorem*)

lemma pos_or_neg: 
  "next_propagate' c c' loc t \<Longrightarrow> t \<in># c_work_neg c loc \<or> t \<in># c_work_pos c loc"
  unfolding next_propagate'_def c_work_pos_def c_work_neg_def
  by auto

lemma count_Abs_work_repro_le:
 "(count (Abs_multiset (nr_work_repro c1)) n < count (Abs_multiset (nr_work_repro c2)) n) = 
  (nr_work_repro c1 n < nr_work_repro c2 n)"
  using total_work_repro.abs_eq total_work_repro.rep_eq by auto

lemma Max_helper:
  "Max S < x \<Longrightarrow> finite S \<Longrightarrow> x \<notin> S"
  using Max_ge leD by auto

lemma Max_less_iff': "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<forall>a\<in>A. a < x) \<Longrightarrow> (Max A < x)"
  using Max_less_iff by auto

lemma Max_less_iff'': "(Max A < x) \<Longrightarrow> finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<forall>a\<in>A. a < x)"
  using Max_less_iff by auto

lemma count_Abs_work_repro:
 "(count (Abs_multiset (nr_work_repro c1)) n = count (Abs_multiset (nr_work_repro c2)) n) = 
  (nr_work_repro c1 n = nr_work_repro c2 n)"
  using total_work_repro.abs_eq total_work_repro.rep_eq by auto

lemma nr_work_repro_eq:
  "(nr_work_repro c1 = nr_work_repro c2) =
  (\<forall> n. nr_work_repro c1 n = nr_work_repro c2 n)"
  by auto

lemma Abs_work_repro:
  "(Abs_multiset (nr_work_repro c1) = Abs_multiset (nr_work_repro c2)) =
  (nr_work_repro c1 = nr_work_repro c2)"
proof (rule Abs_multiset_inject)
  show "nr_work_repro c1 \<in> {f. finite {x. 0 < f x}}"
  by(simp only: mem_Collect_eq, rule fin_nr_work_repro')
next
  show "nr_work_repro c2 \<in> {f. finite {x. 0 < f x}}"
  by(simp only: mem_Collect_eq, rule fin_nr_work_repro')
qed

(*End of helper theorems*)

lemma diff_diff' :
  "diff_order (total_work_repro c) (total_work_repro c') n = diff_order' c c' n"
  by(simp add: diff_order_def total_work_repro_def count_Abs_work_repro count_Abs_work_repro_le diff_order'_def)

lemma diff_order_g:
  assumes H: "\<exists> n. diff_order M N n"
  shows   "M > N"
proof -
  from H obtain n where H': "diff_order M N n" by auto
  show ?thesis
    unfolding less_multiset\<^sub>H\<^sub>O_def less_multiset_less_multiset\<^sub>H\<^sub>O
  proof (safe)
    assume "N = M"
    then show False
      using H'
      unfolding diff_order_def
      by auto
  next
    fix m
    assume "count M m < count N m"
    then show "\<exists>x>m. count N x < count M x"
      using H'
      unfolding diff_order_def
     by (metis nat_neq_iff order_less_imp_not_less)
  qed
qed

lemma diff_order_g_l:
  assumes "diff_order M N n"
    and "diff_order K N m"
    and "n > m"
  shows   "diff_order M K n"
proof -
  from assms show ?thesis
    by(simp add: diff_order_def)
qed

lemma work_n_repro_eq:
 "c_imp c = c_imp c' \<Longrightarrow> work_n_repro c t = work_n_repro c' t"
  by(simp add: work_n_repro_def work_repro_def)

lemma work_repro_to_n:
  assumes H : "\<forall> loc. work_repro c' loc t' \<longrightarrow> work_repro c loc t"
  shows "work_n_repro c t \<ge> work_n_repro c' t'"
  unfolding work_n_repro_def
proof (rule sum_mono)
  fix loc :: 'loc
  from H have "work_repro c' loc t' \<longrightarrow> work_repro c loc t" by auto
  then show "(if work_repro c' loc t' then (1 :: nat) else 0) \<le> (if work_repro c loc t then 1 else 0)"
    by auto
qed

lemma all_eq_sum_eq:
  assumes "\<forall>x. f0 x = f1 x"
  shows "(\<Sum>x\<in>M. f0 x) = (\<Sum>x\<in>M. f1 x)"
  using assms by simp

lemma get_diff_order :
  assumes C1:"c_work_pos c = c_work_pos c'"
    and C2: "\<forall>t. work_n_repro c' t \<le> work_n_repro c t"
    and C3: "\<exists>loc. t \<in># c_work_pos c' loc"
    and C4: "work_n_repro c' t < work_n_repro c t"
  shows "\<exists>m\<ge>work_n_repro c t. diff_order (total_work_repro c) (total_work_repro c') m"
proof -
  let ?M = "{n. \<exists> t. n \<le> work_n_repro c t \<and> work_n_repro c' t < work_n_repro c t \<and> (\<exists>loc. t \<in># c_work_pos c' loc)}"
  have "\<forall> t. finite {n. \<exists> t. n \<le> work_n_repro c t}"
    unfolding work_n_repro_def
    apply(rule allI)
    subgoal for t
      apply(rule finite_subset[where B = "{n. \<exists> t. n \<le> card (UNIV ::'loc set)}"])
      subgoal
        unfolding Collect_mono_iff HOL.simp_thms(36)
        apply(rule allI)
        apply(rule impI)
        apply(erule exE)
        subgoal for n t
          apply(rule order_trans; assumption?)
          apply(rule ord_le_eq_trans[where b = "(\<Sum>loc\<in>(UNIV ::'loc set). 1)"])
           apply(rule sum_le_included)
          by auto
        done
      subgoal
        by simp
      done
    done
  then have fin : "finite ?M"
    apply -
    apply(rule finite_subset; assumption?)
    by auto
  show ?thesis
  proof (rule exI [where x = "Max ?M"] , rule conjI)
    show "work_n_repro c t \<le> Max ?M"
    proof (rule Max_ge)
      show "finite ?M"
        by(rule fin)
    next
      from assms show "work_n_repro c t \<in> ?M"
        by auto
    qed
  next
    let ?N = "\<lambda> loc c''. {t. t \<in># c_work_pos c' loc \<and> Max ?M \<le> work_n_repro c'' t}"
    let ?Sum = "\<lambda> loc c''. sum (count (c_work_pos c' loc)) (?N loc c'')"
    show "diff_order (total_work_repro c) (total_work_repro c') (Max ?M)"
      unfolding diff_diff' diff_order'_def
    proof (rule conjI)
      show "nr_work_repro c' (Max ?M) < nr_work_repro c (Max ?M)"
        unfolding nr_work_repro_def C1
      proof (rule sum_strict_mono_ex1)
        show "finite (UNIV :: 'loc set)"
          by simp
      next
        show "\<forall>loc\<in>UNIV. ?Sum loc c' \<le> ?Sum loc c"
          using C2 C4
          apply -
          apply(simp only: Ball_def UNIV_I verit_implies_simplify)
          apply(rule allI)
          apply(rule sum_mono2; simp?)
          apply(simp only: subset_iff mem_Collect_eq)
          apply(rule allI)
          subgoal for loc t'
            apply(rule impI)
            apply(erule_tac x = t' in allE)
            by auto
          done
      next
        from fin and C1 and C3 and C4 have "\<forall> m. (m = Max ?M) =
          (m \<in> ?M \<and> (\<forall>a\<in>?M. a \<le> m))"
          apply -
          apply(rule allI)
          apply (rule eq_Max_iff)
          by auto
        then have in_set: "\<exists> m. (m \<in> ?M \<and> (\<forall>a\<in>?M. a \<le> m))"
          apply -
          apply(rule exI[where x = "Max ?M"])
          apply(erule allE[where x = "Max ?M"])
          by auto
        then obtain m t' loc where in_set_1: "\<forall>x. (\<exists>t. x \<le> work_n_repro c t \<and> work_n_repro c' t < work_n_repro c t \<and> (\<exists>loc. t \<in># c_work_pos c' loc)) \<longrightarrow> x \<le> m" and
          in_set_2: "m \<le> work_n_repro c t'" and in_set_3: "work_n_repro c' t' < work_n_repro c t'" and in_set_4: "t' \<in># c_work_pos c' loc"
          using C1
          by auto
        show "\<exists>loc\<in>UNIV. ?Sum loc c' < ?Sum loc c"
          unfolding Bex_def
        proof (rule exI [where x = loc] , safe)
          show "loc \<in> UNIV"
            by simp
        next
          show "?Sum loc c' < ?Sum loc c"
          proof(rule sum_strict_mono2 [where b = t'])
            show "finite {work. work \<in># c_work_pos c' loc \<and> Max ?M \<le> work_n_repro c work}"
              by auto
          next
            show "?N loc c' \<subseteq> ?N loc c"
              using C2
              apply(simp only: subset_iff)
              apply(rule allI)
              subgoal for t'
                apply(rule impI)
                apply(erule_tac x = t' in allE)
                by auto
              done
          next
            show "t' \<in> ?N loc c - ?N loc c'"
              unfolding Ball_def mem_Collect_eq Diff_iff simp_thms (22)
            proof safe
              show "t' \<in># c_work_pos c' loc"
                using in_set_4
                by auto
            next
              show "Max ?M \<le> work_n_repro c t'"
              proof (rule eq_refl , rule Max_eqI)
                show "finite ?M"
                  by(rule fin)
              next
                fix n :: nat
                assume G: "n \<in> ?M"
                show "n \<le> work_n_repro c t'"
                  using in_set_1 in_set_2 G
                  apply -
                  apply(simp only: mem_Collect_eq)
                  apply(erule_tac x = n in allE)
                  apply(erule impE; assumption?)
                  apply(rule order_trans; assumption)
                  done
              next
                show "work_n_repro c t' \<in> ?M"
                  using in_set_3 in_set_4
                  by auto
              qed
            next
              assume G1: "t' \<in># c_work_pos c' loc"
                and G2: "Max ?M \<le> work_n_repro c' t'"
              have G3: "Max ?M = work_n_repro c t'"
              proof (rule Max_eqI)
                show "finite ?M"
                  by(rule fin)
              next
                fix m :: nat
                assume G: "m \<in> ?M"
                show "m \<le> work_n_repro c t'"
                  using C2 in_set_1 in_set_2 G
                  unfolding mem_Collect_eq
                  apply -
                  apply(erule allE[where x = m])
                  apply(erule impE; assumption?)
                  apply(rule order_trans; assumption)
                  done
              next
                show "work_n_repro c t' \<in> ?M"
                  using in_set_3 in_set_4 
                  by auto
              qed
              have G4: "work_n_repro c t' > work_n_repro c' t'"
                by (simp add: in_set_3)
              show "False"
                using G2 G3 G4
                by auto
            qed
          next
            show "0 < count (c_work_pos c' loc) t'"
              using in_set_4
              by simp
          next
            fix t'' :: 't
            show "0 \<le> count (c_work_pos c' loc) t''"
              by simp
          qed
        qed
      qed
    next
      show "\<forall>m>Max ?M. nr_work_repro c m = nr_work_repro c' m"
        unfolding nr_work_repro_def C1
      proof (safe , rule all_eq_sum_eq , rule allI)
        fix m :: nat
          and loc :: 'loc
        assume G: "Max {n. \<exists>t. n \<le> work_n_repro c t \<and> work_n_repro c' t < work_n_repro c t \<and> (\<exists>loc. t \<in># c_work_pos c' loc)} < m"
        show "sum (count (c_work_pos c' loc)) {work. work \<in># c_work_pos c' loc \<and> m \<le> work_n_repro c work} = sum (count (c_work_pos c' loc)) {work. work \<in># c_work_pos c' loc \<and> m \<le> work_n_repro c' work}"
        proof (rule sum.mono_neutral_right)
          show "finite {work. work \<in># c_work_pos c' loc \<and> m \<le> work_n_repro c work}"
            by auto
        next
          show "{work. work \<in># c_work_pos c' loc \<and> m \<le> work_n_repro c' work} \<subseteq> {work. work \<in># c_work_pos c' loc \<and> m \<le> work_n_repro c work}"
            using assms dual_order.trans
            by blast
        next
          show "\<forall>i\<in>{work. work \<in># c_work_pos c' loc \<and> m \<le> work_n_repro c work} - {work. work \<in># c_work_pos c' loc \<and> m \<le> work_n_repro c' work}. count (c_work_pos c' loc) i = 0"
            using assms G fin Max_helper
            apply -
            apply(simp only: Ball_def mem_Collect_eq Diff_iff)
            apply(rule allI)
            apply(rule impI)
            apply(erule conjE)+
            apply(drule Max_helper; simp?)
            done
        qed
      qed
    qed
  qed
qed

lemma elems_eq_sum_eq: "(\<And>x. x\<in>M \<longrightarrow> f x = g x) \<Longrightarrow> (\<Sum>x\<in>M. f x) = (\<Sum>x\<in>M. g x)"
  by simp

lemma total_work_repro_from_work_n_repro:
  assumes W: "c_work_pos c = c_work_pos c'" 
  and "(\<forall> t. work_n_repro c t \<ge> work_n_repro c' t)"
shows  "total_work_repro c \<ge> total_work_repro c'"
proof -
  from assms have Disj_aux : "(\<forall> t. (\<exists>loc. t \<in># c_work_pos c loc) \<longrightarrow> work_n_repro c t = work_n_repro c' t) \<or> 
  (\<exists> t. (\<exists>loc. t \<in># c_work_pos c loc \<and> work_n_repro c' t < work_n_repro c t))"
    by (metis le_neq_implies_less)
  from Disj_aux have Disj: "(\<forall> t. (\<exists>loc. t \<in># c_work_pos c loc) \<longrightarrow> work_n_repro c t = work_n_repro c' t) \<or> (\<exists> t.\<exists> n \<ge>work_n_repro c t.  diff_order (total_work_repro c) (total_work_repro c') n)"
  proof
    assume Disj_aux1 : "\<forall>t. (\<exists>loc. t \<in># c_work_pos c loc) \<longrightarrow> work_n_repro c t = work_n_repro c' t"
    from Disj_aux1 show "(\<forall>t. (\<exists>loc. t \<in># c_work_pos c loc) \<longrightarrow> work_n_repro c t = work_n_repro c' t) \<or> (\<exists>t n. work_n_repro c t \<le> n \<and> diff_order (total_work_repro c) (total_work_repro c') n)"
      by auto
  next
    assume Disj_aux2: "\<exists>t loc. t \<in># c_work_pos c loc \<and> work_n_repro c' t < work_n_repro c t"
    from Disj_aux2 obtain t loc where Disj_aux2_1 : "t \<in># c_work_pos c loc" and Disj_aux2_2 : "work_n_repro c' t < work_n_repro c t" by auto
    from assms and Disj_aux2_1 and Disj_aux2_2 show "(\<forall>t. (\<exists>loc. t \<in># c_work_pos c loc) \<longrightarrow> work_n_repro c t = work_n_repro c' t) \<or> (\<exists>t n. work_n_repro c t \<le> n \<and> diff_order (total_work_repro c) (total_work_repro c') n)"
      apply -
      apply(rule disjI2)
      apply(rule exI[where x = t])
      apply(rule get_diff_order)
      by auto
  qed
  from Disj show ?thesis
  proof
    assume Disj1: "\<forall>t. (\<exists>loc. t \<in># c_work_pos c loc) \<longrightarrow> work_n_repro c t = work_n_repro c' t"
    show "total_work_repro c' \<le> total_work_repro c"
    proof (rule eq_refl)
      from Disj1 and W show "total_work_repro c' = total_work_repro c"
        unfolding total_work_repro_def map_fun_def
        apply(simp only:  Abs_work_repro nr_work_repro_eq nr_work_repro_def o_id o_apply mem_Collect_eq)
        apply(rule allI)
        apply(rule elems_eq_sum_eq)
        apply(rule impI)
        apply(rule Groups_Big.comm_monoid_add_class.sum.mono_neutral_right; simp?)
        by auto
    qed
  next
    assume Disj2: "\<exists>t n. work_n_repro c t \<le> n \<and> diff_order (total_work_repro c) (total_work_repro c') n"
    from Disj2 obtain t :: 't and  n :: nat where Disj2_2 : "diff_order (total_work_repro c) (total_work_repro c') n" by auto
    show "total_work_repro c' \<le> total_work_repro c"
    proof (rule less_imp_le , rule diff_order_g , rule exI [where x = n])
      from Disj2_2 show "diff_order (total_work_repro c) (total_work_repro c') n"
        by auto
    qed
  qed
qed

lemma total_work_repro_from_nr_work_repro:
  "\<forall> n. nr_work_repro c1 n \<ge> nr_work_repro c2 n \<Longrightarrow>
  total_work_repro c1 \<ge> total_work_repro c2"
  unfolding le_less less_multiset_less_multiset\<^sub>H\<^sub>O disj_imp less_multiset\<^sub>H\<^sub>O_def total_work_repro_def
      map_fun_def o_def id_apply not_not de_Morgan_conj not_imp not_all not_ex
  apply safe
  subgoal for n
    apply(erule allE[where x = n])
    by(simp add: count_Abs_work_repro_le Abs_work_repro not_less)
  done

definition lesser_imps where
  "lesser_imps c1 c2 = (\<forall> loc t'. zcount ((c_imp c2) loc) t' \<ge> zcount ((c_imp c1) loc) t')"

definition greater_workers_pos where
  "greater_workers_pos c1 c2 = (\<forall> loc t'. count (c_work_pos c1 loc) t' \<ge> count (c_work_pos c2 loc) t')"

lemma greater_workers_pos_eq : 
  "greater_workers_pos c c' \<Longrightarrow> c_work_pos c = c_work_pos d \<Longrightarrow> c_work_pos c' = c_work_pos d' \<Longrightarrow> greater_workers_pos d d'"
  by (simp add: greater_workers_pos_def)

lemma greater_imp:
  "next_propagate' c c' loc t \<Longrightarrow> t \<in># c_work_pos c loc \<Longrightarrow> lesser_imps c c'"
  by (simp add: next_propagate'_def lesser_imps_def c_work_pos_def set_mset_def)

lemma lesser_imps_termination_aux:
  assumes H1: "lesser_imps c c'"
    and H2: "inv_implications_nonneg c"
  shows "work_repro c' loc t \<longrightarrow> work_repro c loc t"
  unfolding work_repro_def
proof ((rule allI | rule impI)+)
  fix t' :: 't
  assume G1: "\<forall>t'. t' \<in>#\<^sub>z c_imp c' loc \<longrightarrow> \<not> t' \<le> t"
    and G2: "t' \<in>#\<^sub>z c_imp c loc"
  from H1 have H1': "zcount (c_imp c loc) t' \<le> zcount (c_imp c' loc) t'" 
    unfolding lesser_imps_def by auto
  from H2 have H2': "0 \<le> zcount (c_imp c loc) t'" 
    unfolding inv_implications_nonneg_def by auto
  from G1 have G1': "t' \<in>#\<^sub>z c_imp c' loc \<longrightarrow> \<not> t' \<le> t" 
    by auto
  show "\<not> t' \<le> t"
    using H1' H2' G1' G2 zcount_ne_zero_iff[symmetric] impE
    unfolding lesser_imps_def inv_implications_nonneg_def
    by (metis order_antisym_conv)
qed

lemma lesser_imps_termination:
  assumes H1: "c_work_pos c = c_work_pos c'"
    and H2: "lesser_imps c c'"
    and H3: "inv_implications_nonneg c"
  shows "total_work_repro c \<ge> total_work_repro c'"
proof (rule total_work_repro_from_work_n_repro)
  show "c_work_pos c = c_work_pos c'"
    using H1 by assumption
next
  from H2 and H3 show "\<forall>t. work_n_repro c' t \<le> work_n_repro c t"
    using lesser_imps_termination_aux work_repro_to_n by auto
qed

(*When workers gets removed our count gets lower*)
lemma greater_works_termination_1:
  assumes H1: "greater_workers_pos c c'" 
    and H2: "c_work_pos c \<noteq> c_work_pos c'"
    and H3: "c_imp c = c_imp c'"
  shows "total_work_repro c \<ge> total_work_repro c'"
proof (rule total_work_repro_from_nr_work_repro , rule allI)
  fix n :: nat
  show "nr_work_repro c' n \<le> nr_work_repro c n"
    unfolding nr_work_repro_def
  proof (rule sum_mono)
    fix loc :: 'loc
    let ?M = "\<lambda> c. {work. work \<in># c_work_pos c loc \<and> n \<le> work_n_repro c work}"
    show "sum (count (c_work_pos c' loc)) (?M c') \<le> sum (count (c_work_pos c loc)) (?M c)"
    proof (rule sum_le_included [where i = id] ; safe ?)
      show "finite (?M c')"
        by auto
    next
      show "finite (?M c)"
        by auto
    next
      fix t :: 't
      assume G1: "t \<in># c_work_pos c' loc"
        and G2: "n \<le> work_n_repro c' t"
      from assms have H: "work_n_repro c' t = work_n_repro c t"
        using work_n_repro_eq by metis
      show "\<exists>t'\<in>(?M c). id t' = t \<and> count (c_work_pos c' loc) t \<le> count (c_work_pos c loc) t'"
        unfolding Bex_def
      proof (rule exI [where x = t] , safe)
        show "t \<in># c_work_pos c loc"
          using G1 H1
          by (metis count_eq_zero_iff count_greater_zero_iff greater_workers_pos_def linorder_not_less)
      next
        show "n \<le> work_n_repro c t"
          using G2 H
          by simp
      next
        show "id t = t"
          by simp
      next
        show "count (c_work_pos c' loc) t \<le> count (c_work_pos c loc) t"
          using H1
          by (simp add: greater_workers_pos_def)
      qed
    qed
  qed
qed

lemma c_worklist_eq:
  "\<forall> t. c_work_pos c t = c_work_pos c' t \<Longrightarrow> c_work_pos c = c_work_pos c'"
  by blast

lemma c_worklist_eq_rev:
  "nr_work_repro c = nr_work_repro c' \<Longrightarrow> \<forall> t. nr_work_repro c t = nr_work_repro c' t"
  by auto

lemma c_worklist_eq_count:
  "\<forall> loc t. count (c_work_pos c loc) t = count (c_work_pos c' loc) t \<Longrightarrow> c_work_pos c = c_work_pos c'"
  by (meson multiset_eqI c_worklist_eq)

lemma sum_eq_elem:
    assumes A2 : "sum (f :: 'a \<Rightarrow> nat) A = sum g B"
  and "finite B"
    and A3 : "\<forall> n. f n \<le> g n"
    and "A \<subseteq> B"
  shows "\<forall> n \<in> B. f n = g n"
proof -
  from A3 have H : "sum f A \<le> sum g A"
    using sum_mono
    by metis
  from assms have H1 : "sum g A \<le> sum g B"
    using sum_mono2
    by blast
  from H and H1 and A2 have H2 : "sum f A = sum g A"
    by (metis verit_la_disequality)
  from assms and H2 show ?thesis
    by (metis leD less_eq_nat.simps(1) nless_le sum_mono2 sum_strict_mono_strong)
qed

lemma greater_works_termination_2_aux:
  assumes H1: "greater_workers_pos c c'"
    and H2: "total_work_repro c = total_work_repro c'"
    and H3: "c_imp c = c_imp c'"
  shows "c_work_pos c = c_work_pos c'"
proof (rule c_worklist_eq_count , safe)
  fix loc :: 'loc
    and t :: 't
  from H2 have H2': "nr_work_repro c' 0 = nr_work_repro c 0" 
    using c_worklist_eq_rev 
    by (auto simp add: total_work_repro_def Abs_work_repro)
  let ?Sum = "\<lambda> loc c. sum (count (c_work_pos c loc)) (set_mset (c_work_pos c loc))"
  have H2'': "?Sum loc c' = ?Sum loc c"
    proof (rule sum_mono_inv [where I = "UNIV :: 'loc set"])
      show "(\<Sum>loc\<in>UNIV. ?Sum loc c') = (\<Sum>loc\<in>UNIV. ?Sum loc c)"
        using H2'
        unfolding nr_work_repro_def
        by auto
    next
      fix loc :: 'loc
      assume "loc \<in> (UNIV :: 'loc set)"
      show "?Sum loc c' \<le> ?Sum loc c"
        unfolding greater_workers_pos_def c_work_pos_def
      proof (rule sum_le_included [where i = id])
        show "finite (set_mset (mset_pos (c_work c' loc)))"
          by auto
      next
        show "finite (set_mset (mset_pos (c_work c loc)))"
          by auto
      next
        show "\<forall>t\<in>#mset_pos (c_work c loc). 0 \<le> count (mset_pos (c_work c loc)) t"
          by auto
      next
        from H1 show "\<forall>t\<in>#mset_pos (c_work c' loc). \<exists>t'\<in>#mset_pos (c_work c loc). id t' = t \<and> count (mset_pos (c_work c' loc)) t \<le> count (mset_pos (c_work c loc)) t'"
          unfolding greater_workers_pos_def c_work_pos_def
          by (meson count_greater_eq_Suc_zero_iff dual_order.trans id_apply)
      qed
    next
      show "loc \<in> UNIV"
        by auto
    next
      show "finite (UNIV :: 'loc set)"
        by auto
  qed
  have H2''' : "\<forall>t\<in>(set_mset (c_work_pos c loc)). (count (c_work_pos c' loc)) t = (count (c_work_pos c loc)) t"
    proof (rule sum_eq_elem[where A = "(set_mset (c_work_pos c' loc))"])
      show "?Sum loc c' = ?Sum loc c"
        using H2'' by auto
    next
      show "finite (set_mset (c_work_pos c loc))"
        by auto
    next
      show "\<forall>t. count (c_work_pos c' loc) t \<le> count (c_work_pos c loc) t"
        using H1 unfolding greater_workers_pos_def
        by auto
    next
      show "(set_mset (c_work_pos c' loc)) \<subseteq> set_mset (c_work_pos c loc)"
        using H1 unfolding greater_workers_pos_def
        by (simp add: mset_subset_eqI set_mset_mono)
  qed
  show "count (c_work_pos c loc) t = count (c_work_pos c' loc) t"
    using H1 H2''' H3
    unfolding greater_workers_pos_def
    by (metis count_gt_imp_in_mset order_le_imp_less_or_eq)
qed

lemma greater_works_termination_2:
  assumes H1: "greater_workers_pos c c'"
    and H2: "c_work_pos c \<noteq> c_work_pos c'"
    and H3: "c_imp c = c_imp c'"
  shows "total_work_repro c \<noteq> total_work_repro c'"
proof -
  show ?thesis
  using greater_works_termination_2_aux assms
  by auto
qed

lemma greater_works_termination:
assumes "greater_workers_pos c c'"
    and "c_work_pos c \<noteq> c_work_pos c'"
  and "c_imp c = c_imp c'"
  shows "total_work_repro c > total_work_repro c'"
proof -
  from assms have H : "total_work_repro c \<ge> total_work_repro c'"
    by (rule greater_works_termination_1)
  from assms have H1 : "total_work_repro c \<noteq> total_work_repro c'"
    by (rule greater_works_termination_2)
  from H1 and H show ?thesis
    by auto
qed

(*Children will have a lower count*)
lemma lower_reproduction':
  assumes "c_imp c = c_imp c'"
    and "t \<le> t'"
  shows "work_n_repro c t \<ge> work_n_repro c' t'"
proof -
  show ?thesis
  proof (rule work_repro_to_n)
    show "\<forall>loc. work_repro c' loc t' \<longrightarrow> work_repro c loc t"
      unfolding work_repro_def
    proof safe
      fix loc :: 'loc
      fix t'' :: 't
      assume G1: "\<forall>t. t \<in>#\<^sub>z c_imp c' loc \<longrightarrow> \<not> t \<le> t'"
        and G2: "t'' \<in>#\<^sub>z c_imp c loc"
        and "t'' \<le> t"
      then show False
        by (metis assms(1,2) order.trans)
    qed
  qed
qed

abbreviation same_frontier :: "'t zmultiset \<Rightarrow> 't zmultiset \<Rightarrow> bool" where
  "same_frontier M N \<equiv> zmset_frontier M = zmset_frontier N"

(*same frontier part*)

lemma term_no_frontier_change:
  "next_propagate' c c' loc t \<Longrightarrow>
   same_frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) (c_imp c loc) \<Longrightarrow>
   greater_workers_pos c c'"
  by(simp add: next_propagate'_def greater_workers_pos_def c_work_pos_def)

lemma term_no_frontier_change_eq:
  assumes H1: "next_propagate' c c' loc t"
    and H2: "t \<in># c_work_pos c loc"
  shows "c_work_pos c \<noteq> c_work_pos c'"
proof (rule notI)
  assume H3: "c_work_pos c = c_work_pos c'"
  from H3 have H3': "count (c_work_pos c loc) t = count (c_work_pos c' loc) t" 
    by auto
  show "False"
    using assms and H3'
    unfolding c_work_pos_def next_propagate'_def
    by(simp add: c_work_pos_def set_mset_def)
qed

lemma no_frontier_change_termination:
  assumes C1: "next_propagate' c c' loc t"
    and C2 : "t \<in># c_work_pos c loc" 
    and C3: "inv_implications_nonneg  c"
    and C4: "same_frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) (c_imp c loc)"
shows "total_work_repro c > total_work_repro c'"
proof (rule order.strict_trans2 [where b = "total_work_repro 
    \<lparr>c_work = c_work c, c_pts = c_pts c, c_imp = c_imp c'\<rparr>"])
  let ?c1 = "\<lparr>c_work = c_work c, c_pts = c_pts c, c_imp = c_imp c'\<rparr>"
  show "total_work_repro c' < total_work_repro ?c1"
  proof (rule greater_works_termination)
    have "greater_workers_pos c c'"
      using term_no_frontier_change assms
      by auto
    then show "greater_workers_pos ?c1 c'"
        using c_worklist_eq greater_workers_pos_eq [where c = c and c' = c']
        unfolding c_work_pos_def
        by auto
  next
    from C1 and C2 have "c_work_pos c \<noteq> c_work_pos c'"
      using term_no_frontier_change_eq
      by auto
    then show "c_work_pos ?c1 \<noteq> c_work_pos c'"
      using c_worklist_eq fun_cong
      unfolding c_work_pos_def
      by auto
  next
    show "c_imp ?c1 = c_imp c'"
      by auto
  qed
next
  let ?c1 = "\<lparr>c_work = c_work c, c_pts = c_pts c, c_imp = c_imp c'\<rparr>"
  show "total_work_repro ?c1 \<le> total_work_repro c"
  proof (rule lesser_imps_termination)
    show "c_work_pos c = c_work_pos ?c1"
      using c_worklist_eq
      by(auto simp add: c_work_pos_def)
  next
    show "lesser_imps c ?c1"
      using assms greater_imp
      by (auto simp add: lesser_imps_def)
  next
    show "inv_implications_nonneg c"
      using C3 by auto
  qed
qed

(*frontier change case*)
lemma in_zmset_sum :
 "a \<in>#\<^sub>z (M + N) \<Longrightarrow> a \<in>#\<^sub>z M \<or> a \<in>#\<^sub>z N"
  by (smt (z3) zcount_ne_zero_iff zcount_union)

lemma result_in_geq:
"results_in t s \<ge> t"
  by (metis flow.zero_le results_in_mono(2) results_in_zero)

lemma after_summary_order:
  assumes "t' \<in>#\<^sub>z after_summary M (summary loc loc')"
  shows "\<exists> t \<le> t'. t  \<in>#\<^sub>z M"
proof (rule sum.not_neutral_contains_not_neutral [where A = "set_antichain (summary loc loc')" and g = "\<lambda> s. (zcount {#results_in t s. t \<in>#\<^sub>z M#} t')"])
  show "(\<Sum>s\<in>set_antichain (summary loc loc'). zcount {#results_in t s. t \<in>#\<^sub>z M#} t') \<noteq> 0"
    using assms 
    by(simp only: after_summary_def set_zmset_def mem_Collect_eq zcount_sum not_False_eq_True)
next
  fix a :: 'sum
  assume "a \<in> set_antichain (summary loc loc')"
    and "zcount {#results_in t a. t \<in>#\<^sub>z M#} t' \<noteq> 0"
  then show "\<exists>t\<le>t'. t \<in>#\<^sub>z M"
    unfolding zcount_ne_zero_iff
    by (metis image_zmset_pre result_in_geq)
qed

lemma frontier_change_order_aux:
"ta \<in>\<^sub>A antichain (minimal_antichain {ta.
       0 < zcount (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) ta}) = 
(ta \<in> (minimal_antichain {ta.
      0 < zcount (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) ta}))"
proof (rule in_antichain_minimal_antichain)
  show "finite {ta. 0 < zcount (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) ta}"
    using finite_Int disjI2
    by (auto simp add: Collect_imp_eq Collect_conj_eq Collect_neg_eq[symmetric])
qed

lemma frontier_change_order_aux':
"ta \<in>\<^sub>A antichain (minimal_antichain {t. 0 < zcount (c_imp c loc) t}) = 
(ta \<in> (minimal_antichain {t. 0 < zcount (c_imp c loc) t}))"
proof (rule in_antichain_minimal_antichain)
  show "finite {t. 0 < zcount (c_imp c loc) t}"
    by (simp add: Collect_conj_eq)
qed

lemma frontier_change_order:
  assumes C1: "t' \<in>#\<^sub>z frontier_changes (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) (c_imp c loc)"
    and C2: "inv_implications_nonneg c"
  shows "t' \<ge> (t :: 't :: order)"
proof -
  have H1: "\<forall> t t' t''. \<not> t \<le> (t' :: 't) \<longrightarrow>  t'' < t' \<longrightarrow> t'' \<noteq> t"
    by auto
  consider "t = t'" | "t \<noteq> t'" by auto
  have C1': "\<not> t \<le> t' \<longrightarrow> zcount (frontier_changes (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#})
     (c_imp c loc)) t' = 0"
  proof (safe , rule not_mem_frontier_diff)
    assume not_leq: "\<not> t \<le> t'"
    have not_eq : "t \<noteq> t'"
      using not_leq
      by auto
    show "t' \<notin>\<^sub>A frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) - frontier (c_imp c loc)"
      unfolding ac_Diff_iff
    proof (safe, erule notE)
      assume G: "t' \<in>\<^sub>A frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#})"
      have G1: "0 < zcount (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) t'"
        using G member_frontier_pos_zmset by blast    
      have G2: "\<forall>t''. 0 < zcount (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) t'' \<longrightarrow> \<not> t'' < t'"
        using G in_frontier_least by blast
      show "t' \<in>\<^sub>A frontier (c_imp c loc)"
        unfolding frontier_def map_fun_def comp_def id_def frontier_change_order_aux frontier_change_order_aux'
        unfolding minimal_antichain_def frontier_def mem_Collect_eq
      proof (safe)
        show "0 < zcount (c_imp c loc) t'"
          using G1 not_eq
          by auto
      next
        fix t'' :: 't
        assume "t'' < t'"
          and "0 < zcount (c_imp c loc) t''"
        then show False
          using G2 not_leq H1
          apply -
          apply(erule allE[where x = t''])
          apply(erule allE[where x = t])
          apply(erule allE[where x = t'])
          apply(erule allE[where x = t''])
          by force
      qed
    qed
  next
    assume not_leq: "\<not> t \<le> t'"
    have not_eq : "t \<noteq> t'"
      using not_leq
      by auto
    show "t' \<notin>\<^sub>A frontier (c_imp c loc) - frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#})"
      unfolding ac_Diff_iff
    proof (safe , erule notE)
      assume G: "t' \<in>\<^sub>A frontier (c_imp c loc)"
      have G1: "0 < zcount (c_imp c loc) t'"
        using G member_frontier_pos_zmset by blast    
      have G2: "\<forall>t''. 0 < zcount (c_imp c loc) t'' \<longrightarrow> \<not> t'' < t'"
        using G in_frontier_least by blast
      show "t' \<in>\<^sub>A frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#})"
        unfolding frontier_def map_fun_def comp_def id_def frontier_change_order_aux frontier_change_order_aux'
        unfolding minimal_antichain_def frontier_def mem_Collect_eq inv_implications_nonneg_def
      proof (safe)
        show "0 < zcount (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) t'"
          using G1 not_eq
          by auto
      next
        fix t'' :: 't
        assume "t'' < t'"
          and "0 < zcount (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) t''"
        then show False
          using G2 H1 not_leq
          apply -
          apply(erule allE[where x = t''])
          apply(erule allE[where x = t])
          apply(erule allE[where x = t'])
          apply(erule allE[where x = t''])
          by fastforce
      qed
    qed
  qed
  show ?thesis
    using C1 C1'
    unfolding set_zmset_def mem_Collect_eq
    by auto
qed

lemma new_workers_are_greater:
  assumes H1: "next_propagate' c c' loc t"
    and H2: "inv_implications_nonneg c"
    and H3: "zcount (c_work c' loc') t' \<noteq>  zcount (c_work c loc') t'"
  shows "t' \<ge> t"
proof -
  consider "t = t'" | "t \<noteq> t'" by auto
  then show ?thesis
  proof(cases, goal_cases eq_t not_eq_t)
  next
    case eq_t
    then show ?case
      by auto
  next
    case not_eq_t
    consider "loc = loc'" | "loc \<noteq> loc'" by auto
    then show ?case
    proof(cases, goal_cases eq_loc not_eq_loc)
      case eq_loc
      have "c_work c' loc' = {#t' \<in>#\<^sub>z c_work c loc'. t' \<noteq> t#}"
        using H1 next_propagate'_def eq_loc
        by fastforce
      then show ?case 
        using H3 not_eq_t
        by fastforce
    next
      case not_eq_loc
      have "t' \<in>#\<^sub>z after_summary
              (frontier_changes (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#})
                (c_imp c loc)) (summary loc loc')"
        using H3 H1 not_eq_t not_eq_loc
        unfolding next_propagate'_def
        by fastforce
      then obtain t'' where H3_1: "t'' \<le> t'" and H3_2: "t'' \<in>#\<^sub>z frontier_changes
           (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) (c_imp c loc)"
        using H3 after_summary_order
        by blast
      have H3_2': "t \<le> t''"
        using H3_2 frontier_change_order H2
        by metis
      show ?case
        using H3_2' H3_1
        by auto
    qed
  qed
qed

lemma nr_repro_gets_smaller_1:
  assumes H1: "next_propagate' c c' loc t"
    and H2: "\<not> same_frontier (c_imp c loc) (c_imp c' loc)"
    and H3: "t \<in># c_work_pos c loc"
    and H4: "inv_implications_nonneg c"
  shows "work_repro c loc t"
proof -
  have H2': "frontier (c_imp c loc) \<noteq>
         frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#})"
    using H1 H2
    unfolding  next_propagate'_def
    by(simp add: set_antichain_inject inv_implications_nonneg_def)
  have G: "\<not> work_repro c loc t \<longrightarrow> frontier (c_imp c loc) = frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#})"
  proof (rule impI)
    assume G1: "\<not> work_repro c loc t"
    show "frontier (c_imp c loc) = frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#})"
    proof (rule frontier_eqI)
      show "\<forall>b. 0 \<le> zcount (c_imp c loc) b"
        using H4
        unfolding inv_implications_nonneg_def
        by auto
    next
      show "\<forall>b. 0 \<le> zcount (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) b"
        using H3 H4
        unfolding c_work_pos_def set_mset_def zcount_union inv_implications_nonneg_def
        by simp
    next
      show "c_imp c loc \<subseteq>#\<^sub>z c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}"
        using H3 H4
        unfolding c_work_pos_def set_mset_def inv_implications_nonneg_def subseteq_zmset_def
        by simp
    next
      fix t' :: 't
      assume G2: "t' \<in>#\<^sub>z c_imp c loc + {#t'' \<in>#\<^sub>z c_work c loc. t'' = t#}"
      obtain t'' :: 't where G1_1: "t'' \<in>#\<^sub>z c_imp c loc" and G1_2: "t'' \<le> t"
        using G1
        unfolding work_repro_def
        by auto
      consider "t' = t" | "t' \<noteq> t"
        by auto
      then show "\<exists>t''. t'' \<in>#\<^sub>z c_imp c loc \<and> t'' \<le> t'"
      proof (cases, goal_cases eq not_eq)
        case eq
        then show ?case 
          using G1_1 G1_2
          by auto
      next
        case not_eq
        then show ?case 
          using G2
          unfolding work_repro_def
          apply -
          apply(rule exI[where x = t'])
          by (metis (mono_tags, lifting) count_filter_zmset in_zmset_sum order_refl zcount_ne_zero_iff)
      qed
    qed
  qed
  show ?thesis
    using H2' G
    by auto
qed

lemma nr_repro_gets_smaller_2:
  assumes H1: "next_propagate' c c' loc t"
    and H2: "t \<in># c_work_pos c loc"
    and H3: "inv_implications_nonneg c"
  shows "\<not> work_repro c' loc t"
proof(rule notI)
  assume "work_repro c' loc t"
  then have "\<not> t \<in>#\<^sub>z c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}"
    using H1
    unfolding work_repro_def next_propagate'_def
    by auto
  then have G1: "zcount (c_imp c loc) t + zcount {#t' \<in>#\<^sub>z c_work c loc. t' = t#} t = 0"
    unfolding set_zmset_def mem_Collect_eq
    by auto
  have G2: "zcount (c_imp c loc) t \<ge> 0"
    using H3
    unfolding inv_implications_nonneg_def
    by auto
  have G3: "zcount {#t' \<in>#\<^sub>z c_work c loc. t' = t#} t > 0"
    using H2
    unfolding c_work_pos_def set_mset_def
    by auto
  then show False
    using G1 G2 G3
    by auto
qed

lemma (in ordered_cancel_comm_monoid_add) sum_gt_sum_same_area_if:
  assumes "finite A" "a \<in> A" "f a < g a"  "\<And>x. x \<in> A - {a} \<Longrightarrow> f x \<le> g x"
  shows "sum f A < sum g A"
proof -
  have "sum f A = f a + sum f (A-{a})"
    by (simp add: assms sum.remove)
  also have "\<dots> \<le> f a + sum g (A-{a})"
    using assms by (meson DiffD1 add_left_mono sum_mono)
  also have "\<dots> < g a + sum g (A-{a})"
    using assms add_less_le_mono by blast
  also have "\<dots> = sum g A"
    using assms by (intro sum.remove [symmetric])
  finally show ?thesis .
qed


lemma nr_repro_gets_smaller:
  assumes "next_propagate' c c' loc t"
    and "\<not> same_frontier (c_imp c loc) (c_imp c' loc)"
    and "t \<in># c_work_pos c loc"
    and "inv_implications_nonneg c"
  shows "work_n_repro c t > work_n_repro c' t"
proof -
  show ?thesis
    unfolding work_n_repro_def
  proof (rule sum_gt_sum_same_area_if [where a = loc])
    show "finite (UNIV :: 'loc set)"
      by auto
  next
    show "loc \<in> UNIV"
      by auto
  next
    show "(if work_repro c' loc t then (1 :: nat) else 0) < (if work_repro c loc t then 1 else 0)"
      using assms
      by(simp add: nr_repro_gets_smaller_1 nr_repro_gets_smaller_2)
  next
    fix loc' :: 'loc
    assume "loc' \<in> UNIV - {loc}"
    from assms have "lesser_imps c c'"
      using greater_imp
      by auto
    then have H1: "\<forall>loc t. work_repro c' loc t \<longrightarrow> work_repro c loc t"
      using lesser_imps_termination_aux assms
      by auto
    then show "(if work_repro c' loc' t then (1 :: nat) else 0) \<le> (if work_repro c loc' t then 1 else 0)"
      by auto
  qed
qed

(*We will prove this by seeing that by first changing the implications then our count will decline in order
 work_n_repro c t, but then when we change the workers all will only have order \<le> work_n_repro c' t < work_n_repro c t
and therefor the count will fall*)


lemma diff_frontier_change_termination_1:
  assumes H1: "next_propagate' c c' loc t"
  and H2 : "t \<in># c_work_pos c loc" 
  and H3: "inv_implications_nonneg c"
  and H4: "\<not> same_frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) (c_imp c loc)"
shows "\<exists> m \<ge> work_n_repro c t. diff_order (total_work_repro c) (total_work_repro (| c_work = c_work c, c_pts = c_pts c, c_imp = c_imp c'|)) m"
proof -
  let ?c1 = "(| c_work = c_work c, c_pts = c_pts c, c_imp = c_imp c'|)"
  from assms have Imps : "lesser_imps c c'"
    using H1 H2 greater_imp
    by auto
  have C1 : "\<forall> t. work_n_repro c t \<ge> work_n_repro ?c1 t"
  proof (rule allI , rule work_repro_to_n)
    fix t :: 't
    show "\<forall>loc. work_repro ?c1 loc t \<longrightarrow> work_repro c loc t"
      using H3 Imps lesser_imps_termination_aux
      by (metis select_convs(3) work_repro_def)
  qed
  have "work_n_repro c t > work_n_repro c' t"
    using H1 H2 H3 H4
    apply -
    apply(rule nr_repro_gets_smaller[where loc = "loc"]; assumption?)
    using next_propagate'_implications_aux_2 by presburger
  then have C2 : "work_n_repro c t > work_n_repro ?c1 t"
    apply -
    apply(rule ord_eq_less_trans[where b = "work_n_repro c' t"])
    subgoal
      apply(rule work_n_repro_eq)
      apply simp
      done
    apply assumption
    done
  from assms have C3: "\<exists> loc. t \<in>#\<^sub>z (c_work c loc)"
    unfolding next_propagate'_def
    by auto
  from H2 and C1 and C2 and C3 show ?thesis
    apply -
    apply(rule get_diff_order)
    unfolding c_work_pos_def
    by auto
qed


lemma sum_gt_sum_same_area:
  fixes f g :: "'i \<Rightarrow> nat"
  assumes "sum f A < sum g A"
   and "finite A"
shows "\<exists>a\<in>A. f a < g a"
proof-
  from assms show ?thesis
    apply -
    apply(rule classical)
    apply(rule FalseE)
    apply(simp only: not_le[symmetric])
    apply(erule notE)
    apply(rule sum_mono)
    by auto
qed

lemma sum_gt_sum:
  fixes f g :: "'i \<Rightarrow> nat"
  assumes "sum f A < sum g B"
   and "finite A"
   and "finite B"
shows "\<exists>b\<in>B. f b < g b \<or> b \<notin> A"
proof-
  from assms show ?thesis
    apply -
    apply(rule classical)
    apply(rule FalseE)
    apply(simp only: not_le[symmetric])
    apply(erule notE)
    apply(rule sum_le_included)
    by auto
qed

lemma diff_frontier_change_termination_2:
  assumes H1: "next_propagate' c c' loc (t :: 't :: order)"
  and H2: "t \<in># c_work_pos c loc" 
  and H3: "inv_implications_nonneg c"
  and H4: "\<not> same_frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) (c_imp c loc)"
  and H5: "total_work_repro c' > total_work_repro (| c_work = c_work c, c_pts = c_pts c, c_imp = c_imp c'|)"
shows "(\<exists> m < work_n_repro c t. diff_order (total_work_repro c') (total_work_repro (| c_work = c_work c, c_pts = c_pts c, c_imp = c_imp c'|)) m)"
proof -
  let ?c1 = "\<lparr>c_work = c_work c, c_pts = c_pts c, c_imp = c_imp c'\<rparr>"
  have D1 : "{n. nr_work_repro ?c1 n < nr_work_repro c' n} \<noteq> {}"
    using H5
    by (metis (no_types, lifting) empty_iff lt_imp_ex_count_lt mem_Collect_eq total_work_repro.rep_eq)
  have "finite {n. 0 < nr_work_repro c' n -  nr_work_repro ?c1 n}"
    using fin_nr_work_repro
    using diff_preserves_multiset by blast
  then have D2 : "finite {n. nr_work_repro ?c1 n < nr_work_repro c' n}"
    by auto
  show ?thesis
  proof (rule exI [where x = "Max {n. nr_work_repro c' n > nr_work_repro ?c1 n}"] , rule conjI)
    show "Max {n. nr_work_repro \<lparr>c_work = c_work c, c_pts = c_pts c, c_imp = c_imp c'\<rparr> n < nr_work_repro c' n} < work_n_repro c t"
    proof (rule Max_less_iff')
      show "finite {n. nr_work_repro ?c1 n < nr_work_repro c' n}"
        using D2
        by auto
    next
      show "{n. nr_work_repro ?c1 n < nr_work_repro c' n} \<noteq> {}"
        using D1
        by auto
    next
      show "\<forall>a\<in>{n. nr_work_repro ?c1 n < nr_work_repro c' n}. a < work_n_repro c t"
        unfolding Ball_def mem_Collect_eq
      proof safe
        fix n :: nat
        assume "nr_work_repro ?c1 n < nr_work_repro c' n"
        then have "\<exists>a. (\<Sum>x\<in>{work. work \<in># mset_pos (c_work c a) \<and> n \<le> work_n_repro ?c1 work}. nat (zcount (c_work c a) x)) < 
          (\<Sum>x\<in>{work. work \<in># mset_pos (c_work c' a) \<and> n \<le> work_n_repro c' work}. nat (zcount (c_work c' a) x))"
          unfolding nr_work_repro_def c_work_pos_def
          apply -
          apply(drule sum_gt_sum_same_area)
          by auto
        then obtain loc' :: 'loc where "(\<Sum>x\<in>{work. work \<in># mset_pos (c_work c loc') \<and> n \<le> work_n_repro ?c1 work}. nat (zcount (c_work c loc') x)) < 
          (\<Sum>x\<in>{work. work \<in># mset_pos (c_work c' loc') \<and> n \<le> work_n_repro c' work}. nat (zcount (c_work c' loc') x))"
          by auto
        then have "\<exists>t'\<in>{work. work \<in># mset_pos (c_work c' loc') \<and> n \<le> work_n_repro c' work}.
         nat (zcount (c_work c loc') t') < nat (zcount (c_work c' loc') t') \<or>
         t' \<notin> {t''. t'' \<in># mset_pos (c_work c loc') \<and> n \<le> work_n_repro ?c1 t''}"
          apply -
          apply(rule sum_gt_sum)
          by auto
        then obtain t' :: 't where G1: "t' \<in># mset_pos (c_work c' loc')" and G2: "n \<le> work_n_repro c' t'" and
         G3: "nat (zcount (c_work c loc') t') < nat (zcount (c_work c' loc') t') \<or>
         t' \<notin> {t''. t'' \<in># mset_pos (c_work c loc') \<and> n \<le> work_n_repro ?c1 t''}"
          by auto
        consider "zcount (c_work c loc') t' < zcount (c_work c' loc') t'" |
          "\<not> zcount (c_work c loc') t' < zcount (c_work c' loc') t'"
          by auto
        then show "n < work_n_repro c t"
        proof cases
          case 1
          have "t \<le> t'"
            using 1 new_workers_are_greater
            by (metis H1 assms(3) verit_comp_simplify1(1))
          then have C: "work_n_repro c' t' \<le> work_n_repro c' t"
            using lower_reproduction'
            by auto
          have "work_n_repro c' t < work_n_repro c t"
            using assms
            apply -
            apply(rule nr_repro_gets_smaller[where loc = loc])
            unfolding next_propagate'_def
            by auto
          then have "work_n_repro c' t' < work_n_repro c t"
            using C dual_order.strict_trans2
            by blast
          then show ?thesis 
            using G2
            by simp
        next
          case 2
          have G3': "t' \<notin> {t''. t'' \<in># mset_pos (c_work c loc') \<and> n \<le> work_n_repro ?c1 t''}"
            using G3 2
            by auto
          show ?thesis
            using G1 G2 G3' 2
            apply(simp only: imp_conv_disj work_n_repro_def work_repro_def select_convs(3) set_mset_def mem_Collect_eq)
            by auto
        qed
      qed
    qed
  next
    show "diff_order (total_work_repro c') (total_work_repro ?c1) (Max {n. nr_work_repro ?c1 n < nr_work_repro c' n})"
      unfolding diff_diff' diff_order'_def
    proof (safe)
      show "nr_work_repro ?c1 (Max {n. nr_work_repro ?c1 n < nr_work_repro c' n}) < 
            nr_work_repro c' (Max {n. nr_work_repro ?c1 n < nr_work_repro c' n})"
        using D1 D2 Max_in by blast
    next
      fix m :: nat
      assume "Max {n. nr_work_repro ?c1 n < nr_work_repro c' n} < m"
      then have "\<forall>a. nr_work_repro ?c1 a < nr_work_repro c' a \<longrightarrow> a < m"
        using Max_less_iff'' D1 D2 H5
        by auto
      then show "nr_work_repro c' m = nr_work_repro ?c1 m"
        using H5
        unfolding total_work_repro_def map_fun_def o_id o_def id_apply
        by (metis antisym_conv3 less_multiset\<^sub>H\<^sub>O order.asym total_work_repro.abs_eq total_work_repro.rep_eq)
    qed
  qed
qed


lemma diff_frontier_change_termination:
  assumes "next_propagate' c c' loc t"
  and "t \<in># c_work_pos c loc" and "inv_implications_nonneg c"
  and "\<not> same_frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) (c_imp c loc)"
shows "total_work_repro c > total_work_repro c'"
proof -
  let ?c1 = "\<lparr>c_work = c_work c, c_pts = c_pts c, c_imp = c_imp c'\<rparr>"
  from assms have H1: "\<exists> m \<ge> work_n_repro c t. diff_order (total_work_repro c) (total_work_repro ?c1) m"
    by(rule diff_frontier_change_termination_1)
  from H1 have H1': "\<exists> m. diff_order (total_work_repro c) (total_work_repro ?c1) m"
    by auto
  consider "\<not> total_work_repro c' > total_work_repro ?c1" |
  "(\<exists> m < work_n_repro c t. diff_order (total_work_repro c') (total_work_repro ?c1) m)"
    using assms diff_frontier_change_termination_2[where loc = loc]
    by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using H1' diff_order_g
      by fastforce
  next
    case 2
    obtain m where H2_1 : "m < work_n_repro c t" and H2_2: "diff_order (total_work_repro c') (total_work_repro ?c1) m"
      using 2 by auto
    obtain n where H1_1: "work_n_repro c t \<le> n" and H1_2: "diff_order (total_work_repro c) (total_work_repro ?c1) n"
      using H1 by auto
    show ?thesis
      using H1_1 H1_2 H2_1 H2_2
      apply -
      apply(rule diff_order_g)
      apply(rule exI[where x = n])
      apply(rule diff_order_g_l[where m = m and N = "(total_work_repro ?c1)"]; assumption?)
      by auto
  qed
qed

lemma terminating_total_work_repro:
  assumes "next_propagate' c c' loc t" 
  and "t \<in># c_work_pos c loc" and "inv_implications_nonneg c"
shows "total_work_repro c > total_work_repro c'"
proof -
  consider "\<not> same_frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) (c_imp c loc)" |
    "same_frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) (c_imp c loc)" by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using assms diff_frontier_change_termination
      by auto
  next
    case 2
    then show ?thesis
      using assms no_frontier_change_termination
      by auto
  qed
qed

subsection\<open>Measure\<close>

definition zero_successors where
"zero_successors t loc  = {loc'. (\<exists> s . s \<in>\<^sub>A summary loc loc' \<and> results_in t s = t)}"

context 
  fixes t :: "'t"
begin 

function weight where
"weight loc = (1 :: nat) + (\<Sum> loc' \<in> zero_successors t loc . weight loc')"
  by auto
termination
  apply(relation "{(loc', loc) . \<exists> s . s \<in>\<^sub>A summary loc loc' \<and> results_in t s = t}")
  subgoal
    apply(rule Wellfounded.finite_acyclic_wf)
     apply simp
    unfolding acyclic_def
    apply safe
    subgoal premises self_loop for loc
    proof -
      have "(loc', loc) \<in> {(loc', loc). \<exists>s. s \<in>\<^sub>A summary loc loc' \<and> results_in t s = t}\<^sup>+ \<Longrightarrow>
        \<exists>xs. path loc loc' xs \<and> xs \<noteq> [] \<and> results_in t (sum_weights (map (\<lambda>(s, l, t). l) xs)) = t" for loc'
        apply (induct loc' rule: converse_trancl_induct)
        apply auto []
         apply (auto simp only: results_in_sum_path_weights_append elim: path)
        done
      from this[OF self_loop] show False using no_zero_cycle[OF _ _ refl, of loc _ t]
        by force
    qed
    done
  apply(auto simp add: zero_successors_def)
  done

end

definition active_work :: "('loc, 't) configuration \<Rightarrow> 't set" where
  "active_work c = {t. \<exists> loc. t \<in>#\<^sub>z c_work c loc \<and> (\<forall>t' loc'. t' \<in>#\<^sub>z c_work c loc' \<longrightarrow> \<not> t' < t)}"

definition measure :: "('loc, 't) configuration \<Rightarrow> 't \<Rightarrow>  nat" where
"measure c t = (\<Sum> loc \<in> {loc . t \<in># c_work_neg c loc} . weight t loc)"

lemma propagate_eq_or_zero_succesor':
  assumes C1: "next_propagate' c c' loc t"
    and   C2: "inv_implications_nonneg c"
    and  C3: "zcount (c_work c loc') t \<noteq> zcount (c_work c' loc') t" 
shows "loc' \<in> {loc'. loc' \<in> zero_successors t loc \<or> loc' = loc}"
proof (cases "loc = loc'")
  case True
  then show ?thesis
    by auto
next
  case False
  have "t \<in>#\<^sub>z (\<Sum>s\<in>set_antichain (summary loc loc').
               {#results_in t s
               . t \<in>#\<^sub>z frontier_changes
                       (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#})
                       (c_imp c loc)#})"
    using assms False
    unfolding next_propagate'_def after_summary_def
    by auto
  then obtain s where C3': "t \<in>#\<^sub>z {#results_in t s
            . t \<in>#\<^sub>z frontier_changes
                       (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#})
                       (c_imp c loc)#}" and C3'' : "s \<in>\<^sub>A summary loc loc'"
    using C1 C2 False
    unfolding next_propagate'_def after_summary_def
    apply(simp only: after_summary_def set_zmset_def mem_Collect_eq zcount_sum not_False_eq_True)
    apply(erule sum.not_neutral_contains_not_neutral)
    apply auto
    done
  obtain t' where C4: "t' \<in>#\<^sub>z frontier_changes
                  (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#})
                  (c_imp c loc)" and C5: "results_in t' s = t"
    using C3'
    apply -
    apply(drule image_zmset_pre)
    by auto
  have G1: "t \<le> t'"
    using C1 C2 C4
    apply -
    apply(rule frontier_change_order; assumption)
    done
  have G2: "t' \<le> t"
    using C5 result_in_geq
    by auto
  have G: "t' = t"
    using G1 G2
    by auto
  show ?thesis
    using False
    unfolding next_propagate'_def zero_successors_def
    apply simp
      apply(rule exI[where x = s])
      apply(rule conjI)
    subgoal
      using C3''
      by auto
    using C5 G
    by auto
qed

lemma propagate_eq_or_zero_succesor:
  assumes C1: "next_propagate' c c' loc t"
    and   C2: "inv_implications_nonneg c"
    and  C3: "count (c_work_neg c loc') t \<noteq> count (c_work_neg c' loc') t" 
  shows "loc' \<in> {loc'. loc' \<in> zero_successors t loc \<or> loc' = loc}"
proof-
  show ?thesis
    using assms
    unfolding c_work_neg_def count_mset_neg
    apply -
    apply(rule propagate_eq_or_zero_succesor'; assumption?)
    apply auto
    done
qed    

lemma sum_weight_aux: "sum (weight t) {loc'. \<exists>s . s \<in>\<^sub>A (summary loc loc') \<and> results_in t s = t} < weight t loc"
  apply(simp only: weight.simps)
  unfolding zero_successors_def
  by linarith

lemma sum_singleton : "sum f {t} = f t"
  by simp

lemma measure_prop_le:
  assumes C1: "next_propagate' c c' loc t"
   and   C2: "inv_implications_nonneg c"
  and C3: "t \<in># c_work_neg c loc"
 shows "measure c' t < measure c t"
proof -
  have "{loc. t \<in># c_work_neg c loc} \<supseteq> ({loc. t \<in># c_work_neg c loc} - {loc'. loc' \<in> zero_successors t loc \<or> loc' = loc}) \<union> {loc}"
    using assms
    unfolding next_propagate'_def c_work_neg_def set_mset_def
    by auto
  then have G1: "sum (weight t) (({loc. t \<in># c_work_neg c loc} - {loc'. loc' \<in> zero_successors t loc \<or> loc' = loc}) \<union> {loc}) \<le> sum (weight t) {loc. t \<in># c_work_neg c loc}"
    apply -
    apply(rule sum_mono2)
    subgoal
      by auto
    subgoal
      using C1 C2 C3
      by simp
    subgoal loc'
      by(rule le0)
    done
  have "{loc. t \<in># c_work_neg c' loc} \<subseteq> ({loc. t \<in># c_work_neg c loc} - {loc'. loc' \<in> zero_successors t loc \<or> loc' = loc}) \<union> {loc'. loc' \<in> zero_successors t loc}"
      using assms
      apply -
      apply(simp add: subset_eq)
      apply(safe)
      subgoal for loc'
        using propagate_eq_or_zero_succesor[where loc' = loc'] C3
        by (metis (mono_tags, lifting) count_eq_zero_iff mem_Collect_eq)
      subgoal for loc'
        unfolding next_propagate'_def c_work_neg_def
        apply(simp add: set_mset_def)
        done
      done
  then have G2:  "sum (weight t) {loc. t \<in># c_work_neg c' loc} \<le> sum (weight t) (({loc. t \<in># c_work_neg c loc} - {loc'. loc' \<in> zero_successors t loc \<or> loc' = loc}) \<union> {loc'. loc' \<in> zero_successors t loc})"
    apply -
    apply(rule sum_mono2)
    subgoal
      by auto
    subgoal
      using C1 C2 C3
      by simp
    subgoal
      by(rule le0)
    done
  have H1: "sum (weight t) (({loc. t \<in># c_work_neg c loc} - {loc'. loc' \<in> zero_successors t loc \<or> loc' = loc}) \<union> {loc'. loc' \<in> zero_successors t loc}) =
      sum (weight t) ({loc. t \<in># c_work_neg c loc} - {loc'. loc' \<in> zero_successors t loc \<or> loc' = loc}) + sum (weight t) {loc'. loc' \<in> zero_successors t loc}"
    apply(subst sum.union_inter_neutral)
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      apply safe
      done
    subgoal
      apply(rule refl)
      done
    done
  have H2: "sum (weight t) (({loc. t \<in># c_work_neg c loc} - {loc'. loc' \<in> zero_successors t loc \<or> loc' = loc}) \<union> {loc}) =
      sum (weight t) ({loc. t \<in># c_work_neg c loc} - {loc'. loc' \<in> zero_successors t loc \<or> loc' = loc}) + sum (weight t) {loc}"
    apply(subst sum.union_inter_neutral)
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      apply safe
      done
    subgoal
      apply(rule refl)
      done
    done
  have  "sum (weight t) {loc'. loc' \<in> zero_successors t loc}
    < sum (weight t) {loc}"
    by (metis Collect_mem_eq sum_weight_aux sum_singleton zero_successors_def)
  then have G: "sum (weight t) (({loc. t \<in># c_work_neg c loc} - {loc'. loc' \<in> zero_successors t loc \<or> loc' = loc}) \<union> {loc'. loc' \<in> zero_successors t loc}) < 
    sum (weight t) (({loc. t \<in># c_work_neg c loc} - {loc'. loc' \<in> zero_successors t loc \<or> loc' = loc}) \<union> {loc})"
    apply(simp only: H1 H2 add_less_cancel_left)
    done
  show ?thesis
    unfolding measure_def
    using G1 G2 G
    by linarith
qed

lemma prop_geq_0_after_summary:
  assumes C1: "0 < zcount (c_work c loc) t"
    and C2: "inv_implications_nonneg c"
  shows "zcount (after_summary
            (frontier_changes (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) (c_imp c loc))
            (summary loc loc')) t \<ge> 0"
proof -
  from assms have H'': "\<forall> t'. t' \<in>#\<^sub>z frontier_changes
                          (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#})
                          (c_imp c loc) \<longrightarrow> t \<le> t'"
    using frontier_change_order 
    by auto
  from assms have H: "t \<notin>\<^sub>A frontier (c_imp c loc) - frontier (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#})"
    unfolding inv_implications_nonneg_def member_antichain_def map_fun_def comp_def
    unfolding id_apply member_antichain_def Antichain.minus_antichain.rep_eq Antichain.frontier.rep_eq
    unfolding Diff_iff minimal_antichain_def mem_Collect_eq
    unfolding  de_Morgan_conj not_not de_Morgan_disj disj_imp
    by simp
  let ?fc = "frontier_changes (c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#}) (c_imp c loc)"
  show ?thesis
    unfolding after_summary_def zcount_sum
  proof (rule sum_nonneg [of "set_antichain (summary loc loc')" "\<lambda> s. zcount {#results_in t s. t \<in>#\<^sub>z ?fc#} t"])
    fix s :: 'sum
    assume "s \<in> set_antichain (summary loc loc')"
    have "\<forall> x t'. t' \<in> (\<lambda>t. results_in t x) -` {t}  \<longrightarrow> t' \<le> t"
      using result_in_geq
      by auto
    then have "\<forall> x. (\<lambda>t. results_in t x) -` {t} \<inter> set_zmset ?fc \<subseteq> {t}"
      using H''
      by (smt (verit) Int_iff antisym insert_iff subsetI)
    then consider "(\<lambda>t. results_in t s) -` {t} \<inter> set_zmset ?fc = {}" | "(\<lambda>t. results_in t s) -` {t} \<inter> set_zmset ?fc = {t}"
      by (meson subset_singletonD)
    then show "0 \<le> zcount {#results_in t s . t \<in>#\<^sub>z ?fc#} t"
    proof cases
      case 1
      then show ?thesis 
        apply(simp only: zcount_image_zmset)
        by auto
    next
      case 2
      then show ?thesis
        using assms H''
        apply(simp only: zcount_image_zmset sum_le_singleton sum_singleton)
        using H not_mem_frontier_diff mem_frontier_diff
        by (smt (verit))
    qed
  qed
qed

lemma prop_worklist_inc_diff_loc: 
  "next_propagate' c c' loc t \<Longrightarrow> loc \<noteq> loc' \<Longrightarrow> zcount (c_work c loc) t > 0 \<Longrightarrow> inv_implications_nonneg c \<Longrightarrow>
zcount (c_work c loc') t \<le> zcount (c_work c' loc') t"
  unfolding next_propagate'_def
  using prop_geq_0_after_summary by auto


lemma measure_prop_leq:
  assumes C1: "next_propagate' c c' loc t"
 and   C2: "inv_implications_nonneg c"
 and    C3: "t' \<in> active_work c"
shows "measure c' t' \<le> measure c t'"
proof -
  consider "t' \<noteq> t" | "t' = t" by auto
  then show ?thesis
  proof (cases, goal_cases not_eq eq)
  next
    case not_eq
    show ?case
      unfolding measure_def measure_def
    proof (rule sum_mono2)
      show "finite {loc. t' \<in># c_work_neg c loc}"
        by auto
    next
      from C1 and C3 and not_eq have "\<not> t \<le> t'"
        unfolding active_work_def next_propagate'_def
        by auto
      then show "{loc. t' \<in># c_work_neg c' loc} \<subseteq> {loc. t' \<in># c_work_neg c loc}"
          unfolding c_work_neg_def set_mset_def
          apply(simp only: Collect_mono_iff configuration.simps(1) count_mset_neg zero_less_nat_eq neg_0_less_iff_less mem_Collect_eq)
          using assms not_eq new_workers_are_greater
          by metis
    next
      fix b :: 'loc
      show "0 \<le> weight t' b"
        by blast
    qed
  next
    case eq
    consider "t \<in># c_work_neg c loc" | "t \<in># c_work_pos c loc"
      using pos_or_neg C1 by auto
    then show ?case
    proof (cases, goal_cases neg pos)
      case neg
      then show ?case
        using assms eq measure_prop_le
        by (simp add: order_less_imp_le)
    next
      case pos
      show ?case
        unfolding measure_def measure_def
      proof (rule sum_mono2)
        show "finite {loc. t' \<in># c_work_neg c loc}"
          by auto
      next
        show "{loc. t' \<in># c_work_neg c' loc} \<subseteq> {loc. t' \<in># c_work_neg c loc}"
          using assms eq pos
          apply(simp only: Collect_mono_iff)
          apply(rule allI)
          apply(rule impI)
          apply(simp only: c_work_neg_def c_work_pos_def configuration.simps(1)
              set_mset_def mem_Collect_eq count_mset_pos zero_less_nat_eq in_filter_zmset_in_zmset zcount_ne_zero_iff[symmetric] count_filter_zmset
              count_mset_neg)
          using prop_worklist_inc_diff_loc
          by (smt (verit) C1 add_strict_increasing2 dataflow_topology.next_propagate'_removes_t_from_loc dataflow_topology.prop_worklist_inc_diff_loc dataflow_topology_axioms zcount_inI)
      next
        fix loc' :: 'loc
        assume "loc' \<in> {loc. t' \<in># c_work_neg c loc} - {loc. t' \<in># c_work_neg c' loc}"
        show "0 \<le> weight t' loc'"
          by blast
      qed
    qed
  qed
qed

subsection\<open>Future fuel\<close>

definition future_fuel :: "('loc, 't) configuration \<Rightarrow>  nat" where
"future_fuel c = (\<Sum> loc \<in> UNIV. (\<Sum> imps \<in> {imps . imps \<in>#\<^sub>z (c_imp c loc) \<and> (\<exists> t \<in> active_work c. t < imps)} . nat (zcount (c_imp c loc) imps)))"

lemma f_f_leq_aux_1:  
 "next_propagate' c c' loc t  \<Longrightarrow> inv_implications_nonneg c \<Longrightarrow>
  x \<notin> active_work c \<Longrightarrow>
 zcount (c_imp c loc') x = zcount (c_imp c' loc') x"
  by (auto simp add: next_propagate'_def active_work_def)

lemma new_workers_are_greater_1:
  assumes "t' \<in>#\<^sub>z c_work c' loc'"
    and "t' \<notin>#\<^sub>z c_work c loc'"
    and "next_propagate' c c' loc t"
    and "inv_implications_nonneg c"
  shows "t' \<ge> t"
proof -
  from assms show ?thesis
    using new_workers_are_greater
    by (metis zcount_ne_zero_iff)
qed

lemma new_workers_are_greater_2:
  assumes "t' \<in>#\<^sub>z c_work c loc'"
    and "t' \<notin>#\<^sub>z c_work c' loc'"
    and "next_propagate' c c' loc t"
    and "inv_implications_nonneg c"
  shows "t' \<ge> t"
proof -
  from assms show ?thesis
    using new_workers_are_greater
    by (metis zcount_ne_zero_iff)
qed

lemma prop_no_lower:
  assumes "t' \<in>#\<^sub>z c_work c loc'"
    and "next_propagate' c c' loc t"
    and "inv_implications_nonneg c"
  shows "\<not> t' < t"
proof -
  from assms show ?thesis
    using next_propagate'_def
    by auto
qed

lemma active_prop :
  assumes C1: "next_propagate' c c' loc t"
    and C2: "t'\<in>active_work c'"
    and C3: "inv_implications_nonneg c"
  shows "\<exists>t''\<in>active_work c. t'' \<le> t'"
proof -
  consider "t'\<in>active_work c" | "t'\<notin>active_work c" by auto
  then show ?thesis
  proof (cases, goal_cases in_active_work not_in_active_work )
    case in_active_work
    then show ?case
      by auto
    next
      case not_in_active_work
      have G1: "t \<in> active_work c" using C1
        using active_work_def next_propagate'_def
        by auto
      from C2 obtain loc where C2_1 : "t' \<in>#\<^sub>z c_work c' loc" and C2_2 :
          "\<forall>t'a. (\<exists>loc'. t'a \<in>#\<^sub>z c_work c' loc') \<longrightarrow> \<not> t'a < t'" unfolding active_work_def by auto
      consider "(t' \<notin>#\<^sub>z c_work c loc)" | "(\<exists>t'a. (\<exists>loc'. t'a \<in>#\<^sub>z c_work c loc') \<and> t'a < t')"
        using not_in_active_work unfolding active_work_def by auto
      then have G2: "t \<le> t'"
      proof (cases)
        case 1
        then show ?thesis
          using C2_1 new_workers_are_greater_1 C1 C3 by auto
      next
        case 2
        from 2 obtain t'' loc' where C4_1: "t'' \<in>#\<^sub>z c_work c loc'" and C4_2: "t'' < t'" by auto
        have C2_2' : "t'' \<notin>#\<^sub>z c_work c' loc'" using C2_2 and C4_2 by auto
        have G: "t \<le> t''" using C4_1 C2_2' C1 C3
          by(rule new_workers_are_greater_2)
        show ?thesis using C4_2 and G
          by auto
      qed
      then show ?case using G1 and G2 by auto
    qed
  qed

lemma active_prop' :
  assumes "\<exists>t\<in>active_work c'. t < x"
and "next_propagate' c c' loc t"
    and "inv_implications_nonneg c"
shows "\<exists>t\<in>active_work c. t < x"
proof -
  from assms show ?thesis
    unfolding Bex_def
    using active_prop order.strict_trans1  by blast
qed

lemma not_active :
"\<exists>t\<in>active_work c. t < x \<Longrightarrow> x \<notin> active_work c"
  by (auto simp add: active_work_def)

lemma c_implicate_eq_prop: 
  "next_propagate' c c' loc t \<Longrightarrow> t' \<noteq> t \<Longrightarrow> zcount (c_imp c loc') t' = zcount (c_imp c' loc') t'"
  by (auto simp add: next_propagate'_def)

lemma prop_active: 
  "next_propagate' c c' loc t \<Longrightarrow> t \<in> active_work c"
  by (auto simp only: next_propagate'_def active_work_def)

lemma f_f_aux:
  assumes C1: "next_propagate' c c' loc t"
    and C2: "inv_implications_nonneg c"
  shows "(\<Sum>imps | imps \<in>#\<^sub>z c_imp c' loc' \<and> (\<exists>t\<in>active_work c'. t < imps).
          nat (zcount (c_imp c' loc') imps))
       \<le> (\<Sum>imps | imps \<in>#\<^sub>z c_imp c loc' \<and> (\<exists>t\<in>active_work c. t < imps).
             nat (zcount (c_imp c loc') imps))"
proof (rule sum_le_included [where i = id])
  show "finite {imps. imps \<in>#\<^sub>z c_imp c' loc' \<and> (\<exists>t\<in>active_work c'. t < imps)}"
    by auto
next
  show "finite {imps. imps \<in>#\<^sub>z c_imp c loc' \<and> (\<exists>t\<in>active_work c. t < imps)}"
    by auto
next
  show "\<forall>y\<in>{imps. imps \<in>#\<^sub>z c_imp c loc' \<and> (\<exists>t\<in>active_work c. t < imps)}.
       0 \<le> nat (zcount (c_imp c loc') y)"
    unfolding Ball_def mem_Collect_eq
    by (safe)
next
  show "\<forall>x\<in>{imps. imps \<in>#\<^sub>z c_imp c' loc' \<and> (\<exists>t\<in>active_work c'. t < imps)}.
       \<exists>y\<in>{imps. imps \<in>#\<^sub>z c_imp c loc' \<and> (\<exists>t\<in>active_work c. t < imps)}.
          id y = x \<and> nat (zcount (c_imp c' loc') x) \<le> nat (zcount (c_imp c loc') y)"
    unfolding Ball_def mem_Collect_eq
  proof (safe)
    fix t' :: 't
      and t'' :: 't
    assume H1: "t' \<in>#\<^sub>z c_imp c' loc'"
      and H2: "t'' \<in> active_work c'"
      and H3: "t'' < t'"
    obtain t''' where H2_1: "t'''\<in>active_work c" and H2_2: "t''' \<le> t''" 
      using H2 active_prop C1 C2 by blast
    have H1': "t' \<in>#\<^sub>z c_imp c loc'" using H1 C1 next_propagate'_implications_aux_2
      by (metis (no_types, lifting) C2 H2 H3 active_prop' f_f_leq_aux_1 not_active zcount_ne_zero_iff)
    have G1: "(zcount (c_imp c' loc') t') \<le> (zcount (c_imp c loc') t')" 
      using next_propagate'_implications_aux_2 C1 C2
      unfolding inv_implications_nonneg_def
      by (smt (verit) H2_1 H2_2 H3 c_implicate_eq_prop not_active order.strict_trans order_le_imp_less_or_eq prop_active)
    show "\<exists>y\<in>{imps. imps \<in>#\<^sub>z c_imp c loc' \<and> (\<exists>t\<in>active_work c. t < imps)}. id y = t' \<and> nat (zcount (c_imp c' loc') t') \<le> nat (zcount (c_imp c loc') y)"
      using H1' H2_1 H2_2 H3 G1 
      by(auto simp add: Bex_def)
  qed
qed

lemma f_f_leq:
  assumes H: "next_propagate' c c' loc t" 
  and "inv_implications_nonneg c"
shows "future_fuel c \<ge> future_fuel c'"
proof -
  from assms show ?thesis
    unfolding future_fuel_def
    apply -
    by(rule sum_mono, rule f_f_aux; simp)
qed

lemma sum_pos_ex_elem_pos_nat: "(0::nat) < (\<Sum>m\<in>M. f m) \<Longrightarrow> \<exists>m\<in>M. 0 < f m"
  by (induct rule: infinite_finite_induct) fastforce+

lemma f_f_le_aux :
  assumes H: "measure c t > 0"
  shows "\<exists> loc. t \<in># c_work_neg c loc"
proof -
  from H obtain loc where H1: "t \<in># c_work_neg c loc" and H2: "0 < weight t loc"
    unfolding measure_def
    using sum_pos_ex_elem_pos_nat 
    by (metis mem_Collect_eq)
  show ?thesis
  proof
    from H1 show "t \<in># c_work_neg c loc"
    unfolding c_work_neg_def set_mset_def
    by (smt (verit) count_filter_zmset select_convs(1) zcount_ne_zero_iff zero_less_nat_eq mem_Collect_eq set_mset_def count_mset_neg)
  qed
qed

lemma f_f_le:
  assumes C1: "next_propagate' c c' loc t" 
    and C2: "t'\<in>active_work c'"
    and C3: "t' \<notin> active_work c" 
    and C4: "measure c' t' > 0"
    and C5: "inv_implications_nonneg c"
    and C6: "inv_implications_nonneg c'"
    and C7: "inv_imp_plus_work_nonneg c"
    and C8: "inv_imp_plus_work_nonneg c'"
  shows "future_fuel c > future_fuel c'"
proof -
  from C1 and C3 have not_eq: "t' \<noteq> t"
    using prop_active by auto
  from C8 and C6 have H1: "\<forall>loc t. zcount (c_work c' loc) t < 0 \<longrightarrow> 0 < zcount (c_imp c' loc) t"
    unfolding inv_implications_nonneg_def inv_imp_plus_work_nonneg_def
    by (metis add.right_neutral add_strict_increasing2 less_add_same_cancel2)
  obtain loc' where C4': "t' \<in># c_work_neg c' loc'"
    using C4 f_f_le_aux
    by blast
  have "0 < (zcount (c_imp c' loc') t')"
    using C4' H1 count_mset_neg
    unfolding c_work_neg_def set_mset_def
    by simp
  then have C4'': "0 < (zcount (c_imp c loc') t')"
      using  c_implicate_eq_prop C1 not_eq zero_less_nat_eq
      by presburger
  show ?thesis
    unfolding future_fuel_def
  proof (rule sum_strict_mono_ex1)
    show "finite (UNIV :: 'loc set)"
      by auto
  next
    show "\<forall>x\<in>UNIV. (\<Sum>imps | imps \<in>#\<^sub>z c_imp c' x \<and> (\<exists>t\<in>active_work c'. t < imps). nat (zcount (c_imp c' x) imps)) \<le> (\<Sum>imps | imps \<in>#\<^sub>z c_imp c x \<and> (\<exists>t\<in>active_work c. t < imps). nat (zcount (c_imp c x) imps))"
      using f_f_aux C1 C5 by blast
  next
    show "\<exists>loc\<in>UNIV. (\<Sum>imps | imps \<in>#\<^sub>z c_imp c' loc \<and> (\<exists>t\<in>active_work c'. t < imps). nat (zcount (c_imp c' loc) imps)) < (\<Sum>imps | imps \<in>#\<^sub>z c_imp c loc \<and> (\<exists>t\<in>active_work c. t < imps). nat (zcount (c_imp c loc) imps))"
      unfolding Bex_def
    proof (rule exI [where x = loc'] , rule conjI)
      show "loc' \<in> UNIV"
        by auto
    next
      have G1: "(\<Sum>imps | imps \<in>#\<^sub>z c_imp c' loc' \<and> (\<exists>x. x \<in> active_work c' \<and> x < imps). nat (zcount (c_imp c' loc') imps)) =
    (\<Sum>imps | imps \<in>#\<^sub>z c_imp c' loc' \<and> (\<exists>t. t\<in>active_work c' \<and> t < imps). nat (zcount (c_imp c loc') imps))"
      proof (rule elems_eq_sum_eq , safe)
        fix t' :: 't and t'' :: 't
        assume H2_1: "t' \<in>#\<^sub>z c_imp c' loc'" 
          and H2_2: "t'' \<in> active_work c'" 
          and H2_3: "t'' < t'"
        show "nat (zcount (c_imp c' loc') t') = nat (zcount (c_imp c loc') t')"
          using C1 C5 C6 H2_2 H2_3
          unfolding inv_implications_nonneg_def
          using eq_nat_nat_iff c_implicate_eq_prop active_prop active_prop' not_active prop_active
          by (metis C5)
      qed
      have G2: "(\<Sum>imps | imps \<in>#\<^sub>z c_imp c' loc' \<and> (\<exists>t. t\<in>active_work c' \<and> t < imps). nat (zcount (c_imp c loc') imps)) < 
        (\<Sum>imps | imps \<in>#\<^sub>z c_imp c loc' \<and> (\<exists>x. x \<in> active_work c \<and> x < imps). nat (zcount (c_imp c loc') imps))"
      proof (rule sum_strict_mono2 [where b = t'])
        show "finite {imps. imps \<in>#\<^sub>z c_imp c loc' \<and> (\<exists>x. x \<in> active_work c \<and> x < imps)}"
          by auto
      next
        show "{imps. imps \<in>#\<^sub>z c_imp c' loc' \<and> (\<exists>t. t \<in> active_work c' \<and> t < imps)} \<subseteq> {imps. imps \<in>#\<^sub>z c_imp c loc' \<and> (\<exists>x. x \<in> active_work c \<and> x < imps)}"
          using active_prop' c_implicate_eq_prop C1 C5
          apply(simp only: Collect_mono_iff)
          apply(rule allI)
          apply(rule impI)
          by (metis not_active prop_active zcount_ne_zero_iff)
      next
        show "t' \<in> {imps. imps \<in>#\<^sub>z c_imp c loc' \<and> (\<exists>x. x \<in> active_work c \<and> x < imps)} - {imps. imps \<in>#\<^sub>z c_imp c' loc' \<and> (\<exists>t. t \<in> active_work c' \<and> t < imps)}"
        proof safe
          show "t' \<in>#\<^sub>z c_imp c loc'"
            using C4''
            by (meson pos_zcount_in_zmset)
        next
          have "\<exists>t\<in>active_work c. t \<le> t'"
            using active_prop C1 C5 C2
            by auto
          then show "\<exists>x. x \<in> active_work c \<and> x < t'"
            using C3
            using order_le_less by blast
        next
          fix t'' :: 't
          assume "t' \<in>#\<^sub>z c_imp c' loc'"
            and "t'' \<in> active_work c'"
            and "t'' < t'"
          then show False
            using disjI2 C2 not_active 
            by blast
        qed
      next
        show "0 < nat (zcount (c_imp c loc') t')"
          using C4''
          by auto
      next
        fix x :: 't
        assume "x \<in> {imps. imps \<in>#\<^sub>z c_imp c loc' \<and> (\<exists>x. x \<in> active_work c \<and> x < imps)}"
        show "0 \<le> nat (zcount (c_imp c loc') x)"
          using C5
          unfolding inv_implications_nonneg_def
          by auto
      qed
      show "(\<Sum>imps | imps \<in>#\<^sub>z c_imp c' loc' \<and> (\<exists>x. x \<in> active_work c' \<and> x < imps). nat (zcount (c_imp c' loc') imps)) < (\<Sum>imps | imps \<in>#\<^sub>z c_imp c loc' \<and> (\<exists>x. x \<in> active_work c \<and> x < imps). nat (zcount (c_imp c loc') imps))"
        using G1 G2
        by linarith
    qed
  qed
qed

subsection\<open>Combining the parts\<close>

lemma finite_active_work:
  "finite (active_work c)"
proof -
  have H:  "finite {t. \<exists> (loc :: 'loc).  t \<in>#\<^sub>z c_work c loc} \<Longrightarrow> finite {t. t \<in> active_work c}"
    by(simp add: active_work_def)
  have H': "finite {t. \<exists>(loc :: 'loc). t \<in>#\<^sub>z c_work c loc}"
    using finite_Union 
    by (auto simp add: Collect_ex_eq)
  from H and H' show ?thesis
    by auto
qed

definition measure_sum :: "('loc, 't) configuration \<Rightarrow>  nat" where
"measure_sum c = (\<Sum> t \<in> active_work c. measure c t)"

lemma measure_sum_prop:
  assumes "next_propagate' c c' loc t" 
  and "\<forall> t'. \<not> (t'\<in>active_work c' \<and> t' \<notin> active_work c \<and> measure c' t' > 0)"
  and "inv_implications_nonneg c"
shows "measure_sum c \<ge> measure_sum c'"
proof -
  have G1: "sum (measure c') (active_work c') = sum (measure c') {t. t \<in> active_work c' \<and> measure c' t > 0}"
    apply(rule Groups_Big.comm_monoid_add_class.sum.mono_neutral_right)
    using finite_active_work
    by auto
  have G2: "sum (measure c') {t \<in> active_work c'. 0 < measure c' t} \<le> sum (measure c) (active_work c)"
  proof (rule sum_le_included [where i = id])
    show "finite {t \<in> active_work c'. 0 < measure c' t}"
      using finite_active_work
      by auto
  next
    show "finite (active_work c)"
      using finite_active_work
      by auto
  next
    show "\<forall>y\<in>active_work c. 0 \<le> measure c y"
      by simp
  next
    show "\<forall>x\<in>{t \<in> active_work c'. 0 < measure c' t}. \<exists>y\<in>active_work c. id y = x \<and> measure c' x \<le> measure c y"
      using assms measure_prop_leq
      by auto
  qed
  show ?thesis
    using G1 G2
    unfolding measure_sum_def
    by auto
qed

lemma measure_sum_prop_neg:
  assumes "next_propagate' c c' loc t" 
  and "t \<in># c_work_neg c loc"
  and C: "\<forall> t'. \<not> (t'\<in>active_work c' \<and> t' \<notin> active_work c \<and> measure c' t' > 0)"
  and "inv_implications_nonneg c"
shows "measure_sum c > measure_sum c'"
proof -
  show ?thesis
    unfolding measure_sum_def
  proof (rule le_less_trans [where y = "sum (measure c') (active_work c)"])
    have H : "sum (measure c') (active_work c') = sum (measure c') {t. t \<in> active_work c' \<and> measure c' t > 0}"
      apply(rule Groups_Big.comm_monoid_add_class.sum.mono_neutral_right)
      using finite_active_work
      by auto
    show "sum (measure c') (active_work c') \<le> sum (measure c') (active_work c)"
      using H finite_active_work assms sum_mono2
      apply(simp only:)
      apply(rule sum_mono2)
      by auto
  next
    show "sum (measure c') (active_work c) < sum (measure c) (active_work c)"
    proof (rule sum_strict_mono_ex1)
      show "finite (active_work c)"
        using finite_active_work by auto
    next
      show "\<forall>x\<in>active_work c. measure c' x \<le> measure c x"
        using measure_prop_leq assms
        by auto
    next
      show "\<exists>a\<in>active_work c. measure c' a < measure c a"
        using assms measure_prop_le prop_active
        by blast
    qed
  qed
qed

definition neg_order :: "('loc, 't) configuration \<Rightarrow> (nat \<times> nat \<times> nat multiset)" where
"neg_order c = (future_fuel c, measure_sum c, total_work_repro c)"

lemma propagation_termination':
  assumes C1: "next_propagate' c c' loc t" 
  and C2: "inv_implications_nonneg c"
  and "inv_implications_nonneg c'"
  and "inv_imp_plus_work_nonneg c"
  and "inv_imp_plus_work_nonneg c'"
shows "neg_order c > neg_order c'"
proof -
  consider "\<exists> t'. (t'\<in>active_work c' \<and> t' \<notin> active_work c \<and> measure c' t' > 0)" |
    "\<not>(\<exists> t'. (t'\<in>active_work c' \<and> t' \<notin> active_work c \<and> measure c' t' > 0))" by auto
  then show ?thesis
  proof (cases, goal_cases le_1 eq_1)
    case le_1
    show ?thesis
      unfolding neg_order_def less_prod_simp
    proof (rule disjI1)
      show "future_fuel c' < future_fuel c"
        using le_1 assms f_f_le
        by auto
    qed
  next
    case eq_1
    show ?thesis
      unfolding neg_order_def less_prod_simp
    proof (rule disjI2 , rule conjI)
      show "future_fuel c' \<le> future_fuel c"
        using C1 C2 f_f_leq
        by auto
    next
      consider "t \<in># c_work_neg c loc" | "t \<in># c_work_pos c loc"
        using C1
        unfolding next_propagate'_def c_work_neg_def c_work_pos_def set_mset_def set_zmset_def
        by (metis in_zmset_notin_mset_neg set_mset_def set_zmset_def)
      then show "measure_sum c' < measure_sum c \<or> measure_sum c' \<le> measure_sum c \<and> total_work_repro c' < total_work_repro c"
      proof (cases, goal_cases neg pos)
        case neg
        then show ?thesis
          using C1 C2 eq_1 measure_sum_prop_neg disjI1
          by blast
      next
        case pos
        then show ?thesis 
          using measure_sum_prop C1 C2 eq_1 disjI2 terminating_total_work_repro
          by blast
      qed
    qed
  qed
qed

lemma propagation_termination:
  assumes "next_propagate c c'" 
  and "inv_imps_work_sum c"
  and "inv_implications_nonneg c"
shows "neg_order c > neg_order c'"
proof -
  from assms show ?thesis
    using propagation_termination' iiws_imp_iipwn p_preserves_inv_implications_nonneg p_preserves_inv_imps_work_sum
    by auto
qed

end
end