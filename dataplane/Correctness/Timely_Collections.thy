theory Timely_Collections

imports
  "../Timely_Stream"
  "../Timely/Operator_State"
begin

declare cin.rep_eq[simp del]
declare enum_class.enum_UNIV[simp] enum_class.enum_distinct[simp]
declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]

section \<open>Data collection (coll) and timestamps ts\<close>

definition "ts inps = cimage (\<lambda> e. case e of Data t d \<Rightarrow> t) (cfilter is_Data (cset_of_llist inps))"
definition "outputs_ts f xs = remdups (filter (\<lambda> t. \<not> frontier_less_equal f t) xs)"

definition "coll inps t = list_of (lmap (\<lambda> e. case e of Data t d \<Rightarrow> d) (lfilter (\<lambda> e. case e of Data t' d \<Rightarrow> t = t' | _ \<Rightarrow> False) inps))"
definition "fcoll inps t = (map (\<lambda> e. case e of Data t d \<Rightarrow> d) (filter (\<lambda> e. case e of Data t' d \<Rightarrow> t = t' | _ \<Rightarrow> False) inps))"


lemma coll_LNil[simp]:
  "coll LNil t = []"
  by (auto simp add: coll_def list_of_LCons_conv)
lemma coll_LCons_Data:
  "lfinite (lfilter (\<lambda>e. event.time e = t) inps) \<Longrightarrow>
   coll (LCons (Data t' e) inps) t = (if t = t' then e # coll inps t else coll inps t)"
  apply (auto simp add: coll_def list_of_LCons_conv)
  apply (rule FalseE)
  apply (subgoal_tac "llength (lfilter (\<lambda>e. event.time e = t') inps) \<ge> llength (lfilter (\<lambda>x. case x of Data t'a d \<Rightarrow> t' = t'a | _ \<Rightarrow> False) inps)")
  subgoal
    by (metis basic_trans_rules(24) enat_ord_simps(3) llength_eq_infty_conv_lfinite)
  subgoal premises
    apply(induct inps)
      apply (auto intro: order_trans split: event.splits)
     apply (smt (verit, best) basic_trans_rules(7) eSuc_ile_mono ile_eSuc lfilter_cong)+
    done
  done
lemma coll_LCons_Drop[simp]:
  "coll (LCons (Drop t') inps) t = coll inps t"
  by (auto simp add: coll_def list_of_LCons_conv)
lemma coll_LCons_Mint[simp]:
  "coll (LCons (Mint t') inps) t = coll inps t"
  by (auto simp add: coll_def list_of_LCons_conv)

lemma coll_append[simp]:
  "coll (llist_of (xs @ ys)) t = coll (llist_of xs) t @ coll (llist_of ys) t"
  apply (simp add: coll_def)
  done

lemma coll_lshift:
  "lfinite (lfilter (\<lambda>e. event.time e = t) inps) \<Longrightarrow>
   coll (xs @@- inps) t = coll (llist_of xs) t @ coll inps t"
  apply (induct xs arbitrary: inps rule: rev_induct)
   apply (simp add: coll_def)
  subgoal for x xs inps
    apply (cases x)
      apply (auto simp add: coll_LCons_Data split: event.splits)
    done
  done

section \<open>Vacancy and Frontier Consequences\<close>
lemma ts_Mint[simp]:
  "ts (LCons (Mint t) inps) = ts inps"
  unfolding  ts_def
  apply (auto split: event.splits)
   apply (metis cinsertE cinsert_code event.inject(1) event.simps(4,6))
  apply (metis cinsert_code cinsert_iff event.inject(1) event.simps(4,6))
  done

lemma ts_Data[simp]:
  "ts (LCons (Data t d) inps) = cinsert t (ts inps)"
  unfolding  ts_def
  apply (auto split: event.splits)
    apply (metis cinsertE cinsert_code event.disc(1) event.inject(1))
   apply (metis cinsert_code cinsert_iff event.inject(1) event.simps(4,7))
  apply (metis cinsert_code cinsert_iff event.inject(1) event.simps(4,7))
  done

lemma ts_Drop[simp]:
  "ts (LCons (Drop t) inps) = ts inps"
  unfolding  ts_def
  apply (auto split: event.splits)
   apply (metis cinsertE cinsert_code event.inject(1) event.simps(4,6))
  apply (metis cinsert_code cinsert_iff event.inject(1) event.simps(5,7))
  done

lemma ts_LNil[simp]:
  "ts LNil = {||}"
  unfolding  ts_def
  by (auto simp add: cset_of_llist.rep_eq split: event.splits)


lemma coll_llist_of_map_Data[simp]:
  "coll (llist_of (map (\<lambda>(d, t). Data t (f d)) xs)) t = map (f o fst) (filter (\<lambda> (x, t'). t' = t) xs)"
  apply (induct xs)
   apply simp
  subgoal for x xs
    apply (cases x)
    apply (auto simp add: coll_LCons_Data)
    done
  done

lemma rcset_ts[simp]:
  "rcset (ts lxs) = event.time ` {x \<in> (lset lxs). is_Data x}"
  unfolding ts_def
  apply (auto simp add:  image_iff cset_of_llist.rep_eq split: event.splits)
   apply force
  apply (metis event.distinct(1,3) event.sel(1) is_Data_def)
  done


section \<open>Timely Input Stream\<close>
lemma not_frontier_less_equal_vacant:
  "\<not> frontier_less_equal (frontier (zmset_of M)) t \<Longrightarrow>
   vacant t M"
  unfolding vacant_def frontier_less_equal_iff2
  by (metis count_eq_zero_iff count_greater_zero_iff of_nat_0_less_iff order_trans_rules(23) trivial_dataflow_topology_interpretation.obtain_elem_frontier zcount_of_mset)
lemma timely_input_stream_vacant_Data_not_in:
  "timely_input_stream lxs C \<Longrightarrow>
   vacant t C \<Longrightarrow>
   Data t d \<notin> lset lxs"
  by (metis event.sel(1) order_refl timely_input_stream_def vacant_monotone_not_in_lset)

lemma timely_input_stream_vacant_coll:
  "timely_input_stream lxs C \<Longrightarrow>
   n \<le> llength lxs \<Longrightarrow>
   vacant t' (C + event.time `# filter_mset is_Mint (mset (ltaken n lxs)) - event.time `# filter_mset is_Drop (mset (ltaken n lxs))) \<Longrightarrow> 
   map fst (filter (\<lambda>(d, t'a). t'a = t') (map (case_event (\<lambda>t d. (d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))) = coll lxs t'"
  unfolding coll_def
  apply (induct n arbitrary: lxs C)
  subgoal
    apply simp
    apply (smt (verit, best) event.case_eq_if event.collapse(1) lfilter_False list_of_LNil llist.map(1) timely_input_stream_vacant_Data_not_in)
    done
  subgoal premises prems for n lxs' C'
    using prems(2-) apply -
    apply (cases lxs')
    subgoal
      by (auto simp add: filter_empty_conv split: event.splits)
    subgoal for e lxs''
      apply (cases e; simp)
      subgoal for t d
        apply (intro conjI impI)
        subgoal
          apply (cases "lfinite lxs''")
          subgoal
            apply (subst list_of_LCons)
             apply simp
            apply simp
            using prems(1) 
            apply (metis (no_types, lifting) Suc_ile_eq iless_Suc_eq lfinite_lfilterI list_of_lmap timely_input_stream_DataI)
            done
          subgoal
            apply (subst list_of_LCons)
            subgoal
              apply simp_all
              unfolding timely_input_stream_def
              apply clarsimp
              apply (erule timely_monotone.cases; simp)
              apply hypsubst_thin
              apply (drule vacant_monotone_not_in_lset_alt[rotated, where t=t and lxs="ldropn n lxs''"])
              subgoal
                apply (rule timely_monotone_ldropn)
                 apply simp_all
                using Suc_ile_eq iless_Suc_eq apply blast
                done
              apply (simp add: lfinite_lfilter)
              apply (rule finite_subset[of _ "{0 ..< n}"])
               apply simp_all
              apply (auto simp: ldropn_ltl image_iff lset_ldropn_conv_lnth del: disjCI split: event.splits)
              apply (metis dual_order.order_iff_strict event.exhaust event.sel(1) not_less)
              done
            using prems(1) 
            apply (metis (no_types, lifting) Suc_ile_eq iless_Suc_eq timely_input_stream_DataI)
            done
          done
        subgoal
          using prems(1) 
          apply (metis (no_types, lifting) Suc_ile_eq iless_Suc_eq timely_input_stream_DataI)
          done
        done
      subgoal for t
        unfolding timely_input_stream_def
        apply clarsimp
        apply (erule timely_monotone.cases; simp)
        subgoal for t'' C''
          apply hypsubst_thin
          apply (subst prems(1)[where C="remove1_mset t'' C''"])
             apply simp_all
          unfolding timely_input_stream_def
           apply blast
          using Suc_ile_eq iless_Suc_eq apply blast
          done
        done
      subgoal for t
        unfolding timely_input_stream_def
        apply clarsimp
        apply (erule timely_monotone.cases; simp)
        subgoal for t''' C'' t''
          apply hypsubst_thin
          apply (subst prems(1)[where C="add_mset t'' C''"])
             apply simp_all
          unfolding timely_input_stream_def
           apply blast
          using Suc_ile_eq iless_Suc_eq apply blast
          done
        done
      done
    done
  done

lemma map_filter_is_Data_Inl_ltaken_ldropn_coll:
  "timely_input_stream lxs C \<Longrightarrow>
   enat n \<le> llength lxs \<Longrightarrow>
   map (\<lambda>x. projl (fst x)) (filter (\<lambda>(d, t). t = t') (map (case_event (\<lambda>t d. (Inl d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))) @ coll (ldropn n lxs) t' =
   coll lxs t'"
  apply (subst coll_lshift[where xs="ltaken n lxs", of t' "ldropn n lxs", simplified])
  subgoal 
    using timely_input_stream_ldrop 
    by (metis timely_input_stream_ldrop timely_input_stream_expires)
  apply (subst (2) coll_def)
  apply (simp add: split_beta filter_map comp_def split: event.splits)
  apply (rule map_cong)
   apply (rule filter_cong)
    apply (auto split: event.splits)
  done


lemma timely_input_stream_advances_frontier:
  "timely_input_stream lxs C \<Longrightarrow>
   \<exists> n \<le> llength lxs.
   \<not> frontier_less_equal (frontier (zmset_of (C + mset (map event.time (filter is_Mint (ltaken n lxs))) - mset (map event.time (filter is_Drop (ltaken n lxs)))))) t \<and>
   (\<forall> d. Data t d \<in> lset lxs \<longrightarrow> Data t d \<in> set (ltaken n lxs)) \<and>
   map fst (filter (\<lambda> (d, t'). t' = t) (map (case_event (\<lambda> t d. (d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))) = coll lxs t"
  unfolding timely_input_stream_def timely_progress_def
  apply clarsimp
  apply (drule spec[of _ t])
  apply clarsimp
  subgoal for n
    apply (rule exI[of _ n])
    apply simp
    apply (intro conjI)
    subgoal
      by (metis vacant_not_frontier_less_equal)
    subgoal
      apply safe
      subgoal for d'
        apply (induct n arbitrary: lxs C)
        subgoal
          using vacant_monotone_not_in_lset by fastforce
        subgoal for n lxs' C'
          apply (cases lxs'; (clarsimp split: if_splits))
          subgoal
            by blast
          subgoal
            using Suc_ile_eq by auto
          subgoal
            using Suc_ile_eq by auto
          subgoal
            using Suc_ile_eq by auto
          done
        done
      done
    subgoal
      unfolding coll_def
      apply simp
      subgoal premises temp
        using temp(1,2,3) apply -
        apply (induct n arbitrary: lxs C)
        subgoal
          apply (clarsimp split: event.splits)
          apply (smt (verit) event.exhaust_sel lfilter_eq_LNil list_of_LNil llist.simps(12) vacant_monotone_not_in_lset verit_comp_simplify1(2))
          done
        subgoal for n lxs' C'
          apply (cases lxs'; (clarsimp split: event.splits if_splits))
          subgoal
            by blast
          subgoal for A lxs''
            apply auto
            apply hypsubst_thin
            subgoal premises prems for t'
              using prems(2-) apply -
              apply (subst prems(1)[where C="remove1_mset t' C'"])
                 apply assumption
              using Suc_ile_eq iless_Suc_eq apply blast
               apply simp_all
              apply (rule arg_cong[where f=list_of])
              apply (rule arg_cong2[where f=lmap])
               apply simp_all
              apply (rule lfilter_cong)
               apply (auto split: event.splits)
              done
            done
          subgoal for A lxs''
            apply auto
            apply hypsubst_thin
            subgoal premises prems for t' t''
              using prems(2-) apply -
              apply (subst prems(1))
                 apply assumption
              using Suc_ile_eq iless_Suc_eq apply blast
               apply simp_all
              apply (rule arg_cong[where f=list_of])
              apply (rule arg_cong2[where f=lmap])
               apply simp_all
              apply (rule lfilter_cong)
               apply (auto split: event.splits)
              done
            done
          subgoal for A lxs''
            apply (auto del: disjCI)
             apply hypsubst_thin
            subgoal premises prems 
              using prems(2-) apply -
              apply (cases "lfinite lxs''")
              subgoal
                apply (subst prems(1))
                   apply assumption
                using Suc_ile_eq iless_Suc_eq apply blast
                 apply simp_all
                apply (auto split: event.splits)
                done
              subgoal
                apply (subst prems(1))
                   apply assumption
                using Suc_ile_eq iless_Suc_eq apply blast
                 apply simp_all
                apply (auto split: event.splits)
                apply (subst list_of_LCons)
                 apply simp_all
                apply (drule vacant_monotone_not_in_lset_alt[rotated, where t=t and lxs="ldropn n lxs''"])
                subgoal
                  using Suc_ile_eq iless_Suc_eq timely_monotone_ldropn by blast
                apply (simp add: lfinite_lfilter)
                apply (rule finite_subset[of _ "{0 ..< n}"])
                 apply simp_all
                apply (auto simp: ldropn_ltl image_iff lset_ldropn_conv_lnth del: disjCI)
                apply (metis dual_order.order_iff_strict event.exhaust event.sel(1) not_less)
                done
              done
            subgoal premises prems for t' t''
              using prems(1,3-) apply -
              apply (subst prems(2))
                 apply assumption
              using Suc_ile_eq iless_Suc_eq apply blast
               apply simp_all
              apply (rule arg_cong[where f=list_of])
              apply (rule arg_cong2[where f=lmap])
               apply simp_all
              apply (rule lfilter_cong)
               apply (auto split: event.splits)
              done
            done
          done
        done
      done
    done
  done

lemma time_monotone_frontier_less_equal:
  "x \<in> lset inps \<Longrightarrow>
   timely_monotone inps C \<Longrightarrow>
   is_Data x \<Longrightarrow>
   frontier_less_equal (frontier (zmset_of C)) (event.time x)"
  unfolding  frontier_less_equal_iff2
  apply (cases x; clarsimp; hypsubst_thin?)
  subgoal for t d
    apply (induct inps arbitrary: C rule: lset_induct)
    subgoal
      apply (erule timely_monotone.cases)
         apply clarsimp+
      apply (meson mem_zmset_of zcount_gt_0_in_frontierD zcount_zmset_of_nonneg zmset_elem_nonneg)
      done
    subgoal for x' xs C
      apply (erule timely_monotone.cases; clarsimp; hypsubst_thin?)
      subgoal for t'
        apply (drule meta_spec)
        apply (drule meta_mp)
         apply assumption
        apply clarsimp
        using in_frontier_minusD apply fastforce
        done
      subgoal for t' t''
        apply (drule meta_spec)
        apply (drule meta_mp)
         apply assumption
        apply clarsimp
        apply (smt (verit, del_insts) in_frontier_iff mem_zmset_of order_trans_rules(23) trivial_dataflow_topology_interpretation.obtain_elem_frontier zcount_add_zmset zcount_ne_zero_iff zcount_zmset_of_nonneg)
        done
      done
    done
  done

lemma timely_input_stream_frontier_less_equal:
  "timely_input_stream inps C \<Longrightarrow>
   (\<forall> x. x \<in> lset inps \<longrightarrow> is_Data x \<longrightarrow> frontier_less_equal (frontier (zmset_of C)) (event.time x))"
  unfolding timely_input_stream_def
  using time_monotone_frontier_less_equal by blast

lemma timely_input_stream_drops_subseteq_C_mints:
  "timely_input_stream lxs C \<Longrightarrow> event.time `# filter_mset is_Drop (mset (ltaken n lxs)) \<subseteq># C + event.time `# filter_mset is_Mint (mset (ltaken n lxs))"
  apply (induct n arbitrary: lxs C)
  subgoal
    by simp
  subgoal for n lxs' C
    apply (cases lxs')
    subgoal
      by auto
    subgoal for e lxs''
      apply (cases e)
      subgoal for t d
        by auto
      subgoal for t
        apply simp
        apply (drule meta_spec[of _ lxs''])
        apply (drule meta_spec[of _ "remove1_mset t C"])
        apply (drule meta_mp)
        using timely_input_stream_DropI apply blast
        apply (simp add: subseteq_mset_def)
        apply (auto split: if_splits)
        unfolding timely_input_stream_def
        apply clarsimp
        apply (erule timely_monotone.cases)
           apply simp_all
        apply (metis Suc_to_right in_countE not_less_eq_eq plus_nat.simps(2))
        done
      subgoal for t
        unfolding timely_input_stream_def
        apply clarsimp
        apply (erule timely_monotone.cases)
           apply simp_all
        apply hypsubst_thin
        apply force
        done
      done
    done
  done



definition icoll where
  \<open>icoll lxs t = list_of (lmap (\<lambda>e. case e of Data _ d \<Rightarrow> d)
  (lfilter (\<lambda>e. case e of Data t' _ \<Rightarrow> t' \<le> t | _ \<Rightarrow> False) lxs))\<close>

lemma icoll_LNil[simp]:
  \<open>icoll LNil t = []\<close>
  unfolding icoll_def by simp

lemma icoll_LCons_Data:
  assumes \<open>lfinite (lfilter (\<lambda>e. event.time e \<le> t) lxs)\<close>
  shows \<open>icoll (LCons (Data t' d) lxs) t =
  (if t' \<le> t then d # icoll lxs t else icoll lxs t)\<close>
proof (cases \<open>t' \<le> t\<close>)
  case True
  have \<open>lfilter (\<lambda>e. case e of Data t' _ \<Rightarrow> t' \<le> t | _ \<Rightarrow> False) lxs
  = lfilter is_Data (lfilter (\<lambda>e. event.time e \<le> t) lxs)\<close>
    using event.case_eq_if lfilter_cong lfilter_lfilter by (smt (verit, best))
  thus ?thesis unfolding icoll_def using assms by simp
next
  case False
  thus ?thesis unfolding icoll_def by simp
qed

lemma icoll_LCons_Drop[simp]:
  \<open>icoll (LCons (Drop t') lxs) t = icoll lxs t\<close>
  unfolding icoll_def by simp

lemma icoll_LCons_Mint[simp]:
  \<open>icoll (LCons (Mint t') lxs) t = icoll lxs t\<close>
  unfolding icoll_def by simp

lemma icoll_append:
  \<open>icoll (llist_of (xs @ ys)) t
  = icoll (llist_of xs) t @ icoll (llist_of ys) t\<close>
  unfolding icoll_def by simp

lemma icoll_lshift:
  \<open>lfinite (lfilter (\<lambda>e. event.time e \<le> t) lxs) \<Longrightarrow>
  icoll (xs @@- lxs) t = icoll (llist_of xs) t @ icoll lxs t\<close>
proof (induction xs arbitrary: lxs rule: rev_induct)
  case (snoc x xs)
  thus ?case by (cases x) (auto simp add: icoll_append icoll_LCons_Data)
qed simp




lemma set_icoll_llist_of:
  \<open>set (icoll (llist_of xs) t) = {d. \<exists>t'. Data t' d \<in> set xs \<and> t' \<le> t}\<close>
  apply (induction xs)
  apply (simp add: icoll_def)
  apply (auto simp: icoll_def split: event.splits)
  done


lemma set_icoll_lshift:
  \<open>lfinite (lfilter (\<lambda>e. event.time e \<le> t) lxs) \<Longrightarrow>
    set (icoll (xs @@- lxs) t) = set (icoll (llist_of xs) t) \<union> set (icoll lxs t)\<close>
  apply (simp add: icoll_lshift)
  done

lemma set_icoll_lsetI:
  assumes finite: \<open>lfinite (lfilter (\<lambda>e. event.time e \<le> t) lxs)\<close>
    and data: \<open>Data t' d \<in> lset lxs\<close>
    and le: \<open>t' \<le> t\<close>
  shows \<open>d \<in> set (icoll lxs t)\<close>
  unfolding icoll_def
  apply (subst set_list_of)
  apply (simp add: lfinite_lmap)
  apply (rule lfinite_lfilter_mono[OF finite])
  apply (auto split: event.splits)
  apply (rule image_eqI[where x=\<open>Data t' d\<close>])
  apply simp
  using data le by (simp add: lset_lmap lset_lfilter)

lemma ts_lsetE:
  assumes \<open>t |\<in>| ts lxs\<close>
  obtains d where \<open>Data t d \<in> lset lxs\<close>
proof -
  from assms obtain e where e_in: \<open>e |\<in>| cset_of_llist lxs\<close>
    and data: \<open>is_Data e\<close>
    and t_eq: \<open>t = (case e of Data t d \<Rightarrow> t)\<close>
    unfolding ts_def
    by (subst (asm) cin_cimage_cfilter) auto
  then show ?thesis
    by (cases e) (auto intro: that simp add: cin.rep_eq cset_of_llist.rep_eq)
qed

lemma ts_lsetI:
  assumes \<open>Data t d \<in> lset lxs\<close>
  shows \<open>t |\<in>| ts lxs\<close>
  unfolding ts_def
  apply (subst cimage_iff)
  apply (rule_tac x=\<open>Data t d\<close> in cBexI)
  apply simp
  using assms by (simp add: cin.rep_eq cset_of_llist.rep_eq)


lemma icoll_empty_if_no_data_le:
  assumes \<open>\<And>t' d. t' \<le> t \<Longrightarrow> Data t' d \<notin> lset lxs\<close>
  shows \<open>icoll lxs t = []\<close>
  unfolding icoll_def
  apply (subst lfilter_False)
  apply (use assms in \<open>auto split: event.splits\<close>)
  done

lemma set_icoll_ltaken_ldropn:
  assumes \<open>lfinite (lfilter (\<lambda>e. event.time e \<le> t) (ldropn n lxs))\<close>
  shows \<open>set (icoll lxs t) =
    {d. \<exists>t'. Data t' d \<in> set (ltaken n lxs) \<and> t' \<le> t} \<union> set (icoll (ldropn n lxs) t)\<close>
  apply (subst ltaken_lshift_ldropn[symmetric, of lxs n])
  apply (subst set_icoll_lshift)
  apply (rule assms)
  apply (simp add: set_icoll_llist_of)
  done

lemma set_icoll_ltaken_if_no_ldropn_data_le:
  assumes finite: \<open>lfinite (lfilter (\<lambda>e. event.time e \<le> t) (ldropn n lxs))\<close>
    and no_data: \<open>\<And>t' d. t' \<le> t \<Longrightarrow> Data t' d \<notin> lset (ldropn n lxs)\<close>
  shows \<open>set (icoll lxs t) = {d. \<exists>t'. Data t' d \<in> set (ltaken n lxs) \<and> t' \<le> t}\<close>
  apply (subst (1) ltaken_lshift_ldropn[symmetric, of lxs n])
  apply (subst icoll_lshift)
  using finite apply blast
  apply (simp add: icoll_empty_if_no_data_le[OF no_data] set_icoll_llist_of)
  done

lemma timely_input_stream_ldropn_no_data_le_if_not_frontier_less_equal:
  assumes stream: \<open>timely_input_stream lxs C\<close>
    and n_le: \<open>enat n \<le> llength lxs\<close>
    and not_frontier: \<open>\<not> frontier_less_equal
      (frontier (zmset_of (C + event.time `# filter_mset is_Mint (mset (ltaken n lxs)) -
        event.time `# filter_mset is_Drop (mset (ltaken n lxs))))) t\<close>
    and u_le: \<open>u \<le> t\<close>
  shows \<open>Data u d \<notin> lset (ldropn n lxs)\<close>
  apply (rule notI)
  apply (rule vacant_monotone_not_in_lset[where e=\<open>Data u d\<close> and t=t and
        C=\<open>C + event.time `# filter_mset is_Mint (mset (ltaken n lxs)) -
          event.time `# filter_mset is_Drop (mset (ltaken n lxs))\<close> and lxs=\<open>ldropn n lxs\<close>])
  apply assumption
  apply (simp add: u_le)
  apply (rule not_frontier_less_equal_vacant[OF not_frontier])
  using timely_input_stream_ldrop[OF n_le stream]
  apply (simp add: timely_input_stream_def)
  done
end