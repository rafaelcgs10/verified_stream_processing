theory Timely_Stream
  imports
    "Coinductive.Coinductive_List"
    "HOL-Library.BNF_Corec"
    "HOL-Library.Multiset"
    Nondeterministic_Dataflow.Coinductive_List_Auxiliary
    Nondeterministic_Dataflow.CSet_LList_Impl
    AntichainOrder
begin

datatype ('t :: order, 'd) event = Data (time: 't) (data: 'd) | Drop (time: 't) | Mint (time: 't)

coinductive timely_monotone :: "('t::order, 'd) event llist \<Rightarrow> 't multiset \<Rightarrow> bool" where
  LNil: "timely_monotone LNil {#}"
| LConsDrop: "\<lbrakk> t \<in># C ; timely_monotone lxs (C - {# t #})\<rbrakk> \<Longrightarrow> timely_monotone (LCons (Drop t) lxs) C"
| LConsMint: "\<lbrakk> t' \<in># C ; t' \<le> t ; timely_monotone lxs (C + {# t #})\<rbrakk> \<Longrightarrow> timely_monotone (LCons (Mint t) lxs) C"
| LConsData: "\<lbrakk> t \<in># C  ; timely_monotone lxs C \<rbrakk> \<Longrightarrow> timely_monotone (LCons (Data t d) lxs) C"

inductive_cases timely_monotone_LNilE[elim!]: "timely_monotone LNil C"
inductive_cases timely_monotone_LConsE[elim!]: "timely_monotone (LCons e lxs) C"

definition "vacant t C = (\<forall>u \<le> t. count C u = 0)"

lemma vacant_diff:
  \<open>vacant t M \<Longrightarrow> vacant t (M - N)\<close>
  unfolding vacant_def by simp

definition "timely_progress lxs C =
   (\<forall> t.
     (\<exists> n \<le> llength lxs.
       vacant t (C + mset (map time (filter is_Mint (ltaken n lxs))) - mset (map time (filter is_Drop (ltaken n lxs))))))"

definition "timely_input_stream lxs C =
 (timely_monotone lxs C \<and> timely_progress lxs C)"

lemma vacant_monotone_not_in_lset:
  "e \<in> lset lxs \<Longrightarrow> time e \<le> t \<Longrightarrow> vacant t C \<Longrightarrow> timely_monotone lxs C \<Longrightarrow> False"
  apply (induct e lxs arbitrary: C rule: llist.set_induct)
   apply (smt (verit, best) count_eq_zero_iff order.trans event.sel(1,2,3) lhd_LCons
      llist.distinct(1) timely_monotone.simps vacant_def)
  apply auto
   apply (metis count_eq_zero_iff insert_DiffM insert_iff set_mset_add_mset_insert vacant_def)
  apply (metis count_add_mset count_eq_zero_iff order.trans vacant_def)
  done

lemma lset_ldropn_conv_lnth: "lset (ldropn i lxs) = lnth lxs ` {k. k \<ge> i \<and> enat k < llength lxs}"
  apply (induct i arbitrary: lxs)
   apply (auto simp: in_lset_conv_lnth ldrop_eSuc_ltl Suc_le_eq)
   apply (metis (no_types, lifting) eSuc_enat gr_implies_not_zero imageI ldrop_enat ldrop_ltl
      ldropn_eq_LNil linorder_not_less llength_eq_0 lnth_ltl mem_Collect_eq not_less_eq_eq)
  apply (smt (verit) image_iff ldrop_eSuc_ltl ldropn_eq_LNil less_imp_Suc_add linorder_not_le llength_eq_0
      lnth_ltl mem_Collect_eq not_less_eq_eq not_less_zero)
  done


lemma vacant_monotone_not_in_lset_alt:
  "timely_monotone lxs C \<Longrightarrow>
  vacant t C \<Longrightarrow>
  (\<forall> t' \<le> t. t' \<notin> event.time ` lset lxs)"
  using vacant_monotone_not_in_lset by fastforce

lemma timely_monotone_ldropn:
  "timely_monotone lxs C \<Longrightarrow>
   enat n \<le> llength lxs \<Longrightarrow>
   timely_monotone (ldropn n lxs) (C + image_mset time (filter_mset is_Mint (mset (ltaken n lxs))) - image_mset time (filter_mset is_Drop (mset (ltaken n lxs))))"
  apply (induct n arbitrary: lxs C)
  subgoal
    by simp
  subgoal for n lxs C
    apply clarsimp
    apply (erule timely_monotone.cases; simp)
    subgoal
      using timely_monotone.LNil by blast
    subgoal
      using Suc_ile_eq by fastforce
    subgoal
      using Suc_ile_eq by fastforce
    subgoal
      using Suc_ile_eq by fastforce
    done
  done

lemma timely_input_stream_Data_expires:
  "Data t d \<in> lset lxs \<Longrightarrow> 
   timely_input_stream lxs C \<Longrightarrow> 
   lfinite (lfilter (\<lambda>e. time e = t) lxs)"
  apply (cases "lfinite lxs")
   apply simp
  apply (simp add: in_lset_conv_lnth)
  apply (erule exE conjE)+
  subgoal for i
    unfolding timely_progress_def timely_input_stream_def
    apply clarsimp
    apply (drule spec[of _ t])
    apply clarsimp
    subgoal for n
      apply (drule vacant_monotone_not_in_lset_alt[rotated, where t=t and lxs="ldropn n lxs"])
      subgoal
        using timely_monotone_ldropn by auto
      subgoal
        apply (simp add: lfinite_lfilter)
        apply (rule finite_subset[of _ "{0 ..< i + n}"])
         apply simp_all
        apply (auto simp: ldropn_ltl image_iff lset_ldropn_conv_lnth)
        apply fastforce
        done
      done
    done
  done


lemma timely_input_stream_Drop_expires:
  "Drop t \<in> lset lxs \<Longrightarrow> 
   timely_input_stream lxs C \<Longrightarrow> 
   lfinite (lfilter (\<lambda>e. time e = t) lxs)"
  apply (cases "lfinite lxs")
   apply simp
  apply (simp add: in_lset_conv_lnth)
  apply (erule exE conjE)+
  subgoal for i
    unfolding timely_progress_def timely_input_stream_def
    apply clarsimp
    apply (drule spec[of _ t])
    apply clarsimp
    subgoal for n
      apply (drule vacant_monotone_not_in_lset_alt[rotated, where t=t and lxs="ldropn n lxs"])
      subgoal
        using timely_monotone_ldropn by auto
      subgoal
        apply (simp add: lfinite_lfilter)
        apply (rule finite_subset[of _ "{0 ..< i + n}"])
         apply simp_all
        apply (auto simp: ldropn_ltl image_iff lset_ldropn_conv_lnth)
        apply fastforce
        done
      done
    done
  done


lemma timely_input_stream_Mint_expires:
  "Mint t \<in> lset lxs \<Longrightarrow> 
   timely_input_stream lxs C \<Longrightarrow> 
   lfinite (lfilter (\<lambda>e. time e = t) lxs)"
  apply (cases "lfinite lxs")
   apply simp
  apply (simp add: in_lset_conv_lnth)
  apply (erule exE conjE)+
  subgoal for i
    unfolding timely_progress_def timely_input_stream_def
    apply clarsimp
    apply (drule spec[of _ t])
    apply clarsimp
    subgoal for n
      apply (drule vacant_monotone_not_in_lset_alt[rotated, where t=t and lxs="ldropn n lxs"])
      subgoal
        using timely_monotone_ldropn by auto
      subgoal
        apply (simp add: lfinite_lfilter)
        apply (rule finite_subset[of _ "{0 ..< i + n}"])
         apply simp_all
        apply (auto simp: ldropn_ltl image_iff lset_ldropn_conv_lnth)
        apply fastforce
        done
      done
    done
  done

lemma timely_input_stream_LCons_not_empty:
  \<open>timely_input_stream (LCons e lxs) C \<Longrightarrow> C \<noteq> {#}\<close>
  unfolding timely_input_stream_def by force


lemma timely_input_stream_expires:
  "timely_input_stream lxs C \<Longrightarrow> 
   lfinite (lfilter (\<lambda>e. time e = t) lxs)"
  apply (cases "lfilter (\<lambda>e. time e = t) lxs")
   apply simp_all
  subgoal for e lxs'
    apply (cases e; simp)
    using timely_input_stream_Data_expires
      apply (metis (mono_tags, lifting) event.sel(1) lfinite_code(2) llist.set_intros(1) lset_lfilter mem_Collect_eq)
    using timely_input_stream_Drop_expires
     apply (smt (verit, ccfv_SIG) event.sel(2) in_lset_lappend_iff lfilter_cong lfilter_eq_LConsD lfinite_code(2) llist.set_intros(1))      
    using timely_input_stream_Mint_expires
    apply (smt (verit, ccfv_SIG) event.sel(3) in_lset_lappend_iff lfilter_cong lfilter_eq_LConsD lfinite_code(2) llist.set_intros(1))
    done
  done

lemma vacant_add_mset[simp]:
  "vacant t' (add_mset t C) \<longleftrightarrow> vacant t' C \<and> \<not> t \<le> t'"
  unfolding vacant_def
  by auto

lemma vacant_le[intro]:
  "vacant (t :: 't :: order) C \<Longrightarrow> t' \<le> t \<Longrightarrow> vacant t' C"
  unfolding vacant_def
  by clarsimp

lemma timely_progress_MintI[intro]:
  "timely_progress (LCons (Mint t) lxs) C \<Longrightarrow> t1 \<in># C \<Longrightarrow> t1 \<le> t \<Longrightarrow> timely_progress lxs (add_mset t C)"
  unfolding timely_progress_def
  apply clarsimp
  subgoal for t'
    apply (cases "t \<le> t'")
    subgoal
      apply (drule spec[of _ t'])
      apply clarsimp
      subgoal for n
        apply (induct n arbitrary: lxs C)
        subgoal
          apply (rule exI[of _ 0])
          apply simp
          unfolding vacant_def
          apply (meson not_in_iff order_trans)
          done
        subgoal for n lxs' C'
          apply simp
          apply (cases lxs'; simp)
          using Suc_ile_eq iless_Suc_eq apply blast
          done
        done
      done
    subgoal
      apply (drule spec[of _ t'])
      apply clarsimp
      subgoal for n
        apply (induct n arbitrary: lxs C)
        subgoal
          apply (rule exI[of _ 0])
          using zero_enat_def order_refl apply auto
          done
        subgoal for n lxs' C'
          apply clarsimp
          apply (cases lxs'; simp)
          subgoal
            using enat_0 by blast
          subgoal
            using Suc_ile_eq by auto
          done
        done
      done
    done
  done

lemma timely_input_stream_MintI[intro]:
  "timely_input_stream (LCons (Mint t) lxs) C \<Longrightarrow> timely_input_stream lxs (add_mset t C)"
  by (auto simp add: timely_input_stream_def)

lemma timely_input_stream_expires_at_n:
  "timely_input_stream lxs C \<Longrightarrow> 
   \<exists> n. t \<notin> event.time ` lset (ldropn n lxs) \<and> n \<le> llength lxs"
  apply (drule timely_input_stream_expires[of _ _ t])
  apply (induct "lfilter (\<lambda>e. event.time e = t) lxs" arbitrary: lxs rule: lfinite_induct)
  subgoal
    by (metis (mono_tags, lifting) enat_0_iff(1) imageE ldropn_0 lfilter_empty_conv lnull_def zero_le)
  subgoal for lxs
    apply (cases "lfilter (\<lambda>e. event.time e = t) lxs"; simp)
    apply (drule lfilter_eq_LConsD)
    apply clarsimp
    apply hypsubst_thin
    subgoal for t' us vs
      apply (drule meta_spec)
      apply (drule meta_mp)
       apply (rule refl)
      apply clarsimp
      subgoal for n
        apply (rule exI[of _ "the_enat (llength us) + n + 1"])
        apply clarsimp
        apply (smt (verit) add.commute add_Suc_right add_diff_cancel_right' eSuc_enat enat_ord_simps(1) ldropn_Suc_LCons ldropn_lappend2 le_add1 lfinite_conv_llength_enat linorder_linear llength_LCons
            llength_lappend lnull_ldropn order_class.order_eq_iff plus_enat_simps(1) the_enat.simps)
        done
      done
    done
  done

lemma timely_progress_DataI[intro]:
  "timely_progress (LCons (Data t d) lxs) C \<Longrightarrow> t \<in># C \<Longrightarrow> timely_progress lxs C"
  unfolding timely_progress_def
  apply clarsimp
  subgoal premises prems for t'
    using prems(1,2) apply -
    apply (drule spec[of _ t'])
    apply clarsimp
    subgoal for n
      apply (induct n arbitrary: lxs C)
      subgoal
        apply simp
        apply (rule exI[of _ 0])
        apply simp
        using i0_lb zero_enat_def apply presburger
        done
      subgoal for n lxs' C'
        apply simp
        apply (cases lxs'; simp)
        subgoal
          using enat_0 by blast
        subgoal
          using Suc_ile_eq iless_Suc_eq by blast
        done
      done
    done
  done

lemma timely_input_stream_DataI[intro]:
  "timely_input_stream (LCons (Data t d) lxs) C \<Longrightarrow> timely_input_stream lxs C"
  by (auto simp add: timely_input_stream_def)


lemma timely_progress_DropI[intro]:
  "timely_progress (LCons (Drop t) lxs) C \<Longrightarrow> t \<in># C \<Longrightarrow> timely_progress lxs (remove1_mset t C)"
  unfolding timely_progress_def
  apply clarsimp
  subgoal premises prems for t'
    using prems(1,2) apply -
    apply (drule spec[of _ t'])
    apply clarsimp
    subgoal for n
      apply (induct n arbitrary: lxs C)
      subgoal
        apply simp
        apply (rule exI[of _ 0])
        apply simp
        using i0_lb zero_enat_def apply (simp add: vacant_diff)
        done
      subgoal for n lxs' C'
        apply simp
        apply (cases lxs'; simp)
        subgoal
          using enat_0 by blast
        subgoal
          using Suc_ile_eq iless_Suc_eq by blast
        done
      done
    done
  done


lemma timely_input_stream_DropI[intro]:
  "timely_input_stream (LCons (Drop t) lxs) C \<Longrightarrow> timely_input_stream lxs ((C - {# t #}))"
  by (auto simp add: timely_input_stream_def)

lemma lfinite_llength_ltaken:
  "lfinite lxs \<Longrightarrow>
   n = llength lxs \<Longrightarrow>
   ltaken n lxs = list_of lxs"
  apply (induct lxs arbitrary: n rule: lfinite_induct)
   apply (auto simp add: lnull_def)
  subgoal for xs n
    apply (cases xs; cases n; simp)
    using zero_enat_def apply force
    apply (metis enat_eSuc_iff eSuc_inject)
    done
  done

lemma vacant_not_frontier_less_equal:
  "vacant t M \<Longrightarrow>
   \<not> frontier_less_equal (frontier (zmset_of M)) t"
  unfolding vacant_def frontier_less_equal_iff2
  apply safe
  subgoal for t'
    apply transfer
    apply (simp add: count_eq_zero_iff in_minimal_antichain)
    done
  done


lemma Data_in_Stream_le_Data_in_C:
  "timely_monotone lxs C \<Longrightarrow>
   Data t d \<in> lset lxs \<Longrightarrow>
   (\<exists> t'\<le>t. t' \<in># C)"
  by (metis event.sel(1) not_in_iff order_class.order_eq_iff vacant_def vacant_monotone_not_in_lset)

lemma Mint_in_Stream_le_Mint_in_C:
  "timely_monotone lxs C \<Longrightarrow>
   Mint t \<in> lset lxs \<Longrightarrow>
   (\<exists> t'\<le>t. t' \<in># C)"
  by (metis count_eq_zero_iff event.sel(3) order_le_less vacant_def vacant_monotone_not_in_lset)


lemma Drop_in_Stream_le_Drop_in_C:
  "timely_monotone lxs C \<Longrightarrow>
   Drop t \<in> lset lxs \<Longrightarrow>
   (\<exists> t'\<le>t. t' \<in># C)"
  by (metis Orderings.order_eq_iff count_inI event.sel(2) vacant_def vacant_monotone_not_in_lset)

lemma setltakenD:
  "x \<in> set (ltaken n lxs) \<Longrightarrow>
   x \<in> lset lxs"
  apply (induct n arbitrary: lxs)
   apply simp
  subgoal for n lxs
    apply (cases lxs)
     apply auto
    done
  done

lemma timely_input_stream_ldrop:
  "enat n \<le> llength lxs \<Longrightarrow>
  timely_input_stream lxs C \<Longrightarrow>
  timely_input_stream (ldropn n lxs) (C + image_mset time (filter_mset is_Mint (mset (ltaken n lxs))) - image_mset time (filter_mset is_Drop (mset (ltaken n lxs))))"
  apply (induct n arbitrary: lxs C)
   apply simp
  subgoal for n lxs C
    apply (cases lxs)
    subgoal
      by simp
    subgoal for e lxs'
      apply (cases e; simp)
      subgoal
        using Suc_ile_eq iless_Suc_eq by blast 
      subgoal
        by (smt (verit, ccfv_SIG) add.commute add_mset_add_single diff_diff_add_mset dual_order.order_iff_strict enat_eSuc_iff event.disc(8,9) event.distinct(1) event.sel(2) ldropn_Suc_LCons ldropn_eq_LNil linorder_not_less
            llength_LCons nat.inject single_subset_iff subset_mset.add_diff_assoc2 timely_input_stream_DropI timely_input_stream_def timely_monotone_LConsE)
      subgoal
         by (metis Suc_ile_eq iless_Suc_eq timely_input_stream_MintI union_mset_add_mset_left)
      done
    done
  done


lemma timely_input_stream_Data_in_C_in:
  "Data t d \<in> set (ltaken n lxs) \<Longrightarrow> timely_input_stream lxs C \<Longrightarrow> t \<in># C \<or> (\<exists>x. x \<in> set (ltaken n lxs) \<and> is_Mint x \<and> t = event.time x)"
  apply (induct n arbitrary: lxs C)
   apply simp_all
  subgoal for n lxs C
    apply (cases lxs)
     apply simp
    subgoal for e lxs'
      apply simp
      unfolding timely_input_stream_def
      apply (clarsimp del: disjCI)
      apply (erule timely_monotone.cases; simp)
      subgoal
        by (meson in_diffD timely_progress_DropI)
      subgoal
        by force
      subgoal
        by auto
      done
    done
  done

end