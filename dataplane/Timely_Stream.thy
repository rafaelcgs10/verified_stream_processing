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

inductive ev_drops for t where
  "lfinite lxs \<Longrightarrow> ev_drops t lxs C"
| "vacant t C \<Longrightarrow> ev_drops t lxs C"
| "t' \<in># C \<Longrightarrow> ev_drops t lxs (C - {# t' #}) \<Longrightarrow> ev_drops t (LCons (Drop t') lxs) C"
| "ev_drops t lxs (C + {# t' #}) \<Longrightarrow> ev_drops t (LCons (Mint t') lxs) C"
| "ev_drops t lxs C \<Longrightarrow> ev_drops t (LCons (Data t' d) lxs) C"

inductive_cases ev_drops_LNilE[elim!]: "ev_drops t LNil C"
inductive_cases ev_drops_LConsE[elim!]: "ev_drops t (LCons e lxs) C"

coinductive timely_productive where
  "lfinite lxs \<Longrightarrow> timely_productive lxs C"
| "\<lbrakk>\<not> lfinite lxs; timely_productive lxs C\<rbrakk> \<Longrightarrow> timely_productive (LCons (Data t d) lxs) C"
| "\<lbrakk>\<not> lfinite lxs; timely_productive lxs (C + {# t #}); ev_drops t lxs (C + {# t #}) \<rbrakk> \<Longrightarrow> timely_productive (LCons (Mint t) lxs) C"
| "\<lbrakk>\<not> lfinite lxs; timely_productive lxs (C - {# t #})\<rbrakk> \<Longrightarrow> timely_productive (LCons (Drop t) lxs) C"

inductive_cases timely_productive_LNilE[elim!]: "timely_productive LNil C"
inductive_cases timely_productive_LConsE[elim!]: "timely_productive (LCons e lxs) C"

definition "timely_input_stream lxs C =
 (timely_monotone lxs C \<and> (\<forall> t. count C t \<noteq> 0 \<longrightarrow> ev_drops t lxs C) \<and> timely_productive lxs C)"

lemma timely_input_stream_ldrop: "enat i < llength lxs \<Longrightarrow> timely_input_stream lxs C \<Longrightarrow>
  \<exists>C'. timely_input_stream (ldropn i lxs) C'"
proof (induct i arbitrary: lxs C)
  case 0
  then show ?case
    by (auto simp: enat_0)
next
  case (Suc i)
  from Suc(2,3) show ?case
    apply (cases lxs)
     apply (auto simp flip: eSuc_enat)
    apply (subst (asm) timely_input_stream_def)
    apply (erule conjE)+
    apply (auto)
    subgoal for lxs' t
      apply (rule Suc(1))
       apply assumption
      apply (unfold timely_input_stream_def) []
      apply (intro conjI)
        apply assumption
       apply (erule all_reg[rotated])
       apply (rule allI)
       apply (auto intro: ev_drops.intros) []
      apply (erule timely_productive.intros(1))
      done
    subgoal for lxs' t
      apply (rule Suc(1))
       apply assumption
      apply (unfold timely_input_stream_def) []
      apply (intro conjI)
        apply assumption
       apply (erule all_reg[rotated])
       apply (rule allI)
       apply (auto simp: vacant_def intro: ev_drops.intros) []
      apply assumption
      done
    subgoal for lxs' t' t
      apply (rule Suc(1))
       apply assumption
      apply (unfold timely_input_stream_def) []
      apply (intro conjI)
        apply assumption
       apply (rule all_reg[rotated])
        apply assumption
       apply (rule allI)
       apply (auto intro: ev_drops.intros) []
      apply (erule timely_productive.intros(1))
      done
    subgoal for lxs' t' t
      apply (rule Suc(1))
       apply assumption
      apply (unfold timely_input_stream_def) []
      apply (intro conjI)
        apply assumption
       apply (rule all_reg[rotated])
        apply assumption
       apply (rule allI)
       apply (auto intro: ev_drops.intros) []
       apply (metis count_eq_zero_iff order.refl ev_drops_LConsE event.distinct(3,5) event.inject(3)
          lfinite_code(2) vacant_def)
      apply assumption
      done
    subgoal for lxs' t' d
      apply (rule Suc(1))
       apply assumption
      apply (unfold timely_input_stream_def) []
      apply (intro conjI)
        apply assumption
       apply (rule all_reg[rotated])
        apply assumption
       apply (rule allI)
       apply (auto intro: ev_drops.intros) []
      apply (erule timely_productive.intros(1))
      done
    subgoal for lxs' t' d
      apply (rule Suc(1))
       apply assumption
      apply (unfold timely_input_stream_def) []
      apply (intro conjI)
        apply assumption
       apply (rule all_reg[rotated])
        apply assumption
       apply (rule allI)
       apply (auto intro: ev_drops.intros) []
      apply assumption
      done
    done
qed


lemma vacant_monotone_not_in_lset:
  "e \<in> lset lxs \<Longrightarrow> time e \<le> t \<Longrightarrow> vacant t C \<Longrightarrow> timely_monotone lxs C \<Longrightarrow> False"
  apply (induct e lxs arbitrary: C rule: llist.set_induct)
   apply (smt (verit, best) count_eq_zero_iff order.trans event.sel(1,2,3) lhd_LCons
      llist.distinct(1) timely_monotone.simps vacant_def)
  apply auto
   apply (metis count_eq_zero_iff insert_DiffM insert_iff set_mset_add_mset_insert vacant_def)
  apply (metis count_add_mset count_eq_zero_iff order.trans vacant_def)
  done

lemma ev_drops_not_in_lset: "ev_drops t lxs C \<Longrightarrow> timely_monotone lxs C \<Longrightarrow> \<exists>j. \<forall>u \<le> t. u \<notin> time ` lset (ldropn j lxs)"
proof (induct lxs C pred: ev_drops)
  case (1 lxs C)
  then show ?case
    by (auto simp: ldropn_all llength_eq_infty_conv_lfinite enat_the_enat intro!: exI[of _ "the_enat (llength lxs)"])
next
  case (2 C lxs)
  then show ?case
    apply -
    apply (rule exI[of _ "0"])
    apply simp
    apply (auto dest: vacant_monotone_not_in_lset)
    done
next
  case (3 t' C lxs)
  then show ?case
    by (metis event.distinct(2,5) event.sel(2) ldropn_Suc_LCons timely_monotone_LConsE)
next
  case (4 C t' lxs)
  then show ?case
    by (metis add_mset_add_single event.distinct(4,5) event.inject(3) ldropn_Suc_LCons
        timely_monotone_LConsE)
next
  case (5 C lxs t' d)
  then show ?case
    by (metis event.distinct(2,3) ldropn_Suc_LCons timely_monotone_LConsE)
qed


lemma lset_ldropn_conv_lnth: "lset (ldropn i lxs) = lnth lxs ` {k. k \<ge> i \<and> enat k < llength lxs}"
  apply (induct i arbitrary: lxs)
   apply (auto simp: in_lset_conv_lnth ldrop_eSuc_ltl Suc_le_eq)
   apply (metis (no_types, lifting) eSuc_enat gr_implies_not_zero imageI ldrop_enat ldrop_ltl
      ldropn_eq_LNil linorder_not_less llength_eq_0 lnth_ltl mem_Collect_eq not_less_eq_eq)
  apply (smt (verit) image_iff ldrop_eSuc_ltl ldropn_eq_LNil less_imp_Suc_add linorder_not_le llength_eq_0
      lnth_ltl mem_Collect_eq not_less_eq_eq not_less_zero)
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
    apply (frule timely_input_stream_ldrop)
     apply assumption
    apply (erule exE conjE)
    subgoal for C'
      apply (subst (asm) llist.collapse(2)[of "ldropn _ _", symmetric])
       apply simp
      apply (subst (asm) lhd_ldropn)
       apply simp
      apply (simp add: timely_input_stream_def)
      apply (auto)
      apply (drule spec, drule mp, assumption)
      apply (drule ev_drops_not_in_lset)
       apply (meson LConsData)
      apply (erule exE)
      subgoal for j
        apply (cases j; simp)
         apply blast
        subgoal for j'
          apply (drule spec[of _ t], drule mp, rule order_refl)
          apply (simp add: lfinite_lfilter)
          apply (rule finite_subset[of _ "{0 ..< i + j}"])
           apply (auto simp: ldropn_ltl image_iff lset_ldropn_conv_lnth)
          done
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
    apply (frule timely_input_stream_ldrop)
     apply assumption
    apply (erule exE conjE)
    subgoal for C'
      apply (subst (asm) llist.collapse(2)[of "ldropn _ _", symmetric])
       apply simp
      apply (subst (asm) lhd_ldropn)
       apply simp
      apply (simp add: timely_input_stream_def)
      apply (auto)
      apply (drule spec, drule mp, assumption)
      apply (drule ev_drops_not_in_lset)
       apply (meson LConsDrop)
      apply (erule exE)
      subgoal for j
        apply (cases j; simp)
         apply blast
        subgoal for j'
          apply (drule spec[of _ t], drule mp, rule order_refl)
          apply (simp add: lfinite_lfilter)
          apply (rule finite_subset[of _ "{0 ..< i + j}"])
           apply (auto simp: ldropn_ltl image_iff lset_ldropn_conv_lnth)
          done
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
    apply (frule timely_input_stream_ldrop)
     apply assumption
    apply (erule exE conjE)
    subgoal for C'
      apply (subst (asm) llist.collapse(2)[of "ldropn _ _", symmetric])
       apply simp
      apply (subst (asm) lhd_ldropn)
       apply simp
      apply (simp add: timely_input_stream_def)
      apply (auto)
      apply (drule spec, drule mp, assumption)
      apply (drule ev_drops_not_in_lset)
       apply (meson LConsMint)
      apply (erule exE)
      subgoal for t' j
        apply (simp add: lfinite_lfilter)
        apply (auto simp: ldropn_ltl image_iff lset_ldropn_conv_lnth)
         apply (meson not_in_iff order_refl vacant_def)
        apply (smt (verit, best) dual_order.order_iff_strict infinite_nat_iff_unbounded_le mem_Collect_eq)
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

lemma timely_input_stream_MintI[intro]:
  "timely_input_stream (LCons (Mint t) lxs) C \<Longrightarrow> timely_input_stream lxs (add_mset t C)"
  apply (auto simp add: timely_input_stream_def intro: ev_drops.intros)
  subgoal for t1 t2
    apply (erule timely_productive.cases; simp)
    subgoal
      apply (auto simp add: timely_input_stream_def intro: ev_drops.intros)
      subgoal
        by (meson not_in_iff union_single_eq_member vacant_def verit_comp_simplify1(2))
      subgoal
        by (meson not_in_iff union_single_eq_member vacant_def verit_comp_simplify1(2))
      subgoal
        by (metis ev_drops_LConsE event.sel(3) event.simps(7,9) lfinite_code(2) not_in_iff vacant_def verit_comp_simplify(2))
      subgoal
        by (metis ev_drops_LConsE event.sel(3) event.simps(7,9) lfinite_code(2) not_in_iff vacant_def verit_comp_simplify(2))
      done
    subgoal
      apply (auto simp add: timely_input_stream_def intro: ev_drops.intros)
      subgoal
        by (meson not_in_iff union_single_eq_member vacant_def verit_comp_simplify1(2))
      subgoal
        by (meson not_in_iff union_single_eq_member vacant_def verit_comp_simplify1(2))
      subgoal
        by (metis ev_drops_LConsE event.sel(3) event.simps(7,9) lfinite_code(2) not_in_iff vacant_def verit_comp_simplify(2))
      subgoal
        by (metis ev_drops_LConsE event.sel(3) event.simps(7,9) lfinite_code(2) not_in_iff vacant_def verit_comp_simplify(2))
      done
    subgoal
      apply (auto simp add: timely_input_stream_def intro: ev_drops.intros)
      subgoal
        by (meson not_in_iff union_single_eq_member vacant_def verit_comp_simplify1(2))
      subgoal
        by (meson not_in_iff union_single_eq_member vacant_def verit_comp_simplify1(2))
      subgoal
        by (metis ev_drops_LConsE event.sel(3) event.simps(7,9) lfinite_code(2) not_in_iff vacant_def verit_comp_simplify(2))
      subgoal
        by (metis ev_drops_LConsE event.sel(3) event.simps(7,9) lfinite_code(2) not_in_iff vacant_def verit_comp_simplify(2))
      done
    done
  subgoal for t1
    using timely_productive.intros(1) by blast
  done

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

lemma timely_input_stream_DataI[intro]:
  "timely_input_stream (LCons (Data t d) lxs) C \<Longrightarrow> timely_input_stream lxs C"
  by (auto simp add: timely_input_stream_def intro: timely_productive.intros ev_drops.intros)

lemma timely_input_stream_DropI[intro]:
  "timely_input_stream (LCons (Drop t) lxs) C \<Longrightarrow> timely_input_stream lxs ((C - {# t #}))"
  apply (auto simp add: timely_input_stream_def intro: timely_productive.intros ev_drops.intros)
  using ev_drops.simps vacant_diff apply fastforce+
  done

lemma timely_input_stream_ldrop_stronger_alt:
  "enat i < llength lxs \<Longrightarrow> timely_input_stream lxs C \<Longrightarrow>
  timely_input_stream (ldropn i lxs) (C + mset (map time (filter is_Mint (ltaken i lxs))) - mset (map time (filter is_Drop (ltaken i lxs))))"
  oops

lemma timely_input_stream_ldrop_stronger:
  "enat i \<le> llength lxs \<Longrightarrow> timely_input_stream lxs C \<Longrightarrow>
  timely_input_stream (ldropn i lxs) (C + mset (map time (filter is_Mint (ltaken i lxs))) - mset (map time (filter is_Drop (ltaken i lxs))))"
  oops

lemma timely_input_stream_Data_expires_le:
  "Data t' d \<in> lset lxs \<Longrightarrow> 
   timely_input_stream lxs C \<Longrightarrow> 
   t' \<le> t \<Longrightarrow>
   lfinite (lfilter (\<lambda>e. time e \<le> t) lxs)"
  apply (cases "lfinite lxs")
   apply simp
  apply (simp add: in_lset_conv_lnth)
  apply (erule exE conjE)+
  subgoal for i
    unfolding timely_input_stream_def
          oops



lemma timely_input_stream_expires_le:
  "timely_input_stream lxs C \<Longrightarrow> 
   lfinite (lfilter (\<lambda>e. time e \<le> t) lxs)"
    apply (cases "lfilter (\<lambda>e. time e \<le> t) lxs")
   apply simp_all
  subgoal for e lxs'
    apply (cases e; simp)
    subgoal for t' d
      apply hypsubst_thin
      subgoal premises prems
        oops

lemma timely_input_stream_expires_at_n_le:
  "timely_input_stream lxs C \<Longrightarrow> 
   \<exists> n \<le> llength lxs. \<forall> t' \<le> t. t' \<notin> event.time ` lset (ldropn n lxs)"
  oops

lemma t_not_in_timely_input_stream_aux:
  "timely_input_stream lxs C \<Longrightarrow> \<not> lfinite lxs \<Longrightarrow> t \<notin> time ` lset lxs \<Longrightarrow> count C t = 0"
  unfolding timely_input_stream_def
  apply (rule ccontr)
  apply clarsimp
  apply (drule spec[of _ t])
  apply simp
  subgoal premises prems
    using prems(6,1,2,3) apply -
    apply (induct lxs C rule: ev_drops.induct)
        apply (simp_all add: vacant_def)
     apply (metis not_in_iff order_refl)
    apply (meson in_remove1_mset_neq)
    done
  done

lemma t_not_in_timely_input_stream:
  "timely_input_stream lxs C \<Longrightarrow>
   \<forall> t' \<le> t. t' \<notin> event.time ` lset lxs \<Longrightarrow>
   \<not> lfinite lxs \<Longrightarrow>
   vacant t C"
  unfolding vacant_def
  apply safe
  subgoal for u
    unfolding not_def
    apply (drule spec[of _ u])
    apply simp
    using t_not_in_timely_input_stream_aux apply blast
    done
  done

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

lemma timely_input_stream_advances:
  "timely_input_stream lxs C \<Longrightarrow>
   \<exists> n \<le> llength lxs. vacant t (C + mset (map time (filter is_Mint (ltaken n lxs))) - mset (map time (filter is_Drop (ltaken n lxs))))"
  apply (cases "lfinite lxs")
  subgoal
    apply (rule exI[of _ "the_enat (llength lxs)"])
    apply (simp add: enat_the_enat llength_eq_infty_conv_lfinite)
    apply (subst (1 2) lfinite_llength_ltaken)
      apply (simp_all add: enat_the_enat llength_eq_infty_conv_lfinite)
 (*    apply (drule timely_input_stream_ldrop_stronger[rotated, where i="the_enat (llength lxs)"])
     apply (simp_all add: enat_the_enat llength_eq_infty_conv_lfinite)
    unfolding timely_input_stream_def
    apply (elim conjE)
    apply (subst (asm) (1 2 3) ldropn_all)
       apply (simp_all add: enat_the_enat llength_eq_infty_conv_lfinite)
    subgoal premises prems
      using prems(3) apply -
      unfolding vacant_def
      apply safe
      subgoal for t'
        apply (rule ccontr)
        apply (drule spec[of _ t'])
        apply (drule mp)
         apply (simp add: enat_the_enat lfinite_llength_ltaken llength_eq_infty_conv_lfinite prems(1))
        apply (metis count_empty enat_the_enat lfinite_llength_ltaken llength_eq_infty_conv_lfinite prems(1,2) timely_monotone_LNilE)
        done
      done
    done
  subgoal
    apply (frule timely_input_stream_expires_at_n_le[where t=t])
    apply (elim exE conjE)
    subgoal for n
      apply (frule timely_input_stream_ldrop_stronger[where i=n, rotated])
       apply assumption
      apply (drule t_not_in_timely_input_stream[where lxs="ldropn n lxs" and t=t])
        apply simp
       apply auto
      done
    done
  done *)
    oops


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

definition "ev_progress lxs C =
   (\<forall> t.
     (\<exists> n \<le> llength lxs.
       vacant t (C + mset (map time (filter is_Mint (ltaken n lxs))) - mset (map time (filter is_Drop (ltaken n lxs)))) \<and>
       (\<forall> t' \<le> t. t' \<notin> event.time ` lset (ldropn n lxs) \<and> n \<le> llength lxs)))"

lemma timely_input_stream_advances_frontier:
  "timely_input_stream lxs C \<Longrightarrow>
   \<exists> n \<le> llength lxs. \<not> frontier_less_equal (frontier (zmset_of (C + mset (map time (filter is_Mint (ltaken n lxs))) - mset (map time (filter is_Drop (ltaken n lxs)))))) t"
  sorry


end