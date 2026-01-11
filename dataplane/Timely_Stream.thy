theory Timely_Stream
  imports
    "Coinductive.Coinductive_List"
    "HOL-Library.BNF_Corec"
    "HOL-Library.Multiset"
    Nondeterministic_Dataflow.Coinductive_List_Auxiliary
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

end