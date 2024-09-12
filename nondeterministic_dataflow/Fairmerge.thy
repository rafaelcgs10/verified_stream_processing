section \<open>The fair merge operator\<close>

theory Fairmerge

imports
  Operator
  Linear_Temporal_Logic_on_Llists
begin

corec fairmerge :: "bool \<Rightarrow> bool \<Rightarrow> (2, 1, nat) op" where
  "fairmerge e1 e2 = (case (e1, e2) of
      (True, True) \<Rightarrow> End
    | (True, False) \<Rightarrow> Read 2 (case_observation (Write (fairmerge e1 e2) 1) (fairmerge e1 e2) End)
    | (False, True) \<Rightarrow> Read 1 (case_observation (Write (fairmerge e1 e2) 1) (fairmerge e1 e2) End)
    | (False, False) \<Rightarrow>
      Read 1 (case_observation (Write (Read 2 (case_observation (Write (fairmerge e1 e2) 1) (fairmerge e1 e2) (fairmerge e1 True))) 1)
     (Read 2 (case_observation (Write (fairmerge e1 e2) 1) (fairmerge e1 e2) (fairmerge e1 True))) (fairmerge True e2)))"

lemma fairmerge_False_False_Read:
  "fairmerge False False = Read p f \<longleftrightarrow> p = 1 \<and> f = (case_observation (Write (Read 2 (case_observation (Write (fairmerge False False) 1) (fairmerge False False) (fairmerge False True))) 1)
     (Read 2 (case_observation (Write (fairmerge False False) 1) (fairmerge False False) (fairmerge False True))) (fairmerge True False))"
  by (subst fairmerge.code; auto)+

lemma fairmerge_False_False_NoRead:
  "fairmerge False False = Write op' p' x = False"
  "fairmerge False False = End = False"
  by (subst fairmerge.code; auto)+

lemma inputs_fairmerge_False_TrueD: "p \<in> inputs op \<Longrightarrow> op = fairmerge False True \<or> (\<exists>x. op = Write (fairmerge False True) 1 x) \<Longrightarrow> p = 1"
  apply (induct p op rule: op.set_induct(1))
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  done

lemma inputs_fairmerge_False_True[simp]: "inputs (fairmerge False True) = {1}"
  apply (auto dest: inputs_fairmerge_False_TrueD)
  apply (subst fairmerge.code; auto split: observation.splits elim!: chd.elims)
  done

lemma inputs_fairmerge_True_FalseD: "p \<in> inputs op \<Longrightarrow> op = fairmerge True False \<or> (\<exists>x. op = Write (fairmerge True False) 1 x) \<Longrightarrow> p = 2"
  apply (induct p op rule: op.set_induct(1))
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  done

lemma inputs_fairmerge_True_False[simp]: "inputs (fairmerge True False) = {2}"
  apply (auto dest: inputs_fairmerge_True_FalseD)
  apply (subst fairmerge.code; auto split: observation.splits elim!: chd.elims)
  done

lemma inputs_fairmerge_False_FalseD: "p \<in> inputs op \<Longrightarrow>
  op = fairmerge False False \<or>
  op = Read 2 (case_observation (Write (fairmerge False False) 1) (fairmerge False False) (fairmerge False True)) \<or>
  (\<exists>x. op = Write (Read 2 (case_observation (Write (fairmerge False False) 1) (fairmerge False False) (fairmerge False True))) 1 x) \<or>
  (\<exists>x. op = Write (fairmerge False False) 1 x) \<Longrightarrow> p = 1 \<or> p = 2"
  apply (induct p op rule: op.set_induct(1))
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  done


lemma inputs_fairmerge_False_False[simp]: "inputs (fairmerge False False) = {1, 2}"
  apply (auto dest: inputs_fairmerge_False_FalseD)
  apply (subst fairmerge.code; auto split: observation.splits elim!: chd.elims)+
  done

section \<open>Cleaned\<close>

lemma cleaned_fairmerge: "cleaned (fairmerge e1 e2)"
  apply (coinduction arbitrary: e1 e2 rule: cleaned_coinduct_upto)
  subgoal for e1 e2
    apply (subst (1 3 5) fairmerge.code)
    apply (auto 3 4 split: bool.splits split: observation.splits
      intro: cc_base intro!: cc_write cc_read cc_cleaned[of End])
    done
  done

section \<open>Correctness\<close>

lemma traced_fairmerge_True_True: "traced (fairmerge True True) lxs \<longleftrightarrow> lxs = LNil"
  by (subst fairmerge.code) (auto intro: traced.intros)

coinductive trace_fmTF where
    "trace_fmTF (LCons (Inp 2 EOS) LNil)"
  | "trace_fmTF lxs \<Longrightarrow> trace_fmTF (LCons (Inp 2 EOB) lxs)"
  | "trace_fmTF lxs \<Longrightarrow> trace_fmTF (LCons (Inp 2 (Observed x)) (LCons (Out 1 x) lxs))"

lemma trace_fmTF_I: "traced (fairmerge True False) lxs \<Longrightarrow> trace_fmTF lxs"
  apply (coinduction arbitrary: lxs)
  subgoal for lxs
    apply (subst (asm) fairmerge.code)
    apply simp
    apply (erule traced_ReadE; simp split: observation.splits)
     apply (erule traced_WriteE; simp)
    apply (erule traced_EndE; simp)
    done
  done

lemma trace_fmTF_D: "trace_fmTF lxs \<Longrightarrow> traced (fairmerge True False) lxs"
  apply (coinduction arbitrary: lxs rule: traced_coinduct_upto)
  subgoal for lxs
    apply (erule trace_fmTF.cases)
      apply simp_all
    subgoal
      apply (subst fairmerge.code)
      apply (auto intro!: tc_traced traced.End) []
      done
    subgoal
      apply (subst fairmerge.code)
      apply (auto intro!: trace_fmTF.intros intro: tc_base) []
      done
    subgoal
      apply (subst fairmerge.code)
      apply (auto intro!: tc_write trace_fmTF.intros intro: tc_base) []
      done
    done
  done

lemma traced_fairmerge_True_False: "traced (fairmerge True False) lxs \<longleftrightarrow> trace_fmTF lxs"
  using trace_fmTF_I trace_fmTF_D by blast

coinductive trace_fmFT where
    "trace_fmFT (LCons (Inp 1 EOS) LNil)"
  | "trace_fmFT lxs \<Longrightarrow> trace_fmFT (LCons (Inp 1 EOB) lxs)"
  | "trace_fmFT lxs \<Longrightarrow> trace_fmFT (LCons (Inp 1 (Observed x)) (LCons (Out 1 x) lxs))"

lemma trace_fmFT_I: "traced (fairmerge False True) lxs \<Longrightarrow> trace_fmFT lxs"
  apply (coinduction arbitrary: lxs)
  subgoal for lxs
    apply (subst (asm) fairmerge.code)
    apply simp
    apply (erule traced_ReadE; simp split: observation.splits)
     apply (erule traced_WriteE; simp)
    apply (erule traced_EndE; simp)
    done
  done

lemma trace_fmFT_D: "trace_fmFT lxs \<Longrightarrow> traced (fairmerge False True) lxs"
  apply (coinduction arbitrary: lxs rule: traced_coinduct_upto)
  subgoal for lxs
    apply (erule trace_fmFT.cases)
      apply simp_all
    subgoal
      apply (subst fairmerge.code)
      apply (auto intro!: tc_traced traced.End) []
      done
    subgoal
      apply (subst fairmerge.code)
      apply (auto intro!: trace_fmFT.intros intro: tc_base) []
      done
    subgoal
      apply (subst fairmerge.code)
      apply (auto intro!: tc_write trace_fmFT.intros intro: tc_base) []
      done
    done
  done

lemma traced_fairmerge_False_True: "traced (fairmerge False True) lxs \<longleftrightarrow> trace_fmFT lxs"
  using trace_fmFT_I trace_fmFT_D by blast

definition "trace_fmFF_A1 \<equiv> {[Inp 1 EOB]} \<union> range (\<lambda>x. [Inp 1 (Observed x), Out 1 x])"
definition "trace_fmFF_A2 \<equiv> {[Inp 2 EOB]} \<union> range (\<lambda>x. [Inp 2 (Observed x), Out 1 x])"

coinductive trace_fmFF where
    "trace_fmTF lxs \<Longrightarrow> trace_fmFF (LCons (Inp 1 EOS) lxs)"
  | "trace_fmFT lxs \<Longrightarrow> a1 \<in> trace_fmFF_A1 \<Longrightarrow> trace_fmFF (a1 @@- LCons (Inp 2 EOS) lxs)"
  | "trace_fmFF lxs \<Longrightarrow> a1 \<in> trace_fmFF_A1 \<Longrightarrow> a2 \<in> trace_fmFF_A2 \<Longrightarrow> trace_fmFF (a1 @@- a2 @@- lxs)"

lemma trace_fmFF_A1_I1: "[Inp 1 EOB] \<in> trace_fmFF_A1"
  by (auto simp: trace_fmFF_A1_def)
lemma trace_fmFF_A1_I2: "[Inp 1 (Observed x), Out 1 x] \<in> trace_fmFF_A1"
  by (auto simp: trace_fmFF_A1_def)
lemma trace_fmFF_A2_I1: "[Inp 2 EOB] \<in> trace_fmFF_A2"
  by (auto simp: trace_fmFF_A2_def)
lemma trace_fmFF_A2_I2: "[Inp 2 (Observed x), Out 1 x] \<in> trace_fmFF_A2"
  by (auto simp: trace_fmFF_A2_def)

lemma trace_fmFF_I: "traced (fairmerge False False) lxs \<Longrightarrow> trace_fmFF lxs"
  apply (coinduction arbitrary: lxs)
  subgoal for lxs
    apply (subst (asm) fairmerge.code)
    apply simp
    apply (elim traced_ReadE traced_WriteE; simp split: observation.splits)
      apply (erule traced_WriteE; simp)
      apply (erule traced_ReadE; simp split: observation.splits)
        apply (erule traced_WriteE; simp)
        apply (rule disjI2)
        apply (rule exI conjI[rotated] disjI1 trace_fmFF_A1_I2 trace_fmFF_A2_I2 | assumption)+
        apply simp
       apply (rule disjI1)
       apply (rule exI conjI[rotated] disjI1 trace_fmFF_A1_I2 trace_fmFT_I | assumption)+
       apply simp
      apply (rule disjI2)
      apply (rule exI conjI[rotated] disjI1 trace_fmFF_A1_I2 trace_fmFF_A2_I1 | assumption)+
      apply simp
     apply (rule disjI1)
     apply (rule trace_fmTF_I | assumption)+
    apply (erule traced_ReadE; simp split: observation.splits)
      apply (erule traced_WriteE; simp)
      apply (rule disjI2)
      apply (rule exI conjI[rotated] disjI1 trace_fmFF_A1_I1 trace_fmFF_A2_I2 | assumption)+
      apply simp
     apply (rule disjI1)
     apply (rule exI conjI[rotated] disjI1 trace_fmFF_A1_I1 trace_fmFT_I | assumption)+
     apply simp
    apply (rule disjI2)
    apply (rule exI conjI[rotated] disjI1 trace_fmFF_A1_I1 trace_fmFF_A2_I1 | assumption)+
    apply simp
    done
  done

lemma trace_fmFF_D: "trace_fmFF lxs \<Longrightarrow> traced (fairmerge False False) lxs"
  apply (coinduction arbitrary: lxs rule: traced_coinduct_upto)
  subgoal for lxs
    apply (erule trace_fmFF.cases)
    supply disjCI[rule del]
      apply (auto simp add: trace_fmFF_A1_def trace_fmFF_A2_def)
    subgoal
      apply (subst fairmerge.code)
      apply (auto intro!: tc_traced traced.End trace_fmTF_D) []
      done
    subgoal
      apply (subst fairmerge.code)
      apply (force intro: tc_read tc_traced[of "fairmerge False True"] trace_fmFT_D) []
      done
    subgoal
      apply (subst fairmerge.code)
      apply (force intro: tc_read tc_write tc_traced[of "fairmerge False True"] trace_fmFT_D) []
      done
    subgoal
      apply (subst fairmerge.code)
      apply (force intro: tc_read tc_write tc_base) []
      done
    subgoal
      apply (subst fairmerge.code)
      apply (force intro: tc_read tc_write tc_base) []
      done
    subgoal
      apply (subst fairmerge.code)
      apply (force intro: tc_read tc_write tc_base) []
      done
    subgoal
      apply (subst fairmerge.code)
      apply (force intro: tc_read tc_write tc_base) []
      done
    done
  done

lemma traced_fairmerge_False_False: "traced (fairmerge False False) lxs \<longleftrightarrow> trace_fmFF lxs"
  using trace_fmFF_I trace_fmFF_D by blast

section\<open>Correctness using the history model\<close>

lemma history_fairmerge_True_True: "history (fairmerge True True) lxs lzs \<longleftrightarrow> lzs = (\<lambda>_. LNil)"
  unfolding history_def traced_fairmerge_True_True by auto

lemma history_fairmerge_True_False: "history (fairmerge True False) lxs lzs \<longleftrightarrow> lzs = (\<lambda>_. lxs 2)"
  unfolding history_def traced_fairmerge_True_False
  apply (auto simp: fun_eq_iff)

coinductive merged where
  "merged LNil lxs lxs"
| "merged lxs LNil lxs"
| "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> merged lxs lys lzs \<Longrightarrow>
   merged (xs @@- lxs) (ys @@- lys) (xs @@- ys @@- lzs)"
| "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> merged lxs lys lzs \<Longrightarrow>
   merged (xs @@- lxs) (ys @@- lys) (ys @@- xs @@- lzs)"

coinductive mergedL where
  "mergedL LNil lxs lxs"
| "mergedL lxs LNil lxs"
| "xs \<noteq> [] \<Longrightarrow> mergedL lys lxs lzs \<Longrightarrow> mergedL (xs @@- lxs) lys (xs @@- lzs)"

inductive_cases mergedL_LNil1E[elim!]: "mergedL LNil lys lzs"
inductive_cases mergedL_LNil2E[elim!]: "mergedL lxs LNil lzs"

lemma mergedL_merged: "mergedL lxs lys lzs \<Longrightarrow> merged lxs lys lzs"
  apply (coinduction arbitrary: lxs lys lzs)
  subgoal for lxs lys lzs
    apply (erule mergedL.cases)
      apply simp
    apply simp
    apply (erule mergedL.cases)
      apply simp
     apply simp
    apply (metis llist.collapse(1) llist.simps(3) lshift_simps(1) lshift_snoc merged.intros(1) not_lnull_conv shift_LNil)
    apply metis
    done
  done

lemma mergedRL_merged: "mergedL lys lxs lzs \<Longrightarrow> merged lxs lys lzs"
  apply (coinduction arbitrary: lxs lys lzs)
  subgoal for lxs lys lzs
    apply (erule mergedL.cases)
      apply simp
    apply simp
    apply (erule mergedL.cases)
      apply simp
     apply simp
    apply (metis llist.collapse(1) llist.disc(1) lshift_simps(1) lshift_simps(2) mergedL.intros(1) not_lnull_conv shift_LNil)
    apply metis
    done
  done

lemma merged_lappend1: "merged lxs lys lzs \<Longrightarrow> merged (xs @@- lxs) lys (xs @@- lzs)"
  apply (coinduction arbitrary: xs lxs lys lzs)
  apply (erule merged.cases)
     apply (metis llist.exhaust list.simps(3) lshift_simps(1) lshift_simps(2) merged.intros(1))
    apply metis
   apply (smt (verit) append_is_Nil_conv lshift_append)
  apply (metis lshift_simps(1))
  done

lemma merged_lappend2: "merged lxs lys lzs \<Longrightarrow> merged lxs (ys @@- lys) (ys @@- lzs)"
  apply (coinduction arbitrary: ys lxs lys lzs)
  apply (erule merged.cases)
     apply metis
    apply (metis llist.exhaust list.simps(3) lshift_simps(1) lshift_simps(2) merged.intros(2))
   apply (metis lshift_simps(1))
  apply (smt (verit) append_is_Nil_conv lshift_append)
  done

lemma merged_LCons1: "merged lxs lys lzs \<Longrightarrow> merged (LCons x lxs) lys (LCons x lzs)"
  by (metis lshift_simps(1) lshift_simps(2) merged_lappend1)

lemma merged_LCons2: "merged lxs lys lzs \<Longrightarrow> merged lxs (LCons y lys) (LCons y lzs)"
  by (metis lshift_simps(1) lshift_simps(2) merged_lappend2)

lemma merged_commute: "merged lxs lys lzs \<Longrightarrow> merged lys lxs lzs"
  apply (coinduction arbitrary: lxs lys lzs)
  subgoal for lxs lys lzs
    apply (erule merged.cases)
       apply (fastforce intro: merged.intros)+
    done
  done

lemma merged_mergedL: "merged lxs lys lzs \<Longrightarrow> mergedL lxs lys lzs \<or> mergedL lys lxs lzs"
  apply (erule merged.cases)
     apply (metis mergedL.intros(1))
    apply (metis mergedL.intros(1))
   apply (rule disjI1)
   apply hypsubst_thin
  subgoal for xs ys lxs lys lzs
    apply (coinduction arbitrary: xs ys lxs lys lzs)
    subgoal for xs ys lxs lys lzs
      apply (erule merged.cases)
         apply (metis mergedL.intros(2))
        apply (metis mergedL.intros(2) mergedL.intros(3))
       apply (metis merged_commute merged_lappend1)
      apply (metis (full_types) append_is_Nil_conv lshift_append merged_commute)
      done
    done
   apply (rule disjI2)
   apply hypsubst_thin
  subgoal for xs ys lxs lys lzs
    apply (coinduction arbitrary: xs ys lxs lys lzs)
    subgoal for xs ys lxs lys lzs
      apply (erule merged.cases)
         apply (metis mergedL.intros(2) mergedL.intros(3))
        apply (metis mergedL.intros(2))
       apply (metis (full_types) append_is_Nil_conv lshift_append merged_commute)
      apply (metis merged_commute merged_lappend1)
      done
    done
  done

lemma merged_alt: "merged lxs lys lzs \<longleftrightarrow> mergedL lxs lys lzs \<or> mergedL lys lxs lzs"
  using mergedL_merged mergedRL_merged merged_mergedL by blast

coinductive mergedL_fueled where
  "mergedL_fueled LNil LNil lxs lxs"
| "mergedL_fueled LNil lxs LNil lxs"
| "length xs = n \<Longrightarrow> n > 0 \<Longrightarrow> mergedL_fueled lns lys lxs lzs \<Longrightarrow> mergedL_fueled (LCons n lns) (xs @@- lxs) lys (xs @@- lzs)"

corec fuel_of_mergedL where
  "fuel_of_mergedL lxs lys lzs = (if lxs = LNil \<or> lys = LNil then LNil else
     (let (xs, lxs', lzs') = (SOME (xs, lxs', lzs'). xs \<noteq> [] \<and> mergedL lys lxs' lzs' \<and> lxs = xs @@- lxs' \<and> lzs = xs @@- lzs')
     in LCons (length xs) (fuel_of_mergedL lys lxs' lzs')))"

lemma mergedL_mergedL_fueled: 
  "mergedL lxs lys lzs \<Longrightarrow> mergedL_fueled (fuel_of_mergedL lxs lys lzs) lxs lys lzs"
  apply (coinduction arbitrary: lxs lys lzs)
  subgoal for lxs lys lzs
    apply (erule mergedL.cases)
    apply (simp add: fuel_of_mergedL.code)
     apply (simp add: fuel_of_mergedL.code)
    apply (cases "lys = LNil")
     apply (auto simp add: fuel_of_mergedL.code lshift_LNil_iff elim: mergedL.cases) []
    apply (rule disjI2)+
    apply hypsubst_thin
    apply (subst fuel_of_mergedL.code)
    apply (rule someI2)
    apply (rule case_prodI conjI refl | assumption)+
    apply (force simp: lshift_LNil_iff)
    done
  done

lemma mergedL_fueled_mergedL: 
  "mergedL_fueled lns lxs lys lzs \<Longrightarrow> mergedL lxs lys lzs"
  apply (coinduction arbitrary: lns lxs lys lzs)
  apply (erule mergedL_fueled.cases)
    apply force+
  done

lemma mergedL_alt: "mergedL lxs lys lzs \<longleftrightarrow> (\<exists>lns. mergedL_fueled lns lxs lys lzs)"
  using mergedL_fueled_mergedL mergedL_mergedL_fueled by blast

coinductive mergedL1_fueled where
  "mergedL1_fueled LNil LNil lxs lxs"
| "mergedL1_fueled LNil lxs LNil lxs"
| "mergedL1_fueled (if n = 0 then lns else LCons n lns) (if n = 0 then lys else lxs) (if n = 0 then lxs else lys) lzs \<Longrightarrow>
   mergedL1_fueled (LCons (Suc n) lns) (LCons x lxs) lys (LCons x lzs)"

lemma mergedL_fueled_mergedL1_fueled: "mergedL_fueled lns lxs lys lzs \<Longrightarrow> mergedL1_fueled lns lxs lys lzs"
  apply (coinduction arbitrary: lns lxs lys lzs)
  apply (erule mergedL_fueled.cases)
  apply simp
   apply simp
  apply hypsubst_thin
  apply simp
  subgoal for xs lns lxs lys lzs
    apply (induct xs arbitrary: lxs lzs)
     apply simp
    subgoal for x xs lxs lzs
      apply (cases xs)
       apply(auto intro: mergedL_fueled.intros)
      apply (metis length_Cons lshift_simps(2) mergedL_fueled.intros(3) zero_less_Suc)
      done
    done
  done

lemma mergedL1_fueled_mergedL_fueled: "mergedL1_fueled lns lxs lys lzs \<Longrightarrow> mergedL_fueled lns lxs lys lzs"
  apply (coinduction arbitrary: lns lxs lys lzs)
  subgoal for lns lxs lys lzs
    apply (cases lns)
     apply (auto elim: mergedL1_fueled.cases) []
    subgoal for n lns'
      apply hypsubst_thin
      apply (rule disjI2)+
      apply simp
    apply (induct n arbitrary: lns lxs lzs)
       apply (auto elim: mergedL1_fueled.cases) []
      apply (erule mergedL1_fueled.cases)
        apply (auto split: if_splits)
       apply (metis length_Cons list.size(3) lshift_simps(1) lshift_simps(2))
      apply (metis length_Cons lshift_simps(2))
      done
    done
  done

lemma mergedL_fueled_alt: "mergedL_fueled lns lxs lys lzs \<longleftrightarrow> mergedL1_fueled lns lxs lys lzs"
  using mergedL_fueled_mergedL1_fueled mergedL1_fueled_mergedL_fueled by blast

lemma produced_fairmerge_True_True: "produced m (fairmerge True True) lxs lzs \<longleftrightarrow> lzs = (\<lambda>_. LNil)"
  oops
(*   by (fastforce simp: fun_eq_iff fairmerge.code intro!: exI[of _ "\<lambda>_. 0"]) *)

(* lemma fairmerge_True_True: "\<lbrakk>fairmerge True True\<rbrakk> lxs lzs \<longleftrightarrow> lzs = (\<lambda>_. LNil)"
  unfolding semantics_def produced_fairmerge_True_True by simp *)

lemma produced_fairmerge_True_False: "produced m (fairmerge True False) lxs lzs \<longleftrightarrow> lzs = (\<lambda>_. lxs 2)"
 (*  unfolding fun_eq_iff semantics_def
  apply safe
   apply (subst num1_eq1)
   apply (coinduction arbitrary: m lzs lxs)
   apply safe
  subgoal for m lzs lxs
  proof (induct "m 2" arbitrary: m lxs)
    case 0
    then show ?case 
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  next
    case (Suc n)
    from Suc(2-) Suc(1)[of "m(2 := n)"] show ?case
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  qed
  subgoal for m lzs lxs
    by (auto dest!: produced_muted simp: muted_def)
  subgoal for m lzs lxs
  proof (induct "m 2" arbitrary: m lxs)
    case 0
    then show ?case 
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  next
    case (Suc n)
    from Suc(2-) Suc(1)[of "m(2 := n)"] show ?case
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  qed
  subgoal for m lzs lxs
  proof (induct "m 2" arbitrary: m lxs)
    case 0
    then show ?case 
      apply (subst (asm) fairmerge.code)
      apply (auto split: observation.splits elim!: chd.elims)
       apply (metis fun_upd_same)
      done
  next
    case (Suc n)
    from Suc(2-) Suc(1)[of "m(2 := n)"] show ?case
      apply (subst (asm) fairmerge.code)
      apply (auto split: observation.splits elim!: chd.elims)
       apply (metis fun_upd_same)
      done
  qed
  apply (coinduction arbitrary: m lxs lzs rule: produced_coinduct_upto)
  apply (rule disjI1)
  apply (subst fairmerge.code)
  apply (auto simp: fun_upd_def[where 'b=nat] muted_def split: observation.splits elim!: chd.elims
      intro!: exI[of _ 0])
   apply (rule produced_cong.write) 
    apply (rule produced_cong.base)
    apply (rule conjI refl)+
   apply (simp add: fun_eq_iff)
  apply (rule produced_cong.produced)
  apply (rule produced_End)
  apply (metis (full_types) num1_eq1)
  done *)
  oops

(* lemma fairmerge_True_False: "\<lbrakk>fairmerge True False\<rbrakk> lxs lzs \<longleftrightarrow> lzs = (\<lambda>_. lxs 2)"
  unfolding semantics_def produced_fairmerge_True_False by simp *)

lemma produced_fairmerge_False_True: "produced m (fairmerge False True) lxs lzs \<longleftrightarrow> lzs = (\<lambda>_. lxs 1)"
  (* unfolding fun_eq_iff semantics_def
  apply safe
   apply (subst num1_eq1)
   apply (coinduction arbitrary: m lzs lxs)
   apply safe
  subgoal for m lzs lxs
  proof (induct "m 1" arbitrary: m lxs)
    case 0
    then show ?case 
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  next
    case (Suc n)
    from Suc(2-) Suc(1)[of "m(1 := n)"] show ?case
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  qed
  subgoal for m lzs lxs
    by (auto dest!: produced_muted simp: muted_def)
  subgoal for m lzs lxs
  proof (induct "m 1" arbitrary: m lxs)
    case 0
    then show ?case 
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  next
    case (Suc n)
    from Suc(2-) Suc(1)[of "m(1 := n)"] show ?case
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  qed
  subgoal for m lzs lxs
  proof (induct "m 1" arbitrary: m lxs)
    case 0
    then show ?case 
      apply (subst (asm) fairmerge.code)
      apply (auto split: observation.splits elim!: chd.elims)
       apply (metis fun_upd_same)
      done
  next
    case (Suc n)
    from Suc(2-) Suc(1)[of "m(1 := n)"] show ?case
      apply (subst (asm) fairmerge.code)
      apply (auto split: observation.splits elim!: chd.elims)
       apply (metis fun_upd_same)
      done
  qed
  apply (coinduction arbitrary: m lxs lzs rule: produced_coinduct_upto)
  apply (rule disjI1)
  apply (subst fairmerge.code)
  apply (auto simp: fun_upd_def[where 'b=nat] muted_def split: observation.splits elim!: chd.elims
      intro!: exI[of _ 0])
   apply (rule produced_cong.write) 
    apply (rule produced_cong.base)
    apply (rule conjI refl)+
   apply (simp add: fun_eq_iff)
  apply (rule produced_cong.produced)
  apply (rule produced_End)
  apply (metis (full_types) num1_eq1)
  done *)
  oops

(* lemma fairmerge_False_True: "\<lbrakk>fairmerge False True\<rbrakk> lxs lzs \<longleftrightarrow> lzs = (\<lambda>_. lxs 1)"
  unfolding semantics_def produced_fairmerge_False_True by simp *)
(* 
lemma "\<lbrakk>fairmerge False False\<rbrakk> (\<lambda>x. if x = 1 then llist_of [1, 2, 3] else llist_of [4, 5]) (\<lambda>_. llist_of [4,1,2,3,5])"
  unfolding semantics_def
  apply (rule exI[of _ "\<lambda>x. 3"])
  apply (subst fairmerge.code; simp)
  apply (rule produced.ReadEOB; auto 0 0 simp: muted_def)
  apply (rule produced.Read[where n=3]; auto 0 0 simp: muted_def)
  apply (rule produced_Write; (auto simp: muted_def)?)
  apply (subst fairmerge.code; simp)
  apply (rule produced.Read[where n=3]; auto 0 0  simp: muted_def)
  apply (rule produced_Write; (auto simp: muted_def)?)
  apply (rule produced.ReadEOB; auto 0 0 simp: muted_def)
  apply (subst fairmerge.code; simp)
  apply (rule produced.Read[where n=3]; auto 0 0 simp: muted_def)
  apply (rule produced_Write; (auto simp: muted_def)?)
  apply (rule produced.ReadEOB; auto 0 0 simp: muted_def)
  apply (subst fairmerge.code; simp)
  apply (rule produced.Read[where n=3]; auto 0 0 simp: muted_def)
  apply (rule produced_Write; (auto simp: muted_def)?)
  apply (rule produced.ReadEOB; auto 0 0 simp: muted_def)
  apply (subst fairmerge.code; simp)
  apply (rule produced.ReadEOB; auto 0 0 simp: muted_def)
  apply (rule produced.Read[where n=3]; auto 0 0 simp: muted_def)
  apply (rule produced_Write; (auto simp: muted_def)?)
  apply (subst fairmerge.code; simp)
  apply (rule produced.Read[where n=3]; auto 0 0 simp: muted_def)
  apply (subst fairmerge.code; simp)
  apply (rule produced.Read[where n=3]; auto 0 0)
  done *)

lemma mergedL1_fueled_fairmerge: "mergedL1_fueled lns (lxs i) (lxs j) (lzs 1) \<Longrightarrow> i = 1 \<and> j = 2 \<or> i = 2 \<and> j = 1 \<Longrightarrow>
  produced (\<lambda>p. if p = j \<and> lns \<noteq> LNil then lhd lns else 0) (fairmerge False False) lxs lzs"
  (* apply (coinduction arbitrary: i j lns lxs lzs rule: produced_coinduct_upto)
  subgoal for i j lns lxs lzs
    apply (erule mergedL1_fueled.cases)
    subgoal for lxs'
      apply (elim disjE conjE)
       apply (rule disjI1)
       apply (subst fairmerge.code; simp add: muted_def)
       apply (rule exI[of _ 0])
       apply (rule produced_cong.produced; auto simp add: produced_fairmerge_True_False fun_eq_iff)
      apply (rule disjI1)
      apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
       apply (rule exI[of _ 0])
       apply (rule produced_cong.produced)
       apply (rule produced_Write[rotated])
         apply (rule produced.Read[rotated])
          apply (simp add: produced_fairmerge_False_True)
         apply (auto simp: fun_eq_iff muted_def) [3]
      apply (rule exI[of _ 0])
      apply (rule produced_cong.produced)
      apply (simp add: produced_fairmerge_True_False)
      apply (auto simp: fun_eq_iff) []
      done
    subgoal for lxs'
      apply (elim disjE conjE)
       apply (rule disjI1)
       apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
        apply (rule exI[of _ 0])
        apply (rule produced_cong.produced)
        apply (rule produced_Write[rotated])
          apply (rule produced.Read[rotated])
           apply (simp add: produced_fairmerge_False_True)
          apply (auto simp: fun_eq_iff muted_def) [3]
       apply (subst fairmerge.code; simp)
       apply (rule exI[of _ 0])
       apply (rule produced_cong.produced)
       apply (simp add: produced_fairmerge_True_False)
       apply (auto simp: fun_eq_iff) []
      apply (rule disjI1)
      apply (subst fairmerge.code; simp add: muted_def)
      apply (rule exI[of _ 0])
      apply (rule produced_cong.produced)
      apply (simp add: produced_fairmerge_True_False)
      apply (auto simp: fun_eq_iff) []
      done
    subgoal for n lns' lys lxs' lzs' x
      apply (elim disjE conjE)
       apply (simp_all split: if_splits)
         apply hypsubst_thin
         apply (cases "lns' = LNil")
      subgoal
        apply (rule disjI1)
        apply (erule mergedL1_fueled.cases; simp)
         apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
         apply (rule exI[of _ 0])
         apply (rule produced_cong.produced)
         apply (rule produced_Write[rotated])
           apply (rule produced.Read[rotated])
            apply (simp add: produced_fairmerge_False_True)
           apply (auto simp: fun_eq_iff muted_def) [3]
        apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
        apply (rule exI[of _ 0])
        apply (rule produced_cong.produced)
        apply (rule produced_Write[rotated])
          apply (rule produced.Read[rotated])
           apply (auto 0 0 simp add: muted_def produced_fairmerge_False_True fun_eq_iff
            split: observation.split elim!: chd.elims)
        apply (rule produced_Write[rotated])
          apply (auto simp: fun_eq_iff) [3]
        apply (subst fairmerge.code; auto split: observation.split elim!: chd.elims)
        apply (rule produced.Read[rotated])
         apply (auto 0 0 simp add: muted_def produced_fairmerge_True_False fun_eq_iff
            split: observation.split elim!: chd.elims)
        done
      subgoal
        apply (rule disjI1)
        apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
        apply (rule exI[of _ "lhd lns'"])
        apply (rule produced_cong.write[where lys' = "CTL 1 lzs"]; auto simp: fun_eq_iff)
        apply (rule produced_cong.read; auto simp: fun_eq_iff)
        apply (rule produced_cong.base)
        apply (auto intro: exI[of _ 2])
        done
        apply hypsubst_thin
      subgoal
        apply (rule disjI1)
        apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
        apply (rule exI[of _ 0])
        apply (rule produced_cong.write[where lys' = "CTL 1 lzs"]; auto simp: fun_eq_iff)
        apply (rule produced_cong.read; auto simp: fun_eq_iff)
        apply (rule produced_cong.base)
        apply (rule exI[of _ 1])
        apply (rule exI[of _ 2])
        apply (rule exI[of _ "LCons n lns'"])
        apply (rule conjI[rotated])
         apply (rule conjI[OF refl])
         apply (rule conjI)
          apply (auto intro: exI[of _ 1]) 
        done
       apply hypsubst_thin
       apply (cases "lns' = LNil")
      subgoal
        apply (rule disjI2)
        apply (rule disjI1)
        apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
        apply (rule produced_cong.produced)
          apply (rule produced.Read[rotated]; auto 0 0 split: observation.split elim!: chd.elims)
        apply (rule produced_Write[where lys = "CTL 1 lzs", rotated])
        apply (auto simp: fun_eq_iff elim: mergedL1_fueled.cases) [3]
        apply (subst fairmerge.code; auto split: observation.split elim!: chd.elims)
        apply (rule produced.Read[rotated]; auto 0 0 split: observation.split elim!: chd.elims)
        apply (rule produced_Write[where lys = "CTL 1 (CTL 1 lzs)", rotated])
        apply (rule produced.Read[rotated]; auto 0 0 split: observation.split elim!: chd.elims)
        apply (rule produced_Write[where lys = "CTL 1 (CTL 1 lzs)", rotated])
        apply (auto simp: muted_def fun_eq_iff produced_fairmerge_False_True produced_fairmerge_True_False elim: mergedL1_fueled.cases)
        done
      subgoal
        apply (rule disjI2)
        apply (rule disjI1)
        apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
        apply (rule produced_cong.read; auto simp: fun_eq_iff)
        apply (rule produced_cong.write[where lys' = "CTL 1 lzs"]; auto simp: fun_eq_iff)
        apply (rule produced_cong.base)
        apply (rule exI[of _ 1])
        apply (rule exI[of _ 2])
        apply (rule exI[of _ "lns'"])
        apply (rule conjI[rotated])
         apply (rule conjI[OF refl])
         apply (rule conjI)
          apply (auto intro: exI[of _ 2]) 
        done
      apply hypsubst_thin
      apply (rule disjI2)
      apply (rule disjI1)
      apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
      apply (rule produced_cong.read; auto simp: fun_eq_iff)
      apply (rule produced_cong.write[where lys' = "CTL 1 lzs"]; auto simp: fun_eq_iff)
      apply (rule produced_cong.base)
      apply (rule exI[of _ 2])
      apply (rule exI[of _ 1])
      apply (rule exI[of _ "LCons n lns'"])
      apply (rule conjI[rotated])
       apply (rule conjI[OF refl])
       apply (rule conjI)
        apply (auto intro: exI[of _ 2]) 
      done
    done
  done *)
  oops

(* lemma merged_fairmerge_False_False:
  "merged (lxs 1) (lxs 2) (lzs 1) \<Longrightarrow> \<lbrakk>fairmerge False False\<rbrakk> lxs lzs"
  unfolding merged_alt mergedL_alt mergedL_fueled_alt semantics_def
  using mergedL1_fueled_fairmerge[of _ lxs 1 2 lzs] mergedL1_fueled_fairmerge[of _ lxs 2 1 lzs]
  by blast *)

end