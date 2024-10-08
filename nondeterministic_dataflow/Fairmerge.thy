section \<open>The fair merge operator\<close>

theory Fairmerge

imports
  Operator
  Linear_Temporal_Logic_on_Llists
begin

lemma neq_1_conv_2[simp]: "p \<noteq> 1 \<longleftrightarrow> (p :: 2) = 2"
  apply (cases p)
  subgoal for z
    apply (cases z; simp)
    subgoal for n
      apply (cases n; simp)
      subgoal for n
        apply (cases n; simp)
        done
      done
    done
  done

lemma neq_2_conv_1[simp]: "p \<noteq> 2 \<longleftrightarrow> (p :: 2) = 1"
  apply (cases p)
  subgoal for z
    apply (cases z; simp)
    subgoal for n
      apply (cases n; simp)
      subgoal for n
        apply (cases n; simp)
        done
      done
    done
  done



corec fairmerge :: "bool \<Rightarrow> bool \<Rightarrow> (2, 1, 'd) op" where
  "fairmerge e1 e2 = (case (e1, e2) of
      (True, True) \<Rightarrow> End
    | (True, False) \<Rightarrow> ARead 2 (case_observation (Write (fairmerge e1 e2) 2) End) (fairmerge e1 e2))"

(* 
corec fairmerge :: "bool \<Rightarrow> bool \<Rightarrow> (2, 1, 'd) op" where
  "fairmerge e1 e2 = (case (e1, e2) of
      (True, True) \<Rightarrow> End
    | (True, False) \<Rightarrow> Read 2 (case_observation (Write (fairmerge e1 e2) 1) (fairmerge e1 e2) End)
    | (False, True) \<Rightarrow> Read 1 (case_observation (Write (fairmerge e1 e2) 1) (fairmerge e1 e2) End)
    | (False, False) \<Rightarrow>
      Read 1 (case_observation (Write (Read 2 (case_observation (Write (fairmerge e1 e2) 1) (fairmerge e1 e2) (fairmerge e1 True))) 1)
     (Read 2 (case_observation (Write (fairmerge e1 e2) 1) (fairmerge e1 e2) (fairmerge e1 True))) (fairmerge True e2)))" *)

end
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
       apply (rule disjI2)
       apply (rule exI conjI[rotated] disjI1 trace_fmFF_A1_I2 trace_fmFF_A2_I1 | assumption)+
       apply simp
      apply (rule disjI1)
      apply (rule exI conjI[rotated] disjI1 trace_fmFF_A1_I2 trace_fmFT_I | assumption)+
      apply simp
     apply (erule traced_ReadE; simp split: observation.splits)
       apply (erule traced_WriteE; simp)
       apply (rule disjI2)
       apply (rule exI conjI[rotated] disjI1 trace_fmFF_A1_I1 trace_fmFF_A2_I2 | assumption)+
       apply simp
      apply (rule disjI2)
      apply (rule exI conjI[rotated] disjI1 trace_fmFF_A1_I1 trace_fmFF_A2_I1 | assumption)+
      apply simp
     apply (rule disjI1)
     apply (rule exI conjI[rotated] disjI1 trace_fmFF_A1_I1 trace_fmFT_I | assumption)+
     apply simp
    apply (rule disjI1)
    apply (erule trace_fmTF_I)
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

lemma Inp_1_lset_trace_fmTF: "Inp (1 :: 2) x \<in> lset ios \<Longrightarrow> \<not> trace_fmTF ios"
  unfolding lset_conv_lnth mem_Collect_eq
  apply safe
  subgoal for n
    apply (induct n arbitrary: ios rule: less_induct)
    subgoal for n ios
      apply (cases n)
      apply (erule trace_fmTF.cases; auto)
      apply (erule trace_fmTF.cases; auto simp: enat_0[symmetric]
        simp: lnth_LCons' gr0_conv_Suc Suc_ile_eq split: if_splits)
      apply (metis less_add_Suc2 plus_1_eq_Suc)
      done
    done
  done

lemma trace_fmTF_lproject1: "trace_fmTF (ios :: (2, 1, 'd) IO llist) \<Longrightarrow> lproject (=) \<bottom> ios (1 :: 2) = LNil"
  by (erule trace_fmTF.cases)
    (auto simp: lproject_empty_conv Inp_1_lset_trace_fmTF simp del: neq_1_conv_2)

lemma eq_repeat_iff: "lxs = repeat x \<longleftrightarrow> lset lxs = {x} \<and> \<not> lfinite lxs"
  apply (safe; simp?)
  apply (coinduction arbitrary: lxs)
  apply (safe; simp?)
   apply force
  by (metis lfinite_ltl lnull_imp_lfinite lset_eq_empty lset_ltl subset_singletonD)

lemma trace_fmTF_lproject2: "trace_fmTF (ios :: (2, 1, 'd) IO llist) \<Longrightarrow> lproject (=) \<bottom> ios 2 = lproject \<bottom> (=) ios 1"
  apply (coinduction arbitrary: ios)
  subgoal for ios
    apply (cases "ios = repeat (Inp 2 EOB)")
    subgoal
      apply (auto simp: lproject_def)
      done
    subgoal
      apply (subgoal_tac "\<exists>n. llength (ltakeWhile ((=) (Inp 2 EOB)) ios) = enat n")
       apply (erule exE)
      subgoal for n
        apply (induct n arbitrary: ios)
        subgoal for ios
          apply (erule trace_fmTF.cases; auto simp: enat_0)
          done
        subgoal for x ios
          apply (erule trace_fmTF.cases; auto simp add: eq_repeat_iff simp flip: enat_0 eSuc_enat)
          done
        done
      using llength_ltakeWhile_eq_infinity'[of "((=) (Inp 2 EOB))" ios]
      apply (cases ios)
       apply (auto simp: eq_repeat_iff simp flip: enat_0)
      done
    done
  done

lemma lconcat_lmap: "lconcat (lmap (\<lambda>z. LNil) lxs) = LNil"
  by (coinduction arbitrary: lxs) auto

abbreviation "cp_trace p lzs \<equiv> lappend (lconcat (lmap (\<lambda>x. LCons (Inp p (Observed x)) (LCons (Out 1 x) LNil)) lzs)) (repeat (Inp p EOB))"

lemma history_fairmerge_True_False: "history (fairmerge True False) lxs lzs \<longleftrightarrow>
  lprefix (lzs 1) (lxs 2)"
  unfolding history_def traced_fairmerge_True_False
  apply (auto simp: fun_eq_iff trace_fmTF_lproject2[symmetric])
  apply (rule exI[of _ "cp_trace 2 (lzs 1)"])
  apply (intro conjI)
  subgoal premises prems
    apply (coinduction arbitrary: lzs)
    subgoal for lzs
      apply (cases "lzs 1")
       apply auto
      apply (smt (verit) iterates_lmap lappend_code(1) lconcat_LNil llist.simps(12) lmap_iterates)
      done
    done
  apply safe
  subgoal for p
    apply (cases "p = 1"; simp?)
  apply (cases "lfinite (lzs 1)")
      apply (auto simp: lproject_def lfilter_lconcat_lfinite lmap_lconcat llist.map_comp
        lconcat_lmap lappend_inf lfilter_lmap
      cong: llist.map_cong if_cong split: if_splits)
    apply (cases "lfinite (lzs 1)")
      apply (auto simp: lproject_def lfilter_lconcat_lfinite lmap_lconcat llist.map_comp
        lconcat_lmap lappend_inf lfilter_lmap
      cong: llist.map_cong if_cong split: if_splits)
    done
  subgoal premises prems
    apply (cases "lfinite (lzs 1)")
      apply (auto simp: lproject_def lfilter_lconcat_lfinite lmap_lconcat llist.map_comp
        lconcat_lmap lappend_inf lfilter_lmap
      cong: llist.map_cong if_cong split: if_splits)
    done
  done

lemma Inp_2_lset_trace_fmFT: "Inp (2 :: 2) x \<in> lset ios \<Longrightarrow> \<not> trace_fmFT ios"
  unfolding lset_conv_lnth mem_Collect_eq
  apply safe
  subgoal for n
    apply (induct n arbitrary: ios rule: less_induct)
    subgoal for n ios
      apply (cases n)
      apply (erule trace_fmFT.cases; auto)
      apply (erule trace_fmFT.cases; auto simp: enat_0[symmetric]
        simp: lnth_LCons' gr0_conv_Suc Suc_ile_eq split: if_splits)
      apply (metis less_add_Suc2 plus_1_eq_Suc)
      done
    done
  done

lemma trace_fmFT_lproject2: "trace_fmFT (ios :: (2, 1, 'd) IO llist) \<Longrightarrow> lproject (=) \<bottom> ios (2 :: 2) = LNil"
  by (erule trace_fmFT.cases)
    (auto simp: lproject_empty_conv Inp_2_lset_trace_fmFT simp del: neq_2_conv_1)

lemma trace_fmFT_lproject1: "trace_fmFT (ios :: (2, 1, 'd) IO llist) \<Longrightarrow> lproject (=) \<bottom> ios 1 = lproject \<bottom> (=) ios 1"
  apply (coinduction arbitrary: ios)
  subgoal for ios
    apply (cases "ios = repeat (Inp 1 EOB)")
    subgoal
      apply (auto simp: lproject_def)
      done
    subgoal
      apply (subgoal_tac "\<exists>n. llength (ltakeWhile ((=) (Inp 1 EOB)) ios) = enat n")
       apply (erule exE)
      subgoal for n
        apply (induct n arbitrary: ios)
        subgoal for ios
          apply (erule trace_fmFT.cases; auto simp: enat_0)
          done
        subgoal for x ios
          apply (erule trace_fmFT.cases; auto simp add: eq_repeat_iff simp flip: enat_0 eSuc_enat)
          done
        done
      using llength_ltakeWhile_eq_infinity'[of "((=) (Inp 1 EOB))" ios]
      apply (cases ios)
       apply (auto simp: eq_repeat_iff simp flip: enat_0)
      done
    done
  done

lemma history_fairmerge_False_True: "history (fairmerge False True) lxs lzs \<longleftrightarrow>
  lprefix (lzs 1) (lxs 1)"
  unfolding history_def traced_fairmerge_False_True
  apply (auto simp: fun_eq_iff trace_fmFT_lproject1[symmetric])
  apply (rule exI[of _ "cp_trace 1 (lzs 1)"])
  apply (intro conjI)
  subgoal premises prems
    apply (coinduction arbitrary: lzs)
    subgoal for lzs
      apply (cases "lzs 1")
       apply auto
      apply (smt (verit) iterates_lmap lappend_code(1) lconcat_LNil llist.simps(12) lmap_iterates)
      done
    done
  apply safe
  subgoal for p
    apply (cases "p = 1"; simp?)
  apply (cases "lfinite (lzs 1)")
      apply (auto simp: lproject_def lfilter_lconcat_lfinite lmap_lconcat llist.map_comp
        lconcat_lmap lappend_inf lfilter_lmap
      cong: llist.map_cong if_cong split: if_splits)
    apply (cases "lfinite (lzs 1)")
      apply (auto simp: lproject_def lfilter_lconcat_lfinite lmap_lconcat llist.map_comp
        lconcat_lmap lappend_inf lfilter_lmap
      cong: llist.map_cong if_cong split: if_splits)
    done
  subgoal premises prems
    apply (cases "lfinite (lzs 1)")
      apply (auto simp: lproject_def lfilter_lconcat_lfinite lmap_lconcat llist.map_comp
        lconcat_lmap lappend_inf lfilter_lmap
      cong: llist.map_cong if_cong split: if_splits)
    done
  done

coinductive merged where
  stop: "merged lxs lys LNil"
| left: "merged lxs lys lzs \<Longrightarrow> merged (LCons x lxs) lys (LCons x lzs)"
| right: "merged lxs lys lzs \<Longrightarrow> merged lxs (LCons y lys) (LCons y lzs)"

inductive_cases merged_LNilE[elim!]: "merged lxs lys LNil"
inductive_cases merged_LConsE[elim!]: "merged lxs lys (LCons z lzs)"

inductive merged_cong for R where
  mc_base: "R lxs lys lzs \<Longrightarrow> merged_cong R lxs lys lzs"
| mc_merged: "merged lxs lys lzs \<Longrightarrow> merged_cong R lxs lys lzs"
| mc_left: "merged_cong R lxs lys lzs \<Longrightarrow> merged_cong R (LCons x lxs) lys (LCons x lzs)"
| mc_right: "merged_cong R lxs lys lzs \<Longrightarrow> merged_cong R lxs (LCons y lys) (LCons y lzs)"

lemma merged_coinduct_upto:
  assumes X: "X lxs lys lzs"
      and CIH: "\<And>lxs lys lzs. X lxs lys lzs \<Longrightarrow> lzs = LNil \<or>
    (\<exists>lxs' lzs' x. lxs = LCons x lxs' \<and> lzs = LCons x lzs' \<and> merged_cong X lxs' lys lzs') \<or>
    (\<exists>lys' lzs' y. lys = LCons y lys' \<and> lzs = LCons y lzs' \<and> merged_cong X lxs lys' lzs')"
    shows "merged lxs lys lzs"
  apply (rule merged.coinduct[of "merged_cong X"])
   apply (rule mc_base, rule X)
  subgoal for lxs lys lzs
    apply (induct lxs lys lzs rule: merged_cong.induct)
    subgoal for lxs lys lzs
      by (drule CIH) auto
    subgoal for lxs lys lzs
      by (erule merged.cases) auto
    subgoal for lxs lys lzs x
      by auto
    subgoal for lxs lys lzs x
      by auto
    done
  done

lemma lprefix_merged1: "lprefix lzs lxs \<Longrightarrow> merged lxs lys lzs"
  by (coinduction arbitrary: lxs lzs) (erule lprefix.cases; auto)

lemma lprefix_merged2: "lprefix lzs lys \<Longrightarrow> merged lxs lys lzs"
  by (coinduction arbitrary: lys lzs) (erule lprefix.cases; auto)

corec merged_trace :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist \<Rightarrow> (2, 1, 'a) IO llist" where
  "merged_trace lxs lys lzs = (case lzs of
       LNil \<Rightarrow> LCons (Inp 1 EOB) (LCons (Inp 2 EOB) (merged_trace lxs lys lzs))
     | LCons z lzs' \<Rightarrow>
       if \<not> lnull lxs \<and> lhd lxs = z \<and> merged (ltl lxs) lys lzs' then LCons (Inp 1 (Observed z)) (LCons (Out 1 z) (LCons (Inp 2 EOB) (merged_trace (ltl lxs) lys lzs')))
       else LCons (Inp 1 EOB) (LCons (Inp 2 (Observed z)) (LCons (Out 1 z) (merged_trace lxs (ltl lys) lzs'))))"

lemma trace_fmFF_merged_trace: "merged lxs lys lzs \<Longrightarrow> trace_fmFF (merged_trace lxs lys lzs)"
  apply (coinduction arbitrary: lxs lys lzs)
  subgoal for lxs lys lzs
    apply (subst (1 2 3) merged_trace.code; auto simp: trace_fmFF_A1_def trace_fmFF_A2_def lnull_def split: llist.splits)
        apply (force intro: merged.intros)
    apply (metis (no_types, lifting) lshift_simps(2) range_eqI singleton_lshift)+
    done
  done

lemma in_lset_merged_trace_LNil[OF _ disjI1, OF _ refl]:
  "r \<in> lset lzs \<Longrightarrow> lzs = merged_trace lxs lys LNil \<or> lzs = LCons (Inp 2 EOB) (merged_trace lxs lys LNil) \<Longrightarrow> r = Inp 1 EOB \<or> r = Inp 2 EOB"
  apply (induct r lzs arbitrary: lxs lys rule: llist.set_induct)
   apply (subst (asm) merged_trace.code; auto)
  apply (subst (asm) (3) merged_trace.code; auto)
  done

lemma lnth_merged_trace:
  "lnth (merged_trace lxs lys lzs) n = r \<Longrightarrow> merged lxs lys lzs \<Longrightarrow>
   r \<in> {Inp 1 EOB, Inp (2 :: 2) EOB} \<union> Inp 1 ` Observed `  lset lxs \<union> Inp 2 ` Observed ` lset lys \<union> Out 1 ` lset lzs"
  apply (induct n arbitrary: lxs lys lzs rule: less_induct)
  subgoal for n lxs lys lzs
    apply (cases n)
     apply (subst (asm) (2) merged_trace.code; auto split: llist.splits if_splits)
    apply (subst (asm) (2) merged_trace.code; auto split: llist.splits)
         apply (auto simp add: lnth_LCons' lnull_def neq_LNil_conv image_iff not_le Suc_less_eq2 gr0_conv_Suc split: if_splits)
         apply (metis empty_iff less_add_Suc2 llist.set(1) plus_1_eq_Suc merged.stop)
        apply (metis less_Suc_eq)
       apply (metis eq_LConsD less_Suc_eq llist.set_cases)
      apply (metis less_Suc_eq)
     apply (metis eq_LConsD less_Suc_eq llist.set_cases)
    apply (metis less_Suc_eq)
    done
  done

lemma in_lset_merged_traceD:
  "r \<in> lset (merged_trace lxs lys lzs) \<Longrightarrow> merged lxs lys lzs \<Longrightarrow>
  r \<in> {Inp 1 EOB, Inp 2 EOB} \<union> Inp 1 ` Observed `  lset lxs \<union> Inp 2 ` Observed ` lset lys \<union> Out 1 ` lset lzs"
  unfolding in_lset_conv_lnth using lnth_merged_trace[of lxs lys lzs _ r]
  by auto

lemma lproject_merged_trace: "merged lxs lys lzs \<Longrightarrow> lproject \<bottom> (=) (merged_trace lxs lys lzs) (1 :: 1) = lzs"
  apply (coinduction arbitrary: lxs lys lzs rule: llist.coinduct_upto)
  subgoal for lxs lys lzs
    apply (subst (1 2 3 5) merged_trace.code; auto split: llist.splits)
         apply (auto simp add: lnull_def lproject_empty_conv intro: llist.cong_base dest!: in_lset_merged_traceD[OF _ merged.stop, simplified])
    done
  done

lemma lhd_merged_trace_1': "merged (LCons x lxs) lys lzs \<Longrightarrow>
  lnth (merged_trace (LCons x lxs) lys lzs) n = Inp 1 (Observed y) \<Longrightarrow>
  lhd (lproject (=) \<bottom> (merged_trace (LCons x lxs) lys lzs) 1) = x"
  apply (induct n arbitrary: lys lzs rule: less_induct)
  subgoal for n lys lzs
    apply (cases n)
    subgoal
      apply (subst merged_trace.code)
      apply (subst (asm) (3) merged_trace.code)
      apply (auto split: llist.splits)
      done
    subgoal for m
      subgoal
        apply (subst merged_trace.code)
        apply (subst (asm) (3) merged_trace.code)
        apply (auto simp: lnth_LCons' gr0_conv_Suc split: llist.splits if_splits)
          apply (meson less_Suc_eq merged.stop)
         apply (meson less_Suc_eq)
        apply (meson less_Suc_eq)
        done
      done
    done
  done

lemma ltl_merged_trace_1': "merged (LCons x lxs) lys lzs \<Longrightarrow>
  lnth (merged_trace (LCons x lxs) lys lzs) n = Inp 1 (Observed y) \<Longrightarrow>
  \<exists>lys' lzs'. ltl (lproject (=) \<bottom> (merged_trace (LCons x lxs) lys lzs) 1) = lproject (=) \<bottom> (merged_trace lxs lys' lzs') 1 \<and> merged lxs lys' lzs'"
  apply (induct n arbitrary: lys lzs rule: less_induct)
  subgoal for n lys lzs
    apply (cases n)
    subgoal
      apply (subst merged_trace.code)
      apply (subst (asm) (4) merged_trace.code)
      apply (auto split: llist.splits)
      done
    subgoal for m
      subgoal
        apply (subst merged_trace.code)
        apply (subst (asm) (4) merged_trace.code)
        apply (auto simp: lnth_LCons' gr0_conv_Suc split: llist.splits if_splits)
            apply (meson less_Suc_eq merged.stop)
           apply (meson less_Suc_eq)
          apply (meson less_Suc_eq)
         apply (meson less_Suc_eq)
        apply (meson less_Suc_eq)
        done
      done
    done
  done

lemma lhd_merged_trace_1: "merged (LCons x lxs) lys lzs \<Longrightarrow>
  Inp 1 (Observed y) \<in> lset (merged_trace (LCons x lxs) lys lzs) \<Longrightarrow>
  lhd (lproject (=) \<bottom> (merged_trace (LCons x lxs) lys lzs) 1) = x"
  unfolding in_lset_conv_lnth by (auto dest: lhd_merged_trace_1')

lemma ltl_merged_trace_1: "merged (LCons x lxs) lys lzs \<Longrightarrow>
  Inp 1 (Observed y) \<in> lset (merged_trace (LCons x lxs) lys lzs) \<Longrightarrow>
  \<exists>lys' lzs'. ltl (lproject (=) \<bottom> (merged_trace (LCons x lxs) lys lzs) 1) = lproject (=) \<bottom> (merged_trace lxs lys' lzs') 1 \<and> merged lxs lys' lzs'"
  unfolding in_lset_conv_lnth by (auto dest: ltl_merged_trace_1')

lemma merged_lprefix_1: "merged lxs lys lzs \<Longrightarrow> lprefix (lproject (=) \<bottom> (merged_trace lxs lys lzs) 1) lxs"
  apply (coinduction arbitrary: lxs lys lzs rule: lprefix_coinduct)
  subgoal for lxs lys lzs
    apply (subst (1 2 3 4) merged_trace.code; auto 0 3 simp add: lnull_def lproject_empty_conv neq_LNil_conv merged.stop lhd_merged_trace_1
        dest: in_lset_merged_trace_LNil in_lset_merged_traceD ltl_merged_trace_1 split: llist.splits)
    done
  done

lemma lhd_merged_trace_2': "merged lxs (LCons y lys) lzs \<Longrightarrow>
  lnth (merged_trace lxs (LCons y lys) lzs) n = Inp 2 (Observed x) \<Longrightarrow>
  lhd (lproject (=) \<bottom> (merged_trace lxs (LCons y lys) lzs) 2) = y"
  apply (induct n arbitrary: lxs lzs rule: less_induct)
  subgoal for n lxs lzs
    apply (cases n)
    subgoal
      apply (subst merged_trace.code)
      apply (subst (asm) (3) merged_trace.code)
      apply (auto split: llist.splits)
      done
    subgoal for m
      subgoal
        apply (subst merged_trace.code)
        apply (subst (asm) (3) merged_trace.code)
        apply (auto simp: lnth_LCons' gr0_conv_Suc split: llist.splits if_splits)
          apply (meson less_Suc_eq merged.stop)
         apply (meson less_Suc_eq)
        apply (meson less_Suc_eq)
        done
      done
    done
  done

lemma ltl_merged_trace_2': "merged lxs (LCons y lys) lzs \<Longrightarrow>
  lnth (merged_trace lxs (LCons y lys) lzs) n = Inp 2 (Observed x) \<Longrightarrow>
  \<exists>lxs' lzs'. ltl (lproject (=) \<bottom> (merged_trace lxs (LCons y lys) lzs) 2) = lproject (=) \<bottom> (merged_trace lxs' lys lzs') 2 \<and> merged lxs' lys lzs'"
  apply (induct n arbitrary: lxs lzs rule: less_induct)
  subgoal for n lys lzs
    apply (cases n)
    subgoal
      apply (subst merged_trace.code)
      apply (subst (asm) (4) merged_trace.code)
      apply (auto split: llist.splits)
      done
    subgoal for m
      subgoal
        apply (subst merged_trace.code)
        apply (subst (asm) (4) merged_trace.code)
        apply (auto simp: lnth_LCons' gr0_conv_Suc split: llist.splits if_splits)
            apply (meson less_Suc_eq merged.stop)
           apply (meson less_Suc_eq)
          apply (meson less_Suc_eq)
        done
      done
    done
  done

lemma lhd_merged_trace_2: "merged lxs (LCons y lys) lzs \<Longrightarrow>
  Inp 2 (Observed x) \<in> lset (merged_trace lxs (LCons y lys) lzs) \<Longrightarrow>
  lhd (lproject (=) \<bottom> (merged_trace  lxs (LCons y lys) lzs) 2) = y"
  unfolding in_lset_conv_lnth by (auto dest: lhd_merged_trace_2')

lemma ltl_merged_trace_2: "merged lxs (LCons y lys) lzs \<Longrightarrow>
  Inp 2 (Observed x) \<in> lset (merged_trace lxs (LCons y lys) lzs) \<Longrightarrow>
  \<exists>lxs' lzs'. ltl (lproject (=) \<bottom> (merged_trace lxs (LCons y lys) lzs) 2) = lproject (=) \<bottom> (merged_trace lxs' lys lzs') 2 \<and> merged lxs' lys lzs'"
  unfolding in_lset_conv_lnth by (auto dest: ltl_merged_trace_2')

lemma merged_lprefix_2: "merged lxs lys lzs \<Longrightarrow> lprefix (lproject (=) \<bottom> (merged_trace lxs lys lzs) 2) lys"
  apply (coinduction arbitrary: lxs lys lzs rule: lprefix_coinduct)
  subgoal for lxs lys lzs
    apply (subst (1 2 3 4) merged_trace.code; auto 0 3 simp add: lnull_def lproject_empty_conv neq_LNil_conv merged.stop lhd_merged_trace_2
        dest: in_lset_merged_trace_LNil in_lset_merged_traceD ltl_merged_trace_2 split: llist.splits)
    done
  done

lemma history_fairmerge_False_False: "history (fairmerge False False) lxs lzs \<longleftrightarrow> merged (lxs 1) (lxs 2) (lzs 1)"
  unfolding history_def traced_fairmerge_False_False
  apply safe
  subgoal for ios
    apply hypsubst_thin
    apply (coinduction arbitrary: lxs ios rule: merged_coinduct_upto)
    subgoal premises prems for lxs ios
    proof (cases "\<exists>n. llength (ltakeWhile ((=) (Inp 1 EOB) \<squnion> (=) (Inp 2 EOB)) ios) = enat n")
      case True
      then show ?thesis
        using prems
        apply (elim exE)
        subgoal for n
          apply (induct n arbitrary: ios rule: less_induct)
          subgoal premises prems for n ios
            using prems(2-)
            apply (cases n)
            apply (erule trace_fmFF.cases)
              apply (simp_all add: enat_0)
            subgoal for lxs'
              apply (cases "lproject \<bottom> (=) lxs' 1"; simp)
              apply (rule disjI2)
              apply (smt (verit, best) LCons_lprefix_conv lprefix_merged2 mc_merged trace_fmTF_lproject2)
              done
            unfolding trace_fmFF_A1_def trace_fmFF_A2_def
             apply (elim UnE insertE emptyE imageE; hypsubst_thin; simp)
            subgoal for lxs' x
              apply (smt (verit, ccfv_SIG) LCons_lprefix_conv bot2E lprefix_merged1 lproject_LCons(2) lproject_LCons(3) mc_merged trace_fmFT_lproject1)
              done
            apply (elim UnE insertE emptyE imageE; hypsubst_thin; simp add: null_def)
             apply (frule spec[of _ 1]; frule spec[of _ 2]; simp)
             apply (rule disjI1)
             apply (simp add: LCons_lprefix_conv)
             apply (erule exE conjE)+
            subgoal for lxs' x ys'
              apply (rule exI conjI | assumption)+
              apply (rule mc_base)
              apply (rule exI[of _ "lxs(1 := ys')"])
              apply simp
              apply (rule exI conjI refl)+
               apply assumption
              apply auto
              done
            apply (frule spec[of _ 1]; frule spec[of _ 2]; simp)
            apply (simp add: LCons_lprefix_conv)
            apply (erule exE conjE)+
            apply simp
            apply (rule disjI1)
            apply (rule mc_right)
            apply (rule mc_base)
            subgoal for lxs' x y lxs'' lys''
              apply (rule exI[of _ "\<lambda>p. if p = 1 then lxs'' else lys''"])
              apply simp
              apply (rule exI conjI refl)+
               apply assumption
              apply simp
              done
            subgoal for m
              apply (erule trace_fmFF.cases)
                apply (simp_all add: enat_0[symmetric] trace_fmFF_A1_def trace_fmFF_A2_def)
               apply (elim disjE imageE; hypsubst_thin; simp add: null_def enat_0[symmetric] eSuc_enat)
               apply (metis (no_types, lifting) lprefix.cases lprefix_merged1 mc_merged trace_fmFT_lproject1)
              apply (elim disjE imageE; hypsubst; simp add: null_def enat_0[symmetric] eSuc_enat eSuc_enat_iff)
              using prems(1)
               apply (elim exE conjE; hypsubst_thin; simp)
              using less_Suc_eq apply blast
              apply (rule disjI2)
              apply (frule spec[of _ 1]; frule spec[of _ 2]; simp)
              apply (simp add: LCons_lprefix_conv)
              apply (elim exE conjE)
              apply (rule exI conjI | assumption)+
              apply (rule mc_base)
              subgoal for lxs' y lys'
                apply (rule exI[of _ "lxs(2 := lys')"]; simp)
                apply auto
                done
              done
            done
          done
        done
    next
      case False
      then show ?thesis
        by (auto simp: llength_ltakeWhile_eq_infinity' lproject_empty_conv)
    qed
    done
  subgoal
    unfolding fun_eq_iff
    apply (rule exI[of _ "merged_trace (lxs 1) (lxs 2) (lzs 1)"] conjI trace_fmFF_merged_trace allI | assumption)+
    subgoal for p
      apply (cases "p = 1")
       apply (auto simp: merged_lprefix_1 merged_lprefix_2)
      done
    apply (auto simp: lproject_merged_trace)
    done
  done

end