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

lemma traced_fairmerge_True_True: "traced m (fairmerge True True) lxs \<longleftrightarrow> lxs = LNil"
  by (subst fairmerge.code) (auto intro: traced.intros)

inductive alw_cong for R \<phi> where
  ac_base: "R ps xs \<Longrightarrow> alw_cong R \<phi> ps xs"
| ac_alw: "alw \<phi> ps xs \<Longrightarrow> alw_cong R \<phi> ps xs"
| ac_LCons: "\<phi> ps (LCons y ys) \<Longrightarrow> alw_cong R \<phi> (y # ps) ys \<Longrightarrow> alw_cong R \<phi> ps (LCons y ys)"

lemma alw_coinduct_upto:
  assumes "X ps xs"
    "(\<And>ps xs. X ps xs \<Longrightarrow> (xs = LNil \<and> \<phi> ps LNil) \<or>
       (\<exists>y ys. xs = LCons y ys \<and> \<phi> ps (LCons y ys) \<and> (alw_cong X \<phi> (y # ps) ys)))"
  shows "alw \<phi> ps xs"
  apply (rule alw.coinduct[OF alw_cong.intros(1)[where R = X and \<phi> = \<phi>]], rule assms(1))
  subgoal for ps xs
    apply (induct ps xs rule: alw_cong.induct)
      apply (auto dest: assms(2))
    done
  done

lemma traced_fairmerge_True_False_aux1: "traced m (fairmerge True False) lxs \<Longrightarrow>
  alw (now ((=) (Inp 2 (Observed x))) imp nxt (now ((=) (Out 1 x)))) ps lxs"
  apply (coinduction arbitrary: ps lxs m rule: alw_coinduct_upto)
  subgoal for ps lxs m
    apply (subst (asm) fairmerge.code)
    apply simp
    apply (erule traced_ReadE; simp)
      apply (rule conjI impI)+
       apply hypsubst_thin
       apply auto []
      apply (erule traced_WriteE; simp)
      apply (rule ac_LCons)
       apply auto []
      apply (rule ac_base)
      apply auto []
     apply (auto simp flip: now_eq1 intro!: ac_alw alw.intros) []
    apply (rule ac_base)
    apply auto []
    done
  done

lemma traced_fairmerge_True_False_aux2: "traced m (fairmerge True False) lxs \<Longrightarrow>
  alw (now ((=) (Out 1 x)) imp prv (now ((=) (Inp 2 (Observed x))))) ps lxs"
  apply (coinduction arbitrary: ps lxs m rule: alw_coinduct_upto)
  subgoal for ps lxs m
    apply (subst (asm) fairmerge.code)
    apply simp
    apply (erule traced_ReadE; simp)
      apply (erule traced_WriteE; simp)
      apply (rule ac_LCons)
       apply auto []
      apply (rule ac_base)
      apply auto []
     apply (auto simp flip: now_eq1 intro!: ac_alw alw.intros) []
    apply (rule ac_base)
    apply auto []
    done
  done

lemma traced_fairmerge_True_False_aux3:
  "traced m (fairmerge True False) lxs \<Longrightarrow>
   \<exists>x. evt (now ((=) (Inp 2 x))) ps lxs \<and> x \<noteq> EOB"
  apply (induct "m 2" arbitrary: m ps lxs)
   apply (subst (asm) fairmerge.code)
   apply simp
   apply (erule traced_ReadE; simp)
    apply ((rule exI conjI; auto)+) [2]
   apply (subst (asm) (2) fairmerge.code)
   apply simp
  apply (erule traced_ReadE; simp)
    apply ((rule exI conjI; auto)+) [2]
  apply (metis evt.intros(2) fun_upd_def)
  done

lemma traced_fairmerge_True_False_aux4: "traced m (fairmerge True False) lxs \<Longrightarrow>
  alw (now ((=) (Inp 2 EOS)) imp not (nxt (now \<top>))) ps lxs"
  apply (coinduction arbitrary: ps lxs m rule: alw_coinduct_upto)
  subgoal for ps lxs m
    apply (subst (asm) fairmerge.code)
    apply simp
    apply (erule traced_ReadE; simp)
      apply (erule traced_WriteE; simp)
       apply hypsubst_thin
      apply (rule ac_LCons)
       apply auto []
      apply (rule ac_base)
      apply auto []
     apply (auto simp flip: now_eq1 intro!: ac_alw alw.intros) []
    apply (rule ac_base)
    apply auto []
    done
  done

lemma traced_fairmerge_True_FalseI: "
  \<exists>x. evt (now ((=) (Inp 2 x))) [] lxs \<and> x \<noteq> EOB \<Longrightarrow>
  \<forall>x. Inp 1 x \<notin> lset lxs \<Longrightarrow>
  alw (now ((=) (Inp 2 EOS)) imp not (nxt (now \<top>))) [] lxs \<Longrightarrow>
  alw (now ((=) (Inp 2 (Observed x))) imp nxt (now ((=) (Out 1 x)))) [] lxs \<Longrightarrow>
  alw (now ((=) (Out 1 x)) imp prv (now ((=) (Inp 2 (Observed x))))) [] lxs \<Longrightarrow>
  traced m (fairmerge True False) lxs"
  oops

find_theorems cleaned alw

section\<open>Correctness using the history model\<close>

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