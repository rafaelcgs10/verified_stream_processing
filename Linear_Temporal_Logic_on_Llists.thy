section \<open>Linear Temporal Logic on Lazy Lists\<close>

theory Linear_Temporal_Logic_on_Llists
  imports 
    "Coinductive.Coinductive_List"
    "HOL-Library.BNF_Corec"
begin

section\<open>Linear temporal logic\<close>

text \<open>Propositional connectives:\<close>

abbreviation (input) IMPL (infix "imp" 60)
  where "\<phi> imp \<psi> \<equiv> \<lambda> ps xs. \<phi> ps xs \<longrightarrow> \<psi> ps xs"

abbreviation (input) OR (infix "dsj" 60)
  where "\<phi> dsj \<psi> \<equiv> \<lambda> ps xs. \<phi> ps xs \<or> \<psi> ps xs"

abbreviation (input) AND (infix "cnj" 60)
  where "\<phi> cnj \<psi> \<equiv> \<lambda> ps xs. \<phi> ps xs \<and> \<psi> ps xs"

abbreviation (input) not where "not \<phi> \<equiv> \<lambda> ps xs. \<not> \<phi> ps xs"

abbreviation (input) "tru \<equiv> \<lambda> xs ps. True"

abbreviation (input) "fls \<equiv> \<lambda> xs ps. False"

lemma imp_not_or: "\<phi> imp \<psi> = (not \<phi>) dsj \<psi>"
  by blast

lemma not_or: "not (\<phi> dsj \<psi>) = (not \<phi>) cnj (not \<psi>)"
  by auto

lemma not_cnj: "not (\<phi> cnj \<psi>) = (not \<phi>) dsj (not \<psi>)"
  by blast

lemma non_not[simp]: "not (not \<phi>) = \<phi>" by simp

text \<open>Temporal (LTL) connectives:\<close>

fun now where
  "now P ps LNil = False"
| "now P ps (LCons x xs) = P x"

fun wow where
  "wow P ps LNil = True"
| "wow P ps (LCons x xs) = P x"

fun nxt where
  "nxt \<phi> ps LNil = \<phi> ps LNil"
| "nxt \<phi> ps (LCons x xs) = \<phi> (x#ps) xs"

fun prv where
  "prv \<phi> [] xs = False"
| "prv \<phi> (x#ps) xs = \<phi> ps (LCons x xs)"

definition "HLD s = now (\<lambda>x. x \<in> s)"

abbreviation HLD_nxt (infixr "\<cdot>" 65) where
  "s \<cdot> P \<equiv> HLD s cnj nxt P"

context
  notes [[inductive_internals]]
begin

inductive evt for \<phi> where
  evt_base: "\<phi> ps xs \<Longrightarrow> evt \<phi> ps xs"
| evt_step: "evt \<phi> (x#ps) (xs) \<Longrightarrow> evt \<phi> ps (LCons x xs)"

inductive_cases evt_baseE: "evt \<phi> ps xs"
inductive_cases evt_stepE: "evt \<phi> ps (LCons x xs)"

coinductive alw for \<phi> where
  LNil_all[simp]: "alw \<phi> ps LNil"
| alw_step: "\<lbrakk>\<phi> ps (LCons x xs); alw \<phi> (x#ps) xs\<rbrakk> \<Longrightarrow> alw \<phi> ps (LCons x xs)"

inductive_cases LNil_allE: "alw \<phi> ps LNil"
inductive_cases alwE: "alw \<phi> ps (LCons x xs)"

inductive onc for \<phi> where
  onc_base: "\<phi> ps xs \<Longrightarrow> onc \<phi> ps xs"
| onc_step: "onc \<phi> ps (LCons x xs) \<Longrightarrow> onc \<phi> (x#ps) xs"

inductive_cases onc_baseE: "onc \<phi> ps xs"
inductive_cases onc_stepE: "onc \<phi> (x#ps) xs"

inductive hst for \<phi> where
  Nil_all[simp]: "hst \<phi> [] xs"
| hst_step: "\<lbrakk>\<phi> (x#ps) xs; hst \<phi> ps (LCons x xs)\<rbrakk> \<Longrightarrow> hst \<phi> (x#ps) xs"

inductive_cases Nil_allE: "hst \<phi> [] xs"
inductive_cases hstE: "hst \<phi> (x#ps) xs"

end

lemma alw_LConsD: "alw P ps (LCons x xs) \<Longrightarrow> alw P (x#ps) xs"
  by (meson alwE)

lemma alw_headD: "alw P ps (LCons x xs) \<Longrightarrow> P ps (LCons x xs)"
  using alw.cases by blast

lemma alw_LCons_iff: "alw P ps (LCons x xs) \<longleftrightarrow> alw P (x#ps) xs \<and> P ps (LCons x xs)"
  by (metis alw.simps eq_LConsD) 

lemma hst_LCons_iff: "hst P (x#ps) xs \<longleftrightarrow> hst P ps (LCons x xs) \<and> P (x#ps) xs"
  by (metis hstE hst_step)

lemma alw_eq_fun:
  "alw P ps xs \<Longrightarrow> P = Q \<Longrightarrow> alw Q ps xs"
  by simp

lemma now_mono:
  assumes now: "now P ps xs" and 0: "\<And> x ps. P x \<Longrightarrow> Q x"
  shows "now Q ps xs"
  using assms by (metis now.simps(1) now.simps(2) llist.exhaust)

lemma wow_mono:
  assumes wow: "wow P ps xs" and 0: "\<And> x. P x \<Longrightarrow> Q x"
  shows "wow Q ps xs"
  using assms by (metis wow.simps(1) wow.simps(2) llist.exhaust)

lemma HLD_iff: "\<omega> \<noteq> LNil \<Longrightarrow> HLD s ps \<omega> \<longleftrightarrow> lhd \<omega> \<in> s"
  using HLD_def by (metis now.simps(2) llist.exhaust_sel)

lemma HLD_LCons[simp]: "HLD X ps (LCons x \<omega>) \<longleftrightarrow> x \<in> X"
  by (simp add: HLD_iff)

lemma nxt_mono:
  assumes nxt: "nxt \<phi> ps xs" and 0: "\<And> xs ps. \<phi> ps xs \<Longrightarrow> \<psi> ps xs"
  shows "nxt \<psi> ps xs"
  using assms by (metis nxt.elims nxt.simps(2))

declare evt.intros[intro]
declare onc.intros[intro]
declare alw.cases[elim]

lemma alw_coinduct[consumes 1, case_names alw ltl]:
  "P ps xs \<Longrightarrow> (\<And>x ps. P ps x \<Longrightarrow> \<phi> ps x) \<Longrightarrow> (\<And>xs ps x. P ps (LCons x xs) \<Longrightarrow> \<not> alw \<phi> (x#ps) xs \<Longrightarrow> P (x#ps) xs) \<Longrightarrow> alw \<phi> ps xs"
  using alw.coinduct[of P ps xs \<phi>] 
  by (metis neq_LNil_conv)

lemma evt_mono:
  assumes evt: "evt \<phi> ps xs" and 0: "\<And> xs ps. \<phi> ps xs \<Longrightarrow> \<psi> ps xs"
  shows "evt \<psi> ps xs"
  using evt by induct (auto simp: 0)

lemma alw_mono:
  assumes alw: "alw \<phi> ps xs" and 0: "\<And> xs ps. \<phi> ps xs \<Longrightarrow> \<psi> ps xs"
  shows "alw \<psi> ps xs"
  using alw by coinduct (auto simp: 0)

lemma onc_mono:
  assumes onc: "onc \<phi> ps xs" and 0: "\<And> xs ps. \<phi> ps xs \<Longrightarrow> \<psi> ps xs"
  shows "onc \<psi> ps xs"
  using onc by induct (auto simp: 0)

lemma hst_mono:
  assumes hst: "hst \<phi> ps xs" and 0: "\<And> xs ps. \<phi> ps xs \<Longrightarrow> \<psi> ps xs"
  shows "hst \<psi> ps xs"
  using hst apply induct 
  by (auto simp add: 0 hst_step)

lemma alw_cnj: "alw (\<phi> cnj \<psi>) = alw \<phi> cnj alw \<psi>"
proof-
  {fix ps xs assume "alw (\<phi> cnj \<psi>) ps xs" hence "(alw \<phi> cnj alw \<psi>) ps xs"
      by (auto elim: alw_mono)
  }
  moreover
  {fix ps xs assume "(alw \<phi> cnj alw \<psi>) ps xs" hence "alw (\<phi> cnj \<psi>) ps xs"
      by coinduct auto
  }
  ultimately show ?thesis by blast
qed

lemma evt_nxt: "evt \<phi> ps xs = (\<phi> dsj nxt (evt \<phi>)) ps xs"
  by (metis (no_types, lifting) evt.simps nxt.elims nxt.simps(2))

lemma onc_prv: "onc \<phi> ps xs = (\<phi> dsj prv (onc \<phi>)) ps xs"
  by (metis onc.simps prv.elims(2) prv.simps(2))

lemma alw_nxt: "xs \<noteq> LNil \<Longrightarrow> alw \<phi> ps xs = (\<phi> cnj nxt (alw \<phi>)) ps xs"
  by (metis (mono_tags, lifting) alw_LCons_iff nxt.elims)

lemma hst_prv: "ps \<noteq> Nil \<Longrightarrow> hst \<phi> ps xs = (\<phi> cnj prv (hst \<phi>)) ps xs"
  by (metis hst.simps prv.elims(1) prv.simps(2))

lemma evt_evt[simp]: "evt (evt \<phi>) ps xs = evt \<phi> ps xs"
proof-
  {fix xs ps
    assume "evt (evt \<phi>) ps xs" hence "evt \<phi> ps xs"
      by induct auto
  }
  thus ?thesis  apply (cases xs)
    by blast+
qed

lemma alw_alw[simp]: "alw (alw \<phi>) = alw \<phi>"
proof-
  {fix xs ps
    assume "alw \<phi> ps xs" hence "alw (alw \<phi>) ps xs"
      by coinduct auto
  }
  thus ?thesis using LNil_all by fastforce
qed

lemma onc_onc[simp]: "onc (onc \<phi>) ps xs = onc \<phi> ps xs"
proof-
  {fix xs ps
    assume "onc (onc \<phi>) ps xs" hence "onc \<phi> ps xs"
      by induct auto
  }
  thus ?thesis  apply (cases xs)
    by blast+
qed

corec (friend) lshift :: "'a list \<Rightarrow> 'a llist \<Rightarrow> 'a llist" (infixr \<open>@@-\<close> 65) where
  "lshift xs ys = (case xs of [] \<Rightarrow> (case ys of LNil \<Rightarrow> LNil | LCons y' ys' \<Rightarrow> LCons y' ys') | x#xs \<Rightarrow> LCons x (lshift xs ys))"

lemma lshift_simps[simp]:
  "lshift [] lxs = lxs"
  "lshift (x#xs) lxs = LCons x (lshift xs lxs)"
  by (subst lshift.code; auto split: llist.splits)+

lemma snoc_shift[simp]: "(xs @ [x]) @@- ws = xs @@- LCons x ws"
  by (induct xs) auto

lemma shift_in_list: "xs @@- xxs = LCons x ys \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> x \<in> set xs"
  apply (induct xs)
   apply simp_all
  done

lemma shift_LNil[simp]:
  "xs @@- LNil = llist_of xs"
  apply (induct xs)
   apply simp_all
  done

lemma in_lset_shift_eq: "v \<in> lset (xs @@- lxs) \<longleftrightarrow> v \<in> set xs \<or> v \<in> lset lxs"
  apply safe
  subgoal
    apply (induct xs arbitrary: lxs)
     apply simp
    apply simp
    apply safe
    apply blast
    done
  subgoal
    apply (induct xs arbitrary: lxs)
     apply simp_all
    apply (elim disjE)
     apply simp_all
    done
  subgoal
    apply (induct xs arbitrary: lxs)
     apply simp_all
    done
  done

lemma lset_shift[simp]: "lset (xs @@- lxs) = set xs \<union> lset lxs"
  by (auto simp add: in_lset_shift_eq)

lemma LNil_eq_shift_iff:
  "LNil = xs @@- ys \<longleftrightarrow> xs = [] \<and> ys = LNil"
  apply (induct xs arbitrary: ys)
  by auto

lemma ldrop_shift: "ldrop i (w @@- s) = drop i w @@- ldrop (i - length w) s"
  apply (induct i arbitrary: w s)
  using zero_enat_def apply force
  by (metis (no_types, lifting) Cons_nth_drop_Suc Suc_pred diff_Suc_Suc diff_zero drop.simps(1) drop0 drop_Suc eSuc_enat ldrop_simps(3) length_drop length_greater_0_conv list.size(3) lshift_simps(1) lshift_simps(2))

lemma lmap_shift: "lmap f (w @@- s) = map f w @@- lmap f s"
  apply (induct w)
   apply simp
  apply simp
  done

lemma ldropn_shift: "ldropn i (w @@- s) = drop i w @@- ldropn (i - length w) s"
  by (metis ldrop_enat ldrop_shift)

lemma lshift_append[simp]:
  "(hs1 @ hs2) @@- ws = hs1 @@- hs2 @@- ws"
  apply (induct "hs1" arbitrary: hs2 ws)
   apply simp
  apply simp
  done

lemma shfit_same_prefix:
  "xs @@- lxs = xs @@- lys \<Longrightarrow> lxs = lys"
  apply (induct xs)
   apply simp
  by simp

lemma  shift_LCons_Cons:
  "(x1 # xs) @@- lxs = LCons x2 lxs' \<Longrightarrow> x1 = x2 \<and> (xs @@- lxs) = lxs'"
  by simp

lemma lnull_shift[simp]:
  "lnull (xs @@- lxs) = (List.null xs \<and> lnull lxs)"
  by (metis LNil_eq_shift_iff llist.disc(1) llist.expand null_def)


lemma shift_eq_shift_drop_length:
  "length xs < length ys \<Longrightarrow>
   xs @@- lxs = ys @@- lys \<Longrightarrow> lxs = (drop (length xs) ys) @@- lys"
  apply (induct xs arbitrary: lxs lys ys)
   apply auto[1]
  subgoal for a xs lxs lys ys
    apply (cases ys)
     apply auto[1]
    apply simp
    done
  done

lemma shift_eq_shift_ldropn_length:
  "length ys < length zs \<Longrightarrow>
   xs @@- lxs = ys @@- lys \<Longrightarrow> lxs = ldropn (length xs) (ys @@- lys)"
  apply (induct xs arbitrary: lxs lys ys)
   apply auto[1]
  subgoal for a xs lxs lys ys
    apply (cases ys)
     apply auto[1]
     apply (metis length_greater_0_conv list.size(3) lshift_simps(1))
    apply simp
    done
  done

lemma shift_eq_shift_ldropn_length_2:
  "length xs < length ys \<Longrightarrow>
   xs @@- lxs = ys @@- lys \<Longrightarrow> lys = ldropn ((length ys - length xs)) lxs"
  apply (induct xs arbitrary: lxs lys ys)
   apply (simp add: ldropn_shift)
  subgoal for a xs lxs lys ys
    apply (cases ys)
     apply auto[1]
    apply simp
    done
  done

lemma shift_same_prefix:
  "length xs = length ys \<Longrightarrow> xs @@- lxs = ys @@- lys \<Longrightarrow> xs = ys \<and> lxs = lys"
  apply (induct xs arbitrary: lxs lys ys)
   apply (simp add: ldropn_shift)
  subgoal for a xs lxs lys ys
    apply (cases ys)
     apply auto[1]
    apply simp
    done
  done

lemma lfinite_shift[simp]:
  "lfinite (xs @@- lxs) = lfinite lxs"
  apply (induct xs)
   apply auto
  done

lemma llength_shift:
  "llength (xs @@- lxs) = length xs + llength lxs"
  apply (induct xs arbitrary: lxs)
  using zero_enat_def apply auto[1]
  apply simp
  apply (metis eSuc_enat eSuc_plus)
  done

lemma lnth_shift:
  "n < length xs \<Longrightarrow>
   lnth (xs @@- lxs) n = xs ! n"
  apply (induct xs arbitrary: n lxs)
   apply auto[1]
  apply simp
  using less_Suc_eq_0_disj apply fastforce
  done

lemma alw_shift:
  assumes "alw \<phi> ps (xs @@- lxs)"
  shows "alw \<phi> (rev xs@ps) lxs"
  using assms apply - 
  apply (induct xs arbitrary: ps lxs)
   apply auto
  done

lemma shift_shift:
  "xs @@- (ys @@- zs) = (xs @ ys) @@- zs"
  by (induct xs) auto

lemma LCons_shift:
  "LCons y (ys @@- lxs) = LCons x (xs @@- lxs) \<Longrightarrow>
   y = x"
  by blast

lemma alw_ldropn:
  assumes "alw \<phi> ps xs" shows "alw \<phi> (rev (list_of (ltake n xs))@ps) (ldropn n xs)"
  using assms apply -
  apply (induct n arbitrary: xs ps)
   apply (simp_all add: enat_0)
  subgoal for n xs ps
    apply (cases xs)
     apply (auto simp flip: eSuc_enat)
    done
  done

lemma nxt_ldropn: "(nxt ^^ n) \<phi> ps xs \<longleftrightarrow> \<phi> (rev (list_of (ltake n xs))@ps) (ldropn n xs)"
  apply (induct n arbitrary: xs ps)
   apply (simp_all add: enat_0)
  subgoal for n xs ps
    apply (cases xs)
     apply (auto simp flip: eSuc_enat)
    done
  done

lemma prv_implies_ldropn: "(prv ^^ n) \<phi> ps xs \<Longrightarrow> \<phi> (drop n ps) ((rev (take n ps)) @@- xs)"
  apply (induct n arbitrary: xs ps)
   apply (simp_all add: enat_0)
  subgoal for n xs ps
    apply (cases ps)
     apply auto
    done
  done

lemma ldropn_implies_prv: 
  "\<phi> (drop n ps) ((rev (take n ps)) @@- xs) \<Longrightarrow>
   n < length ps \<Longrightarrow>
   (prv ^^ n) \<phi> ps xs"
  apply (induct n arbitrary: xs ps)
   apply (simp_all add: enat_0)
  subgoal for n xs ps
    apply (cases ps)
     apply auto
    done
  done

lemma evt_shift:
  assumes "evt \<phi> (rev xl @ ps) xs"
  shows "evt \<phi> ps (xl @@- xs)"
  using assms apply -
  apply (induct xl arbitrary: ps xs)
   apply auto
  done

lemma onc_shift:
  assumes"onc \<phi> ps (xl @@- xs)"
  shows "onc \<phi> (rev xl @ ps) xs"
  using assms apply -
  apply (induct xl arbitrary: ps xs)
   apply auto
  done

lemma evt_imp_shift:
  assumes "evt \<phi> ps xs" shows "\<exists> xl xs2. xs = xl @@- xs2 \<and> \<phi> (rev xl @ ps) xs2"
  using assms 
  apply (induct ps xs rule: evt.induct) 
   apply auto
   apply (metis append_Nil lshift_simps(1) rev.simps(1))
  by (metis append.assoc append_Nil lshift_simps(2) rev.simps(2) rev_append rev_is_rev_conv)

lemma alw_evt_shift: "xs1 \<noteq> LNil \<Longrightarrow> alw \<phi> (rev xl @ ps) xs1 \<Longrightarrow> evt (alw \<phi>) ps (xl @@- xs1)"
  by (simp add: evt_base evt_shift)

lemma evt_ex_nxt:
  assumes "evt \<phi> ps xs" 
  shows "\<exists> n. (nxt ^^ n) \<phi> ps xs"
  using assms proof induct
  case (evt_base xs) thus ?case by (intro exI[of _ 0]) auto
next
  case (evt_step x ps xs)
  thus ?case
    apply -
    apply (subst nxt_ldropn)
    apply (elim exE)
    subgoal for n
      apply (rule exI[of _ "Suc n"])
      apply (simp flip: nxt_ldropn eSuc_enat)
      done
    done
qed

lemma onc_ex_prv:
  assumes "onc \<phi> ps xs" 
  shows "\<exists> n. (prv ^^ n) \<phi> ps xs"
  using assms proof induct
  case (onc_base ps xs) thus ?case by (intro exI[of _ 0]) auto
next
  case (onc_step x ps xs)
  thus ?case
    apply -
    apply (elim exE)
    subgoal for n
      apply (rule exI[of _ "Suc n"])
      apply simp
      done
    done
qed

definition "wait \<phi> ps xs \<equiv> LEAST n. (nxt ^^ n) \<phi> ps xs"

lemma nxt_wait:
  assumes "evt \<phi> ps xs"  shows "(nxt ^^ (wait \<phi> ps xs)) \<phi> ps xs"
  unfolding wait_def using evt_ex_nxt[OF assms] by(rule LeastI_ex)

lemma nxt_wait_least:
  assumes evt: "evt \<phi> ps xs" and nxt: "(nxt ^^ n) \<phi> ps xs"  shows "wait \<phi> ps xs \<le> n"
  unfolding wait_def 
  by (simp add: Least_le nxt)

lemma ldrop_wait:
  assumes "evt \<phi> ps xs"  shows "\<phi> (rev (list_of (ltake (enat (wait \<phi> ps xs)) xs)) @ ps) (ldrop (wait \<phi> ps xs) xs)"
  using nxt_wait[OF assms]
  by (simp add: ldrop_enat nxt_ldropn)

lemma ldrop_wait_least:
  assumes evt: "evt \<phi> ps xs" and nxt: "\<phi> (rev (list_of (ltake n xs)) @ ps) (ldrop n xs)"  shows "wait \<phi> ps xs \<le> n"
  using assms nxt_wait_least 
  apply (simp add: ldrop_enat nxt_ldropn)
  apply blast
  done

lemma ev_or: "evt (\<phi> dsj \<psi>) = evt \<phi> dsj evt \<psi>"
proof-
  {fix ps xs assume "(evt \<phi> dsj evt \<psi>) ps xs" hence "evt (\<phi> dsj \<psi>) ps xs"
      by (auto elim: evt_mono)
  }
  moreover
  {fix ps xs assume "evt (\<phi> dsj \<psi>) ps xs" hence "(evt \<phi> dsj evt \<psi>) ps xs"
      by induct auto
  }
  ultimately show ?thesis by blast
qed

lemma oc_or: "onc (\<phi> dsj \<psi>) = onc \<phi> dsj onc \<psi>"
proof-
  {fix ps xs assume "(onc \<phi> dsj onc \<psi>) ps xs" hence "onc (\<phi> dsj \<psi>) ps xs"
      by (auto elim: onc_mono)
  }
  moreover
  {fix ps xs assume "onc (\<phi> dsj \<psi>) ps xs" hence "(onc \<phi> dsj onc \<psi>) ps xs"
      by induct auto
  }
  ultimately show ?thesis by blast
qed

lemma alw_mp:
  assumes "alw \<phi> ps xs" and "alw (\<phi> imp \<psi>) ps xs"
  shows "alw \<psi> ps xs"
proof-
  {assume "alw \<phi> ps xs \<and> alw (\<phi> imp \<psi>) ps xs" hence ?thesis
      by coinduct auto
  }
  thus ?thesis using assms by auto
qed

lemma all_imp_alw:
  assumes "\<And> xs ps. \<phi> ps xs"  shows "alw \<phi> ps xs"
proof-
  {assume "\<forall> xs ps. \<phi> ps xs"
    hence ?thesis using neq_LNil_conv by coinduct auto
  }
  thus ?thesis using assms by auto
qed

lemma evt_now_sset:
  "evt (now P) ps xs \<longleftrightarrow> (\<exists> x \<in> lset xs. P x)" (is "?L \<longleftrightarrow> ?R")
proof safe
  assume ?L thus ?R apply induct
     apply (metis now.elims(2) lset_intros(1))
    apply simp
    done
next
  fix x assume "x \<in> lset xs" "P x"
  thus ?L using evt.evt_base evt.evt_step 
    apply -
    apply (induct xs arbitrary: ps rule: lset_induct)
     apply auto[1]
    apply blast
    done   
qed

lemma onc_now_set:
  "onc (now P) ps xs \<longleftrightarrow> (\<exists> x \<in> set ps. P x) \<or> (\<not> lnull xs \<and> P (lhd xs))" (is "?L \<longleftrightarrow> ?R")
proof (rule iffI)
  assume ?L thus ?R
       apply induct
    using now.elims(2) apply fastforce
    apply auto
    done
next
  assume ?R
  thus ?L
    apply -
    apply (induct ps arbitrary: xs)
    using now.elims(3) apply fastforce
    apply (metis now.simps(2) lhd_LCons_ltl onc_base onc_step set_ConsD)
    done   
qed

lemma hst_now_in_set:
  "hst (now P) ps xs \<Longrightarrow> (\<forall> x \<in> set ps. P x) \<or> (\<not> lnull xs \<and> P (lhd xs))" 
    apply (induct rule: hst.induct)
     apply fastforce
    apply (metis lhd_LCons llist.disc(2) now.elims(2))
  done

lemma in_set_hst_now:
  "\<forall> x \<in> set ps. P x \<Longrightarrow> \<not> lnull xs \<Longrightarrow> P (lhd xs) \<Longrightarrow> hst (now P) ps xs" 
  apply (induct ps arbitrary: xs)
   apply fastforce
  subgoal for x ps xs
    by (metis hst_step lhd_LCons_ltl list.set_intros(1) list.set_intros(2) llist.disc(2) now.simps(2))
  done

lemma alw_invar:
  assumes "\<phi> ps xs" and "alw (\<phi> imp nxt \<phi>) ps xs"
  shows "alw \<phi> ps xs"
proof-
  {assume "\<phi> ps xs \<and> alw (\<phi> imp nxt \<phi>) ps xs" hence ?thesis
      by coinduct auto
  }
  thus ?thesis using assms by auto
qed

lemma hst_invar:
  assumes "hst (\<phi> imp prv \<phi>) ps xs" and "\<phi> ps xs" 
  shows "hst \<phi> ps xs"
proof-
  {assume "hst (\<phi> imp prv \<phi>) ps xs" "\<phi> ps xs" hence ?thesis
      apply induct
       apply simp_all
      apply (rule hst_step)
       apply auto
      done
  }
  thus ?thesis using assms by auto
qed

lemma evt_False[simp]: "evt (\<lambda>ps x. False) ps \<omega> \<longleftrightarrow> False"
proof
  assume "evt (\<lambda>ps x. False) ps \<omega>" then show False
    by induct auto
qed auto

lemma onc_False[simp]: "onc (\<lambda>ps x. False) ps xs \<longleftrightarrow> False"
proof
  assume "onc (\<lambda>ps x. False) ps xs" then show False
    by induct auto
qed auto

lemma alw_False[simp]: "xs \<noteq> LNil \<Longrightarrow> alw (\<lambda>_ x. False) ps xs \<longleftrightarrow> False"
  by auto

lemma hst_False[simp]: "ps \<noteq> [] \<Longrightarrow> hst (\<lambda>_ x. False) ps xs \<longleftrightarrow> False"
  using hst.cases by auto

lemma evt_then_ldropn: "evt P ps xs \<Longrightarrow> (\<exists>m. P (rev (list_of (ltake m xs)) @ ps) (ldropn m xs))"
  apply (induct rule: evt.induct)
   apply (metis append_Nil ldropn_0 list_of_LNil ltake_0 rev.simps(1) zero_enat_def)
  apply (metis evt.evt_step evt_ex_nxt nxt_ldropn)
  done

lemma onc_then_ldropn: "onc P ps xs \<Longrightarrow> (\<exists>m. P (drop m ps) ((rev (take m ps)) @@- xs))"
  apply (induct rule: onc.induct)
   apply auto
   apply (metis drop0 lshift_simps(1) rev.simps(1) take0)
  apply (metis drop_Suc_Cons rev_eq_Cons_iff rev_rev_ident snoc_shift take_Suc_Cons)
  done

lemma alw_imp_ldropn: "(\<forall>m. P (rev (list_of (ltake m xs)) @ ps) (ldropn m xs)) \<Longrightarrow> alw P ps xs"
  apply (coinduction arbitrary: ps xs) 
  subgoal for ps xs
    apply (cases xs)
     apply simp_all
    apply (intro conjI disjI1)
    subgoal
      by (metis LNil_eq_ltake_iff Nil_is_rev_conv enat_0_iff(1) ldropn_0 list_of_LNil self_append_conv2)
    subgoal
      by (smt (verit, best) append.assoc append.simps(2) eSuc_enat enat.simps(3) enat_ord_simps(4) ldropn_ltl lfinite_ltake list_of_LCons llist.sel(3) ltake_eSuc_LCons rev.simps(2) self_append_conv2)
    done
  done  

lemma hst_imp_ldropn: "(\<forall>m. P (drop m ps) ((rev (take m ps)) @@- xs)) \<Longrightarrow> hst P ps xs"
  apply (induct ps arbitrary: xs) 
  subgoal for xs
    by auto
  subgoal for x ps xs
    by (metis drop0 drop_Suc_Cons hst_step lshift_simps(1) rev.simps(2) rev_is_Nil_conv snoc_shift take0 take_Suc_Cons)
  done

lemma ldrop_not_finite_alw_ex: "alw P ps xs \<Longrightarrow> \<not> lfinite xs \<Longrightarrow> (\<exists> m. P (rev (list_of (ltake m xs)) @ ps) (ldrop m xs))"
  by (metis alw_nxt evt_base ldrop_wait lfinite_LNil)

lemma cnj_eq: 
  assumes eq: "\<And>xs ps. P ps xs \<Longrightarrow> Q1 ps xs \<longleftrightarrow> Q2 ps xs"
  shows "(P cnj Q1) = P cnj Q2 "
  using assms by blast

lemma cnj_left: "L ps xs \<Longrightarrow> (L cnj R) ps xs = R ps xs"
  by blast  

lemma cnj_right: "R ps xs \<Longrightarrow> (L cnj R) ps xs = L ps xs"
  by blast

lemma alwD: "xs \<noteq> LNil \<Longrightarrow> alw P ps xs \<Longrightarrow> P ps xs"
  by blast

lemma alw_alwD: "alw P ps xs \<Longrightarrow> alw (alw P) ps xs"
  by simp

lemma now_LCons: "now P ps (LCons x xs) \<longleftrightarrow> P x"
  by simp

lemma wow_LCons: "wow P ps (LCons x xs) \<longleftrightarrow> P x"
  by simp

lemma now_eq1[simp]: "now ((=) x) = HLD {x}"
  apply (auto simp add: HLD_def now_mono)
  apply metis
  done

lemma now_eq2[simp]: "now (\<lambda>y. y = x) = HLD {x}"
  unfolding HLD_def
  by auto

lemma alw_now[simp]: 
  "alw (now P) ps (LCons x xs) = (P x \<and> alw (now P) (x#ps) xs)"
  using  alw.simps now_LCons
  by (simp add: alw_nxt)

lemma alw_wow: "alw (wow P) ps (LCons x xs) = (P x \<and> alw (wow P) (x#ps) xs)"
  using  alw.simps wow_LCons
  by (simp add: alw_nxt)

lemma lfinite_evt_wow: "lfinite xs \<Longrightarrow> evt (wow P) ps xs"
  apply (induct xs arbitrary: ps rule: lfinite_induct)
   apply (simp add: lnull_def )
   apply force
  apply (metis evt_step lhd_LCons_ltl)
  done

lemma evt_wow_lfinite: "evt (wow P) ps xs \<Longrightarrow> \<forall>x \<in> lset xs. \<not> P x \<Longrightarrow> lfinite xs"
proof (induct xs rule: evt.induct)
  case (evt_base ps xs)
  then show ?case
    by (cases xs) auto
next
  case (evt_step ps xs)
  then show ?case 
    by (cases xs) auto
qed

lemma lappend_llist_of: "lappend (llist_of xs) ys = xs @@- ys"
  by (induct xs) auto

lemma evt_wow_finds_n: 
  "evt (wow P) ps xs \<Longrightarrow> (\<exists> n. P (lnth xs n)) \<or> lfinite xs"
  apply (induct pred: evt)
  subgoal for ps xs
    apply (cases xs)
     apply simp
    apply (rule disjI1)
    apply (rule exI[of _ 0])
    apply simp
    done
  by (metis lfinite.simps lnth_Suc_LCons)

lemma evt_wow_finds_n_alt: 
  "evt (wow P) ps xs \<Longrightarrow> \<not> lfinite xs \<Longrightarrow> \<exists> n. P (lnth xs n)"
  using evt_wow_finds_n by blast

lemma llength_eSuc_ltl:
  "\<not> lnull xs \<Longrightarrow> llength xs = eSuc (llength (ltl xs))"
  by (simp add: enat_unfold llength_def)

lemma lnth_imp_evt_wow:
  "P (lnth lxs n) \<Longrightarrow> n < llength lxs \<Longrightarrow> evt (wow P) ps lxs"
  apply (induct n arbitrary: ps lxs)
  subgoal
    by (metis evt_base lnth_0 wow.elims(3))
  subgoal for n ps lxs
    apply (cases lxs)
     apply simp
    apply simp
    using Suc_ile_eq by blast
  done

lemma ldropn_lfinite_lfinter:
  "n < llength lxs \<Longrightarrow> \<forall> x \<in> lset (ldropn n lxs) . \<not> P x \<Longrightarrow> lfinite (lfilter P lxs)"
  apply (induct n arbitrary: lxs)
   apply simp
  subgoal for n lxs
    apply (cases lxs)
     apply simp
    apply simp
    using Suc_ile_eq apply blast
    done
  done

lemma list_of_lshift:
  "lfinite lxs \<Longrightarrow>
   list_of (xs @@- lxs) = xs @ (list_of lxs)"
  by (metis lappend_llist_of lfinite_llist_of list_of_lappend list_of_llist_of)

lemma ltakeWhile_lshift:
  "ltakeWhile P (xs @@- lxs) =
  (if \<exists>x\<in>set xs. \<not> P x then llist_of (takeWhile P xs)
   else xs @@- (ltakeWhile P lxs))"
  apply (induct xs)
  apply auto
  done

lemma ltakeWhile_llist_of[simp]:
  "ltakeWhile P (llist_of xs) = llist_of (takeWhile P xs)"
  by (metis lset_llist_of ltakeWhile_all ltakeWhile_lshift shift_LNil takeWhile_eq_all_conv)

lemma lshift_filter[simp]:
  "lfilter P (xs @@- lxs) = filter P xs @@- lfilter P lxs"
  by (metis lappend_llist_of lfilter_lappend_lfinite lfilter_llist_of lfinite_llist_of)

lemma lshift_LNil_split:
  "xs @@- lxs = LNil \<longleftrightarrow> xs = [] \<and> lxs = LNil "
  by (metis LNil_eq_shift_iff)

lemma singleton_lshift:
  "[x] @@- lxs = LCons x lxs"
  apply simp
  done

lemma nxt_ldropn_simp[simp]:
  "nxt P (rev (list_of (ltake (enat m) xs)) @ ps) (ldropn m xs) = 
   P (rev (list_of (ltake (enat (Suc m)) xs)) @ ps) (ldropn (Suc m) xs)"
  apply (induct m arbitrary: ps xs)
  subgoal
    apply simp
    apply (smt (verit, ccfv_threshold) One_nat_def append.simps(2) enat_ord_simps(4) infinity_ne_i1 lappend_ltake_enat_ldropn ldropn_0 ldropn_ltl lfinite_ltake list_of_LCons list_of_LNil list_of_lappend llist.sel(3) ltake.ctr(1) ltake_LNil ltake_eSuc_LCons nxt.elims one_eSuc one_enat_def rev.simps(1) rev.simps(2) zero_enat_def)
    done
  subgoal for m ps xs
    apply (cases xs)
    apply (simp_all flip: eSuc_enat)
    apply (simp add: eSuc_enat)
    done
  done

lemma all_nxt_alw:
  "(\<And>n. (nxt ^^ n) P ps xs) \<Longrightarrow>
   alw P ps xs"
  by (simp add: alw_imp_ldropn nxt_ldropn)

end
