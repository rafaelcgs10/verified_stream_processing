section \<open>Linear Temporal Logic on Lazy Lists\<close>

theory Linear_Temporal_Logic_on_Llists
  imports 
    "Coinductive.Coinductive_List"
    "HOL-Library.BNF_Corec"
begin

section\<open>Linear temporal logic\<close>

text \<open>Propositional connectives:\<close>

abbreviation (input) IMPL (infix "impll" 60)
  where "\<phi> impll \<psi> \<equiv> \<lambda> xs. \<phi> xs \<longrightarrow> \<psi> xs"

abbreviation (input) OR (infix "or" 60)
  where "\<phi> or \<psi> \<equiv> \<lambda> xs. \<phi> xs \<or> \<psi> xs"

abbreviation (input) AND (infix "aand" 60)
  where "\<phi> aand \<psi> \<equiv> \<lambda> xs. \<phi> xs \<and> \<psi> xs"

abbreviation (input) not where "not \<phi> \<equiv> \<lambda> xs. \<not> \<phi> xs"

abbreviation (input) "true \<equiv> \<lambda> xs. True"

abbreviation (input) "false \<equiv> \<lambda> xs. False"

lemma impll_not_or: "\<phi> impll \<psi> = (not \<phi>) or \<psi>"
  by blast

lemma not_or: "not (\<phi> or \<psi>) = (not \<phi>) aand (not \<psi>)"
  by blast

lemma not_aand: "not (\<phi> aand \<psi>) = (not \<phi>) or (not \<psi>)"
  by blast

lemma non_not[simp]: "not (not \<phi>) = \<phi>" by simp

text \<open>Temporal (LTL) connectives:\<close>

fun holdsll where
  "holdsll P LNil = False"
| "holdsll P (LCons x xs) = P x"

fun wholdsll where
  "wholdsll P LNil = True"
| "wholdsll P (LCons x xs) = P x"

fun nxt where "nxt \<phi> xs = \<phi> (ltl xs)"

definition "HLDLL s = holdsll (\<lambda>x. x \<in> s)"

abbreviation HLD_nxt (infixr "\<cdot>" 65) where
  "s \<cdot> P \<equiv> HLDLL s aand nxt P"

context
  notes [[inductive_internals]]
begin

inductive evll for \<phi> where
  base: "\<phi> xs \<Longrightarrow> evll \<phi> xs"
| step: "evll \<phi> (xs) \<Longrightarrow> evll \<phi> (LCons x xs)"

inductive_cases baseE: "evll \<phi> xs"
inductive_cases stepE: "evll \<phi> (LCons x xs)"

coinductive alwll for \<phi> where
  finite_all[simp]: "alwll \<phi> LNil"
| alwll: "\<lbrakk>\<phi> xs; alwll \<phi> (ltl xs)\<rbrakk> \<Longrightarrow> alwll \<phi> xs"

inductive_cases finite_allE: "alwll \<phi> LNil"
inductive_cases alwllE: "alwll \<phi> xs"

end


lemma alwll_LConsD: "alwll P (LCons x xs) \<Longrightarrow> alwll P xs"
  by (metis alwll.cases eq_LConsD)


lemma alwll_headD: "alwll P (LCons x xs) \<Longrightarrow> P (LCons x xs)"
  using alwll.cases by blast

lemma alwll_LCons_iff: "alwll P (LCons x xs) \<longleftrightarrow> alwll P xs \<and> P (LCons x xs)"
  by (metis alwll.simps eq_LConsD) 

lemma alwll_eq_fun:
  "alwll P xs \<Longrightarrow> P = Q \<Longrightarrow> alwll Q xs"
  by simp

lemma holds_mono:
  assumes holdsll: "holdsll P xs" and 0: "\<And> x. P x \<Longrightarrow> Q x"
  shows "holdsll Q xs"
  using assms by (metis holdsll.simps(1) holdsll.simps(2) llist.exhaust)

lemma wholds_mono:
  assumes wholdsll: "wholdsll P xs" and 0: "\<And> x. P x \<Longrightarrow> Q x"
  shows "wholdsll Q xs"
  using assms by (metis wholdsll.simps(1) wholdsll.simps(2) llist.exhaust)

lemma HLDLL_iff: "\<omega> \<noteq> LNil \<Longrightarrow> HLDLL s \<omega> \<longleftrightarrow> lhd \<omega> \<in> s"
  using HLDLL_def by (metis holdsll.simps(2) llist.exhaust_sel)

lemma HLDLL_LCons[simp]: "HLDLL X (LCons x \<omega>) \<longleftrightarrow> x \<in> X"
  by (simp add: HLDLL_iff)

lemma nxt_mono:
  assumes nxt: "nxt \<phi> xs" and 0: "\<And> xs. \<phi> xs \<Longrightarrow> \<psi> xs"
  shows "nxt \<psi> xs"
  using assms by auto

declare evll.intros[intro]
declare alwll.cases[elim]

lemma evll_induct_strong[consumes 1, case_names base step]:
  "evll \<phi> x \<Longrightarrow> (\<And>xs. \<phi> xs \<Longrightarrow> P xs) \<Longrightarrow> (\<And>xs. evll \<phi> (ltl xs) \<Longrightarrow> \<not> \<phi> xs \<Longrightarrow> P (ltl xs) \<Longrightarrow> P xs) \<Longrightarrow> P x"
  apply (induct rule: evll.induct) apply auto
  by (metis ltl_simps(2))

lemma alwll_coinduct[consumes 1, case_names alwll ltl]:
  "X x \<Longrightarrow> (\<And>x. X x \<Longrightarrow> \<phi> x) \<Longrightarrow> (\<And>x. X x \<Longrightarrow> \<not> alwll \<phi> (ltl x) \<Longrightarrow> X (ltl x)) \<Longrightarrow> alwll \<phi> x"
  using alwll.coinduct[of X x \<phi>] by auto

lemma evll_mono:
  assumes evll: "evll \<phi> xs" and 0: "\<And> xs. \<phi> xs \<Longrightarrow> \<psi> xs"
  shows "evll \<psi> xs"
  using evll by induct (auto simp: 0)

lemma alwll_mono:
  assumes alwll: "alwll \<phi> xs" and 0: "\<And> xs. \<phi> xs \<Longrightarrow> \<psi> xs"
  shows "alwll \<psi> xs"
  using alwll by coinduct (auto simp: 0)


lemma alwll_aand: "alwll (\<phi> aand \<psi>) = alwll \<phi> aand alwll \<psi>"
proof-
  {fix xs assume "alwll (\<phi> aand \<psi>) xs" hence "(alwll \<phi> aand alwll \<psi>) xs"
   by (auto elim: alwll_mono)
  }
  moreover
  {fix xs assume "(alwll \<phi> aand alwll \<psi>) xs" hence "alwll (\<phi> aand \<psi>) xs"
   by coinduct auto
  }
  ultimately show ?thesis by blast
qed

lemma evll_nxt: "xs \<noteq> LNil \<Longrightarrow> evll \<phi> xs = (\<phi> or nxt (evll \<phi>)) xs"
  by (metis evll.simps llist.exhaust_sel ltl_simps(2) nxt.elims)

lemma alwll_nxt: "xs \<noteq> LNil \<Longrightarrow> alwll \<phi> xs = (\<phi> aand nxt (alwll \<phi>)) xs"
  by (metis alwll.simps nxt.simps)

lemma evll_evll[simp]: "evll (evll \<phi>) xs = evll \<phi> xs"
proof-
  {fix xs
    assume "evll (evll \<phi>) xs" hence "evll \<phi> xs"
      by induct auto
  }
  thus ?thesis  apply (cases xs)
    by blast+
qed

lemma alwll_alwll[simp]: "alwll (alwll \<phi>) = alwll \<phi>"
proof-
  {fix xs
    assume "alwll \<phi> xs" hence "alwll (alwll \<phi>) xs"
      by coinduct auto
  }
  thus ?thesis using finite_all by fastforce
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
  apply auto
  apply (metis eSuc_enat eSuc_plus)
  done

lemma lnth_shift:
  "n < length xs \<Longrightarrow>
   lnth (xs @@- lxs) n = xs ! n"
  apply (induct xs arbitrary: n lxs)
  apply auto[1]
  apply auto
  using less_Suc_eq_0_disj apply fastforce
  done

lemma alwll_shift:
assumes "alwll \<phi> (xl @@- xs)"
shows "alwll \<phi> xs"
using assms by (induct xl) auto

lemma shift_shift:
   "xs @@- (ys @@- zs) = (xs @ ys) @@- zs"
  by (induct xs) auto

lemma LCons_shift:
  "LCons y (ys @@- lxs) = LCons x (xs @@- lxs) \<Longrightarrow>
   y = x"
  by blast

lemma alwll_ldropn:
  assumes "alwll \<phi> xs"  shows "alwll \<phi> (ldropn n xs)"
  using assms apply (induct n arbitrary: xs)
   apply simp
  by (metis alwll.simps ldropn_lnull ldropn_ltl lnull_def)

lemma nxt_ldropn: "(nxt ^^ n) \<phi> xs \<longleftrightarrow> \<phi> (ldropn n xs)"
  apply (induct n arbitrary: xs)
   apply simp
  by (simp add: ldropn_ltl)


lemma evll_shift:
assumes "evll \<phi> xs"
shows "evll \<phi> (xl @@- xs)"
using assms by (induct xl) auto

lemma evll_imp_shift:
assumes "evll \<phi> xs"  shows "\<exists> xl xs2. xs = xl @@- xs2 \<and> \<phi> xs2"
using assms by induct (metis lshift_simps(1), metis lshift_simps(2))+

lemma alwll_evll_shift: "xs1 \<noteq> LNil \<Longrightarrow> alwll \<phi> xs1 \<Longrightarrow> evll (alwll \<phi>) (xl @@- xs1)"
  by (simp add: base evll_shift)

lemma evll_ex_nxt:
assumes "evll \<phi> xs" 
shows "\<exists> n. (nxt ^^ n) \<phi> xs"
using assms proof induct
  case (base xs) thus ?case by (intro exI[of _ 0]) auto
next
  case (step xs)
  thus ?case
    by (metis ldropn_Suc_LCons nxt_ldropn)
qed

definition "wait \<phi> xs \<equiv> LEAST n. (nxt ^^ n) \<phi> xs"

lemma nxt_wait:
  assumes "evll \<phi> xs"  shows "(nxt ^^ (wait \<phi> xs)) \<phi> xs"
  unfolding wait_def using evll_ex_nxt[OF assms] by(rule LeastI_ex)
 
lemma nxt_wait_least:
  assumes evll: "evll \<phi> xs" and nxt: "(nxt ^^ n) \<phi> xs"  shows "wait \<phi> xs \<le> n"
  unfolding wait_def 
  by (simp add: Least_le nxt)

lemma ldrop_wait:
  assumes "evll \<phi> xs"  shows "\<phi> (ldrop (wait \<phi> xs) xs)"
  using nxt_wait[OF assms]
  by (simp add: ldrop_enat nxt_ldropn)

lemma sdrop_wait_least:
  assumes evll: "evll \<phi> xs" and nxt: "\<phi> (ldrop n xs)"  shows "wait \<phi> xs \<le> n"
   using assms nxt_wait_least 
   by (metis ldrop_enat nxt_ldropn)

lemma ev_or: "evll (\<phi> or \<psi>) = evll \<phi> or evll \<psi>"
proof-
  {fix xs assume "(evll \<phi> or evll \<psi>) xs" hence "evll (\<phi> or \<psi>) xs"
      by (auto elim: evll_mono)
  }
  moreover
  {fix xs assume "evll (\<phi> or \<psi>) xs" hence "(evll \<phi> or evll \<psi>) xs"
      by induct auto
  }
  ultimately show ?thesis by blast
qed

lemma alwll_mp:
  assumes "alwll \<phi> xs" and "alwll (\<phi> impll \<psi>) xs"
  shows "alwll \<psi> xs"
proof-
  {assume "alwll \<phi> xs \<and> alwll (\<phi> impll \<psi>) xs" hence ?thesis
      by coinduct auto
  }
  thus ?thesis using assms by auto
qed

lemma all_imp_alwll:
  assumes "\<And> xs. \<phi> xs"  shows "alwll \<phi> xs"
proof-
  {assume "\<forall> xs. \<phi> xs"
    hence ?thesis by coinduct auto
  }
  thus ?thesis using assms by auto
qed

lemma evll_holds_sset:
  "evll (holdsll P) xs \<longleftrightarrow> (\<exists> x \<in> lset xs. P x)" (is "?L \<longleftrightarrow> ?R")
proof safe
  assume ?L thus ?R apply induct
     apply (metis holdsll.elims(2) lset_intros(1))
    apply simp
    done
next
  fix x assume "x \<in> lset xs" "P x"
  thus ?L using evll.base evll.step 
    by (smt (verit, best) holdsll.simps(2) llist.distinct(1) lset_induct)
qed

lemma alwll_invar:
  assumes "\<phi> xs" and "alwll (\<phi> impll nxt \<phi>) xs"
  shows "alwll \<phi> xs"
proof-
  {assume "\<phi> xs \<and> alwll (\<phi> impll nxt \<phi>) xs" hence ?thesis
      by coinduct auto
  }
  thus ?thesis using assms by auto
qed

lemma evll_False: "evll (\<lambda>x. False) \<omega> \<longleftrightarrow> False"
proof
  assume "evll (\<lambda>x. False) \<omega>" then show False
    by induct auto
qed auto

lemma alwll_False: "\<omega> \<noteq> LNil \<Longrightarrow> alwll (\<lambda>x. False) \<omega> \<longleftrightarrow> False"
  by auto

lemma evll_then_sdropn: "evll P \<omega> \<Longrightarrow> (\<exists>m. P (ldropn m \<omega>))"
    apply (induct rule: evll_induct_strong)
     apply (auto intro: exI[of _ 0] exI[of _ "Suc n" for n])
    by (metis ldropn_ltl)

lemma alwll_imp_ldropn: "(\<forall>m. P (ldropn m \<omega>)) \<Longrightarrow> alwll P \<omega>"
  apply (coinduction arbitrary: \<omega>) 
  apply (auto elim: allE[of _ 0] allE[of _ "Suc n" for n])
  apply (simp add: ldropn_ltl)
  done

lemma alwll_imp_ldrop: "(\<forall>m. P (ldrop m \<omega>)) \<Longrightarrow> alwll P \<omega>"
  apply (coinduction arbitrary: \<omega>) 
  apply (auto elim: allE[of _ 0] allE[of _ "Suc n" for n])
  apply (simp add: ldrop_ltl)
  done

lemma ldrop_not_finite_alwll_ex: "alwll P \<omega> \<Longrightarrow> \<not> lfinite \<omega> \<Longrightarrow> (\<exists> m. P (ldrop m \<omega>))"
    by (metis alwll_nxt ldrop_0 lfinite.simps)

lemma aand_eq: 
  assumes eq: "\<And>\<omega>. P \<omega> \<Longrightarrow> Q1 \<omega> \<longleftrightarrow> Q2 \<omega>"
  shows "(P aand Q1) = P aand Q2 "
  using assms by blast

lemma aand_left[simp]: "L xs \<Longrightarrow> (L aand R) xs = R xs"
  by blast  

lemma aand_right[simp]: "R xs \<Longrightarrow> (L aand R) xs = L xs"
  by blast
   
lemma alwllD: "x \<noteq> LNil \<Longrightarrow> alwll P x \<Longrightarrow> P x"
  by blast

lemma alwll_alwllD: "alwll P \<omega> \<Longrightarrow> alwll (alwll P) \<omega>"
  by simp

lemma holdsll_LCons: "holdsll P (LCons x s) \<longleftrightarrow> P x"
  by simp

lemma wholdsll_LCons: "wholdsll P (LCons x s) \<longleftrightarrow> P x"
  by simp

lemma holdll_eq1[simp]: "holdsll ((=) x) = HLDLL {x}"
  apply rule 
  apply(auto simp: HLDLL_iff)
  using holdsll.elims(1) apply force
  apply (simp add: HLDLL_def holds_mono)
  done

lemma holdll_eq2[simp]: "holdsll (\<lambda>y. y = x) = HLDLL {x}"
  apply rule
  apply  (auto simp: HLDLL_iff)
  using holdsll.elims(2) apply fastforce
  apply (metis (full_types) holdll_eq1 holds_mono)
  done

lemma alw_holds: "alwll (holdsll P) (LCons h t) = (P h \<and> alwll (holdsll P) t)"
  using  alwll.simps holdsll_LCons
  by (metis llist.distinct(1) ltl_simps(2))

lemma alw_wholds: "alwll (wholdsll P) (LCons h t) = (P h \<and> alwll (wholdsll P) t)"
  using  alwll.simps wholdsll_LCons
  by (metis llist.distinct(1) ltl_simps(2))

lemma evll_not_finite_imp_ldrop: "evll P xs \<Longrightarrow> \<not> lfinite xs \<Longrightarrow> \<exists>m . P (ldrop m xs)"
  apply (induct rule: evll_induct_strong) 
   apply (rule exI[of _ 0])
   apply simp
  subgoal for xs
    by (metis ldrop_ltl lfinite_ltl)
  done

lemma lfinite_evll_wholdsll: "lfinite xs \<Longrightarrow> evll (wholdsll P) xs"
  by (induct xs rule: lfinite_induct) (auto simp: lnull_def evll_nxt)

lemma evll_wholdsll_lfinite: "evll (wholdsll P) xs \<Longrightarrow> \<forall>x \<in> lset xs. \<not> P x \<Longrightarrow> lfinite xs"
proof (induct xs rule: evll_induct_strong)
  case (base xs)
  then show ?case
    by (cases xs) auto
next
  case (step xs)
  then show ?case 
    by (cases xs) auto
qed

lemma lappend_llist_of: "lappend (llist_of xs) ys = xs @@- ys"
  by (induct xs) auto

lemma finite_alwll_evll_wholdsll_lfinite: "finite {i. z \<le> i \<and> i < llength xs + z \<and> P (lnth xs (i - z))} \<Longrightarrow>
    alwll (evll (wholdsll P)) xs \<Longrightarrow> lfinite xs"
  apply (induct "{i. z \<le> i \<and> i < llength xs + z \<and> P (lnth xs (i - z))}" arbitrary: xs z rule: finite_linorder_min_induct)
  subgoal for xs z
    apply (drule alwll_ldropn[of _ _ z])
    apply (cases "ldropn z xs")
     apply simp
     apply (metis lfinite_LNil lfinite_ldropn)
    apply simp
    apply (drule alwll_headD)
    apply (drule evll_wholdsll_lfinite)
     apply (metis add.commute add_diff_cancel_left' enat_less_enat_plusI2 in_lset_conv_lnth in_lset_ldropnD le_add1)
    apply (metis lfinite_ldropn)
    done
  subgoal for i A xs z
    apply (drule meta_spec[of _ "ldropn (Suc (i - z)) xs"])
    apply (drule meta_spec[of _ "Suc i"])
    apply (drule meta_mp)
    subgoal
      apply (auto simp: set_eq_iff ldropn_Suc_conv_ldropn[symmetric])
      subgoal for x
        apply (frule spec[of _ x], drule iffD1, erule disjI2)
        apply (drule spec[of _ i], drule iffD1, rule disjI1, rule refl)
        apply (cases "llength xs")
        apply auto
        done
      subgoal for x
        apply (frule spec[of _ x], drule iffD1, erule disjI2)
        apply (drule spec[of _ i], drule iffD1, rule disjI1, rule refl)
        apply (cases "llength xs")
         apply auto
        apply (smt (verit) Nat.add_diff_assoc2 Suc_diff_le Suc_le_eq add.commute enat_ord_simps(2) le_add_diff_inverse less_diff_conv2 lnth_ldropn nat_le_linear not_less_eq_eq)
        using Suc_diff_Suc by force
      subgoal for x
        apply (subst (asm) lnth_ldropn)
        apply (cases "llength xs"; auto)
        apply (frule spec[of _ i], drule iffD1, rule disjI1, rule refl)
        apply (cases "i = x")
         apply auto
        apply (drule spec[of _ x], drule iffD2)
         apply simp_all
        apply (cases "llength xs"; auto)
         apply (metis Suc_diff_Suc Suc_leD order_le_imp_less_or_eq order_less_le_trans)
        using Suc_diff_Suc by force
        done
    apply (drule meta_mp)
     apply (erule alwll_ldropn)
    apply simp
    done
  done

lemma alwll_evll_wholdsll_alt:
  "alwll(evll (wholdsll P)) xs \<longleftrightarrow> lfinite xs \<or> infinite {i. enat i < llength xs \<and> P (lnth xs i)}"
  apply (rule iffI[rotated], erule disjE)
  subgoal
    by (induct xs rule: lfinite_induct)
      (auto simp: lnull_def lfinite_evll_wholdsll elim!: alwll.alwll[rotated])
  subgoal
    apply (coinduction arbitrary: xs)
    subgoal for xs
      apply (cases xs)
       apply simp
      apply (rule disjI2 exI conjI)+
       apply assumption
      apply (rule conjI)
      subgoal premises prems for z zs
        using prems(1) unfolding prems(2)[symmetric]
        apply -
        apply (drule infinite_imp_nonempty)
        apply simp
        apply (erule exE conjE)+
        subgoal for i
          apply (subst lappend_ltake_ldrop[symmetric, of _ "i"])
          apply (subgoal_tac "lfinite (ltake i xs)")
           apply (unfold lfinite_eq_range_llist_of) []
           apply safe
           apply (simp_all add: lappend_llist_of ldrop_enat ldropn_Suc_conv_ldropn[symmetric])
          apply (rule evll_shift)
          apply (rule evll.base)
          apply simp
          done
        done
      apply simp
      apply safe
      apply (erule notE)
      apply (drule finite_imageI[of _ Suc])
      apply (drule finite_insert[THEN iffD2, of _ 0])
      apply (erule finite_subset[rotated])
      apply (auto simp: image_iff lnth_LCons' gr0_conv_Suc Suc_ile_eq)
      apply blast
      apply (metis Suc_ile_eq Suc_pred gr0I)
      done
    done
  subgoal
    apply (rule disjCI)
    apply (unfold not_not)
    using finite_alwll_evll_wholdsll_lfinite[of 0, folded zero_enat_def, simplified]
    by blast
  done


lemma evll_wholdsll_Inl_in_set: 
  "evll (wholdsll sum.isl) xs \<Longrightarrow> (\<exists> x \<in> lset xs. sum.isl x) \<or> lfinite xs"
  apply (induct pred: evll)
  subgoal for xs
    apply (cases xs)
     apply simp_all
    done
  subgoal for xs x
    apply simp
    done
  done

lemma evll_wholdsll_finds_n: 
  "evll (wholdsll P) xs \<Longrightarrow> (\<exists> n. P (lnth xs n)) \<or> lfinite xs"
  apply (induct pred: evll)
  subgoal for xs
    apply (cases xs)
     apply simp
    apply (rule disjI1)
    apply (rule exI[of _ 0])
    apply simp
    done
  by (metis lfinite.simps lnth_Suc_LCons)

lemma evll_wholdsll_finds_n_alt: 
  "evll (wholdsll P) xs \<Longrightarrow> \<not> lfinite xs \<Longrightarrow> \<exists> n. P (lnth xs n)"
  using evll_wholdsll_finds_n by blast

lemma llength_eSuc_ltl:
  "\<not> lnull xs \<Longrightarrow> llength xs = eSuc (llength (ltl xs))"
   by (simp add: enat_unfold llength_def)

lemma lnth_imp_evll_wholdsll:
  "P (lnth lxs n) \<Longrightarrow> n < llength lxs \<Longrightarrow> evll (wholdsll P) lxs"
  apply (induct n arbitrary: lxs)
  subgoal
    by (metis base lnth_0 wholdsll.elims(3))
  subgoal for n lxs
    apply (cases lxs)
     apply simp
    apply simp
    using Suc_ile_eq apply blast
    done
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

end
