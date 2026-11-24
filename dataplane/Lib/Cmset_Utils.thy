theory Cmset_Utils
  imports
    Countable_Multiset.Countable_Multiset
    "HOL-Library.Multiset"
    "HOL-Library.Conditional_Parametricity"
begin

(* TODO: Move. *)
lemma enat_minus_plus:
  \<open>(x :: enat) - (y + z) = x - y - z\<close>
proof (cases x)
  case (enat x')
  show ?thesis
  proof (cases \<open>y + z \<le> x\<close>)
    case True
    then show ?thesis using enat iadd_le_enat_iff by fastforce
  next
    case False
    then show ?thesis using enat add.commute add.right_neutral enat_minus_mono1 enat_pm_iff(2)
        idiff_infinity_right idiff_self ile0_eq nle_le by (smt (verit, best))
  qed
qed simp

(*
(* TODO: Move. *)
lemma mult_Sup_commute:
  \<open>\<Squnion> {f1 b1 :: enat |b1. \<phi>1 b1} * \<Squnion> {f2 b2 |b2. \<phi>2 b2}
  = \<Squnion> {f1 b1 * f2 b2 |b1 b2. \<phi>1 b1 \<and> \<phi>2 b2}\<close> (is \<open>?L1 * ?L2 = ?R\<close>)
proof (rule order.antisym)
  show \<open>?L1 * ?L2 \<le> ?R\<close> 
  proof (cases \<open>?L1 = 0 \<or> ?L2 = 0\<close>)
    case False
    show ?thesis sorry
  qed fastforce
next
  have \<open>\<forall>x \<in> {f1 b1 * f2 b2 |b1 b2. \<phi>1 b1 \<and> \<phi>2 b2}. x \<le> ?L1 * ?L2\<close> using Sup_upper[of \<open>f1 _\<close>]
      Sup_upper[of \<open>f2 _\<close>] Sup_upper mem_Collect_eq mult_mono zero_le by (smt (verit, del_insts))
  then show \<open>?R \<le> ?L1 * ?L2\<close> using Sup_le_iff by blast
qed

lemma mult_Sup_commute':
  \<open>A1 \<noteq> {} \<Longrightarrow> A2 \<noteq> {} \<Longrightarrow> \<Squnion> A1 * \<Squnion> A2 = \<Squnion> {(a1 :: enat) * a2 |a1 a2. a1 \<in> A1 \<and> a2 \<in> A2}\<close>  
  using mult_Sup_commute[of id \<open>\<lambda>a1. a1 \<in> A1\<close> id \<open>\<lambda>a2. a2 \<in> A2\<close>] by simp 

lemma isum_product_Times:
  \<open>isum f A * isum g B = isum (\<lambda>(a, b). f a * g b) (A \<times> B)\<close>
proof -
  have \<open>isum f A * isum g B =
  \<Squnion> (sum f ` {C |C. C \<subseteq> A \<and> finite C}) * \<Squnion> (sum g ` {C |C. C \<subseteq> B \<and> finite C})\<close>
    unfolding isum_def ..
  also have \<open>\<dots> = \<Squnion> {n * m |n m. n \<in> sum f ` {C |C. C \<subseteq> A \<and> finite C}
  \<and> m \<in> sum g ` {C |C. C \<subseteq> B \<and> finite C}}\<close> by (subst mult_Sup_commute') auto
  also have \<open>\<dots> = \<Squnion> (sum (\<lambda>(a, b). f a * g b) ` {AB |AB. AB \<subseteq> A \<times> B \<and> finite AB})\<close>
  proof (rule Sup_cong; safe; (intro bexI)?)
    fix A' B'
    show \<open>sum f A' * sum g B' \<le> sum (\<lambda>(a, b). f a * g b) (A' \<times> B')\<close>
      by (subst sum_product, subst sum.cartesian_product) auto
  next
    fix AB
    assume \<open>AB \<subseteq> A \<times> B\<close> \<open>finite AB\<close>
    then show \<open>sum f (fst ` AB) * sum g (snd ` AB) \<in> {n * m |n m.
  n \<in> sum f ` {C |C. C \<subseteq> A \<and> finite C} \<and> m \<in> sum g ` {C |C. C \<subseteq> B \<and> finite C}}\<close> by fastforce
    show \<open>(\<Sum>(a, b) \<in> AB. f a * g b) \<le> sum f (fst ` AB) * sum g (snd ` AB)\<close>
      by (subst sum_product, subst sum.cartesian_product) (metis (lifting) \<open>finite AB\<close>
          subset_fst_snd Sigma_cong order.refl finite_SigmaI finite_imageI sum_mono3)
  qed blast+
  also have \<open>\<dots> = isum (\<lambda>(a, b). f a * g b) (A \<times> B)\<close> unfolding isum_def ..
  finally show ?thesis .
qed

lemma isum_product:
  \<open>isum f A * isum g B = isum (\<lambda>a. isum (\<lambda>b. f a * g b) B) A\<close>
   by (simp add: isum_Times isum_product_Times)
*)

lemma cmset_eq_iff:
  \<open>M = N \<longleftrightarrow> (\<forall>x. cmcount M x = cmcount N x)\<close>
  using UNIV_I cmcount.abs_eq cmcount.rep_eq cmset.abs_eq_iff eq_cmset_def inj_cmcount inv_into_f_f
  by (metis (no_types, lifting))

abbreviation \<open>in_cmset x M \<equiv> x \<in> cmset M\<close>

section \<open>Lifted definitions\<close>

context begin
interpretation cmset_as_Quotient .

lift_definition cmset_of_list :: \<open>'a list \<Rightarrow> 'a cmset\<close> is llist_of parametric llist_of_transfer .

(* Parametricity? *)
lift_definition cmUnion :: \<open>'a cmset cmset \<Rightarrow> 'a cmset\<close> is lmerge unfolding cmset.pcr_cr_eq
proof (elim relcomppE, subst (asm) conversep_iff)
  fix lxss lyss :: \<open>'a llist llist\<close> and lXs lYs
  assume lXs_lYs: \<open>llist_all2 cr_cmset lxss lXs\<close> \<open>eq_cmset lXs lYs\<close> \<open>llist_all2 cr_cmset lyss lYs\<close>
  then have \<open>llength lxss = llength lXs\<close> \<open>llength lyss = llength lYs\<close> using llist_all2_conv_all_lnth
    by blast+
  moreover from this have \<open>llength lxss = llength lyss\<close> using eq_cmset_llength[OF lXs_lYs(2)]
    by metis
  moreover obtain \<pi> where \<open>lbij_on \<pi> lYs\<close> \<open>lpermute \<pi> lYs = lXs\<close> using \<open>eq_cmset lXs lYs\<close>
    unfolding eq_cmset_alt by blast
  ultimately have lxss_lyss: \<open>\<forall>n. enat n < llength lxss \<longrightarrow> eq_cmset (lnth lxss n) (lnth lyss (\<pi> n))\<close>
    using lXs_lYs llist_all2_conv_all_lnth cr_cmset_def eq_cmset_def bij_betw_iff_bijections
      lnth_lpermute mem_Collect_eq Collect_cong cmcount.abs_eq by (smt (verit, ccfv_SIG))
  define \<pi>' where \<open>\<pi>' = (\<lambda>n. if n < llength lyss then \<pi> n else n)\<close>
  then have \<open>inj \<pi>'\<close> \<open>\<pi>' ` UNIV = UNIV\<close> using \<open>lbij_on \<pi> lYs\<close> \<open>llength lyss = llength lYs\<close>
      bij_betw_iff_bijections mem_Collect_eq injI surj_def by (smt (verit, best))+
  show \<open>eq_cmset (lmerge lxss) (lmerge lyss)\<close> unfolding eq_cmset_def count_llist_lmerge
  proof
    fix x
    have *: \<open>(if enat (\<pi>' n) < llength lyss then count_llist (lnth lyss (\<pi>' n)) x else 0)
  = (if enat n < llength lxss then count_llist (lnth lxss n) x else 0)\<close> for n
      using lxss_lyss \<open>lbij_on \<pi> lYs\<close> by (auto simp add: \<pi>'_def eq_cmset_def
          \<open>llength lxss = llength lyss\<close> \<open>llength lyss = llength lYs\<close> dest: bij_betwE)
    have \<open>LSUM lyss (\<lambda>lxs. count_llist lxs x) = LSUM lenats
  (\<lambda>n. if enat n < llength lyss then count_llist (lnth lyss n) x else 0)\<close> using LSUM_extend_lenats
      by fast
    also have \<open>\<dots> = isum
  (\<lambda>n. if enat n < llength lyss then count_llist (lnth lyss n) x else 0) (lset lenats)\<close>
      using LSUM_isum[OF ldistinct_lupt] by (simp add: lset_lupt)
    also have \<open>\<dots> = isum
  (\<lambda>n. if enat (\<pi>' n) < llength lyss then count_llist (lnth lyss (\<pi>' n)) x else 0) (lset lenats)\<close>
      by (rule isum_reindex_cong; simp add: lset_lupt \<open>inj \<pi>'\<close> \<open>\<pi>' ` UNIV = UNIV\<close>)
    also have \<open>\<dots> = LSUM lenats
  (\<lambda>n. if enat (\<pi>' n) < llength lyss then count_llist (lnth lyss (\<pi>' n)) x else 0)\<close>
      using LSUM_isum[OF ldistinct_lupt] by (simp add: lset_lupt)
    also have \<open>\<dots> = LSUM lenats
  (\<lambda>n. if enat n < llength lxss then count_llist (lnth lxss n) x else 0)\<close> unfolding * ..
    also have \<open>\<dots> = LSUM lxss (\<lambda>lxs. count_llist lxs x)\<close> by (subst (2) LSUM_extend_lenats) fast
    finally show \<open>LSUM lxss (\<lambda>lxs. count_llist lxs x) = LSUM lyss (\<lambda>lxs. count_llist lxs x)\<close> ..
  qed
qed

end

context includes cset.lifting begin
interpretation cmset_as_typedef .

definition fun_upd_eSuc :: \<open>'a \<Rightarrow> ('a \<Rightarrow> enat) \<Rightarrow> 'a \<Rightarrow> enat\<close> where
  \<open>fun_upd_eSuc x M = M(x := eSuc (M x))\<close>
parametric_constant fun_upd_eSuc_parametric: fun_upd_eSuc_def

(* Question: use definition or unfold to avoid having it in transfer rules? *)
lift_definition cminsert :: \<open>'a \<Rightarrow> 'a cmset \<Rightarrow> 'a cmset\<close> is
  fun_upd_eSuc parametric fun_upd_eSuc_parametric
proof -
  fix x and M :: \<open>'a \<Rightarrow> enat\<close>
  let ?M' = \<open>fun_upd_eSuc x M\<close>
  assume \<open>countable {y. M y \<noteq> 0}\<close>
  moreover have \<open>{y. ?M' y \<noteq> 0} = insert x {y. M y \<noteq> 0}\<close> unfolding fun_upd_eSuc_def by force
  ultimately show \<open>countable {y. ?M' y \<noteq> 0}\<close> by fastforce
qed

abbreviation \<open>cmsingle x \<equiv> cminsert x cmempty\<close>

definition non_zero_elements :: \<open>('a \<Rightarrow> enat) \<Rightarrow> 'a set\<close> where
  \<open>non_zero_elements M = {x. M x \<noteq> 0}\<close>
parametric_constant non_zero_elements_parametric: non_zero_elements_def

lift_definition cset_of_cmset :: \<open>'a cmset \<Rightarrow> 'a cset\<close> is
  non_zero_elements parametric non_zero_elements_parametric[OF bi_unique_eq refl]
  unfolding non_zero_elements_def .

definition enat_of_membership :: \<open>'a set \<Rightarrow> 'a \<Rightarrow> enat\<close> where
  \<open>enat_of_membership X x = (if x \<in> X then 1 else 0)\<close>
parametric_constant enat_of_membership_parametric: enat_of_membership_def

lift_definition cmset_of_cset :: \<open>'a cset \<Rightarrow> 'a cmset\<close> is
  enat_of_membership parametric enat_of_membership_parametric[of HOL.eq, OF refl refl]
  unfolding enat_of_membership_def by simp

(* Parametricity? *)
lift_definition cmfilter :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a cmset \<Rightarrow> 'a cmset\<close> is
  \<open>\<lambda>P M x. if P x then M x else 0 :: enat\<close> using countable_subset mem_Collect_eq subsetI
  by (metis (mono_tags, lifting))

end

subsection \<open>Commutative monoid\<close>

(* This instance could be moved to Countable_Multiset.Countable_Multiset, with 0 and (+) as lifted
definitions. *)
instantiation cmset :: (type) comm_monoid_add
begin

definition \<open>0 = cmempty\<close>

definition \<open>(+) = cmadd\<close>

instance
  by (standard; unfold zero_cmset_def plus_cmset_def; transfer)
    (simp_all add: count_llist_linterleave eq_cmset_def)

end

subsection \<open>Minus\<close>

instantiation cmset :: (type) minus
begin
interpretation cmset_as_typedef .

parametric_constant fun_diff_parametric: fun_diff_def

lift_definition minus_cmset :: \<open>'a cmset \<Rightarrow> 'a cmset \<Rightarrow> 'a cmset\<close> is
  minus parametric fun_diff_parametric
proof -
  fix M N :: \<open>'a \<Rightarrow> enat\<close>
  assume \<open>countable {x. M x \<noteq> 0}\<close>
  moreover have \<open>{x. M x - N x \<noteq> 0} \<subseteq> {x. M x \<noteq> 0}\<close> by force
  ultimately show \<open>countable {x. (M - N) x \<noteq> 0}\<close> using countable_subset by auto
qed

instance ..

end

subsection \<open>Bounded distributive lattice with bottom element\<close>

instantiation cmset :: (type) \<open>{bounded_lattice_bot, distrib_lattice}\<close>
begin
interpretation cmset_as_typedef .

lift_definition inf_cmset :: \<open>'a cmset \<Rightarrow> 'a cmset \<Rightarrow> 'a cmset\<close> is inf
proof -
  fix M N :: \<open>'a \<Rightarrow> enat\<close>
  assume \<open>countable {x. M x \<noteq> 0}\<close>
  moreover have \<open>{x. (M \<sqinter> N) x \<noteq> 0} \<subseteq> {x. M x \<noteq> 0}\<close> unfolding inf_fun_def inf_enat_def by force
  ultimately show \<open>countable {x. (M \<sqinter> N) x \<noteq> 0}\<close> using countable_subset by meson
qed

lift_definition sup_cmset :: \<open>'a cmset \<Rightarrow> 'a cmset \<Rightarrow> 'a cmset\<close> is sup
proof -
  fix M N :: \<open>'a \<Rightarrow> enat\<close>
  assume \<open>countable {x. M x \<noteq> 0}\<close> \<open>countable {x. N x \<noteq> 0}\<close>
  moreover have \<open>{x. (M \<squnion> N) x \<noteq> 0} \<subseteq> {x. M x \<noteq> 0} \<union> {x. N x \<noteq> 0}\<close> by force
  ultimately show \<open>countable {x. (M \<squnion> N) x \<noteq> 0}\<close> using countable_subset countable_Un by meson
qed

definition \<open>\<bottom> = cmempty\<close>

definition \<open>M \<le> N \<longleftrightarrow> (\<forall>x. cmcount M x \<le> cmcount N x)\<close>

definition \<open>(M :: _ cmset) < N \<longleftrightarrow> M \<le> N \<and> \<not> N \<le> M\<close>

instance
proof
  fix X Y Z :: \<open>'a cmset\<close>
  show \<open>X \<le> Y \<Longrightarrow> Y \<le> Z \<Longrightarrow> X \<le> Z\<close> unfolding less_eq_cmset_def using order.trans by blast
  show \<open>X \<le> Y \<Longrightarrow> Y \<le> X \<Longrightarrow> X = Y\<close> unfolding less_eq_cmset_def cmset_eq_iff order_eq_iff by fast
  show \<open>X \<squnion> Y \<sqinter> Z = (X \<squnion> Y) \<sqinter> (X \<squnion> Z)\<close> by transfer (meson sup_inf_distrib1)
qed (unfold bot_cmset_def less_eq_cmset_def less_cmset_def; transfer; simp)+

end

section \<open>Transfer rules\<close>

declare (in cmset_as_Quotient) cmset_of_list.transfer[transfer_rule]
declare (in cmset_as_Quotient) cmUnion.transfer[transfer_rule]

lemma (in cmset_as_typedef) cmset_of_list_transfer[transfer_rule]:
  \<open>rel_fun (=) cr_cmset (\<lambda>xs. enat \<circ> count_list xs) cmset_of_list\<close>
  by (auto simp add: rel_fun_def cr_cmset_def cmset_of_list.abs_eq cmcount.abs_eq)

declare (in cmset_as_typedef) cminsert.transfer[transfer_rule]
declare (in cmset_as_typedef) cset_of_cmset.transfer[transfer_rule]
declare (in cmset_as_typedef) cmset_of_cset.transfer[transfer_rule]
declare (in cmset_as_typedef) cmfilter.transfer[transfer_rule]

lemma (in cmset_as_Quotient) cminsert_transfer[transfer_rule]:
  \<open>rel_fun A (rel_fun (pcr_cmset A) (pcr_cmset A)) LCons cminsert\<close>
  unfolding rel_fun_def pcr_cmset_def cr_cmset_def relcompp_apply
  using cmset_eq_iff cmcount.abs_eq cminsert.rep_eq count_llist_LCons fun_upd_apply fun_upd_eSuc_def
    llist.rel_intros(2) by (smt (verit, del_insts))

lemma (in cmset_as_Quotient) cset_of_cmset_transfer[transfer_rule]:
  \<open>rel_fun (pcr_cmset A) (pcr_cset A) lset cset_of_cmset\<close>
  unfolding rel_fun_def pcr_cmset_def cr_cmset_def pcr_cset_def cr_cset_def rel_set_def
    relcompp_apply using cmcount.abs_eq cset_of_cmset.rep_eq in_lset_iff_count_llist
    llist_all2_lsetD1 llist_all2_lsetD2 mem_Collect_eq non_zero_elements_def by (smt (verit, best))

context begin
interpretation cmset_as_Quotient .

(* TODO *)
lemma cmcount_cmUnion:
  \<open>cmcount (cmUnion M) x = isum (\<lambda>N. cmcount N x * cmcount M N) (cmset M)\<close>
  apply (simp add: cmUnion_def)
  apply transfer
  apply (simp add: count_llist_lmerge cmcount.rep_eq)
  subgoal for M x
    apply (subst LSUM_extend_lenats)
    apply (subst LSUM_isum)
     apply (simp add: lset_lupt)
    apply (subst isum_zeros_congR[where S=\<open>{n \<in> lset lenats. enat n < llength (rep_cmset M)}\<close>])
      apply fast
     apply simp
    apply (subst isum_cong[OF refl, where h=\<open>\<lambda>n. count_llist (lnth (lmap rep_cmset (rep_cmset M)) n) x\<close>])
     apply simp
    apply (subst count_llist_isum)
    sorry
  done

lemma cmset_cmUnion:
  \<open>cmset (cmUnion M) = \<Union> (cmset ` cmset M)\<close>
  unfolding set_eq_iff cmset_alt cmcount_cmUnion isum_eq_0_iff by force

end

lemma (in cmset_as_typedef) cmUnion_transfer[transfer_rule]:
  \<open>rel_fun (pcr_cmset cr_cmset) cr_cmset (\<lambda>M x. isum (\<lambda>N. N x * M N) {N. M N \<noteq> 0}) cmUnion\<close>
  apply (clarsimp simp add: rel_fun_def pcr_cmset_def cr_cmset_def relcompp_apply)
  apply (rule ext)
  subgoal for M M' x
    apply (simp add: cmcount_cmUnion cmset_alt)
    apply (rule isum_reindex_cong[of cmcount])
    using inj_cmcount unfolding inj_on_def apply blast
     apply (intro equalityI subsetI)
    subgoal for N
      apply (simp add: image_def)
      apply (drule spec[of _ \<open>inv cmcount N\<close>])
      apply (rule exI[of _ \<open>inv cmcount N\<close>])
      sorry
     apply fastforce
    apply simp
    done
  done

lemma (in cmset_as_Quotient) cmfilter_transfer[transfer_rule]:
  \<open>rel_fun (rel_fun A (=)) (rel_fun (pcr_cmset A) (pcr_cmset A)) lfilter cmfilter\<close>
  unfolding rel_fun_def pcr_cmset_def cr_cmset_def relcompp_apply cmset_eq_iff cmcount.abs_eq
    cmfilter.rep_eq
proof (safe, rule exI)
  fix P Q lxs M lys
  assume \<open>\<forall>x y. A x y \<longrightarrow> P x \<longleftrightarrow> Q y\<close> \<open>llist_all2 A lxs lys\<close> \<open>\<forall>x. count_llist lys x = cmcount M x\<close>
  then show \<open>llist_all2 A (lfilter P lxs) (lfilter Q lys)
  \<and> (\<forall>x. count_llist (lfilter Q lys) x = (if Q x then cmcount M x else 0))\<close>
    using llist_all2_lfilterI count_llist_alt lfilter_cong lfilter_lfilter lfilter_empty_conv
      llength_LNil by (smt (verit, best))
qed

declare (in cmset_as_typedef) minus_cmset.transfer[transfer_rule]
declare (in cmset_as_typedef) inf_cmset.transfer[transfer_rule]
declare (in cmset_as_typedef) sup_cmset.transfer[transfer_rule]

section \<open>Miscellaneous\<close>

lemma cmset_cmempty[simp]:
  \<open>cmset cmempty = {}\<close>
  unfolding cmset_alt using cmcount_cmempty by simp

context begin
interpretation cmset_as_Quotient .

lemma cmimage_cmempty[simp]:
  \<open>cmimage f cmempty = cmempty\<close>
  by transfer (simp add: eq_cmset_def)

end

context begin
interpretation cmset_as_typedef .

lemma cmcount_cminsert:
  \<open>cmcount (cminsert x M) y = (if y = x then eSuc (cmcount M x) else cmcount M y)\<close>
  by transfer (simp add: fun_upd_eSuc_def)

lemma cmset_cminsert[simp]:
  \<open>cmset (cminsert x M) = insert x (cmset M)\<close>
  by transfer (auto simp add: fun_upd_eSuc_def)

lemma cmset_cmsingle[simp]:
  \<open>cmset (cmsingle x) = {x}\<close>
  by transfer (simp add: fun_upd_eSuc_def)

end

lemma cmimage_cmUnion:
  \<open>cmimage f (cmUnion M) = cmUnion (cmimage (cmimage f) M)\<close> unfolding cmset_eq_iff
proof
  fix x
  have \<open>cmcount (cmimage f (cmUnion M)) x = isum (cmcount (cmUnion M)) {y. f y = x}\<close> by simp
  also have \<open>\<dots> = isum (\<lambda>y. isum (\<lambda>N. cmcount N y * cmcount M N) (cmset M)) {y. f y = x}\<close>
    unfolding cmcount_cmUnion ..
  show \<open>cmcount (cmimage f (cmUnion M)) x = cmcount (cmUnion (cmimage (cmimage f) M)) x\<close> sorry
qed

lemma cmfilter_cmUnion:
  \<open>cmfilter P (cmUnion M) = cmUnion (cmimage (cmfilter P) M)\<close> unfolding cmset_eq_iff
proof
  fix x
  show \<open>cmcount (cmfilter P (cmUnion M)) x = cmcount (cmUnion (cmimage (cmfilter P) M)) x\<close>
  proof (cases \<open>P x\<close>)
    case True
    then have \<open>cmcount (cmfilter P (cmUnion M)) x = cmcount (cmUnion M) x\<close> unfolding cmfilter.rep_eq
      by force
    also have \<open>\<dots> = isum (\<lambda>N. cmcount N x * cmcount M N) (cmset M)\<close> unfolding cmcount_cmUnion ..
    show ?thesis sorry
  qed (simp add: cmfilter.rep_eq cmcount_cmUnion isum_eq_0_iff cmset.set_map)
qed

lemma cmcount_plus:
  \<open>cmcount (M + N) x = cmcount M x + cmcount N x\<close>
  unfolding plus_cmset_def cmcount_cmadd ..

lemma cmset_plus:
  \<open>cmset (M + N) = cmset M \<union> cmset N\<close>
  unfolding cmset_alt cmcount_plus by force

context begin
interpretation cmset_as_typedef .

lemma cminsert_plus_left:
  \<open>cminsert x (M + N) = cminsert x M + N\<close>
  unfolding plus_cmset_def cmset_eq_iff by transfer (simp add: fun_upd_eSuc_def flip: iadd_Suc)

end

lemma cminsert_plus_right:
  \<open>cminsert x (M + N) = M + cminsert x N\<close>
  using cminsert_plus_left add.commute by metis

lemma cmempty_plus[simp]:
  \<open>cmempty + M = M\<close>
  \<open>M + cmempty = M\<close>
  by (simp_all flip: zero_cmset_def)

lemma cminsert_is_plus:
  \<open>cminsert x M = cmsingle x + M\<close>
  using cminsert_plus_left cmempty_plus(1) by metis

context begin
interpretation cmset_as_typedef .

lemma cmcount_minus:
  \<open>cmcount (M - N) x = cmcount M x - cmcount N x\<close>
  by transfer simp

end

lemma cmcount_infinity_in_cmset_minus:
  \<open>cmcount M x = \<infinity> \<Longrightarrow> in_cmset x (M - N)\<close>
  unfolding cmset_alt cmcount_minus by simp

lemma cmcount_less_in_cmset_minus:
  \<open>cmcount N x < cmcount M x \<Longrightarrow> in_cmset x (M - N)\<close>
  unfolding cmset_alt cmcount_minus using add.right_neutral add_diff_assoc_enat enat_add_sub_same
    enat_ord_simps(4) less_le_not_le mem_Collect_eq by (smt (verit))

lemma in_cmset_minus_elim:
  assumes \<open>in_cmset x (M - N)\<close>
  obtains (less) n m where \<open>cmcount N x = enat n\<close> \<open>cmcount M x = enat m\<close> \<open>n < m\<close>
  | (infinity) \<open>cmcount M x = \<infinity>\<close>
proof (cases \<open>cmcount M x\<close>)
  case (enat m)
  then show ?thesis using assms less enat.exhaust[of \<open>cmcount N x\<close>] zero_enat_def
    unfolding cmset_alt cmcount_minus by force
qed simp

lemma in_cmset_minus_left:
  \<open>in_cmset x (M - N) \<Longrightarrow> in_cmset x M\<close>
  using cmset_alt enat_0_iff(1) i0_ne_infinity in_cmset_minus_elim mem_Collect_eq not_less_zero
  by (metis (full_types))

lemma in_cmset_plus_minus:
  assumes \<open>in_cmset x (M + M' - N)\<close> \<open>\<not>in_cmset x (M' - N)\<close>
  shows \<open>in_cmset x M\<close> using assms(1)
proof (cases rule: in_cmset_minus_elim)
  case (less n m)
  then show ?thesis
    using cmcount_less_in_cmset_minus assms(2) unfolding cmcount_plus cmset_alt by force
next
  case infinity
  have \<open>cmcount M' x \<noteq> \<infinity>\<close> using cmcount_infinity_in_cmset_minus assms(2) by fast
  then show ?thesis using infinity unfolding cmcount_plus cmset_alt by fastforce
qed

lemma cmset_minus_plus:
  \<open>(M :: _ cmset) - (N + N') = M - N - N'\<close>
  using cmset_eq_iff enat_minus_plus cmcount_plus cmcount_minus by metis

lemma cmempty_minus[simp]:
  \<open>cmempty - M = cmempty\<close>
  \<open>M - cmempty = M\<close>
  using cmset_eq_iff cmcount_cmempty cmcount_minus idiff_0 idiff_0_right by metis+

lemma cminsert_minus:
  \<open>in_cmset x M \<Longrightarrow> cminsert x (M - cmsingle x) = M\<close>
  unfolding cmset_eq_iff cmset_alt cmcount_cminsert cmcount_minus using neq_zero_conv_eSuc by force

context begin
interpretation cmset_as_typedef .

lemma cmset_inf:
  \<open>cmset (M \<sqinter> N) = cmset M \<inter> cmset N\<close>
  by transfer (auto simp add: inf_enat_def min_def)

lemma cmset_sup:
  \<open>cmset (M \<squnion> N) = cmset M \<union> cmset N\<close>
  by transfer (auto simp add: sup_enat_def max_def)

end

lemma cmset_less_eq:
  \<open>M \<le> N \<Longrightarrow> cmset M \<subseteq> cmset N\<close>
  unfolding less_eq_cmset_def cmset_alt using Collect_mono_iff le_zero_eq
  by (metis (mono_tags, lifting))

lemma cmset_less:
  \<open>M < N \<Longrightarrow> cmset M \<subseteq> cmset N\<close>
  unfolding less_cmset_def less_eq_cmset_def cmset_alt using Collect_mono_iff le_zero_eq
  by (metis (mono_tags, lifting))

(* TODO: Move. *)
lemma isum_eq_singl_Ball: 
  assumes fx: "f a = x" and f: "\<forall>a' \<in> A. a' \<noteq> a \<longrightarrow> f a' = 0" and a: "a \<in> A"
  shows "isum f A = x"
proof -
  have "isum f A = isum f {a}"
    by (rule isum_zeros_cong) (use assms in auto)
  then show ?thesis by (simp add: fx)
qed

lemma cmUnion_disjoint_in_cmset:
  assumes \<open>\<And>N N'. in_cmset N M \<Longrightarrow> in_cmset N' M \<Longrightarrow> N \<noteq> N' \<Longrightarrow> N \<sqinter> N' = cmempty\<close>
    \<open>in_cmset x (cmUnion M)\<close>
  shows \<open>\<exists>!N. in_cmset N M \<and> cmcount (cmUnion M) x = cmcount N x * cmcount M N\<close>
proof -
  let ?P = \<open>\<lambda>N. in_cmset N M \<and> in_cmset x N\<close>
  define N where \<open>N = (SOME N. ?P N)\<close>
  have \<open>\<exists>N. ?P N\<close> using assms(2) isum_eq_0_iff unfolding cmset_alt cmcount_cmUnion by force
  then have N: \<open>in_cmset N M\<close> \<open>in_cmset x N\<close> unfolding N_def using someI_ex[where P=\<open>?P\<close>] by auto
  then have neq_N_0: \<open>\<forall>N'. in_cmset N' M \<and> N' \<noteq> N \<longrightarrow> cmcount N' x = 0\<close> using assms(1)
      IntI cmset_alt cmset_cmempty cmset_inf emptyE mem_Collect_eq by (metis (mono_tags, lifting))
  have cmcount_M_N: \<open>cmcount (cmUnion M) x = cmcount N x * cmcount M N\<close> unfolding cmcount_cmUnion
    using isum_eq_singl_Ball[OF _ _ N(1)] neq_N_0 by force
  moreover have \<open>\<forall>N'. in_cmset N' M \<and> cmcount (cmUnion M) x = cmcount N' x * cmcount M N' \<longrightarrow> N' = N\<close>
    using assms(2) neq_N_0 cmset_alt by fastforce
  ultimately show ?thesis using N(1) by blast
qed

section \<open>Conversion from list to countable multiset\<close>

lemma cmcount_cmset_of_list[simp]:
  \<open>cmcount (cmset_of_list xs) x = enat (count_list xs x)\<close>
  by (simp add: fun_eq_iff cmset_of_list_def cmcount.abs_eq)

lemma cmset_cmset_of_list[simp]:
  \<open>cmset (cmset_of_list xs) = set xs\<close>
  by (simp add: cmset_alt flip: count_llist_llist_of lset_llist_of in_lset_iff_count_llist)

(* TODO? Use transfer in cmset_as_Quotient. *)
lemma cmset_of_list_Nil[simp]:
  \<open>cmset_of_list [] = cmempty\<close>
  by (simp add: cmempty_def cmset_of_list.abs_eq)

context begin
interpretation cmset_as_Quotient .

lemma cmset_of_list_Cons[simp]:
  \<open>cmset_of_list (x # xs) = cminsert x (cmset_of_list xs)\<close>
  by transfer (simp add: eq_cmset_def)

lemma cmfilter_cmset_of_list:
  \<open>cmfilter P (cmset_of_list xs) = cmset_of_list (filter P xs)\<close>
  by transfer (simp add: eq_cmset_def)

lemma cmimage_cmset_of_list:
  \<open>cmimage f (cmset_of_list xs) = cmset_of_list (map f xs)\<close> unfolding cmset_eq_iff
proof
  fix x
  have \<open>cmcount (cmimage f (cmset_of_list xs)) x = isum (cmcount (cmset_of_list xs)) {y. f y = x}\<close>
    by force
  also have \<open>\<dots> = isum (enat \<circ> count_list xs) {y. f y = x}\<close> using cmcount_cmset_of_list comp_def
    by metis
  also have \<open>\<dots> = isum (count_llist (llist_of xs)) {y. f y = x}\<close> using count_llist_llist_of
      comp_def by metis
  also have \<open>\<dots> = count_llist (lmap f (llist_of xs)) x\<close> unfolding comp_def count_llist_lmap ..
  also have \<open>\<dots> = enat (count_list (map f xs) x)\<close> by simp
  also have \<open>\<dots> = cmcount (cmset_of_list (map f xs)) x\<close> using cmcount_cmset_of_list by metis
  finally show \<open>cmcount (cmimage f (cmset_of_list xs)) x = cmcount (cmset_of_list (map f xs)) x\<close> .
qed

end

(* TODO? Use transfer in cmset_as_Quotient. *)
lemma cmset_of_list_append:
  \<open>cmset_of_list (xs @ ys) = cmset_of_list xs + cmset_of_list ys\<close>
  by (simp add: plus_cmset_def cmcount.abs_eq cmset_eq_iff cmset_of_list.abs_eq)

section \<open>Conversion between countable set and countable multiset\<close>

lemma cmcount_cmset_of_cset:
  \<open>cmcount (cmset_of_cset X) x = (if cin x X then 1 else 0)\<close>
  unfolding cmset_of_cset.rep_eq enat_of_membership_def cin.rep_eq by fast

context includes cset.lifting begin
interpretation cmset_as_typedef .

lemma cmset_rcset[simp]:
  \<open>cmset (cmset_of_cset X) = rcset X\<close>
  by transfer (simp add: enat_of_membership_def)

lemma rcset_cmset[simp]:
  \<open>rcset (cset_of_cmset M) = cmset M\<close>
  by transfer (simp add: non_zero_elements_def)

lemma cset_of_cmset_of_cset[simp]:
  \<open>cset_of_cmset (cmset_of_cset X) = X\<close>
  by transfer (simp add: non_zero_elements_def enat_of_membership_def)

lemma cmset_of_cset_cempty[simp]:
  \<open>cmset_of_cset cempty = cmempty\<close>
  by transfer (simp add: enat_of_membership_def fun_eq_iff)

lemma cmimage_cmset_of_cset:
  \<open>inj (f :: 'a \<Rightarrow> 'b) \<Longrightarrow> cmimage f (cmset_of_cset X) = cmset_of_cset (cimage f X)\<close>
proof (transfer, rule ext)
  fix f :: \<open>'a \<Rightarrow> 'b\<close> and X x
  assume \<open>inj f\<close>
  show \<open>isum (enat_of_membership X) {y. f y = x} = enat_of_membership (f ` X) x\<close>
  proof (cases \<open>x \<in> f ` X\<close>)
    case True
    then obtain y where \<open>y \<in> X\<close> \<open>x = f y\<close> by blast
    moreover from this have \<open>{y. f y = x} = {y}\<close> using inj_eq[OF \<open>inj f\<close>] by blast
    ultimately show ?thesis unfolding enat_of_membership_def by simp
  qed (auto simp add: isum_eq_0_iff enat_of_membership_def)
qed

lemma cmset_of_cset_cUn:
  \<open>cInt X Y = cempty \<Longrightarrow> cmset_of_cset (cUn X Y) = cmset_of_cset X + cmset_of_cset Y\<close>
  unfolding plus_cmset_def
  by transfer (auto simp add: enat_of_membership_def fun_eq_iff)

lemma cminsert_cmset_of_cset:
  \<open>\<not>cin x X \<Longrightarrow> cminsert x (cmset_of_cset X) = cmset_of_cset (cinsert x X)\<close>
  by transfer (simp add: fun_upd_eSuc_def enat_of_membership_def fun_eq_iff one_eSuc)

lemma cmset_cmset_of_cset_minus:
  \<open>cmset (cmset_of_cset X - cmset_of_cset Y) = rcset X - rcset Y\<close>
  by transfer (force simp add: enat_of_membership_def)

end

end