theory Cmset_Utils
  imports
    Countable_Multiset.Countable_Multiset
    "HOL-Library.Conditional_Parametricity"
begin

lemma cmset_eq_iff:
  \<open>M = N \<longleftrightarrow> (\<forall>x. cmcount M x = cmcount N x)\<close>
  using UNIV_I cmcount.abs_eq cmcount.rep_eq cmset.abs_eq_iff eq_cmset_def inj_cmcount inv_into_f_f
  by (metis (no_types, lifting))

section \<open>Lifted definitions\<close>

context includes cset.lifting begin
interpretation cmset_as_typedef .

definition \<open>fun_upd_eSuc x M = M(x := eSuc (M x))\<close>
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

definition \<open>non_zero_elements M = {x. M x \<noteq> (0 :: enat)}\<close>
parametric_constant non_zero_elements_parametric: non_zero_elements_def

lift_definition cset_of_cmset :: \<open>'a cmset \<Rightarrow> 'a cset\<close> is
  non_zero_elements parametric non_zero_elements_parametric[OF bi_unique_eq refl]
  unfolding non_zero_elements_def .

definition \<open>enat_of_membership X x = (if x \<in> X then 1 :: enat else 0)\<close>
parametric_constant enat_of_membership_parametric: enat_of_membership_def

lift_definition cmset_of_cset :: \<open>'a cset \<Rightarrow> 'a cmset\<close> is
  enat_of_membership parametric enat_of_membership_parametric[of HOL.eq, OF refl refl]
  unfolding enat_of_membership_def by simp

end

declare (in cmset_as_typedef) cminsert.transfer[transfer_rule]
declare (in cmset_as_typedef) cset_of_cmset.transfer[transfer_rule]
declare (in cmset_as_typedef) cmset_of_cset.transfer[transfer_rule]

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

abbreviation \<open>in_cmset x M \<equiv> x \<in> cmset M\<close>
abbreviation \<open>cmsingle x \<equiv> cminsert x cmempty\<close>

lemma cmset_cmempty[simp]:
  \<open>cmset cmempty = {}\<close>
  unfolding cmset_alt using cmcount_cmempty by simp

context begin
interpretation cmset_as_typedef .

lemma cmset_cmsingle[simp]:
  \<open>cmset (cmsingle x) = {x}\<close>
  by transfer (simp add: fun_upd_eSuc_def)

end

section \<open>Commutative monoid\<close>

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

lemma cmcount_plus:
  \<open>cmcount (M + N) x = cmcount M x + cmcount N x\<close>
  unfolding plus_cmset_def cmcount_cmadd ..

lemma in_cmset_plus:
  \<open>in_cmset x (M + N) \<longleftrightarrow> in_cmset x M \<or> in_cmset x N\<close>
  unfolding cmset_alt cmcount_plus by simp

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

section \<open>Minus\<close>

instantiation cmset :: (type) minus
begin
interpretation cmset_as_typedef .

parametric_constant fun_diff_parametric: fun_diff_def

lift_definition minus_cmset :: \<open>'a cmset \<Rightarrow> 'a cmset \<Rightarrow> 'a cmset\<close> is
  \<open>(-)\<close> parametric fun_diff_parametric
proof -
  fix M N :: \<open>'a \<Rightarrow> enat\<close>
  assume \<open>countable {x. M x \<noteq> 0}\<close>
  moreover have \<open>{x. M x - N x \<noteq> 0} \<subseteq> {x. M x \<noteq> 0}\<close> by force
  ultimately show \<open>countable {x. (M - N) x \<noteq> 0}\<close> using countable_subset by auto
qed

instance ..

end

declare (in cmset_as_typedef) minus_cmset.transfer[transfer_rule]

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

lemma cmset_minus_plus:
  \<open>(M :: _ cmset) - (N + N') = M - N - N'\<close>
  using cmset_eq_iff enat_minus_plus cmcount_plus cmcount_minus by metis

lemma cmempty_minus[simp]:
  \<open>cmempty - M = cmempty\<close>
  \<open>M - cmempty = M\<close>
  using cmset_eq_iff cmcount_cmempty cmcount_minus idiff_0 idiff_0_right by metis+

section \<open>Bounded distributive lattice with bottom element\<close>

instantiation cmset :: (type) \<open>{bounded_lattice_bot, distrib_lattice}\<close>
begin
interpretation cmset_as_typedef .

lift_definition inf_cmset :: \<open>'a cmset \<Rightarrow> 'a cmset \<Rightarrow> 'a cmset\<close> is \<open>\<lambda>M N x. min (M x) (N x)\<close>
proof -
  fix M N :: \<open>'a \<Rightarrow> enat\<close>
  assume \<open>countable {x. M x \<noteq> 0}\<close>
  moreover have \<open>{x. min (M x) (N x) \<noteq> 0} \<subseteq> {x. M x \<noteq> 0}\<close> by force
  ultimately show \<open>countable {x. min (M x) (N x) \<noteq> 0}\<close> using countable_subset by meson
qed

lift_definition sup_cmset :: \<open>'a cmset \<Rightarrow> 'a cmset \<Rightarrow> 'a cmset\<close> is \<open>\<lambda>M N x. max (M x) (N x)\<close>
proof -
  fix M N :: \<open>'a \<Rightarrow> enat\<close>
  assume \<open>countable {x. M x \<noteq> 0}\<close> \<open>countable {x. N x \<noteq> 0}\<close>
  moreover have \<open>{x. max (M x) (N x) \<noteq> 0} \<subseteq> {x. M x \<noteq> 0} \<union> {x. N x \<noteq> 0}\<close> by force
  ultimately show \<open>countable {x. max (M x) (N x) \<noteq> 0}\<close> using countable_subset countable_Un by meson
qed

definition \<open>\<bottom> = cmempty\<close>

definition \<open>M \<le> N \<longleftrightarrow> (\<forall>x. cmcount M x \<le> cmcount N x)\<close>

definition \<open>(M :: _ cmset) < N \<longleftrightarrow> M \<le> N \<and> \<not> N \<le> M\<close>

instance
proof
  fix X Y Z :: \<open>'a cmset\<close>
  show \<open>X \<le> Y \<Longrightarrow> Y \<le> Z \<Longrightarrow> X \<le> Z\<close> unfolding less_eq_cmset_def using order.trans by blast
  show \<open>X \<le> Y \<Longrightarrow> Y \<le> X \<Longrightarrow> X = Y\<close> unfolding less_eq_cmset_def cmset_eq_iff order_eq_iff by fast
  show \<open>X \<squnion> Y \<sqinter> Z = (X \<squnion> Y) \<sqinter> (X \<squnion> Z)\<close> by transfer (use max_min_distrib2 in fast)
qed (unfold bot_cmset_def less_eq_cmset_def less_cmset_def; transfer; simp)+

end

declare (in cmset_as_typedef) inf_cmset.transfer[transfer_rule]
declare (in cmset_as_typedef) sup_cmset.transfer[transfer_rule]

section \<open>Conversion from list to countable multiset\<close>

context begin
interpretation cmset_as_Quotient .

lift_definition cmset_of_list :: \<open>'a list \<Rightarrow> 'a cmset\<close> is llist_of parametric llist_of_transfer .

end

declare (in cmset_as_Quotient) cmset_of_list.transfer[transfer_rule]

lemma (in cmset_as_typedef) cmset_of_list_transfer[transfer_rule]:
  \<open>rel_fun (list_all2 A) (pcr_cmset A) (\<lambda>xs x. enat (count_list xs x)) cmset_of_list\<close>
  oops

(* TODO? Use transfer in cmset_as_Quotient. *)
lemma cmset_of_list_Nil[simp]:
  \<open>cmset_of_list [] = cmempty\<close>
  by (simp add: cmempty_def cmset_of_list.abs_eq)

context begin
interpretation cmset_as_Quotient .

lemma cmset_of_list_Cons[simp]:
  \<open>cmset_of_list (x # xs) = cminsert x (cmset_of_list xs)\<close>
  by transfer (simp add: eq_cmset_def)

end

(* TODO? Use transfer in cmset_as_Quotient. *)
lemma cmset_of_list_append:
  \<open>cmset_of_list (xs @ ys) = cmset_of_list xs + cmset_of_list ys\<close>
  by (simp add: plus_cmset_def cmcount.abs_eq cmset_eq_iff cmset_of_list.abs_eq)

(* TODO? Use transfer in cmset_as_Quotient. *)
lemma cmset_cmset_of_list[simp]:
  \<open>cmset (cmset_of_list xs) = set xs\<close>
  using set_eq_iff cmcount.abs_eq cmset_alt cmset_of_list.abs_eq in_lset_iff_count_llist
    lset_llist_of mem_Collect_eq by (metis (mono_tags, lifting))

section \<open>Conversion between countable set and countable multiset\<close>

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

end

end