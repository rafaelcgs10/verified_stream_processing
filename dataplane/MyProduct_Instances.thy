theory MyProduct_Instances

imports
  Containers.Collection_Order
  "HOL-Library.Countable"
  Nondeterministic_Dataflow.CSet_LList_Impl
begin

datatype ('a, 'b) myprod = MyPair (myfst: 'a) (mysnd: 'b)

derive ccompare myprod

(* Copy of Product_Plus *)

subsection \<open>Operations\<close>

instantiation myprod :: (zero, zero) zero
begin

definition zero_myprod_def: "0 = MyPair 0 0"

instance ..
end

instantiation myprod :: (plus, plus) plus
begin

definition plus_myprod_def:
  "x + y = MyPair (myfst x + myfst y) (mysnd x + mysnd y)"

instance ..
end

instantiation myprod :: (minus, minus) minus
begin

definition minus_myprod_def:
  "x - y = MyPair (myfst x - myfst y) (mysnd x - mysnd y)"

instance ..
end

instantiation myprod :: (uminus, uminus) uminus
begin

definition uminus_myprod_def:
  "- x = MyPair (- myfst x) (- mysnd x)"

instance ..
end

lemma myfst_zero [simp]: "myfst 0 = 0"
  unfolding zero_myprod_def by simp

lemma mysnd_zero [simp]: "mysnd 0 = 0"
  unfolding zero_myprod_def by simp

lemma myfst_add [simp]: "myfst (x + y) = myfst x + myfst y"
  unfolding plus_myprod_def by simp

lemma mysnd_add [simp]: "mysnd (x + y) = mysnd x + mysnd y"
  unfolding plus_myprod_def by simp

lemma myfst_diff [simp]: "myfst (x - y) = myfst x - myfst y"
  unfolding minus_myprod_def by simp

lemma mysnd_diff [simp]: "mysnd (x - y) = mysnd x - mysnd y"
  unfolding minus_myprod_def by simp

lemma myfst_uminus [simp]: "myfst (- x) = - myfst x"
  unfolding uminus_myprod_def by simp

lemma mysnd_uminus [simp]: "mysnd (- x) = - mysnd x"
  unfolding uminus_myprod_def by simp

lemma add_MyPair [simp]: "MyPair a b + MyPair c d = MyPair (a + c) (b + d)"
  unfolding plus_myprod_def by simp

lemma diff_MyPair [simp]: "MyPair a b - MyPair c d = MyPair (a - c) (b - d)"
  unfolding minus_myprod_def by simp

lemma uminus_MyPair [simp, code]: "- MyPair a b = MyPair (- a) (- b)"
  unfolding uminus_myprod_def by simp

subsection \<open>Class instances\<close>

lemma myprod_eq_iff: "s = t \<longleftrightarrow> myfst s = myfst t \<and> mysnd s = mysnd t"
  by (cases s, cases t) simp

lemma myprod_eqI [intro?]: "myfst p = myfst q \<Longrightarrow> mysnd p = mysnd q \<Longrightarrow> p = q"
  by (simp add: myprod_eq_iff)

instance myprod :: (semigroup_add, semigroup_add) semigroup_add
  by standard (simp add: myprod_eq_iff add.assoc)

instance myprod :: (ab_semigroup_add, ab_semigroup_add) ab_semigroup_add
  by standard (simp add: myprod_eq_iff add.commute)

instance myprod :: (monoid_add, monoid_add) monoid_add
  by standard (simp_all add: myprod_eq_iff)

instance myprod :: (comm_monoid_add, comm_monoid_add) comm_monoid_add
  by standard (simp add: myprod_eq_iff)

instance myprod :: (cancel_semigroup_add, cancel_semigroup_add) cancel_semigroup_add
  by standard (simp_all add: myprod_eq_iff)

instance myprod :: (cancel_ab_semigroup_add, cancel_ab_semigroup_add) cancel_ab_semigroup_add
  by standard (simp_all add: myprod_eq_iff diff_diff_eq)

instance myprod :: (cancel_comm_monoid_add, cancel_comm_monoid_add) cancel_comm_monoid_add ..

instance myprod :: (group_add, group_add) group_add
  by standard (simp_all add: myprod_eq_iff)

instance myprod :: (ab_group_add, ab_group_add) ab_group_add
  by standard (simp_all add: myprod_eq_iff)

lemma myfst_sum: "myfst (\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. myfst (f x))"
proof (cases "finite A")
  case True
  then show ?thesis by induct simp_all
next
  case False
  then show ?thesis by simp
qed

lemma mysnd_sum: "mysnd (\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. mysnd (f x))"
proof (cases "finite A")
  case True
  then show ?thesis by induct simp_all
next
  case False
  then show ?thesis by simp
qed

lemma sum_myprod: "(\<Sum>x\<in>A. MyPair (f x) (g x)) = MyPair (\<Sum>x\<in>A. f x) (\<Sum>x\<in>A. g x)"
proof (cases "finite A")
  case True
  then show ?thesis by induct (simp_all add: zero_myprod_def)
next
  case False
  then show ?thesis by (simp add: zero_myprod_def)
qed

(* Copy of Product_Order *)

subsection \<open>Pointwise ordering\<close>

instantiation myprod :: (ord, ord) ord
begin

definition
  "x \<le> y \<longleftrightarrow> myfst x \<le> myfst y \<and> mysnd x \<le> mysnd y"

definition
  "(x:: ('a, 'b) myprod) < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

instance ..

end

lemma myfst_mono: "x \<le> y \<Longrightarrow> myfst x \<le> myfst y"
  unfolding less_eq_myprod_def by simp

lemma mysnd_mono: "x \<le> y \<Longrightarrow> mysnd x \<le> mysnd y"
  unfolding less_eq_myprod_def by simp

lemma MyPair_mono: "x \<le> x' \<Longrightarrow> y \<le> y' \<Longrightarrow> MyPair x y \<le> MyPair x' y'"
  unfolding less_eq_myprod_def by simp

lemma MyPair_le [simp]: "MyPair a b \<le> MyPair c d \<longleftrightarrow> a \<le> c \<and> b \<le> d"
  unfolding less_eq_myprod_def by simp

lemma atLeastAtMost_myprod_eq: "{a..b} = (\<Union>x\<in>{myfst a..myfst b}. \<Union>y\<in>{mysnd a..mysnd b}. {MyPair x y})"
  by (auto simp: less_eq_myprod_def) force

instance myprod :: (preorder, preorder) preorder
proof
  fix x y z :: "('a, 'b) myprod"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (rule less_myprod_def)
  show "x \<le> x"
    unfolding less_eq_myprod_def
    by fast
  assume "x \<le> y" and "y \<le> z" thus "x \<le> z"
    unfolding less_eq_myprod_def
    by (fast elim: order_trans)
qed

instance myprod :: (order, order) order
  by standard (simp add: myfst_mono myprod_eq_iff mysnd_mono order_antisym)

subsection \<open>Binary infimum and supremum\<close>

instantiation myprod :: (inf, inf) inf
begin

definition "inf x y = MyPair (inf (myfst x) (myfst y)) (inf (mysnd x) (mysnd y))"

lemma inf_MyPair_MyPair [simp]: "inf (MyPair a b) (MyPair c d) = MyPair (inf a c) (inf b d)"
  unfolding inf_myprod_def by simp

lemma myfst_inf [simp]: "myfst (inf x y) = inf (myfst x) (myfst y)"
  unfolding inf_myprod_def by simp

lemma mysnd_inf [simp]: "mysnd (inf x y) = inf (mysnd x) (mysnd y)"
  unfolding inf_myprod_def by simp

instance ..

end

instance myprod :: (semilattice_inf, semilattice_inf) semilattice_inf
  by standard (simp_all add: less_eq_myprod_def)

instantiation myprod :: (sup, sup) sup
begin

definition
  "sup x y = MyPair (sup (myfst x) (myfst y)) (sup (mysnd x) (mysnd y))"

lemma sup_MyPair_MyPair [simp]: "sup (MyPair a b) (MyPair c d) = MyPair (sup a c) (sup b d)"
  unfolding sup_myprod_def by simp

lemma myfst_sup [simp]: "myfst (sup x y) = sup (myfst x) (myfst y)"
  unfolding sup_myprod_def by simp

lemma mysnd_sup [simp]: "mysnd (sup x y) = sup (mysnd x) (mysnd y)"
  unfolding sup_myprod_def by simp

instance ..

end

instance myprod :: (semilattice_sup, semilattice_sup) semilattice_sup
  by standard (simp_all add: less_eq_myprod_def)

instance myprod :: (lattice, lattice) lattice ..

instance myprod :: (distrib_lattice, distrib_lattice) distrib_lattice
  by standard (simp add: sup_inf_distrib1 sup_myprod_def)

subsection \<open>Top and bottom elements\<close>

instantiation myprod :: (top, top) top
begin

definition
  "top = MyPair top top"

instance ..

end

lemma myfst_top [simp]: "myfst top = top"
  unfolding top_myprod_def by simp

lemma mysnd_top [simp]: "mysnd top = top"
  unfolding top_myprod_def by simp

lemma MyPair_top_top: "MyPair top top = top"
  unfolding top_myprod_def by simp

instance myprod :: (order_top, order_top) order_top
  by standard (simp add: less_eq_myprod_def)

instantiation myprod :: (bot, bot) bot
begin

definition
  "bot = MyPair bot bot"

instance ..

end

lemma myfst_bot [simp]: "myfst bot = bot"
  unfolding bot_myprod_def by simp

lemma mysnd_bot [simp]: "mysnd bot = bot"
  unfolding bot_myprod_def by simp

lemma MyPair_bot_bot: "MyPair bot bot = bot"
  unfolding bot_myprod_def by simp

instance myprod :: (order_bot, order_bot) order_bot
  by standard (simp add: less_eq_myprod_def)

instance myprod :: (bounded_lattice, bounded_lattice) bounded_lattice ..

instance myprod :: (boolean_algebra, boolean_algebra) boolean_algebra
  by standard (simp_all add: myprod_eqI diff_eq)

subsection \<open>Complete lattice operations\<close>

instantiation myprod :: (Inf, Inf) Inf
begin

definition "Inf A = MyPair (INF x\<in>A. myfst x) (INF x\<in>A. mysnd x)"

instance ..

end

instantiation myprod :: (Sup, Sup) Sup
begin

definition "Sup A = MyPair (SUP x\<in>A. myfst x) (SUP x\<in>A. mysnd x)"

instance ..

end

instance myprod :: (conditionally_complete_lattice, conditionally_complete_lattice)
    conditionally_complete_lattice
  by standard (force simp: less_eq_myprod_def Inf_myprod_def Sup_myprod_def bdd_below_def bdd_above_def
    intro!: cInf_lower cSup_upper cInf_greatest cSup_least)+

instance myprod :: (complete_lattice, complete_lattice) complete_lattice
  by standard (simp_all add: less_eq_myprod_def Inf_myprod_def Sup_myprod_def
    INF_lower SUP_upper le_INF_iff SUP_le_iff bot_myprod_def top_myprod_def)

lemma myfst_Inf: "myfst (Inf A) = (INF x\<in>A. myfst x)"
  by (simp add: Inf_myprod_def)

lemma myfst_INF: "myfst (INF x\<in>A. f x) = (INF x\<in>A. myfst (f x))"
  by (simp add: myfst_Inf image_image)

lemma myfst_Sup: "myfst (Sup A) = (SUP x\<in>A. myfst x)"
  by (simp add: Sup_myprod_def)

lemma myfst_SUP: "myfst (SUP x\<in>A. f x) = (SUP x\<in>A. myfst (f x))"
  by (simp add: myfst_Sup image_image)

lemma mysnd_Inf: "mysnd (Inf A) = (INF x\<in>A. mysnd x)"
  by (simp add: Inf_myprod_def)

lemma mysnd_INF: "mysnd (INF x\<in>A. f x) = (INF x\<in>A. mysnd (f x))"
  by (simp add: mysnd_Inf image_image)

lemma mysnd_Sup: "mysnd (Sup A) = (SUP x\<in>A. mysnd x)"
  by (simp add: Sup_myprod_def)

lemma mysnd_SUP: "mysnd (SUP x\<in>A. f x) = (SUP x\<in>A. mysnd (f x))"
  by (simp add: mysnd_Sup image_image)

lemma INF_MyPair: "(INF x\<in>A. MyPair (f x) (g x)) = MyPair (INF x\<in>A. f x) (INF x\<in>A. g x)"
  by (simp add: Inf_myprod_def image_image)

lemma SUP_MyPair: "(SUP x\<in>A. MyPair (f x) (g x)) = MyPair (SUP x\<in>A. f x) (SUP x\<in>A. g x)"
  by (simp add: Sup_myprod_def image_image)

text \<open>Alternative formulations for set infima and suprema over the myproduct
of two complete lattices:\<close>

lemma INF_myprod_alt_def:
  "Inf (f ` A) = MyPair (Inf ((myfst \<circ> f) ` A)) (Inf ((mysnd \<circ> f) ` A))"
  by (simp add: Inf_myprod_def image_image)

lemma SUP_myprod_alt_def:
  "Sup (f ` A) = MyPair (Sup ((myfst \<circ> f) ` A)) (Sup((mysnd \<circ> f) ` A))"
  by (simp add: Sup_myprod_def image_image)

subsection \<open>Complete distributive lattices\<close>

instance myprod :: (complete_distrib_lattice, complete_distrib_lattice) complete_distrib_lattice
proof
  fix A::"('a, 'b) myprod set set"
  show "Inf (Sup ` A) \<le> Sup (Inf ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y})"
    by (simp add: Inf_myprod_def Sup_myprod_def INF_SUP_set image_image)
qed

(* Bekic's Theorem omitted *)

instantiation myprod :: (ordered_ab_semigroup_add, ordered_ab_semigroup_add) ordered_ab_semigroup_add
begin
instance by standard (simp add: add_left_mono less_eq_myprod_def)
end

instantiation myprod :: (ordered_comm_monoid_add, ordered_comm_monoid_add) ordered_comm_monoid_add
begin
instance ..
end

instantiation myprod :: (ordered_ab_semigroup_monoid_add_imp_le, ordered_ab_semigroup_monoid_add_imp_le) ordered_ab_semigroup_monoid_add_imp_le
begin
instance by standard (simp add: less_eq_myprod_def)
end

instantiation myprod :: (canonically_ordered_monoid_add, canonically_ordered_monoid_add) canonically_ordered_monoid_add
begin
instance
proof
  fix a b :: \<open>('a, 'b) myprod\<close>
  show \<open>a \<le> b \<longleftrightarrow> (\<exists>c. b = a + c)\<close>
    by (simp add: le_iff_add less_eq_myprod_def) (metis myprod.exhaust_sel myprod.sel(1,2) plus_myprod_def)
qed
end

definition "to_prod p = (case p of MyPair p1 p2 \<Rightarrow> (p1, p2))"
definition "from_prod p = (case p of (p1, p2) \<Rightarrow> MyPair p1 p2)"

instance myprod :: (countable, countable) countable
  apply (rule countable_classI [of "(\<lambda>(x, y). (prod_encode) (to_nat x, to_nat y)) o to_prod"])
  apply  (auto simp add: to_prod_def split: myprod.splits)
  done

instantiation myprod :: (cenum, cenum) cenum begin
definition cenum_myprod :: "('a, 'b) myprod llist" where "cenum_myprod = lmerge (lmap (\<lambda> x. lmap (MyPair x) cenum) cenum)"
instance
  apply standard
  unfolding cenum_myprod_def from_prod_def lset_lmap
  apply (auto simp: cenum_prod_def image_iff inj_on_def order_less_subst2 UNIV_cenum[symmetric] cenum_distinct
      intro!: ldistinct_linterleave ldistinct_lmerge
      dest!: cenum_distinct[unfolded ldistinct_conv_lnth, rule_format, THEN notE, rotated -1] split: myprod.splits)
  subgoal for x
    apply (cases x)
    apply auto
    done
  done
end

end