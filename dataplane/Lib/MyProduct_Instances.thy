theory MyProduct_Instances

imports
  Containers.Collection_Order
  "HOL-Library.Countable"
  Nondeterministic_Dataflow.CSet_LList_Impl
  "HOL-Library.Product_Lexorder"
begin

class order_ccompare = order + ccompare +
  assumes not_none: "ID CCOMPARE('a) \<noteq> None" 
    and extension: "\<And> s t. s < t \<Longrightarrow> cless s t"
begin
lemma comparator_ccomp:
  "comparator ccomp"
  by (simp add: local.ID_ccompare' local.not_none)
end

instantiation nat :: order_ccompare
begin
instance
  apply standard
  apply (simp_all add: lt_of_comp_def compare_nat_def ID_code ccompare_nat_def)
  apply (metis compare_nat_def two_comparisons_into_compare(6))
  done
end

instantiation prod :: (order_ccompare, order_ccompare) order_ccompare
begin
instance
  apply standard
  subgoal
    by (metis (lifting) ID_code ccompare_prod_def is_none_code(1,2) not_none option.case_eq_if)
  subgoal for s t
    unfolding ccompare_prod_def
    apply (auto simp add: not_none split: option.splits)
    subgoal for a b
      apply (cases s; cases t)
    unfolding ID_def
    apply auto
     apply (metis ID_Some extension lt_of_comp_prod option.sel)
    apply (metis ID_Some cless_eq_conv_cless extension lt_of_comp_prod not_none option.sel order_le_less)
    done
  done
  done
end

datatype ('a, 'b) myprod = MyPair (myfst: 'a) (mysnd: 'b)

lemma the_ID_Some[simp]:
  "the (ID (Some x)) = x"
  by (auto simp: ID_def)


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


lemma myfst_Sup: "myfst (Sup A) = (SUP x\<in>A. myfst x)"
  by (simp add: Sup_myprod_def)


lemma mysnd_Inf: "mysnd (Inf A) = (INF x\<in>A. mysnd x)"
  by (simp add: Inf_myprod_def)


lemma mysnd_Sup: "mysnd (Sup A) = (SUP x\<in>A. mysnd x)"
  by (simp add: Sup_myprod_def)




text \<open>Alternative formulations for set infima and suprema over the myproduct
of two complete lattices:\<close>



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


instantiation myprod :: (order_ccompare, order_ccompare) order_ccompare
begin

definition ccompare_myprod :: "(('a, 'b) myprod \<Rightarrow> ('a, 'b) myprod \<Rightarrow> order) option" where
  "ccompare_myprod = Some (\<lambda>a b. if a < b then Lt else (if b < a then Gt else ccomp (myfst a, mysnd a) (myfst b, mysnd b)))"

instance
  apply standard
    defer
  subgoal
    by (simp add: ID_code ccompare_myprod_def)
  subgoal
    by (simp add: ID_code ccompare_myprod_def lt_of_comp_def)
  subgoal for comp
    unfolding ccompare_myprod_def option.inject
    apply hypsubst_thin
    apply standard
    subgoal for x y
      apply (cases x; cases y)
      apply (auto simp add: comparator.sym[OF comparator_ccomp]  less_eq_myprod_def less_myprod_def split: if_splits)
      done
    subgoal for x y
      apply (cases x; cases y)
      apply (auto simp add: comparator.eq[OF comparator_ccomp]  less_eq_myprod_def less_myprod_def split: if_splits)
      done
    subgoal for x y z
      apply (cases x; cases y; cases z)
      apply (clarsimp intro: simp add: not_none ccompare_prod_def less_eq_myprod_def less_myprod_def split: order.splits if_splits option.splits intro: )
      using comparator.comp_trans[OF comparator_ccomp] apply force
             apply (metis ID_code ccompare comparator.Lt_lt_conv comparator_def order.trans extension option.sel order.distinct(3,5) order_le_less)
            apply (metis ID_code ccompare comparator.Lt_lt_conv comparator_def order.trans extension option.sel order.distinct(3,5) order_le_less)
           apply (metis ID_code ccompare comparator.Lt_lt_conv comparator_def order.trans extension option.sel order.distinct(3,5) order_le_less)
          apply (metis ID_code ccompare comparator.Lt_lt_conv comparator_def order.trans extension option.sel order.distinct(3,5) order_le_less)
      subgoal
        by (smt (verit)
            \<open>\<And>y x. invert_order (if x < y then Lt else if y < x then Gt else ccomp (myfst x, mysnd x) (myfst y, mysnd y)) = (if y < x then Lt else if x < y then Gt else ccomp (myfst y, mysnd y) (myfst x, mysnd x))\<close>
            comparator.Lt_lt_conv comparator_ccomp comparator_def extension less_eq_myprod_def less_myprod_def myprod.sel(1,2) option.sel order.distinct(3)
            order.simps(6) order_le_less)
        prefer 3
      subgoal
        by (metis (no_types, opaque_lifting) \<open>\<And>z y x. ccomp x y = Lt \<Longrightarrow> ccomp y z = Lt \<Longrightarrow> ccomp x z = Lt\<close> comparator.Gt_lt_conv comparator.Lt_lt_conv
            comparator_ccomp extension option.sel order.distinct(1) order.simps(6) order_le_imp_less_or_eq)
      subgoal
        by (metis comparator.Gt_lt_conv comparator.weak_eq comparator_ccomp extension option.sel order.distinct(1) order.simps(6) order_le_less)
      subgoal
        by (metis comparator.Gt_lt_conv comparator.weak_eq comparator_ccomp extension option.sel order.distinct(1) order.simps(6) order_le_less)
      done
    done
  done
end


lemma myprod_le_iff_myfst_le_if_mysnd_zero:
  fixes s t :: \<open>('a::ord, 'b::{zero, order}) myprod\<close>
  assumes \<open>mysnd s = 0\<close>
    and \<open>mysnd t = 0\<close>
  shows \<open>s \<le> t \<longleftrightarrow> myfst s \<le> myfst t\<close>
  using assms
  apply (cases s; cases t)
  apply auto
  done

lemma myfst_le_if_myprod_le_mysnd_zero:
  fixes s t :: \<open>('a::ord, 'b::{zero, order}) myprod\<close>
  assumes \<open>s \<le> t\<close>
    and \<open>mysnd s = 0\<close>
    and \<open>mysnd t = 0\<close>
  shows \<open>myfst s \<le> myfst t\<close>
  using assms
  apply (simp add: myprod_le_iff_myfst_le_if_mysnd_zero)
  done

lemma myprod_le_if_myfst_le_mysnd_zero:
  fixes s t :: \<open>('a::ord, 'b::{zero, order}) myprod\<close>
  assumes \<open>myfst s \<le> myfst t\<close>
    and \<open>mysnd s = 0\<close>
    and \<open>mysnd t = 0\<close>
  shows \<open>s \<le> t\<close>
  using assms
  apply (simp add: myprod_le_iff_myfst_le_if_mysnd_zero)
  done
section \<open>Defaults for Products\<close>

text \<open>The defaults instance for pairs.\<close>

instantiation prod :: (defaults, type) defaults
begin
definition defaults_prod where "defaults_prod = defaults \<times> defaults"
instance
proof qed
end

subsection \<open>Linear Orders from ccompare\<close>

lemma class_linorder_lt_of_comp:
  "ID ccompare = Some a \<Longrightarrow> class.linorder (\<lambda>t u. lt_of_comp a t u \<or> t = u) (lt_of_comp a)"
  apply (frule ID_ccompare)
  apply (erule arg_cong2[where ?f=class.linorder, THEN iffD1, rotated 2])
   apply (auto simp add: le_of_comp_def lt_of_comp_def fun_eq_iff split: order.splits)
   apply (meson ID_ccompare' comparator.nEq_neq_conv)
  apply (simp add: ID_code ccompare comparator.comp_same)
  done

lemma linorder_order_ccompare:
 "class.linorder (\<lambda>(t :: 't :: order_ccompare) u. cless t u \<or> t = u) cless"
 proof -
    from not_none obtain comp where comp: "ID CCOMPARE('t) = Some comp" by auto
    have "class.linorder (\<lambda>t u. lt_of_comp comp t u \<or> t = u) (lt_of_comp comp)"
      by (rule class_linorder_lt_of_comp[OF comp])
    also have "lt_of_comp comp = (cless :: 't \<Rightarrow> 't \<Rightarrow> bool)"
      using comp by simp
    finally show ?thesis by assumption
  qed

end