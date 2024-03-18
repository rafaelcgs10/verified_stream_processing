section \<open>Pointwise order on sum types\<close>

theory Sum_Order
  imports 
    Main
begin

subsection \<open>Pointwise ordering\<close>

instantiation sum :: (ord, ord) ord
begin

inductive less_eq_sum :: "'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool" where
  Inl_leq: "t \<le> u \<Longrightarrow> less_eq_sum (Inl t) (Inl u)"
| Inr_leq: "t \<le> u \<Longrightarrow> less_eq_sum (Inr t) (Inr u)"

definition
  "(x::'a + 'b) < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

instance ..

end

instance sum :: (preorder, preorder) preorder
proof
  fix x y z :: "'a + 'b"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (rule less_sum_def)
  show "x \<le> x"
    apply (cases x)
     apply (auto intro: less_eq_sum.intros)
    done

  assume "x \<le> y" and "y \<le> z" thus "x \<le> z"
    apply (cases x; cases y; cases z)
           apply (auto intro!: less_eq_sum.intros elim!: less_eq_sum.cases order_trans)
    done
qed

instance sum :: (order, order) order
  apply standard
  subgoal for x y
    apply (cases x; cases y)
       apply (auto intro!: antisym elim: less_eq_sum.cases)
    done
  done


lemma [simp,code]:
  "Inl l1 < Inl l2 \<longleftrightarrow> (l1::_::order) < l2"
  "Inr r1 < Inr r2 \<longleftrightarrow> (r1::_::order) < r2"
  "Inr a < Inl b \<longleftrightarrow> False"
  "Inl a < Inr b \<longleftrightarrow> False"
  "Inl l1 = Inl l2 \<longleftrightarrow> (l1::_::order) = l2"
  "Inr r1 = Inr r2 \<longleftrightarrow> (r1::_::order) = r2"
  "Inr a = Inl b \<longleftrightarrow> False"
  "Inl a = Inr b \<longleftrightarrow> False"
  "Inl l1 \<le> Inl l2 \<longleftrightarrow> (l1::_::order) \<le> l2"
  "Inr r1 \<le> Inr r2 \<longleftrightarrow> (r1::_::order) \<le> r2"
  "Inr a \<le> Inl b \<longleftrightarrow> False"
  "Inl a \<le> Inr b \<longleftrightarrow> False"
  apply auto
  apply (metis Inl_Inr_False Inl_leq less_eq_sum.cases less_le_not_le less_sum_def sum.sel(1))
  apply (smt (verit, best) Inl_Inr_False Inl_leq dual_order.strict_implies_order leD less_eq_sum.cases less_sum_def sum.sel(1))
  apply (metis Inl_Inr_False Inr_inject less_eq_sum.cases less_sum_def nless_le)
  subgoal
    by (smt (verit) Inr_leq dual_order.strict_iff_order less_eq_sum.cases less_sum_def old.sum.inject(2) sum.simps(4))
  subgoal
    by (metis Inl_Inr_False less_eq_sum.cases less_sum_def)
  subgoal
    by (metis Inl_Inr_False less_eq_sum.cases less_sum_def)
  subgoal
    using less_eq_sum.cases by fastforce
  subgoal
    using Inl_leq by blast
  subgoal
    using less_eq_sum.cases by blast
  subgoal
    by (simp add: Inr_leq)
  subgoal
    using less_eq_sum.simps by blast
  subgoal
    using less_eq_sum.cases by fastforce
  done


lemma [simp]:
  "Inl a \<le> Inr a \<longleftrightarrow> False"
  "Inr b \<le> Inl b \<longleftrightarrow> False"
  using less_eq_sum.cases by fastforce+

lemma [simp]:
  "\<not> wm \<le> (case (wm::_::order) of Inl x \<Rightarrow> Inr x | Inr x \<Rightarrow> Inl x) \<longleftrightarrow> True"
  apply (cases wm)
  apply auto
  done

end