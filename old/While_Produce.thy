theory While_Produce
  imports
    "Coinductive.Coinductive_List"
    "HOL-Library.While_Combinator"
begin

codatatype ('o, 'i) op = Logic ("apply": "('i \<Rightarrow> ('o, 'i) op \<times> 'o list)")

abbreviation "produce_inner_aux op lxs \<equiv>
  while_option
    (\<lambda>(op, lxs). \<not> lnull lxs \<and> snd (apply op (lhd lxs)) = [])
    (\<lambda>(op, lxs). (fst (apply op (lhd lxs)), ltl lxs))
    (op, lxs)"

abbreviation "produce_inner op lxs \<equiv>
  (case produce_inner_aux op lxs of
    None \<Rightarrow> None
  | Some (op', lxs') \<Rightarrow> if lnull lxs' then None else
    let (op'', out) = apply op' (lhd lxs') in Some (op'', hd out, tl out, ltl lxs'))"

lemma produce_inner_induct:
  assumes "produce_inner op lxs = Some y"
  and "\<And>op h lxs' op' zs. apply op h = (op', []) \<Longrightarrow> Q op' lxs' zs \<Longrightarrow> Q op (LCons h lxs') zs"
  and "\<And>op h x xs lxs' op'. apply op h = (op', x # xs) \<Longrightarrow> Q op (LCons h lxs') (op', x, xs, lxs')"
  shows "Q op lxs y"
  using assms(1)
  apply (simp split: option.splits prod.splits if_splits)
  apply (frule while_option_stop)
  apply (drule while_option_rule[rotated,
        where P="\<lambda>(op', lxs'). \<forall>zs. Q op' lxs' zs \<longrightarrow> Q op lxs zs"])
    apply simp
     apply (auto simp: neq_Nil_conv lnull_def neq_LNil_conv assms(2,3))
   apply (metis assms(2) prod.collapse)
  done

lemma produce_inner_code: "produce_inner op lxs = (case lxs of
        LNil \<Rightarrow> None
     | LCons h lxs' \<Rightarrow> (case apply op h of
                         (lgc', []) \<Rightarrow> produce_inner lgc' lxs'
                       | (lgc', x#xs) \<Rightarrow> Some (lgc', x, xs, lxs')))"
  by (subst (1) while_option_unfold)
    (auto split: llist.splits prod.splits list.splits)


end