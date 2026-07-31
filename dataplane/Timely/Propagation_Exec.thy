theory Propagation_Exec

imports
  Tree_Compile
  Containers.Collection_Order
begin           

section \<open>Executable Propagation Primitives\<close>

text \<open>
  These definitions and lemmas connect the executable stepper with the abstract
  dataflow-topology locale and establish basic algebraic properties used later.
\<close>

lemma AF_empty[simp]:
  "A -++- {}\<^sub>A = {#}\<^sub>z"
  by (metis after_summary_def dataflow_topology_from_tree.after_summary_empty_summary)

lemma AP_simp[simp]:
  "M -++- S = (\<Sum>s \<in> set_antichain S. image_zmset (\<lambda>t. t -+- s) M)"
  by (metis after_summary_def dataflow_topology_from_tree.after_summary_def)

definition take_step_locale where
  "take_step_locale df = take_step' df cless"

fun take_step where
  "take_step summary (CM loc t delta) c =
  (let c_pointstamps_old = c_pts c loc; c_pointstamps_new = (c_pts c)(loc := update_zmultiset (c_pts c loc) t delta)
   in c\<lparr>c_pts := c_pointstamps_new, c_work := (c_work c)(loc := c_work c loc + frontier_change_code c_pointstamps_old (c_pointstamps_new loc))\<rparr>)"
| "take_step summary PR c =
   (let (t, loc) = mymin_code (t_loc_pairs c); c_implications_old = c_imp c loc; c_implications_new = (c_imp c)(loc := c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#});
    c_worklist_removed_loc = map_entry loc (filter_zmset (\<lambda>t'. t' \<noteq> t)) (c_work c)
    in c\<lparr>c_work := \<lambda>loc'. c_worklist_removed_loc loc' + after_summary (frontier_change_code c_implications_old (c_implications_new loc)) (summary loc loc'),
        c_imp := c_implications_new\<rparr>)"

definition "propagate_all_locale summary df c0 = (while_option (Not o (worklist_is_empty summary))
                                           (take_step_locale df PR) c0)"

definition "propagate_all summary c0 = (while_option (Not o (worklist_is_empty summary))
                                        (take_step summary PR) c0)"

lemma take_step_fast_code[simp]:
  "take_step_locale df x = take_step (antichain_from_list oo (dataflow_tree_to_graph df)) x"
  unfolding take_step_locale_def
  apply (cases x)
   apply (auto simp add: fun_eq_iff mymin_code_def)
  done

lemma class_linorder_lt_of_comp:
  "ID ccompare = Some a \<Longrightarrow> class.linorder (\<lambda>t u. lt_of_comp a t u \<or> t = u) (lt_of_comp a)"
  apply (frule ID_ccompare)
  apply (erule arg_cong2[where ?f=class.linorder, THEN iffD1, rotated 2])
   apply (auto simp add: le_of_comp_def lt_of_comp_def fun_eq_iff split: order.splits)
   apply (meson ID_ccompare' comparator.nEq_neq_conv)
  apply (simp add: ID_code ccompare comparator.comp_same)
  done

lemma mymin_code_in_worklist:
  assumes "\<not> worklist_is_empty su c"
  and "mymin_code (t_loc_pairs c) = (t :: 't :: {order, ccompare}, (loc :: 'loc :: {enum,linorder}))"
  and "ID CCOMPARE('t) \<noteq> None"
  shows "t \<in>#\<^sub>z c_work c loc"
proof -
  have cless_linorder: "class.linorder (\<lambda>(t :: 't) u. cless t u \<or> t = u) cless"
  proof -
    from assms(3) obtain comp where comp: "ID CCOMPARE('t) = Some comp" by auto
    have "class.linorder (\<lambda>(t :: 't) u. lt_of_comp comp t u \<or> t = u) (lt_of_comp comp)"
      by (rule class_linorder_lt_of_comp[OF comp])
    also have "lt_of_comp comp = cless"
      using comp by simp
    finally show ?thesis
      by assumption
  qed
  interpret tloc: linorder "t_loc_linord cless" "\<lambda>(t :: 't \<times> 'loc) u. t_loc_linord cless t u \<and> t \<noteq> u"
    by (rule linorder_t_loc_linord[OF cless_linorder])
  have nonempty: "t_loc_pairs c \<noteq> {}"
    using assms(1)
    unfolding worklist_is_empty_def t_loc_pairs_def enum_class.enum_UNIV
    by auto
  have finite: "finite (t_loc_pairs c)"
    by (auto simp: t_loc_pairs_def intro:)
  have "(t, loc) \<in> t_loc_pairs c"
    using assms(2)
    unfolding mymin_code_def mymin_def
    using tloc.Min_in[OF finite nonempty]
    by simp
  then show ?thesis
    unfolding t_loc_pairs_def set_zmset_def
    by auto
qed

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

lemma mymin_code_is_minimum:
  assumes "mymin_code (t_loc_pairs c) = (t :: 't :: order_ccompare, (loc :: 'loc :: {enum,linorder}))"
  and "t' \<in>#\<^sub>z c_work c loc'"
  shows "\<not> t' < t"
proof -
  interpret tloc: linorder "t_loc_linord (cless :: 't \<Rightarrow> 't \<Rightarrow> bool)" "\<lambda>t u. t_loc_linord cless t u \<and> t \<noteq> u"
    by (rule linorder_t_loc_linord[OF linorder_order_ccompare])
  have finite: "finite (t_loc_pairs c)"
    by (auto simp: t_loc_pairs_def)
  have t'_in: "(t', loc') \<in> t_loc_pairs c"
    using assms(2) unfolding t_loc_pairs_def set_zmset_def
    by (auto simp: enum_UNIV)
  have "t_loc_linord cless (t, loc) (t', loc')"
    using assms(1) t'_in
    unfolding mymin_code_def mymin_def
    using tloc.Min_le[OF finite t'_in]
    by simp
  then have "cless t t' \<or> t = t'"
    unfolding t_loc_linord_def
    by (auto split: prod.splits)
  then show ?thesis
    using extension
    by (metis ID_code ccompare comparator.Gt_lt_conv comparator.le_lt_convs(4) not_none option.exhaust_sel order.distinct(5))
qed

lemma take_step_enum_dataflow_topology_take_step:
  "enum_dataflow_topology su dataflow_topology_from_tree.followed_by \<Longrightarrow>
   take_step su = enum_dataflow_topology.take_step su dataflow_topology_from_tree.followed_by cless"
  apply (rule ext)+
  subgoal for S c
    apply (cases S; hypsubst_thin)
     apply (simp add: Executable.enum_dataflow_topology.take_step.simps)
    apply (subst Executable.enum_dataflow_topology.take_step.simps(2))
     apply assumption
    apply (simp add: after_summary_def mymin_code_def)
    done
  done

lemma take_step_comm:
  "(take_step su (CM l2 t2 m2) \<circ>\<circ>\<circ> take_step) su (CM l1 t1 m1) = (take_step su (CM l1 t1 m1) \<circ>\<circ>\<circ> take_step) su (CM l2 t2 m2)"
  apply (rule ext)
  apply (auto simp add: fun_upd_twist update_zmultiset_comm)
  done

lemma take_step_plus[simp]:
  "take_step su (CM l t m) (take_step su (CM l t n) c) = take_step su (CM l t (m + n)) c"
  by (cases c; auto simp add: add.commute)

abbreviation "show_frontier x \<equiv> let f = Max_antichain x in if f = 42 then STR ''{}'' else STR ''{ '' + show_nat (Max_antichain x) + STR '' }''"

definition show_myprod where
  "show_myprod show1 show2 x = enclose (show1 (myfst x) + STR '','' + show2 (mysnd x))"

definition "show_myprod_frontier F \<equiv> (
  let S = to_prod ` antichain.set_antichain F in
  let m1 = Min S in 
  let S' = (S - {m1}) in 
  if F = {}\<^sub>A then STR ''{}'' else STR ''{'' + show_prod show_nat show_nat m1 + (if S' \<noteq> {} then STR '', '' +  show_prod show_nat show_nat (Min S')  else STR '''') + STR ''}'')"

abbreviation "show_frontiers impf \<equiv> show_list (show_prod show_loc show_frontier) (map (\<lambda> l. (l, frontier (impf l))) enum_location_inst.enum_location)"

end
