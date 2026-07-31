theory Zero_Cyc_Check
  imports
    (* "Vespa_Lib.Graph"
    "Dataplane.Antichain_Aux"
    "Dataplane.Executable_Aux" *)
    (*     "Collections.Collections"
 *)
    "DFS_Framework.Cyc_Check"
    Executable
    Progress_Tracking.Graph
    Progress_Tracking.Auxiliary

begin

declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]

(* Zero cycle checking and it correctness proof *)

section \<open>Graphs from Weight Functions\<close>

text \<open>Building graphs that keep only zero-weight summary edges.\<close>

abbreviation remove_non_zero_weights where
  "remove_non_zero_weights weights l1 l2 \<equiv> 
   (if (0::'a) \<in>\<^sub>A weights l1 l2 then antichain_from_list [0::'a::{order, monoid_add}] else antichain_from_list [])"

definition weights_to_graph_fun where
  "weights_to_graph_fun g l1 = filter (not (is_empty_antichain \<circ> (g l1))) Enum.enum"

lemma remove_non_zero_weights_is_graph: 
  "Graph.graph weights \<Longrightarrow> Graph.graph (remove_non_zero_weights weights)"
  using antichain_from_list_def Graph.graph_def conjI antichain_from_list_def empty_antichain.abs_eq
    mem_antichain_nonempty empty_antichain_def antichain_from_list.abs_eq filter.simps(1) list.set(1)
  by (smt (verit, del_insts))

lemma remove_non_zero_weights_path_all_zeros:
  assumes G: "Graph.graph weights"
    and P: "graph.path (remove_non_zero_weights weights) (loc::'loc::{enum,hashable,linorder}) loc' xs"
  shows "list_all (\<lambda> x . fst (snd x) = 0) xs"
  using P apply (induct rule: graph.path.induct [where weights="remove_non_zero_weights weights"])
  subgoal apply (simp add: G remove_non_zero_weights_is_graph) done
  subgoal apply (simp add: P) done
  subgoal apply simp done
  subgoal
    apply (subst list_all_append)
    apply (rule conjI)
    subgoal apply simp done
    subgoal apply (simp)
      apply (simp add: antichain_from_list_def split: if_splits)
      subgoal 
        apply (subst (asm) member_antichain.abs_eq)
        subgoal
          apply (simp add: eq_onp_def incomparable_def)
          done
        subgoal apply fastforce done
        done
      subgoal apply (metis empty_antichain_def mem_antichain_nonempty) done
      done
    done
  done

lemma remove_non_zero_sum_path_weights_zero:
  assumes G: "Graph.graph weights"
    and P: "graph.path (remove_non_zero_weights weights) loc loc' xs"
  shows "graph.sum_path_weights xs = 0"
  using P apply (induct rule: graph.path.induct [where weights="remove_non_zero_weights weights"])
  subgoal apply (simp add: G remove_non_zero_weights_is_graph) done
  subgoal apply (simp add: P) done
  subgoal apply simp done
  subgoal
    apply (subst map_append)
    apply (subst foldr_append)
    apply (simp)
    apply (simp add: antichain_from_list_def split: if_splits)
    subgoal 
      apply (subst (asm) member_antichain.abs_eq)
      subgoal
        apply (simp add: eq_onp_def incomparable_def)
        done
      subgoal apply fastforce done
      done
    subgoal apply (metis empty_antichain_def mem_antichain_nonempty) done
    done
  done

lemma remove_non_zero_weights_doenst_increase_weights:
  assumes G: "Graph.graph weights" 
    and P: "graph.path (remove_non_zero_weights weights) (loc::'loc::{enum,hashable,linorder}) loc xs"
    and S: "s = graph.sum_path_weights xs"
    and L: "t < t + s"
  shows "False"
proof - 
  from G P remove_non_zero_sum_path_weights_zero have "graph.sum_path_weights xs = 0" by blast
  from this L S show ?thesis by force
qed

lemma empty_path_inversion:
  assumes H1: "graph.path weights loc1 loc2 []"
    and H2: "Graph.graph weights"
  shows "loc1 = loc2"
  using assms graph.path0E by auto

lemma path_end_inversion_1: "Graph.graph weights \<Longrightarrow> graph.path weights loc1 loc2 (xs' @ [(l1, lbl, l2)]) \<Longrightarrow> l2 = loc2"
  using graph.path_AppendE by blast

lemma path_end_inversion_2: "Graph.graph weights \<Longrightarrow> graph.path weights loc1 loc2 ([(l1, lbl, l2)]) \<Longrightarrow> lbl \<in>\<^sub>A weights l1 l2"
  by (meson graph.path_edge list.set_intros(1))

lemma remove_non_zero_weights_only_zero: "(0::'a::{monoid_add,order}) \<in>\<^sub>A weights l1 l2 \<Longrightarrow> (0::'a) \<in>\<^sub>A remove_non_zero_weights weights l1 l2"
  unfolding antichain_from_list_def
  by (smt (verit, best) antichain_from_list.rep_eq antichain_from_list_def antichain_from_list_is_empty filter.simps(1,2) is_empty_antichain_empty_list is_empty_antichain_not_empty_list list.set_intros(1) member_antichain.rep_eq)

lemma remove_non_zero_weights_preserves_zero_path:
  assumes G: "Graph.graph weights"
    and P: "graph.path weights loc1 loc2 xs"
    and H: "list_all (\<lambda> x . fst (snd x) = 0) xs"
  shows "graph.path (remove_non_zero_weights weights) loc1 loc2 xs"
  using assms proof (induction xs arbitrary: loc1 loc2 rule: rev_induct)
  case Nil
  then show ?case using assms by (metis empty_path_inversion graph.path.intros(1) remove_non_zero_weights_is_graph)
next
  case (snoc a xs')
  then show ?case
  proof (cases a)
    case (fields l1 lbl l2)
    then have H3: "lbl = 0" 
      using assms snoc by simp
    then have H2: "loc2 = l2" 
      using assms snoc fields path_end_inversion_1 by blast
    then have H4: "graph.path (remove_non_zero_weights weights) loc1 l1 xs'" 
      using assms snoc by (metis fields graph.path_AppendE list_all_append)
    then obtain l2' where H5: "graph.path weights loc1 l2' xs' \<and> graph.path weights l2' loc2 [a]" 
      using snoc graph.path_appendE by blast
    then have H6: "l2' = l1" 
      using assms snoc fields H3 H4 by (metis graph.path_determines_loc list_all_append remove_non_zero_weights_is_graph)
    then have "graph.path (remove_non_zero_weights weights) l2' loc2 [a]" 
      using assms snoc fields H3 H4 H5 H6 by (metis H2 graph.path_singleton path_end_inversion_2 remove_non_zero_weights_is_graph remove_non_zero_weights_only_zero)
    then show ?thesis 
      using assms snoc fields graph.path_trans H3 H4 H5 H6 remove_non_zero_weights_is_graph by blast
  qed
qed

abbreviation no_zero_cycle where
  "no_zero_cycle weights \<equiv> (\<forall> loc t s xs. (graph.path weights loc loc xs \<longrightarrow> xs \<noteq> [] \<longrightarrow> s = graph.sum_path_weights xs \<longrightarrow> (t::'t::ordered_ab_semigroup_monoid_add_imp_le) < t + s))"

abbreviation no_zero_cycle_alt where
  "no_zero_cycle_alt weights \<equiv> (\<forall> loc xs. (graph.path weights loc loc xs \<longrightarrow> xs \<noteq> [] \<longrightarrow> 0 < ((graph.sum_path_weights xs)::'a::{ordered_ab_semigroup_monoid_add_imp_le})))"

lemma path_always_ge_zero: "Graph.graph (weights::'a::{enum,order} \<Rightarrow> 'a::{enum,order} \<Rightarrow> 'b::{monoid_add,order} antichain) \<Longrightarrow> x \<in> set xs \<Longrightarrow> case x of (s, l, t) \<Rightarrow> l \<ge> (0::'b)"
  unfolding Graph.graph_def
  by fast

lemma path_always_gt_zero_aux: "Graph.graph (weights::'a::{enum,order} \<Rightarrow> 'a::{enum,order} \<Rightarrow> 'b::{monoid_add,order} antichain) \<Longrightarrow>
              \<not> list_all (\<lambda>(s, l, t). l = (0::'b::{order, monoid_add})) xs \<Longrightarrow>
             \<exists>x\<in>set xs. (case x of (s, l, t) \<Rightarrow> l > (0::'b::{order, monoid_add}))"
  unfolding Graph.graph_def list_all_def
  apply simp
  apply transfer
  subgoal for weight weights
    apply simp
    apply (elim bexE)
    apply transfer
    subgoal for x weight weights 
      apply (rule bexI [where x=x])
      subgoal 
        apply (cases x)
        apply simp
        apply (metis order_le_less)
        done
      subgoal
        apply simp
        done
      done
    done
  done

lemma path_always_gt_zero: 
  assumes G: "Graph.graph (weights::'a::{enum,order} \<Rightarrow> 'a::{enum,order} \<Rightarrow> 'b::{monoid_add,order} antichain)" 
    and L: "\<not> list_all (\<lambda>(s, l, t). l = (0::'b)) xs"
  shows "graph.sum_path_weights xs > (0::'b)"
proof -
  have "\<exists> x\<in>set xs. (case x of (s, l, t) \<Rightarrow> l > (0::'b))" using assms by (rule path_always_gt_zero_aux)
  then obtain x where X: "x\<in>set xs"  and C: "(case x of (s, l, t) \<Rightarrow> l > (0::'b))" by blast
  then show ?thesis
  proof(induct xs)
    case Nil
    then show ?case using list.pred_inject(1) by simp
  next
    case (Cons a xs')
    then show ?case
    proof(cases "a = x")
      case True
      then show ?thesis
      proof(cases x)
        case (fields l1 b l2)
        with Cons True assms show ?thesis
          apply simp
          using graph.le_plus(1) order_trans_rules(22) by blast
      qed
    next
      case False
      then show ?thesis
      proof(cases a)
        case (fields l1 b l2)
        then show ?thesis
        proof(cases "b > (0::'b)")
          case True
          with Cons fields assms show ?thesis
            apply simp
            using graph.le_plus(1) order_trans_rules(22) by blast
        next
          case False
          with Cons fields assms show ?thesis
            apply simp
            by (metis graph.le_plus(2) graph.sum_le_zero graph.zero_le less_le old.prod.case)
        qed
      qed
    qed
  qed
qed

(*
  lemma "b > 0 \<Longrightarrow> a < a + (b::'a::{monoid_add,order})"
*)

lemma path_always_increase: 
  assumes G: "Graph.graph (weights::'a::{enum,order} \<Rightarrow> 'a::{enum,order} \<Rightarrow> 'b::ordered_ab_semigroup_monoid_add_imp_le antichain)" 
    and L: "\<not> list_all (\<lambda>(s, l, t). l = (0::'b)) xs"
  shows "t' < t' + (foldr (+) (map (\<lambda>(s, l, t). l) xs) (0::'b))"
  using path_always_gt_zero assms Groups.ordered_ab_semigroup_monoid_add_imp_le_class.less_add_same_cancel1 by blast

lemma fst_snd_eq: "(\<lambda>x. fst (snd x) = 0) = (\<lambda>(s, l, t). l = 0)"
  by (simp add: split_def)


section \<open>Enumerable Graphs\<close>

text \<open>The graph_enum locale connects weight functions to the DFS
  framework.\<close>

locale graph_enum = Graph.graph weights
  for weights :: "'vtx :: {order, enum} \<Rightarrow> 'vtx \<Rightarrow> 'lbl :: {order, monoid_add} antichain"
begin
end

lemma remove_non_zero_weights_preserves_no_zero_cycle:
  assumes N: "no_zero_cycle (remove_non_zero_weights weights)"
    and G: "graph_enum weights" 
  shows "no_zero_cycle weights"
  apply safe
  subgoal for loc' t' s' xs'
  proof -
    assume H1: "graph.path weights loc' loc' xs'" and H2: "xs' \<noteq> []"
    from G have H3: "Graph.graph (remove_non_zero_weights weights)" using graph_enum_def remove_non_zero_weights_is_graph by blast
    show ?thesis
    proof(cases "list_all (\<lambda> x . fst (snd x) = 0) xs'")
      case True
      with assms H1 H2 H3 show ?thesis using remove_non_zero_weights_preserves_zero_path graph_enum_def by blast
    next
      case False
      show ?thesis
        using assms(1) assms(2)[unfolded graph_def] H1 H2 H3 fst_snd_eq path_always_increase
        by (metis False)
    qed
  qed
  done

abbreviation graph_from_weights where
  "graph_from_weights weights \<equiv> 
  (
    \<lparr> gi_V = \<lambda> v \<Rightarrow> True, gi_E = weights_to_graph_fun (remove_non_zero_weights weights), gi_V0 = Enum.enum\<rparr>
  )"

lemma no_cycle_no_self_path:
  assumes 1: "acyclic (g_E G \<inter> ((g_E G)\<^sup>* `` g_V0 G \<times> UNIV))"
  shows "\<forall> loc l . l \<noteq> [] \<longrightarrow> \<not> path (g_E G \<inter> ((g_E G)\<^sup>* `` g_V0 G \<times> UNIV)) loc l loc"
proof -
  from 1 have "\<forall> loc. (loc, loc) \<notin> (g_E G \<inter> (g_E G)\<^sup>* `` g_V0 G \<times> UNIV)\<^sup>+" by (meson acyclic_def)
  with 1 show ?thesis by (metis path_is_trancl)
qed

lemma gi_in_G:
  assumes 0: "(f, G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
    and 1: "List.member (gi_E f l1) l2"
  shows "(l1, l2) \<in> g_E G"
proof -
  have H1: "(gi_E, g_E) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext \<rightarrow> \<langle>Id\<rangle>slg_rel" 
    using Param_Tool.param(3) by (smt (verit, best))
  with assms have H2: "(gi_E f, g_E G) \<in> \<langle>Id\<rangle>slg_rel" 
    using fun_rel_def fun_relD1 by fastforce
  with assms H1 have "\<exists> b . (gi_E f, b) \<in> Id \<rightarrow> br set distinct \<and> (b, g_E G) \<in> br (\<lambda>succs. {(u, v). v \<in> succs u}) (\<lambda>_. True)" 
    by (simp add: slg_rel_def list_set_rel_def Relation.relcomp.simps) 
  then obtain b where H3: "(gi_E f, b) \<in> Id \<rightarrow> br set distinct" and H4: "(b, g_E G) \<in> br (\<lambda>succs. {(u, v). v \<in> succs u}) (\<lambda>_. True)" 
    by blast
  with assms show ?thesis
    by (metis List.member_iff fun_relE1 in_br_conv mem_Collect_eq old.prod.case)
qed

lemma g_V0_complete:
  assumes "(graph_from_weights (weights::'a::{enum,hashable,linorder} \<Rightarrow> 'a \<Rightarrow> 'b::ordered_ab_semigroup_monoid_add_imp_le antichain), G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
  shows "l \<in> g_V0 G"
proof -
  have "(gi_V0, g_V0) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext \<rightarrow> \<langle>Id\<rangle>list_set_rel" using Param_Tool.param(2)
    by (smt (verit, best))
  with assms have H2: "(gi_V0 (graph_from_weights weights), g_V0 G) \<in> \<langle>Id\<rangle>list_set_rel" 
    using fun_rel_def fun_relD1 by fastforce
  then have "(enum_class.enum, g_V0 G) \<in> {(x, y). list_all2 (\<lambda>x x'. (x, x') \<in> Id) x y} O br set distinct" 
    by (simp add: list_set_rel_def list_rel_def)
  then have "g_V0 G = set enum_class.enum" using in_br_conv relcomp.simps 
    by (metis list_rel_def list_rel_id pair_in_Id_conv)
  then show ?thesis by (simp add: enum_class.in_enum)
qed

lemma zero_set[simp]: "{x. x = 0 \<and> x \<le> 0} = {0::'b::ordered_ab_semigroup_monoid_add_imp_le}"
  by fastforce

lemma in_weights_in_weights_to_graph_fun:
  assumes "l \<in>\<^sub>A  (weights::'a::{enum,hashable,linorder} \<Rightarrow> 'a \<Rightarrow> 'b::ordered_ab_semigroup_monoid_add_imp_le antichain) l1 l2" 
  shows "List.member (weights_to_graph_fun (weights) l1) l2"
  unfolding weights_to_graph_fun_def
  using assms by (auto simp add: is_empty_antichain.rep_eq  mem_Collect_eq member_antichain.rep_eq enum_class.enum_UNIV split: if_splits)

lemma weights_in_G:
  assumes R: "((graph_from_weights weights), G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
    and G: "Graph.graph weights"
    and I: "0 \<in>\<^sub>A (remove_non_zero_weights (weights::'a::{enum,hashable,linorder} \<Rightarrow> 'a \<Rightarrow> 'b::ordered_ab_semigroup_monoid_add_imp_le antichain)) l1 l2"
  shows "(l1, l2) \<in> (g_E G)"
  apply (rule gi_in_G[of "(graph_from_weights weights)" _ Rm])
  subgoal using R by simp
  subgoal using in_weights_in_weights_to_graph_fun assms by (metis gen_g_impl.select_convs(2))
  done

lemma in_remove_non_zero_weights_is_zero: 
  assumes "lbl \<in>\<^sub>A remove_non_zero_weights (weights::'a::{enum,order} \<Rightarrow> 'a \<Rightarrow> 'b::ordered_ab_semigroup_monoid_add_imp_le antichain) l2 l3"
  shows "lbl = 0"
  using assms unfolding antichain_from_list_def apply (simp split: if_splits) 
  subgoal 
    apply (subst (asm) member_antichain.abs_eq)
    subgoal using Collect_cong assms eq_onp_same_args
        mem_Collect_eq antichain_from_list.rep_eq set_antichain singletonD
      by (metis (no_types, lifting) ext Set.empty_def empty_set filter.simps(1,2) list.simps(15) singleton_conv)
    subgoal by force
    done
  apply (metis empty_antichain.abs_eq mem_antichain_nonempty)
  done

lemma path_graph_path:
  assumes R: "((graph_from_weights (weights::'a::{enum,hashable,linorder} \<Rightarrow> 'a \<Rightarrow> 'b::ordered_ab_semigroup_monoid_add_imp_le antichain)), G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
    and G: "Graph.graph weights"
    and P1: "graph.path (remove_non_zero_weights weights) loc1 loc2 xs"
  shows "\<exists> l . path (g_E G \<inter> ((g_E G)\<^sup>* `` g_V0 G \<times> UNIV)) loc1 l loc2 \<and> (xs \<noteq> [] \<longrightarrow> l \<noteq> [])"
proof(induct rule: graph.path.induct [of "(remove_non_zero_weights weights)" loc1 loc2 xs])
  case 1
  with G show ?case using remove_non_zero_weights_is_graph by blast
next
  case 2
  with assms show ?case by simp
next
  case (3 l1 l2)
  with assms show ?case by (meson path0)
next
  case (4 l1 l2 xs lbl l3)
  with assms have L: "0 \<in>\<^sub>A remove_non_zero_weights weights l2 l3" using in_remove_non_zero_weights_is_zero by blast
  from 4 obtain l where P: "path (g_E G \<inter> (g_E G)\<^sup>* `` g_V0 G \<times> UNIV) l1 l l2" by blast
  with assms L have E: "(l2, l3) \<in> g_E G" using weights_in_G by blast
  with assms L have "l2 \<in> g_V0 G" using g_V0_complete by blast
  with assms L E have "(l2, l3) \<in> (g_E G \<inter> (g_E G)\<^sup>* `` g_V0 G \<times> UNIV)" by blast
  with assms 4 L P have "path (g_E G \<inter> (g_E G)\<^sup>* `` g_V0 G \<times> UNIV) l1 (l @ [l2]) l3" by (meson path_append_conv)
  then show ?case by blast
qed 

lemma no_path_no_zero_cycle:
  assumes R: "((graph_from_weights (weights::'a::{enum,hashable,linorder} \<Rightarrow> 'a \<Rightarrow> 'b::{canonically_ordered_monoid_add, ordered_ab_semigroup_monoid_add_imp_le} antichain)), G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
    and G: "Graph.graph weights"
    and N: "(\<forall> loc' l . l \<noteq> [] \<longrightarrow> \<not> path (g_E G \<inter> ((g_E G)\<^sup>* `` g_V0 G \<times> UNIV)) loc' l loc')"
  shows "no_zero_cycle (remove_non_zero_weights weights)"
  apply safe      
  subgoal for loc' t' s' xs'
  proof -
    assume H1: "graph.path (remove_non_zero_weights weights) loc' loc' xs'" and H2: "xs' \<noteq> []"
    show ?thesis
    proof(induct rule: graph.path.induct [of "(remove_non_zero_weights weights)" loc' loc'])
      case 1
      with G show ?case using remove_non_zero_weights_is_graph by blast
    next
      case 2
      with H1 show ?case by simp
    next
      case (3 l1 l2)
      with assms H1 H2 have "\<exists>l. path (g_E G \<inter> (g_E G)\<^sup>* `` g_V0 G \<times> UNIV) loc' l loc' \<and> (xs' \<noteq> [] \<longrightarrow> l \<noteq> [])" using  path_graph_path[of weights G Rm loc' loc' xs'] by blast
      with 3 H2 obtain l where " path (g_E G \<inter> ((g_E G)\<^sup>* `` g_V0 G \<times> UNIV)) loc' l loc' \<and> l \<noteq> []" by blast
      with assms H1 H2 show ?case by blast
    next
      case (4 l1 l2 xs lbl l3)
      with assms H1 show ?case by (smt (verit, ccfv_threshold) add_strict_increasing graph.le_plus(1) graph.sum_path_weights_append_singleton less_add_same_cancel1)
    qed
  qed
  done

lemma acyclic_no_zero_cycle_with_remove_non_zero_weights:
  assumes R: "((graph_from_weights (weights::'a::{enum,hashable,linorder} \<Rightarrow> 'a \<Rightarrow> 'b::{canonically_ordered_monoid_add, ordered_ab_semigroup_monoid_add_imp_le} antichain)), G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
    and G: "Graph.graph weights"
    and N: "acyclic (g_E G \<inter> ((g_E G)\<^sup>* `` g_V0 G \<times> UNIV))"
  shows "no_zero_cycle (remove_non_zero_weights weights)"
  apply (rule no_path_no_zero_cycle [of weights G Rm])
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal using assms no_cycle_no_self_path by blast
  done

lemma acyclic_no_zero_cycle:
  assumes R: "((graph_from_weights (weights::'a::{enum,hashable,linorder} \<Rightarrow> 'a \<Rightarrow> 'b::{canonically_ordered_monoid_add, ordered_ab_semigroup_monoid_add_imp_le} antichain)), G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
    and G: "graph_enum weights"
    and N: "acyclic (g_E G \<inter> ((g_E G)\<^sup>* `` g_V0 G \<times> UNIV))"
  shows "no_zero_cycle weights"
  apply (rule remove_non_zero_weights_preserves_no_zero_cycle)
  subgoal apply (rule no_path_no_zero_cycle[of weights G Rm])
    subgoal using assms by simp
    subgoal using assms graph_enum_def by blast
    subgoal using assms no_cycle_no_self_path by blast
    done
  subgoal using assms by simp
  done

lemma acyclic_no_zero_cycle_alt:
  assumes R: "((graph_from_weights (weights::'a::{enum,hashable,linorder} \<Rightarrow> 'a \<Rightarrow> 'b::{canonically_ordered_monoid_add, ordered_ab_semigroup_monoid_add_imp_le} antichain)), G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
    and G: "graph_enum weights"
    and N: "acyclic (g_E G \<inter> ((g_E G)\<^sup>* `` g_V0 G \<times> UNIV))"
  shows "no_zero_cycle_alt weights"
proof -
  from assms have "no_zero_cycle weights" using acyclic_no_zero_cycle graph_enum_def by blast
  then have "no_zero_cycle_alt weights" using less_add_same_cancel1[symmetric] by blast
  then show ?thesis by blast
qed

section \<open>Executable Checkers\<close>

text \<open>Boolean checkers for self loops and zero cycles on enumerable
  graphs.\<close>

(* Checks for self loops  *)
definition no_self_loop_checker  where
  "no_self_loop_checker g = (set (map set_antichain (map ((\<lambda> loc . (g loc loc))) Enum.enum)) = {{}})"

lemma  no_enum_card_0: "CARD('a::enum) = 0 \<Longrightarrow> False"
  by simp

lemma range_is_set_enum: "range f = set (map f Enum.enum)"
  apply (simp add: UNIV_enum)
  done

lemma empty_enum_eq_card_zero: "(Enum.enum :: 'a :: enum list) = [] = (CARD('a::enum) = 0)"
  apply (simp add: card_UNIV_length_enum)
  done

lemma set_image2: "(\<lambda> x . f x x) ` (UNIV::'a::enum set) = {y} \<Longrightarrow> f x x = y"
  by blast

lemma set_image_sigleton: "{f x} = f ` {x}"
  by fastforce

lemma set_antichain_image_inject:"set_antichain ` s1 = set_antichain ` s2 = (s1 = s2)"
  by (metis inj_on_def inj_on_image inj_on_inverseI insert_iff set_antichain_inverse)

lemma self_loop_checker_sound: "no_self_loop_checker g \<Longrightarrow> g (loc::'loc::enum) loc = {}\<^sub>A"
  unfolding no_self_loop_checker_def
  apply (rule set_image2)
  apply (subst range_is_set_enum)
  apply (subst (asm) set_map)
  apply (subst (asm) empty_antichain.rep_eq[symmetric])
  apply (subst (asm) set_image_sigleton [where f=set_antichain])
  apply (subst (asm) set_antichain_image_inject)
  apply fast
  done

(* Checks that the graph is indeed a graph *)
definition graph_checker :: "('a::{enum,hashable,linorder} \<Rightarrow> 'a \<Rightarrow> 'b::{canonically_ordered_monoid_add, ordered_ab_semigroup_monoid_add_imp_le} antichain) \<Rightarrow> bool" where
  "graph_checker weights \<equiv> Enum.enum_all (\<lambda> loc . is_empty_antichain (weights loc loc))"

lemma no_self_loop_checker_is_graph_checker:
  "no_self_loop_checker = graph_checker"
  unfolding no_self_loop_checker_def graph_checker_def is_empty_antichain_def Set.is_empty_iff
  apply (auto simp add: enum_UNIV)
  done

lemma graph_checker_correct: "graph_checker weights \<Longrightarrow> Graph.graph weights"
  unfolding Graph.graph_def graph_checker_def
  apply (rule conjI)
  subgoal using zero_order(1) by blast
  subgoal apply (rule conjI)
    subgoal by (simp add: add_mono_thms_linordered_semiring(1))
    subgoal
      apply (subst (asm) all_code[symmetric])
      apply (metis Set.is_empty_iff empty_antichain.abs_eq is_empty_antichain.rep_eq set_antichain_inverse)
      done
    done
  done

lemma using_enum_is_digraph:
  assumes "(\<lparr>gi_V = \<lambda> v \<Rightarrow> True, gi_E = (f::('a::enum) \<Rightarrow> 'a list), gi_V0 = Enum.enum\<rparr>, G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
  shows "Digraph.graph G"
proof -
  have H1: "(gi_E, g_E) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext \<rightarrow> \<langle>Id\<rangle>slg_rel" 
    using Param_Tool.param(3) by (smt (verit, best))
  with assms have H1: "(gi_E \<lparr>gi_V = \<lambda> v \<Rightarrow> True, gi_E = (f::('a::enum) \<Rightarrow> 'a list), gi_V0 = Enum.enum\<rparr>, g_E G) \<in> \<langle>Id\<rangle>slg_rel" 
    using fun_rel_def fun_relD1 by fastforce
  have "(gi_V0, g_V0) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext \<rightarrow> \<langle>Id\<rangle>list_set_rel"
    using Param_Tool.param(2) by (smt (verit, best))
  with assms have "(gi_V0 \<lparr>gi_V = \<lambda> v \<Rightarrow> True, gi_E = (f::('a::enum) \<Rightarrow> 'a list), gi_V0 = Enum.enum\<rparr>, g_V0 G) \<in> \<langle>Id\<rangle>list_set_rel"
    using fun_rel_def fun_relD1 by fastforce
  then have "(enum_class.enum, g_V0 G) \<in> {(x, y). list_all2 (\<lambda>x x'. (x, x') \<in> Id) x y} O br set distinct" 
    by (simp add: list_set_rel_def list_rel_def)
  then have H2: "g_V0 G = set enum_class.enum" 
    using in_br_conv relcomp.simps by (metis list_rel_def list_rel_id pair_in_Id_conv)
  have "(gi_V, g_V) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext \<rightarrow> \<langle>Id\<rangle>fun_set_rel" 
    using Param_Tool.param(4) by (smt (verit, best))
  with assms have "(gi_V \<lparr>gi_V = \<lambda> v \<Rightarrow> True, gi_E = (f::('a::enum) \<Rightarrow> 'a list), gi_V0 = Enum.enum\<rparr>, g_V G) \<in> \<langle>Id\<rangle>fun_set_rel" 
    using fun_rel_def fun_relD1 by fastforce
  then have "(gi_V \<lparr>gi_V = \<lambda>x. True, gi_E = f, gi_V0 = enum_class.enum\<rparr>, g_V G) \<in> (Id \<rightarrow> bool_rel) O br Collect (\<lambda>_. True)" 
    using fun_set_rel_def by blast
  then obtain a b c where "gi_V \<lparr>gi_V = \<lambda>x. True, gi_E = f, gi_V0 = enum_class.enum\<rparr> = a \<and> g_V G = c \<and> (a, b) \<in> Id \<rightarrow> bool_rel \<and> (b, c) \<in> br Collect (\<lambda>_. True)" 
    using Relation.relcomp.simps by simp
  then have H3: "g_V G = UNIV" by (metis (no_types, lifting) br_def UNIV_eq_I fun_relE1 gen_g_impl.simps(1) in_br_conv mem_Collect_eq param_if)
  from assms H2 H3 Digraph.graph_def show ?thesis by (metis UNIV_Times_UNIV subset_UNIV)
qed

lemma using_enum_is_finite:
  assumes "(\<lparr>gi_V = \<lambda> v \<Rightarrow> True, gi_E = (f::('a::enum) \<Rightarrow> 'a list), gi_V0 = Enum.enum\<rparr>, G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
  shows "finite ((g_E G)\<^sup>* `` g_V0 G)"
proof -
  have H1: "(gi_E, g_E) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext \<rightarrow> \<langle>Id\<rangle>slg_rel" 
    using Param_Tool.param(3) by (smt (verit, best))
  with assms have H1: "(gi_E \<lparr>gi_V = \<lambda> v \<Rightarrow> True, gi_E = (f::('a::enum) \<Rightarrow> 'a list), gi_V0 = Enum.enum\<rparr>, g_E G) \<in> \<langle>Id\<rangle>slg_rel" 
    using fun_rel_def fun_relD1 by fastforce
  have "(gi_V0, g_V0) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext \<rightarrow> \<langle>Id\<rangle>list_set_rel" 
    using Param_Tool.param(2) by (smt (verit, best))
  with assms have "(gi_V0 \<lparr>gi_V = \<lambda> v \<Rightarrow> True, gi_E = (f::('a::enum) \<Rightarrow> 'a list), gi_V0 = Enum.enum\<rparr>, g_V0 G) \<in> \<langle>Id\<rangle>list_set_rel" 
    using fun_rel_def fun_relD1 by fastforce
  then have "(enum_class.enum, g_V0 G) \<in> {(x, y). list_all2 (\<lambda>x x'. (x, x') \<in> Id) x y} O br set distinct" 
    by (simp add: list_set_rel_def list_rel_def)
  then have H2: "g_V0 G = set enum_class.enum" 
    using in_br_conv relcomp.simps by (metis list_rel_def list_rel_id pair_in_Id_conv)
  with H1 show ?thesis using finite by blast
qed

(* Check if the sucessors are all distinct *)
definition implementation_graph_checker where
  "implementation_graph_checker (weights::('a::enum) \<Rightarrow> 'a list) = Enum.enum_all (distinct \<circ> weights)"

lemma implementation_graph_checker_correct: "implementation_graph_checker weights = (\<forall> x . distinct (weights x))"
  unfolding implementation_graph_checker_def
  apply (subst Enum.all_code)
  apply simp
  apply auto
  done

abbreviation fun_to_rel :: "('a::enum \<Rightarrow> 'a list) \<Rightarrow> ('a \<times> 'a) set" where
  "fun_to_rel f \<equiv> { (x, y) . x \<in> (UNIV::'a set) \<and> y \<in> set (f x)}"

lemma exists_graph: "(\<forall> x .distinct (f x)) \<Longrightarrow> \<exists>G Rm. (\<lparr>gi_V = \<lambda> v \<Rightarrow> True, gi_E = (f::('a::enum) \<Rightarrow> 'a list), gi_V0 = Enum.enum\<rparr>, G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
  unfolding g_impl_rel_ext_def fun_set_rel_def slg_rel_def list_set_rel_def list_rel_def gen_g_impl_rel_ext_def 
  apply simp
  apply (rule conjI)
  subgoal
    by (simp add: in_br_conv)
  subgoal
    apply (rule conjI)
    subgoal
      apply (subst List.List.list.rel_eq)
      apply (rule exI[where x="fun_to_rel f"])
      apply (rule Relation.relcomp.relcompI [where b="set \<circ> f"])
       apply (rule fun_relI)
      subgoal for a1 a2
        apply (subst IdD[where b=a2])
         apply simp
        apply (rule Relation.relcomp.relcompI[where b="f a2"])
         apply force
        apply (simp add: br_def)
        done
      subgoal 
        apply (simp add: br_def)
        done
      done
    subgoal
      apply (rule conjI)
      subgoal
        apply (rule exI[where x="UNIV"])
        apply (subst List.List.list.rel_eq)
        apply (rule Relation.relcomp.relcompI [where b="Enum.enum"])
         apply simp
        apply (simp add: br_def Enum.enum_class.UNIV_enum Enum.enum_class.enum_distinct)
        done
      using Param_Tool.param(3) apply blast
      done
    done
  done

abbreviation "zero_cycle_checker \<equiv> acyclic o fun_to_rel o weights_to_graph_fun o remove_non_zero_weights"



lemma decide_graph_construction:
  assumes "\<not> cyc_checker_codeT \<lparr>gi_V = \<lambda>x. True, gi_E = weights_to_graph_fun (remove_non_zero_weights summary), gi_V0 = enum_class.enum\<rparr>"
    and "graph.path summary loc loc xs" and "xs \<noteq> []"
    and "graph_checker summary"
    and "implementation_graph_checker (weights_to_graph_fun (remove_non_zero_weights summary))"
  shows "t < t + foldr (+) (map (\<lambda>(s, l, t). l) xs) 0"
proof -
  from assms have G: "Graph.graph summary" 
    using graph_checker_correct by blast
  from assms obtain G Rm where E: "((graph_from_weights summary), G) \<in> \<langle>Rm, Id\<rangle> g_impl_rel_ext" 
    using exists_graph implementation_graph_checker_correct by blast
  with assms have D: "Digraph.graph G"
    using Digraph.graph_def using_enum_is_digraph by blast
  from assms have F: "finite ((g_E G)\<^sup>* `` g_V0 G)" 
    using using_enum_is_finite E by blast
  with assms G D F E have A: "acyclic (g_E G \<inter> (g_E G)\<^sup>* `` g_V0 G \<times> UNIV)"
    using cyc_checker_codeT_correct[of G _ Rm] by blast
  with assms E G show ?thesis
    using acyclic_no_zero_cycle[unfolded graph_enum_def] by fast
qed

lemma empty_graph_no_zero_cyc:
  "graph.path summary loc loc xs \<Longrightarrow>
   summary = (\<lambda>_ _. frontier {#}\<^sub>z)  \<Longrightarrow>
   Graph.graph summary \<Longrightarrow>
   xs \<noteq> [] \<Longrightarrow>
   0 < foldr (+) (map (\<lambda>(s, l, t). l) xs) 0"
  apply (induct xs rule: rev_induct)
   apply simp
  subgoal for x xs'
    apply (simp split: prod.splits)
    apply (cases x)
    apply simp
    apply (erule graph.path_AppendE)
     apply assumption
    using frontier_empty_zmset mem_antichain_nonempty apply blast
    done
  done

abbreviation "has_zero_cyc s \<equiv> cyc_checker_codeT (graph_from_weights s)"


end
