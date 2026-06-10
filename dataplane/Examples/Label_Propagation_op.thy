theory Label_Propagation_op

imports
  Dataplane.Timely_Builder_Op
  Dataplane.MyProduct_Instances
  Wcc
begin

definition union_with where
  \<open>union_with f g h x = f (g x) (h x)\<close>

fun unions_with where
  \<open>unions_with f [] = undefined\<close>
| \<open>unions_with f (g # gs) = foldl (union_with f) g gs\<close>

primrec list_span where
  \<open>list_span _ [] = ([], [])\<close>
| \<open>list_span P (x # xs) =
    (if P x then let (ys, zs) = list_span P xs in (x # ys, zs) else ([], x # xs))\<close>

lemma list_span_length_le:
  \<open>(ys, zs) = list_span P xs \<Longrightarrow> length ys \<le> length xs\<close>
  \<open>(ys, zs) = list_span P xs \<Longrightarrow> length zs \<le> length xs\<close>
  by (induction xs arbitrary: ys zs) (auto split: if_splits prod.splits)

function group_by where
  \<open>group_by _ [] = []\<close>
| \<open>group_by f (x # xs) = (let (ys, zs) = list_span (f x) xs in (x # ys) # group_by f zs)\<close>
  by pat_completeness auto
termination by (lexicographic_order simp add: list_span_length_le)

definition insort_union where
  \<open>insort_union = fold insort_insert\<close>

lemma set_insort_union[simp]:
  \<open>set (insort_union xs ys) = set xs \<union> set ys\<close>
  by (induction xs arbitrary: ys) (simp_all add: insort_union_def set_insort_insert)

lemma distinct_insort_union[simp]:
  \<open>distinct (insort_union xs ys) \<longleftrightarrow> distinct ys\<close>
  by (induction xs arbitrary: ys)
    (simp_all add: insort_union_def distinct_insort insort_insert_key_def)

lemma sorted_insort_union:
  \<open>sorted ys \<Longrightarrow> sorted (insort_union xs ys)\<close>
  by (induction xs) (simp_all add: insort_union_def fold_invariant sorted_insort_insert)

record ('d, 'v :: linorder, 't1, 't2) label_propagation_state =
  \<open>(2, 'd, 'v \<times> 'v, 'v set set, ('t1, 't2) myprod) operator_state_ty2\<close> +
  timestamps :: \<open>'t1 list\<close> graph :: \<open>'t1 \<Rightarrow> 'v \<Rightarrow> 'v list\<close> vertices :: \<open>'t1 \<Rightarrow> 'v list\<close>
  label :: \<open>'t1 \<Rightarrow> 'v \<Rightarrow> 'v\<close>

definition neighbors where
  \<open>neighbors os t = (let ts = filter ((\<ge>) t) (timestamps os) in
  if is_Nil ts then graph os t else unions_with List.union (map (graph os) ts))\<close>

definition all_vertices where
  \<open>all_vertices os t = (let ts = filter ((\<ge>) t) (timestamps os) in
  if is_Nil ts then set (remdups (vertices os t)) else set (remdups (concat (map (vertices os) ts))))\<close>

definition all_edges where
  \<open>all_edges os t = {(v, w) \<in> (all_vertices os t) \<times> (all_vertices os t). w \<in> set (neighbors os t v)}\<close>

definition min_label where
  \<open>min_label os t v = (let ts = filter ((\<ge>) t) (timestamps os) in
  if is_Nil ts then label os t v else Min (set (map (\<lambda>t. label os t v) ts)))\<close>

lemma set_foldl_union_with:
  "set (foldl (union_with List.union) g gs y) = (\<Union>f\<in>set (g # gs). set (f y))"
proof (induction gs arbitrary: g)
  case Nil
  then show ?case by simp
next
  case (Cons h hs)
  then show ?case
    by (auto simp: union_with_def)
qed

lemma set_unions_with_List_union:
  assumes "fs \<noteq> []"
  shows "set (unions_with List.union fs y) = (\<Union>f\<in>set fs. set (f y))"
proof (cases fs)
  case Nil
  then show ?thesis
    using assms by simp
next
  case (Cons g gs)
  then show ?thesis
    using set_foldl_union_with[of g gs y] by simp
qed


lemma all_edges_update_insert:
  assumes "timestamps os' = timestamps os"
    and "vertices os' = vertices os"
    and "v1 \<in> all_vertices os t"
    and "v2 \<in> all_vertices os t"
    and "v1 \<noteq> v2"
    and "t \<in> set (filter ((\<ge>) t) (timestamps os))"
    and "graph os' = (graph os)(t := (map_entry v1 (List.insert v2) ((graph os) t))(v2 := List.insert v1 ((graph os) t v2)))"
  shows "all_edges os' t = insert (v1, v2) (insert (v2, v1) (all_edges os t))"
proof -
  let ?ts = "filter ((\<ge>) t) (timestamps os)"
  have ts_ne: "?ts \<noteq> []"
    using assms(6) by fastforce
  have vertices_eq: "all_vertices os' t = all_vertices os t"
    using assms(1,2) unfolding all_vertices_def by simp
  have neighbors_eq:
    "set (neighbors os' t v) =
      (if v = v1 then insert v2 (set (neighbors os t v))
       else if v = v2 then insert v1 (set (neighbors os t v))
       else set (neighbors os t v))" for v
    using assms(1,5,6,7) ts_ne
    unfolding neighbors_def by (auto simp: set_unions_with_List_union)
  show ?thesis
    using assms(3,4,5) vertices_eq neighbors_eq
    unfolding all_edges_def by (auto split: if_splits)
qed



definition exit_scope where
  "exit_scope f A = frontier ((zmset_of o mset_set) (f ` set_antichain A))"

lemma frontier_less_equal_exit_scope:
  "\<not> frontier_less_equal (exit_scope myfst A) (myfst t) \<Longrightarrow>
   \<not> frontier_less_equal A t"
proof
  assume not_projected: "\<not> frontier_less_equal (exit_scope myfst A) (myfst t)"
  assume "frontier_less_equal A t"
  then obtain t' where t'_in: "t' \<in>\<^sub>A A" and t'_le: "t' \<le> t"
    unfolding frontier_less_equal_iff2 by blast
  have zcount_pos: "0 < zcount (zmset_of (mset_set (myfst ` set_antichain A))) (myfst t')"
    using t'_in by (simp add: member_antichain.rep_eq)
  have "frontier_less_equal (exit_scope myfst A) (myfst t')"
    unfolding exit_scope_def o_def using zcount_pos by (rule frontier_less_equal_zcount_pos)
  then have "frontier_less_equal (exit_scope myfst A) (myfst t)"
    using myfst_mono[OF t'_le] by (rule frontier_less_equal_trans)
  then show False
    using not_projected by contradiction
qed


lemma frontier_less_equal_antichain_plusI1:
  assumes "frontier_less_equal A t"
  shows "frontier_less_equal (A + B) t"
proof -
  obtain a where a_in: "a \<in>\<^sub>A A" and a_le: "a \<le> t"
    using assms unfolding frontier_less_equal_iff2 by blast
  have fin: "finite (set_antichain A \<union> set_antichain B)"
    by simp
  have "a \<in> set_antichain A \<union> set_antichain B"
    using a_in unfolding member_antichain.rep_eq by simp
  then obtain a' where a'_in: "a' \<in> minimal_antichain (set_antichain A \<union> set_antichain B)" and a'_le: "a' \<le> a"
    using minimal_antichain_member[OF fin] by blast
  then have "a' \<in>\<^sub>A A + B"
    unfolding member_antichain.rep_eq plus_antichain.rep_eq by simp
  moreover have "a' \<le> t"
    using a'_le a_le by order
  ultimately show ?thesis
    unfolding frontier_less_equal_iff2 by blast
qed

lemma frontier_less_equal_antichain_plusI2:
  assumes "frontier_less_equal B t"
  shows "frontier_less_equal (A + B) t"
  using frontier_less_equal_antichain_plusI1[OF assms, of A]
  by (simp add: antichain_add_commute)

lemma exit_scope_memberE:
  assumes "y \<in>\<^sub>A exit_scope myfst A"
  obtains x where "x \<in>\<^sub>A A" and "myfst x = y"
proof -
  have y_front: "y \<in>\<^sub>A frontier (zmset_of (mset_set (myfst ` set_antichain A)))"
    using assms unfolding exit_scope_def o_def by simp
  have "0 < zcount (zmset_of (mset_set (myfst ` set_antichain A))) y"
    using y_front by (simp add: in_frontier_iff)
  then obtain x where "x \<in> set_antichain A" and "myfst x = y"
    by auto
  then show ?thesis
    using that unfolding member_antichain.rep_eq by blast
qed

lemma frontier_less_equal_exit_scopeI:
  assumes "x \<in>\<^sub>A A"
  shows "frontier_less_equal (exit_scope myfst A) (myfst x)"
proof -
  have "0 < zcount (zmset_of (mset_set (myfst ` set_antichain A))) (myfst x)"
    using assms by (simp add: member_antichain.rep_eq)
  then show ?thesis
    unfolding exit_scope_def o_def by (rule frontier_less_equal_zcount_pos)
qed

lemma frontier_less_equal_exit_scope_plusI1:
  assumes "x \<in>\<^sub>A A"
  shows "frontier_less_equal (exit_scope myfst (A + B)) (myfst x)"
proof -
  have fin: "finite (set_antichain A \<union> set_antichain B)"
    by simp
  have "x \<in> set_antichain A \<union> set_antichain B"
    using assms unfolding member_antichain.rep_eq by simp
  then obtain x' where x'_in: "x' \<in> minimal_antichain (set_antichain A \<union> set_antichain B)" and x'_le: "x' \<le> x"
    using minimal_antichain_member[OF fin] by blast
  then have "x' \<in>\<^sub>A A + B"
    unfolding member_antichain.rep_eq plus_antichain.rep_eq by simp
  then have "frontier_less_equal (exit_scope myfst (A + B)) (myfst x')"
    by (rule frontier_less_equal_exit_scopeI)
  then show ?thesis
    using myfst_mono[OF x'_le] by (rule frontier_less_equal_trans)
qed

lemma frontier_less_equal_exit_scope_plusI2:
  assumes "x \<in>\<^sub>A B"
  shows "frontier_less_equal (exit_scope myfst (A + B)) (myfst x)"
  using frontier_less_equal_exit_scope_plusI1[OF assms, of A]
  by (simp add: antichain_add_commute)

lemma exit_scope_plus_distrib:
  "exit_scope myfst (A + B) = exit_scope myfst A + exit_scope myfst B"
proof (rule antisym)
  show "exit_scope myfst (A + B) \<le> exit_scope myfst A + exit_scope myfst B"
    unfolding less_eq_antichain_def
  proof safe
    fix y
    assume y_in: "y \<in>\<^sub>A exit_scope myfst A + exit_scope myfst B"
    have "y \<in> set_antichain (exit_scope myfst A) \<union> set_antichain (exit_scope myfst B)"
      using y_in minimal_antichain_subset
      unfolding member_antichain.rep_eq plus_antichain.rep_eq by blast
    then show "\<exists>x. x \<in>\<^sub>A exit_scope myfst (A + B) \<and> x \<le> y"
    proof
      assume "y \<in> set_antichain (exit_scope myfst A)"
      then obtain x where x_in: "x \<in>\<^sub>A A" and y_eq: "myfst x = y"
        using exit_scope_memberE unfolding member_antichain.rep_eq by blast
      show ?thesis
        using frontier_less_equal_exit_scope_plusI1[OF x_in, of B]
        unfolding frontier_less_equal_iff2 y_eq by blast
    next
      assume "y \<in> set_antichain (exit_scope myfst B)"
      then obtain x where x_in: "x \<in>\<^sub>A B" and y_eq: "myfst x = y"
        using exit_scope_memberE unfolding member_antichain.rep_eq by blast
      show ?thesis
        using frontier_less_equal_exit_scope_plusI2[OF x_in, of A]
        unfolding frontier_less_equal_iff2 y_eq by blast
    qed
  qed
next
  show "exit_scope myfst A + exit_scope myfst B \<le> exit_scope myfst (A + B)"
    unfolding less_eq_antichain_def
  proof safe
    fix y
    assume y_in: "y \<in>\<^sub>A exit_scope myfst (A + B)"
    then obtain x where x_in: "x \<in>\<^sub>A A + B" and y_eq: "myfst x = y"
      using exit_scope_memberE by blast
    have "x \<in> set_antichain A \<union> set_antichain B"
      using x_in minimal_antichain_subset
      unfolding member_antichain.rep_eq plus_antichain.rep_eq by blast
    then show "\<exists>x. x \<in>\<^sub>A exit_scope myfst A + exit_scope myfst B \<and> x \<le> y"
    proof
      assume "x \<in> set_antichain A"
      then have "x \<in>\<^sub>A A"
        unfolding member_antichain.rep_eq by simp
      then have "frontier_less_equal (exit_scope myfst A) y"
        using frontier_less_equal_exit_scopeI[of x A] y_eq by simp
      then show ?thesis
        using frontier_less_equal_antichain_plusI1[of "exit_scope myfst A" y "exit_scope myfst B"]
        unfolding frontier_less_equal_iff2 by blast
    next
      assume "x \<in> set_antichain B"
      then have "x \<in>\<^sub>A B"
        unfolding member_antichain.rep_eq by simp
      then have "frontier_less_equal (exit_scope myfst B) y"
        using frontier_less_equal_exit_scopeI[of x B] y_eq by simp
      then show ?thesis
        using frontier_less_equal_antichain_plusI2[of "exit_scope myfst B" y "exit_scope myfst A"]
        unfolding frontier_less_equal_iff2 by blast
    qed
  qed
qed



value "exit_scope myfst (frontier {#MyPair (1 :: nat) (0 :: nat), MyPair (0 :: nat) (1 :: nat)#}\<^sub>z)"

(* Note: I assume that the timestamps of data read on port 0 are of the form "MyPair t1 0", i.e.,
the second component is assumed to be always 0. *)
(* Should the logic return a set of sets for the connected components or a list of lists? *)
definition label_propagation_op_logic where
  \<open>label_propagation_op_logic os = cUn (cUn
  (case (input os 0) of
    [] \<Rightarrow> {||}
  | (d, t) # xs \<Rightarrow>
    let (v1, v2) = trace (STR ''input0-------'') (de1 os d);
        t1 = trace (STR ''input0 edge: ('' +  show_nat v1 + STR '', '' + show_nat v2 + STR '')'') (myfst t);
        (l1, l2) = pairself (min_label os t1) (v1, v2);
        (v, l) = if (trace (STR ''labels:: l1:'' +  show_nat l1 + STR '', l2: '' + show_nat l2) l1) > l2 then (v1, l2) else (v2, l1);
        os' = os\<lparr>input := (input os)(0 := xs), timestamps := List.insert t1 (timestamps os),
  graph := (graph os)(t1 := (graph os t1)(v1 := List.insert v2 (graph os t1 v1),
    v2 := List.insert v1 (graph os t1 v2))),
  vertices := (vertices os)(t1 := List.union [v1, v2] (vertices os t1)),
  label := (label os)(t1 := (label os t1)(v := l))\<rparr>;
        ts = trace (STR ''input0 label upd: '' +  show_nat v + STR '': '' + show_nat l + STR '' @ '' + show_nat t1) (filter ((\<le>) t1) (timestamps os')) ;
        batch = concat (map (\<lambda> t1. let vs = neighbors os' t1 v in
          if min_label os t1 v > trace (STR ''neighbors: '' +  show_list show_nat vs) l
          then map (\<lambda>v'. (en1 os (v', l), Cap (MyPair t1 (mysnd t)) 1)) (filter (\<lambda>v'. min_label os t1 v' > l) vs)
          else []) ts)
     in trace (STR ''input0: looping back batch: '' + show_list (show_prod (show_prod show_nat show_nat) (show_myprod show_nat show_nat)) (map (\<lambda> (x, p). (de1 os x, time p)) batch)) {|release_caps (produces os' batch) 1|})
  (case input os 1 of
    [] \<Rightarrow> {||}
  | (d, t) # xs \<Rightarrow>
    let (v, l) = trace (STR ''input1-------'') (de1 os d);
        t1 = myfst t;
        os' = os\<lparr>input := (input os)(1 := xs),
          label := (label os)(t1 := (label os t1)(v := min (min_label os t1 v) l))\<rparr>;
        ts = trace (STR ''input1 label upd: '' +  show_nat v + STR '': '' + show_nat l + STR '' @ '' + show_nat t1) (filter ((\<le>) t1) (timestamps os)) ;
        batch = concat (map (\<lambda> t1. 
          let vs = neighbors os t1 v in 
          if min_label os t1 v > l
          then map (\<lambda>v'. (en1 os (v', l), Cap (MyPair t1 (mysnd t)) 1)) (filter (\<lambda>v'. min_label os' t1 v' > l) vs)
          else []) ts)
    in {|release_caps (produces os' batch) 1|}))
  (let below_times = filter (\<lambda> t. \<not> frontier_less_equal (exit_scope myfst (front os 0 + front os 1)) (myfst t)) (ocaps os 0);
       output_times = rmdups {} (map myfst below_times);
       batch = map (\<lambda>t. let cap = Cap (MyPair t 0) 0 in (en2 os ((components_from_labels (all_edges os t) (min_label os t))), cap)) output_times
   in if batch = []
        then {||}
        else {|(drop_caps ((produces os batch)) (map (\<lambda>t. Cap t 0) below_times ))|})\<close>

term components_from_labels
term "all_vertices os t "

term "components_from_labels (all_edges os t) (\<lambda> v. min_label os t v)"

(* @ map (\<lambda>t. Cap t 1) (filter P (ocaps os 1)) *)
definition label_propagation_op where
  \<open>label_propagation_op os = builder_op True cUNIV cUNIV os label_propagation_op_logic\<close>



(* FIXME: move me closer to dependencies *)

lemma vertices_drop_caps[simp]:
  "vertices (drop_caps os caps) = vertices os"
  unfolding drop_caps_def
  by auto

lemma timestamps_drop_caps[simp]:
  "timestamps (drop_caps os caps) = timestamps os"
  unfolding drop_caps_def
  by auto

lemma vertices_release_caps[simp]:
  "vertices (release_caps os p) = vertices os"
  unfolding release_caps_def
  by auto

lemma timestamps_release_caps[simp]:
  "timestamps (release_caps os p) = timestamps os"
  unfolding release_caps_def trace_simp Let_def
  by auto

lemma timestamps_produces[simp]:
  "timestamps (produces os batch) = timestamps os"
  unfolding produces_def trace_simp Let_def
  by auto

lemma all_vertices_release_caps[simp]:
  "all_vertices (release_caps os p) = all_vertices os"
  unfolding all_vertices_def
  by (auto split: list.splits cong: if_cong)

lemma min_label_drop_caps[simp]:
  "min_label (drop_caps os p) = min_label os"
  unfolding drop_caps_def  Let_def trace_simp min_label_def
  by (auto cong: if_cong)

lemma min_label_release_caps[simp]:
  "min_label (release_caps os p) = min_label os"
  unfolding release_caps_def Let_def trace_simp
  by (auto split: list.splits)


lemma outpu_release_caps[simp]:
  "outpu (release_caps os p) = outpu os"
  unfolding release_caps_def Let_def trace_simp
  by (auto split: list.splits)

lemma front_release_caps[simp]:
  "front (release_caps os p) = front os"
  unfolding release_caps_def Let_def trace_simp
  by (auto split: list.splits)


lemma neighbors_drop_caps[simp]:
  "neighbors (drop_caps os caps) = neighbors os"
  unfolding drop_caps_def neighbors_def
  by auto

lemma neighbors_produces[simp]:
  "neighbors (produces os batch) = neighbors os"
  unfolding produces_def neighbors_def
  by auto

lemma graph_drop_caps[simp]:
  "label_propagation_state.graph (drop_caps os caps) = label_propagation_state.graph os"
  unfolding drop_caps_def 
  by auto

lemma graph_release_caps[simp]:
  "label_propagation_state.graph (release_caps os p) = label_propagation_state.graph os"
  unfolding release_caps_def
  by auto

lemma neighbors_release_caps[simp]:
  "neighbors (release_caps os p) = neighbors os"
  unfolding release_caps_def neighbors_def
  by auto

lemma all_vertices_drop_caps[simp]:
  "all_vertices (drop_caps os caps) = all_vertices os"
  unfolding all_vertices_def drop_caps_def
  apply clarsimp
  apply fastforce
  done

lemma all_vertices_produces[simp]:
  "all_vertices (produces os batch) = all_vertices os"
  unfolding all_vertices_def produces_def
  apply clarsimp
  apply fastforce
  done

lemma all_edges_drop_caps[simp]:
  "all_edges (drop_caps os caps) = all_edges os"
  unfolding all_edges_def
  by auto

lemma vertices_produces[simp]:
  "vertices (produces os batch) = vertices os"
  unfolding produces_def
  by auto

lemma all_edges_produces[simp]:
  "all_edges (produces os batch) = all_edges os"
  unfolding all_edges_def
  by (auto cong: if_cong)

lemma all_edges_release_caps[simp]:
  "all_edges (release_caps os p) = all_edges os"
  unfolding release_caps_def all_edges_def
  by auto

lemma input_release_caps[simp]:
  "input (release_caps os p) = input os"
  unfolding release_caps_def
  by auto

lemma min_label_produces[simp]:
  "min_label (produces os batch) = min_label os"
  unfolding produces_def min_label_def
  by (auto cong: if_cong)



end
