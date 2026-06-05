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

definition exit_scope where
  "exit_scope f A = frontier ((zmset_of o mset_set) (f ` set_antichain A))"


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
  (let os = trace (STR ''front0:'' + show_myprod_frontier (front os 0) + STR '', front1: '' + show_myprod_frontier (front os 1)) (release_caps os 1) ;
       below_times = trace (STR ''ocaps1: '' + show_list (show_prod show_nat show_nat) (map to_prod (ocaps os 1))) (filter (\<lambda> t. \<not> frontier_less_equal (exit_scope myfst (front os 0 + front os 1)) (myfst t)) (ocaps os 0));
       output_times = rmdups {} (map myfst below_times);
       batch = map (\<lambda>t. let cap = Cap (MyPair t 0) 0 in (en2 os (
          (components_from_labels (all_edges os t) (min_label os t))), cap))
        (trace (STR ''below_times: '' + show_list show_nat (map myfst below_times) + STR '', ocaps: '' + show_list show_nat (map myfst (ocaps os 0)) + STR '', outpu_times: '' + show_list show_nat output_times)
         output_times)
   in if trace (STR ''main logic batch: '' + show_list show_nat (map (myfst o time o snd) batch)) batch = []
        then {||}
        else {|(drop_caps ((produces os batch)) (map (\<lambda>t. Cap t 0) below_times @ map (\<lambda>t. Cap t 1) (filter (\<lambda> t. \<not> frontier_less_equal (exit_scope myfst (front os 0 + front os 1)) (myfst t)) (ocaps os 1)) ))|})\<close>

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

end