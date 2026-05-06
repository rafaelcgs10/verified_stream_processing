theory Label_Propagation_op

imports
  Dataplane.Timely_Infrastructure
  Dataplane.MyProduct_Instances
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
  if is_Nil ts then vertices os t else mergesort_remdups (concat (map (vertices os) ts)))\<close>

definition all_edges where
  \<open>all_edges os t = {(v, w). w \<in> set (neighbors os t v)}\<close>

definition min_label where
  \<open>min_label os t v = (let ts = filter ((\<ge>) t) (timestamps os) in
  if is_Nil ts then label os t v else Min (set (map (\<lambda>t. label os t v) ts)))\<close>

(* Note: I assume that the timestamps of data read on port 0 are of the form "MyPair t1 0", i.e.,
the second component is assumed to be always 0. *)
(* Should the logic return a set of sets for the connected components or a list of lists? *)
definition label_propagation_op_logic where
  \<open>label_propagation_op_logic os = cUn (cUn
  (case input os 0 of
    [] \<Rightarrow> {||}
  | (d, t) # xs \<Rightarrow>
    let (v1, v2) = de1 os d;
        t1 = myfst t;
        (l1, l2) = pairself (min_label os t1) (v1, v2);
        (v, l) = if l1 > l2 then (v1, l2) else (v2, l1);
        os' = os\<lparr>input := (input os)(0 := xs), timestamps := List.insert t1 (timestamps os),
  graph := (graph os)(t1 := (graph os t1)(v1 := List.insert v2 (graph os t1 v1),
    v2 := List.insert v1 (graph os t1 v2))),
  vertices := (vertices os)(t1 := List.union [v1, v2] (vertices os t1)),
  label := (label os)(t1 := (label os t1)(v := l))\<rparr>;
        vs = neighbors os' t1 v;
        batch = if min_label os t1 v > l
          then map (\<lambda>v'. (en1 os (v', l), Cap t 1)) (filter (\<lambda>v'. min_label os t1 v' > l) vs)
          else []
     in {|drop_cap (produces os' batch) (Cap t 1)|})
  (case input os 1 of
    [] \<Rightarrow> {||}
  | (d, t) # xs \<Rightarrow>
    let (v, l) = de1 os d;
        t1 = myfst t;
        os' = os\<lparr>input := (input os)(1 := xs),
          label := (label os)(t1 := (label os t1)(v := min (min_label os t1 v) l))\<rparr>;
        vs = neighbors os t1 v;
        batch = if min_label os t1 v > l
          then map (\<lambda>v'. (en1 os (v', l), Cap t 1)) (filter (\<lambda>v'. min_label os t1 v' > l) vs)
          else []
    in {|drop_cap (produces os' batch) (Cap t 1)|}))
  (let P = \<lambda>t. \<forall>n < length (all_vertices os (myfst t)).
         \<not> frontier_less_equal (front os 0 + front os 1) (MyPair (myfst t) n);
       below_times = filter P (ocaps os 0);
       output_times = mergesort_remdups (map myfst below_times);
       batch = map (\<lambda>t. let cap = Cap (MyPair t 0) 0 in (en2 os (set (map set
          (group_by (\<lambda>v1 v2. min_label os t v1 = min_label os t v2) (all_vertices os t)))), cap))
        output_times
   in if batch = []
        then {||}
        else {|drop_caps (produces os batch) (map (\<lambda>t. Cap t 0) below_times
          @ map (\<lambda>t. Cap t 1) (filter P (ocaps os 1)))|})\<close>

definition label_propagation_op where
  \<open>label_propagation_op os = builder_op True cUNIV cUNIV os label_propagation_op_logic\<close>

end