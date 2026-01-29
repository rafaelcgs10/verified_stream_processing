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
| \<open>list_span P (x # xs) = (let (ys, zs) = list_span P xs in if P x then (x # ys, zs) else ([], xs))\<close>

lemma list_span_length_le:
  \<open>(ys, zs) = list_span P xs \<Longrightarrow> length ys \<le> length xs\<close>
  \<open>(ys, zs) = list_span P xs \<Longrightarrow> length zs \<le> length xs\<close>
  by (induction xs arbitrary: ys zs) (auto split: if_splits prod.splits)

function group_by where
  \<open>group_by _ [] = []\<close>
| \<open>group_by f (x # xs) = (let (ys, zs) = list_span (f x) xs in (x # ys) # (group_by f zs))\<close>
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

record ('d, 'v :: linorder, 't1, 't2) label_propagation_state = \<open>(2, 'd, 'v \<times> 'v, 'v list list, ('t1, 't2) myprod) operator_state_ty2\<close> +
  timestamps :: \<open>'t1 list\<close> graph :: \<open>'t1 \<Rightarrow> 'v \<Rightarrow> 'v list\<close> vertices :: \<open>'t1 \<Rightarrow> 'v list\<close> label :: \<open>'t1 \<Rightarrow> 'v \<Rightarrow> 'v\<close>

definition neighbors where
  \<open>neighbors os t =
  (let ts = filter ((\<le>) t) (timestamps os)
  in if is_Nil ts then graph os t else unions_with List.union (map (graph os) ts))\<close>

definition update_label where
  \<open>update_label os l v t =
  (let ts = filter ((\<le>) t) (timestamps os);
       f = if is_Nil ts then label os t else unions_with min (map (label os) ts)
  in (label os)(t := f(v := min (f v) l)))\<close>

(* Note: I assume that the timestamps of data read on port 0 are of the form "MyPair t1 0", i.e.,
the second component is assumed to be always 0. *)
definition label_propagation_op_logic where
  \<open>label_propagation_op_logic os = cUn (cUn
  (case input os 0 of
    [] \<Rightarrow> {||}
  | (d, t) # xs \<Rightarrow>
    let (v1, v2) = de1 os d;
        t1 = myfst t;
        (v, l) = if label os t1 v1 > label os t1 v2 then (v1, label os t1 v2) else (v2, label os t1 v1);
        os' = os\<lparr>input := (input os)(0 := xs), timestamps := List.insert t1 (timestamps os),
  graph := (graph os)(t1 := (graph os t1)(v1 := List.insert v2 (graph os t1 v1), v2 := List.insert v1 (graph os t1 v2))),
  vertices := (vertices os)(t1 := insort_union [v1, v2] (vertices os t1)),
  label := update_label os l v t1\<rparr>;
        vs = neighbors os' t1 v;
        batch = if label os t1 v > l
          then map (\<lambda>v'. (en1 os (v', l), Cap t 1)) (filter (\<lambda>v'. label os t1 v' > l) vs)
          else []
     in {|produces os' batch|})
  (case input os 1 of
    [] \<Rightarrow> {||}
  | (d, t) # xs \<Rightarrow>
    let (v, l) = de1 os d;
        t1 = myfst t;
        os' = os\<lparr>input := (input os)(1 := xs), label := update_label os l v t1\<rparr>;
        vs = neighbors os t1 v;
        batch = if label os t1 v > l
          then map (\<lambda>v'. (en1 os (v', l), Cap t 1)) (filter (\<lambda>v'. label os t1 v' > l) vs)
          else []
    in {|produces os' batch|}))
  (let P = \<lambda>t. \<forall>n. \<not> frontier_less_equal (front os 0 + front os 1) (MyPair (myfst t) n);
       output_times = filter P (ocaps os 0);
       batch = map (\<lambda>t. let cap = Cap t 0; t1 = myfst t in
        (en2 os (group_by (\<lambda>v1 v2. label os t1 v1 = label os t1 v2) (vertices os t1)), cap)) output_times
   in {|drop_caps (produces os batch) (map (\<lambda>t. Cap t 0) output_times @ map (\<lambda>t. Cap t 1) (filter P (ocaps os 1)))|})\<close>

definition label_propagation_op where
  \<open>label_propagation_op os = builder_op True cUNIV cUNIV os label_propagation_op_logic\<close>

end