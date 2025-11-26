theory Label_Propagation

imports
  Dataplane.Timely_Infrastructure
  Dataplane.Timely_Stream
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

definition neighbors where
  \<open>neighbors G t ts = (if is_Nil ts then G t else unions_with List.union (map G ts))\<close>

definition update_label :: \<open>('t \<Rightarrow> 'v :: linorder \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 't \<Rightarrow> 't list \<Rightarrow> 't \<Rightarrow> 'v \<Rightarrow> 'v\<close> where
  \<open>update_label label l v t ts =
  (let f = if is_Nil ts then label t else unions_with min (map label ts)
  in label(t := f(v := min (f v) l)))\<close>

record ('d, 'v, 't1, 't2) label_propagation_state = \<open>(2, 'd, 'v \<times> 'v, 'v list list, ('t1, 't2) myprod) operator_state_ty2\<close> +
  ts :: \<open>'t1 list\<close> G :: \<open>'t1 \<Rightarrow> 'v \<Rightarrow> 'v list\<close> vs :: \<open>'t1 \<Rightarrow> 'v list\<close> label :: \<open>'t1 \<Rightarrow> 'v \<Rightarrow> 'v\<close>  

definition label_propagation_op_logic where
  \<open>label_propagation_op_logic os = {|
  (case input os 0 of (d, t) # xs \<Rightarrow>
    let (u, v) = de1 os d;
        t1 = myfst t;
        (w, l) = if label os t1 u > label os t1 v then (u, label os t1 v) else (v, label os t1 u);
        os' = os\<lparr>input := (input os)(0 := xs), ts := List.insert t1 (ts os),
  G := (G os)(t1 := (G os t1)(u := List.insert v (G os t1 u), v := List.insert u (G os t1 v))),
  vs := (vs os)(t1 := insort_union [u, v] (vs os t1)),
  label := update_label (label os) l w t1 (filter ((\<le>) t1) (ts os))\<rparr>;
        ws = neighbors (G os') t1 (filter ((\<le>) t1) (ts os)) w;
        batch = if label os t1 w > l
          then map (\<lambda>v. (en1 os (v, l), Cap t 1)) (filter (\<lambda>v. label os t1 v > l) ws)
          else []
     in produces os' batch),
  (case input os 1 of (d, t) # xs \<Rightarrow>
    let (v, l) = de1 os d;
        t1 = myfst t;
        os' = os\<lparr>input := (input os)(1 := xs), label := update_label (label os) l v t1 (filter ((\<le>) t1) (ts os))\<rparr>;
        ws = neighbors (G os) t1 (filter ((\<le>) t1) (ts os)) v;
        batch = if label os t1 v > l
          then map (\<lambda>v. (en1 os (v, l), Cap t 1)) (filter (\<lambda>v. label os t1 v > l) ws)
          else []
    in produces os' batch),
  (let dropped_times = filter (Not \<circ> frontier_less_equal (front os 0)) (ocaps os 0)
   in drop_caps os (map (\<lambda>t. Cap t 0) dropped_times @ map (\<lambda>t. Cap t 1) dropped_times)),
  (let P = \<lambda>t. \<forall>n. \<not> frontier_less_equal (front os 0 + front os 1) (MyPair (myfst t) n);
       output_times = filter P (ocaps os 0);
       batch = map (\<lambda>t. let cap = Cap t 0; t1 = myfst t in
        (en2 os (group_by (\<lambda>u v. label os t1 u = label os t1 v) (vs os t1)), cap)) output_times
   in drop_caps (produces os batch) (map (\<lambda>t. Cap t 0) output_times @ map (\<lambda>t. Cap t 1) output_times))
  |}\<close>

end