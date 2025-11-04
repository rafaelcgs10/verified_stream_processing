theory ConnectedComponents

imports
  Accumulator
  Increment_top
begin

context
  fixes edges :: \<open>('a \<times> 'a) set\<close> (\<open>E\<close>)
begin

(* Undirected reachability and connected components *)

definition reachable where
  \<open>reachable x y \<equiv> (x, y) \<in> (E \<union> E\<inverse>)\<^sup>*\<close>

definition is_subcc :: \<open>'a set \<Rightarrow> bool\<close>  where
  \<open>is_subcc S \<equiv> \<forall>x \<in> S. \<forall>y \<in> S. reachable x y\<close>

definition is_cc :: \<open>'a set \<Rightarrow> bool\<close>  where
  \<open>is_cc S \<equiv> S \<noteq> {} \<and> is_subcc S \<and> (\<forall>S'. S \<subseteq> S' \<and> is_subcc S' \<longrightarrow> S' = S)\<close>

abbreviation ccs :: \<open>'a set set\<close> where
  \<open>ccs \<equiv> {S. is_cc S}\<close>

definition is_ccs :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>is_ccs \<equiv> (=) ccs\<close>

lemma is_ccs_Uniq:
  \<open>Uniq is_ccs\<close>
  unfolding Uniq_def is_ccs_def by blast

end

(* cc_spec assumes the input is in order. *)
abbreviation cc_spec where
  \<open>cc_spec \<equiv> accumulator_op (\<lambda>_. (\<union>)) (\<lambda>_. The \<circ> is_ccs) (\<lambda>_. (=) {}) (\<lambda>_. 0)\<close>

(* TODO move *)
abbreviation \<open>choice4 op1 op2 op3 op4 \<equiv> choice2 (choice3 op1 op2 op3) op4\<close>
abbreviation \<open>choice5 op1 op2 op3 op4 op5 \<equiv> choice2 (choice4 op1 op2 op3 op4) op5\<close>
abbreviation \<open>choice6 op1 op2 op3 op4 op5 op6 \<equiv> choice2 (choice5 op1 op2 op3 op4 op5) op6\<close>
abbreviation \<open>choice7 op1 op2 op3 op4 op5 op6 op7 \<equiv> choice2 (choice6 op1 op2 op3 op4 op5 op6) op7\<close>
abbreviation "produces os batch \<equiv> os\<lparr> outpu := (\<lambda> p. outpu os p @ map (\<lambda> (x, cap). (x, time cap)) (filter (\<lambda> (x, cap). out cap = p) batch)), produ := produ os @ map (\<lambda> (x, cap). (out cap, time cap, 1)) batch \<rparr>"

definition union_with where
  \<open>union_with f g h x = f (g x) (h x)\<close>

fun unions_with where
  \<open>unions_with f [] = undefined\<close>
| \<open>unions_with f (g # gs) = foldl (union_with f) g gs\<close>

primrec list_span where
  \<open>list_span _ [] = ([], [])\<close>
| \<open>list_span P (x # xs) = (let (ys, zs) = list_span P xs in if P x then (x # ys, zs) else ([], xs))\<close>

lemma list_span_length_le[termination_simp]:
  \<open>(ys, zs) = list_span P xs \<Longrightarrow> length ys \<le> length xs\<close>
  \<open>(ys, zs) = list_span P xs \<Longrightarrow> length zs \<le> length xs\<close>
  by (induction xs arbitrary: ys zs) (auto split: if_splits prod.splits)

fun group_by where
  \<open>group_by _ [] = []\<close>
| \<open>group_by f (x # xs) = (let (ys, zs) = list_span (f x) xs in (x # ys) # (group_by f zs))\<close>

(*
primrec remdups_f where
  \<open>remdups_f f [] = []\<close>
| \<open>remdups_f f (x # xs) = (if f x \<in> f ` set xs then remdups_f f xs else x # remdups_f f xs)\<close>

lemma remdups_f_remdups:
  \<open>remdups_f id xs = remdups xs\<close>
  by (induction xs) simp_all

lemma remdups_f_subset:
  \<open>set (remdups_f f xs) \<subseteq> set xs\<close>
  by (induction xs) auto

lemma distinct_remdups_f:
  \<open>distinct (remdups_f f xs)\<close>
proof (induction xs)
  case (Cons a xs)
  then show ?case
    using remdups_f_subset by fastforce
qed simp

lemma distinct_map_remdups_f:
  \<open>distinct (map f (remdups_f f xs))\<close>
proof (induction xs)
  case (Cons a xs)
  then show ?case
    using remdups_f_subset by fastforce
qed simp

lemma distinct_remdups_f_id:
  \<open>distinct (map f xs) \<Longrightarrow> remdups_f f xs = xs\<close>
  by (induction xs) simp_all

lemma remdups_f_id_iff_distinct[simp]:
  \<open>remdups_f f xs = xs \<longleftrightarrow> distinct (map f xs)\<close>
  by (metis distinct_map_remdups_f distinct_remdups_f_id)
*)

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
  \<open>neighbors G t tis = (if is_Nil tis then G t else unions_with List.union (map G tis))\<close>

definition update_label :: \<open>('t \<Rightarrow> 'v :: linorder \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 't \<Rightarrow> 't list \<Rightarrow> 't \<Rightarrow> 'v \<Rightarrow> 'v\<close> where
  \<open>update_label label a b t tis =
  (let f = if is_Nil tis then label t else unions_with min (map label tis)
  in label(t := f(b := min (f b) a)))\<close>

(* TODO Check minting of capabilities, on proper ports. *)
(* TODO Finish definition when checking the frontiers (before outputting). *)
declare [[unify_search_bound = 420]]
corec label_prop_op where
  \<open>label_prop_op os caps tis G vs label = choice6
  (Read None (\<lambda>st. case st of Inl (Inr f) \<Rightarrow> label_prop_op (os\<lparr>front := f\<rparr>) caps tis G vs label | _ \<Rightarrow> \<oslash>))
  (Read (Some (0 :: 2)) (\<lambda>x. case x of
    Inr (Inr (s, d), t) \<Rightarrow>
      let t1 = myfst t;
          t' = MyPair t1 0;
          (caps', os') = if t1 \<in> set (map myfst (caps (0 :: 1))) then (caps, os) else (caps(0 := caps 0 @ [t']), mint_cap os 0 t');
          os'' = consume os' 0 t 1;
          G' = G(t1 := (G t1)(s := List.insert d (G t1 s), d := List.insert s (G t1 d)));
          (a, b) = (min s d, max s d);
          label' = update_label label a b t1 (filter ((\<le>) t1) tis);
          bs = neighbors G' t1 (filter ((\<le>) t1) tis) b;
          batch = if label t1 b > a
            then map (\<lambda>v. (Inr (v, a), Cap t 1)) (filter (\<lambda>v. label t1 v > a) bs)
            else [];
          os''' = produces os'' batch
     in label_prop_op os''' caps' (List.insert t1 tis) G' (insort_union [s, d] vs) label'
  | _ \<Rightarrow> \<oslash>))
  (Read (Some (1 :: 2)) (\<lambda>x. case x of
    Inr (Inr (n, x), t) \<Rightarrow>
      let os' = consume os 1 t 1;
          t1 = myfst t;
          label' = update_label label x n t1 (filter ((\<le>) t1) tis);
          ns = neighbors G t1 (filter ((\<le>) t1) tis) n;
          batch = if label t1 n > x
            then map (\<lambda>v. (Inr (v, x), Cap t 1)) (filter (\<lambda>v. label t1 v > x) ns)
            else [];
          os'' = produces os' batch
    in label_prop_op os'' caps tis G vs label'
  | _ \<Rightarrow> \<oslash>))
  (let A = front os 0 + front os 1;
       dropped_caps = map (\<lambda>t. Cap t 0) (filter undefined (caps 0));
       caps' = caps(0 := filter undefined (caps 0));
       output_caps = sort_key (myfst \<circ> time) dropped_caps;
       batch = map (\<lambda>cap. let t = myfst (time cap) in
        (Inl (group_by (\<lambda>v u. label t v = label t u) vs), cap)) output_caps;
       os' = produces os batch;
       os'' = drop_caps os' dropped_caps
  in Silent (label_prop_op os'' caps' tis G vs label))
  (Choice (cimage (\<lambda>p. case outpu os p of
    x # xs \<Rightarrow> send_output (label_prop_op (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) caps tis G vs label) p x)
    (cfilter (\<lambda>p. outpu os p \<noteq> []) c\<UU>)))
  (let (os', st) = obtain_progress os
  in send_progress (label_prop_op os' caps tis G vs label) st)\<close>

abbreviation inp_op' where
  \<open>inp_op' os caps ins \<equiv>
  map_op (case_option (Inl (0 :: 3)) (\<lambda>p. Inr (0, p))) (case_option (Inl (0 :: 3)) (\<lambda>p. Inr (0, p)))
  (ooo_input_top os caps ins)\<close>

abbreviation label_op where
  \<open>label_op os caps tis G vs label \<equiv>
  map_op (case_option (Inl (1 :: 3)) (\<lambda>p. Inr (1, p))) (case_option (Inl (1 :: 3)) (\<lambda>p. Inr (1, p)))
  (label_prop_op os caps tis G vs label)\<close>

abbreviation incr_op' where
  \<open>incr_op' incr os \<equiv>
  map_op (case_option (Inl (2 :: 3)) (\<lambda>p. Inr (2, p))) (case_option (Inl (2 :: 3)) (\<lambda>p. Inr (2, p)))
  (increment_top incr os)\<close>

(* Issue: I would like to consider the input and increment operators with only 1 input port and 1
output port, however this is not possible here because the numeral type 2 for ports is the same for
all operators in the graph.  I cannot use map_op to solve this issue because the type parameter for
ports occurs inside the shared_state type, which occurs inside the type of data for the operators,
and this is a dead type parameter. *)

abbreviation label_incr_op where
  \<open>label_incr_op os1 caps tis G vs label buf incr os2 \<equiv>
  map_op (case_sum id id) (case_sum id id)
  (comp_op [Inr (1 :: 3, 1 :: 2) \<mapsto> Inr (2 :: 3, 0 :: 2)] buf (label_op os1 caps tis G vs label)
    (incr_op' incr os2))\<close>

abbreviation label_incr_loop_op where
  \<open>label_incr_loop_op os1 caps tis G vs label buf1 incr os2 buf2 \<equiv>
  (loop_op [Inr (2 :: 3, 1 :: 2) \<mapsto> Inr (1 :: 3, 0 :: 2)] buf2 (label_incr_op os1 caps tis G vs label buf1 incr os2))\<close>

abbreviation cc_op where
  \<open>cc_op os1 caps1 ins os2 caps2 tis G vs label buf1 incr os3 buf2 buf3 \<equiv>
  map_op (case_sum id id) (case_sum id id)
  (comp_op [Inr (0 :: 3, 0 :: 2) \<mapsto> Inr (1 :: 3, 0 :: 2)] buf3 (inp_op' os1 caps1 ins)
    (label_incr_loop_op os2 caps2 tis G vs label buf1 incr os3 buf2))\<close>

abbreviation cc_edges where
  \<open>cc_edges \<equiv> (\<lambda>l.
  if l = Loc (0 :: 3) (Src (0 :: 2)) then [Loc (1 :: 3) (Trg (0 :: 2))]
  else if l = Loc 1 (Src 1) then [Loc 2 (Trg 0)]
  else if l = Loc 2 (Src 0) then [Loc 1 (Trg 1)]
  else [])\<close>

(* Note: I omit some internal connections of the input and increment operators. *)
abbreviation cc_summary where
  \<open>cc_summary \<equiv> (\<lambda>l1 l2.
  if l1 = Loc (0 :: 3) (Trg (0 :: 2)) \<and> l2 = Loc (0 :: 3) (Src (0 :: 2))
  then antichain {0}
  else if l1 = Loc 0 (Src 0) \<and> l2 = Loc 1 (Trg 0)
  then antichain {0}
  else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
  then antichain {0}
  else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 1)
  then antichain {0}
  else if l1 = Loc 1 (Trg 1) \<and> l2 = Loc 1 (Src 0)
  then antichain {0}
  else if l1 = Loc 1 (Trg 1) \<and> l2 = Loc 1 (Src 1)
  then antichain {0}
  else if l1 = Loc 1 (Src 1) \<and> l2 = Loc 2 (Trg 0)
  then antichain {0}
  else if l1 = Loc 2 (Trg 0) \<and> l2 = Loc 2 (Src 0)
  then antichain {0}
  else if l1 = Loc 2 (Src 0) \<and> l2 = Loc 1 (Trg 1)
  then antichain {MyPair 0 1}
  else {}\<^sub>A)\<close>
end