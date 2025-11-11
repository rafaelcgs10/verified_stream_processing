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

lemma list_span_length_le:
  \<open>(ys, zs) = list_span P xs \<Longrightarrow> length ys \<le> length xs\<close>
  \<open>(ys, zs) = list_span P xs \<Longrightarrow> length zs \<le> length xs\<close>
  by (induction xs arbitrary: ys zs) (auto split: if_splits prod.splits)

function group_by where
  \<open>group_by _ [] = []\<close>
| \<open>group_by f (x # xs) = (let (ys, zs) = list_span (f x) xs in (x # ys) # (group_by f zs))\<close>
  by pat_completeness auto
termination by (lexicographic_order simp add: list_span_length_le)
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

(* Note: I assume that the timestamps of data read on port "Some 0" are of the form "MyPair t1 0",
i.e., the second component is assumed to be always 0. *)
declare [[unify_search_bound = 100]]
corec label_prop_op where
  \<open>label_prop_op os caps tis G vs label = choice6
  (Read None (\<lambda>st. case st of Inl (Inr f) \<Rightarrow> label_prop_op (os\<lparr>front := f\<rparr>) caps tis G vs label | _ \<Rightarrow> \<oslash>))
  (Read (Some (0 :: 2)) (\<lambda>x. case x of
    Inr (Inr (s, d), t) \<Rightarrow>
      let t1 = myfst t;
          (caps', os') = if t \<in> set caps
            then (caps, os)
            else (insort_insert_key myfst t caps, mint_cap (mint_cap os 0 t) 1 t);
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
  (let P = \<lambda>t. \<forall>n. \<not> frontier_less_equal (front os 0 + front os 1) (MyPair (myfst t) n);
       output_caps = filter P caps;
       caps' = filter (Not \<circ> P) caps;
       batch = map (\<lambda>cap. let t1 = myfst (time cap) in
        (Inl (group_by (\<lambda>v u. label t1 v = label t1 u) vs), cap)) (map (\<lambda>t. Cap t 0) output_caps);
       os' = produces os batch;
       os'' = drop_caps os' (map (\<lambda>t. Cap t 0) output_caps @ map (\<lambda>t. Cap t 1) output_caps)
  in Silent (label_prop_op os'' caps' tis G vs label))
  (Choice (cimage (\<lambda>p. case outpu os p of
    x # xs \<Rightarrow> send_output (label_prop_op (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) caps tis G vs label) p x)
    (cfilter (\<lambda>p. outpu os p \<noteq> []) c\<UU>)))
  (let (os', st) = obtain_progress os
  in send_progress (label_prop_op os' caps tis G vs label) st)\<close>

lemma label_prop_op_elim:
  assumes \<open>step io (label_prop_op os caps tis G vs label) op\<close>
  obtains st where \<open>io = Inp None st\<close> \<open>is_Inr st \<or> is_Inl st \<and> is_Inl (projl st)\<close> \<open>op = \<oslash>\<close>
  | f where \<open>io = Inp None (Inl (Inr f))\<close> \<open>op = label_prop_op (os\<lparr>front := f\<rparr>) caps tis G vs label\<close>
  | x where \<open>io = Inp (Some 0) x\<close> \<open>is_Inl x \<or> is_Inr x \<and> is_Inl (fst (projr x))\<close> \<open>op = \<oslash>\<close>
  | s d t t1 caps' os' os'' G' a b label' bs batch os''' where \<open>io = Inp (Some 0) (Inr (Inr (s, d), t))\<close>
    \<open>t1 = myfst t\<close> \<open>(caps', os') = (if t \<in> set caps
            then (caps, os)
            else (insort_insert_key myfst t caps, mint_cap (mint_cap os 0 t) 1 t))\<close>
    \<open>os'' = consume os' 0 t 1\<close> \<open>G' = G(t1 := (G t1)(s := List.insert d (G t1 s), d := List.insert s (G t1 d)))\<close>
    \<open>(a, b) = (min s d, max s d)\<close> \<open>label' = update_label label a b t1 (filter ((\<le>) t1) tis)\<close>
    \<open>bs = neighbors G' t1 (filter ((\<le>) t1) tis) b\<close> \<open>batch = (if label t1 b > a
            then map (\<lambda>v. (Inr (v, a), Cap t 1)) (filter (\<lambda>v. label t1 v > a) bs)
            else [])\<close>
    \<open>os''' = produces os'' batch\<close> \<open>op = label_prop_op os''' caps' (List.insert t1 tis) G' (insort_union [s, d] vs) label'\<close>
  | x where \<open>io = Inp (Some 1) x\<close> \<open>is_Inl x \<or> is_Inr x \<and> is_Inl (fst (projr x))\<close> \<open>op = \<oslash>\<close>
  | n x t os' t1 label' ns batch os'' where \<open>io = Inp (Some 1) (Inr (Inr (n, x), t))\<close>
    \<open>os' = consume os 1 t 1\<close> \<open>t1 = myfst t\<close> \<open>label' = update_label label x n t1 (filter ((\<le>) t1) tis)\<close>
    \<open>ns = neighbors G t1 (filter ((\<le>) t1) tis) n\<close> \<open>batch = (if label t1 n > x
            then map (\<lambda>v. (Inr (v, x), Cap t 1)) (filter (\<lambda>v. label t1 v > x) ns)
            else [])\<close>
    \<open>os'' = produces os' batch\<close> \<open>op = label_prop_op os'' caps tis G vs label'\<close>
  | P output_caps caps' batch os' os'' where \<open>io = Tau\<close>
    \<open>P = (\<lambda>t. \<forall>n. \<not> frontier_less_equal (front os 0 + front os 1) (MyPair (myfst t) n))\<close>
    \<open>output_caps = filter P caps\<close> \<open>caps' = filter (Not \<circ> P) caps\<close>
    \<open>batch = map (\<lambda>cap. let t1 = myfst (time cap) in
        (Inl (group_by (\<lambda>v u. label t1 v = label t1 u) vs), cap)) (map (\<lambda>t. Cap t 0) output_caps)\<close>
    \<open>os' = produces os batch\<close> \<open>os'' = drop_caps os' (map (\<lambda>t. Cap t 0) output_caps @ map (\<lambda>t. Cap t 1) output_caps)\<close>
    \<open>op = label_prop_op os'' caps' tis G vs label\<close>
  | p x xs where \<open>io = Out (Some p) (Inr x)\<close> \<open>outpu os p = x # xs\<close>
    \<open>op = label_prop_op (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) caps tis G vs label\<close> \<open>p \<notin> defaults\<close>
  | os' st where \<open>io = Out None (Inl (Inl st))\<close> \<open>(os', st) = obtain_progress os\<close> \<open>op = label_prop_op os' caps tis G vs label\<close>
  oops

lemma step_label_prop_op_Read_None[intro]:
  \<open>io = Inp None (Inl (Inr f)) \<Longrightarrow> op = label_prop_op (os\<lparr>front := f\<rparr>) caps tis G vs label \<Longrightarrow>
  step io (label_prop_op os caps tis G vs label) op\<close>
  by (subst label_prop_op.code) fastforce

lemma step_label_prop_op_Read_Some0[intro]:
  assumes \<open>io = Inp (Some 0) (Inr (Inr (s, d), t))\<close> \<open>t1 = myfst t\<close> \<open>(caps', os') = (if t \<in> set caps
            then (caps, os)
            else (insort_insert_key myfst t caps, mint_cap (mint_cap os 0 t) 1 t))\<close>
    \<open>os'' = consume os' 0 t 1\<close> \<open>G' = G(t1 := (G t1)(s := List.insert d (G t1 s), d := List.insert s (G t1 d)))\<close>
    \<open>(a, b) = (min s d, max s d)\<close> \<open>label' = update_label label a b t1 (filter ((\<le>) t1) tis)\<close>
    \<open>bs = neighbors G' t1 (filter ((\<le>) t1) tis) b\<close> \<open>batch = (if label t1 b > a
            then map (\<lambda>v. (Inr (v, a), Cap t 1)) (filter (\<lambda>v. label t1 v > a) bs)
            else [])\<close>
    \<open>os''' = produces os'' batch\<close> \<open>op = label_prop_op os''' caps' (List.insert t1 tis) G' (insort_union [s, d] vs) label'\<close>
  shows \<open>step io (label_prop_op os caps tis G vs label) op\<close>
proof -
  let ?f = \<open>\<lambda>x. case x of
    Inr (Inr (s, d), t) \<Rightarrow>
      let t1 = myfst t;
          (caps', os') = if t \<in> set caps
            then (caps, os)
            else (insort_insert_key myfst t caps, mint_cap (mint_cap os 0 t) 1 t);
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
  | _ \<Rightarrow> \<oslash>\<close>
  have \<open>Read (Some 0) ?f |\<in>| choices (label_prop_op os caps tis G vs label)\<close>
    by (subst (2) label_prop_op.code) force
  moreover have \<open>op = ?f (Inr (Inr (s, d), t))\<close>
      using assms(2-) by (auto split: prod.splits)
  ultimately show ?thesis
    using assms(1) by blast
qed

lemma step_label_prop_op_Read_Some1[intro]:
  assumes \<open>io = Inp (Some 1) (Inr (Inr (n, x), t))\<close> \<open>os' = consume os 1 t 1\<close> \<open>t1 = myfst t\<close>
    \<open>label' = update_label label x n t1 (filter ((\<le>) t1) tis)\<close>
    \<open>ns = neighbors G t1 (filter ((\<le>) t1) tis) n\<close> \<open>batch = (if label t1 n > x
            then map (\<lambda>v. (Inr (v, x), Cap t 1)) (filter (\<lambda>v. label t1 v > x) ns)
            else [])\<close>
    \<open>os'' = produces os' batch\<close> \<open>op = label_prop_op os'' caps tis G vs label'\<close>
  shows \<open>step io (label_prop_op os caps tis G vs label) op\<close>
proof -
  let ?f = \<open>\<lambda>x. case x of
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
  | _ \<Rightarrow> \<oslash>\<close>
  have \<open>Read (Some 1) ?f |\<in>| choices (label_prop_op os caps tis G vs label)\<close>
    by (subst (2) label_prop_op.code) force
  thus ?thesis
    using assms Read_in_choices_step[where f=\<open>?f\<close> and x=\<open>Inr (Inr (n, x), t)\<close>] by fastforce
qed

lemma step_label_prop_op_Write_Some[intro]:
  \<open>outpu os p = x # xs \<Longrightarrow> op = label_prop_op (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) caps tis G vs label \<Longrightarrow>
  p \<notin> defaults \<Longrightarrow>
  step (Out (Some p) (Inr x)) (label_prop_op os caps tis G vs label) op\<close>
  by (subst label_prop_op.code) force

lemma step_label_prop_op_Write_None[intro]:
  \<open>(os', st) = obtain_progress os \<Longrightarrow> op = label_prop_op os' caps tis G vs label \<Longrightarrow>
  step (Out None (Inl (Inl st))) (label_prop_op os caps tis G vs label) op\<close>
  by (subst label_prop_op.code) auto

lemma step_label_prop_op_Silent[intro]:
  \<open>io = Tau \<Longrightarrow> P = (\<lambda>t. \<forall>n. \<not> frontier_less_equal (front os 0 + front os 1) (MyPair (myfst t) n)) \<Longrightarrow>
  output_caps = filter P caps \<Longrightarrow> caps' = filter (Not \<circ> P) caps \<Longrightarrow>
  batch = map (\<lambda>cap. let t1 = myfst (time cap) in
        (Inl (group_by (\<lambda>v u. label t1 v = label t1 u) vs), cap)) (map (\<lambda>t. Cap t 0) output_caps) \<Longrightarrow>
  os' = produces os batch \<Longrightarrow> os'' = drop_caps os' (map (\<lambda>t. Cap t 0) output_caps @ map (\<lambda>t. Cap t 1) output_caps) \<Longrightarrow>
  op = label_prop_op os'' caps' tis G vs label \<Longrightarrow>
  step io (label_prop_op os caps tis G vs label) op\<close>
  by (subst label_prop_op.code) auto

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
  \<open>cc_op os1 caps1 ins buf1 os2 caps2 tis G vs label buf2 incr os3 buf3 \<equiv>
  map_op (case_sum id id) (case_sum id id)
  (comp_op [Inr (0 :: 3, 0 :: 2) \<mapsto> Inr (1 :: 3, 0 :: 2)] buf1 (inp_op' os1 caps1 ins)
    (label_incr_loop_op os2 caps2 tis G vs label buf2 incr os3 buf3))\<close>

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

lemma
  \<open>edges sg = cc_edges \<Longrightarrow>
  summ sg = cc_summary \<Longrightarrow>
  \<forall>x \<in> lset (ins 0). (case x of Data t d \<Rightarrow> mysnd t = 0 \<and> is_Inr d | Watermark wm \<Rightarrow> mysnd wm = 0) \<Longrightarrow>
  ins 1 = LNil \<Longrightarrow>
  monotone (ins 0) WM \<Longrightarrow>
  \<forall>x \<in> set (buf1 (Inr (1, 0))) \<union> set (buf2 (Inr (2, 0))) \<union> set (buf3 ((Inr (1, 0)))). is_Inr x \<and> is_Inr (fst (projr x)) \<Longrightarrow>
  sorted (map myfst caps2) \<Longrightarrow>
  dataflow_op sg (cc_op os1 caps1 ins buf1 os2 caps2 tis G vs label buf2 incr os3 buf3)
  \<approx> map_op (Pair 1) (Pair 1) (source_op ins')\<close>
  oops

end