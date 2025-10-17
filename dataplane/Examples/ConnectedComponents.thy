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

abbreviation cc_spec where
  \<open>cc_spec \<equiv> accumulator_op (\<lambda>_. (\<union>)) (\<lambda>_. The \<circ> is_ccs) (\<lambda>_. (=) {}) (\<lambda>_. 0)\<close>

abbreviation \<open>choice4 op1 op2 op3 op4 \<equiv> choice2 (choice3 op1 op2 op3) op4\<close>
abbreviation \<open>choice5 op1 op2 op3 op4 op5 \<equiv> choice2 (choice4 op1 op2 op3 op4) op5\<close>
abbreviation \<open>choice6 op1 op2 op3 op4 op5 op6 \<equiv> choice2 (choice5 op1 op2 op3 op4 op5) op6\<close>
abbreviation \<open>choice7 op1 op2 op3 op4 op5 op6 op7 \<equiv> choice2 (choice6 op1 op2 op3 op4 op5 op6) op7\<close>

abbreviation "produces os batch \<equiv> os\<lparr> outpu := (\<lambda> p. outpu os p @ map (\<lambda> (x, cap). (x, time cap)) (filter (\<lambda> (x, cap). out cap = p) batch)), produ := produ os @ map (\<lambda> (x, cap). (out cap, time cap, 1)) batch \<rparr>"

abbreviation \<open>mint os caps p t \<equiv> let cap = Cap t p in
  if cap \<in> set caps then (caps, os) else (caps @ [cap], mint_cap os p t)\<close>

(* TODO move *)

definition union_with where
  \<open>union_with f g h x = f (g x) (h x)\<close>

fun unions_with where
  \<open>unions_with f [] = undefined\<close>
| \<open>unions_with f (g # gs) = foldl (union_with f) g gs\<close>

primrec list_span where
  \<open>list_span _ [] = ([], [])\<close>
| \<open>list_span P (x # xs) = (let (ys, zs) = list_span P xs in if P x then (x # ys, zs) else ([], xs))\<close>

function group_by where
  \<open>group_by _ [] = []\<close>
| \<open>group_by f (x # xs) = (let (ys, zs) = list_span (f x) xs in (x # ys) # (group_by f zs))\<close>
  by auto (meson list.exhaust)

definition update_graph where
  \<open>update_graph G s d t tis =
  (let f = if is_Nil tis then (\<lambda>_. []) else unions_with List.union (map (the \<circ> G) tis)
  in G(t \<mapsto> f(s := List.insert d (f s), d := List.insert s (f d))))\<close>

definition update_label :: \<open>('a \<Rightarrow> 'b :: linorder \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b\<close> where
  \<open>update_label label a b t tis =
  (let f = if is_Nil tis then id else unions_with min (map label tis)
  in label(t := (label t)(b := min (f b) a)))\<close>

primrec remdups_f where
  \<open>remdups_f f [] = []\<close>
| \<open>remdups_f f (x # xs) = (if f x \<in> f ` set xs then remdups_f f xs else x # remdups_f f xs)\<close>

lemma remdups_f_id:
  \<open>remdups_f id xs = remdups xs\<close>
  by (induction xs) simp_all

corec label_prop_op where
  \<open>label_prop_op os caps tis G vs label = choice6
  (Read None (\<lambda>st. case st of Inl (Inr f) \<Rightarrow> label_prop_op (os\<lparr>front := f\<rparr>) caps tis G vs label | _ \<Rightarrow> \<oslash>))
  (Read (Some (0 :: 2)) (\<lambda>x. case x of
    Inr (Inl (s, d), t) \<Rightarrow>
      let (caps', os') = mint os caps 0 t;
          os'' = consume os' 0 t 1;
          t1 = myfst t;
          G' = update_graph G s d t1 (filter ((\<le>) t1) tis);
          (a, b) = (min s d, max s d);
          label' = update_label label a b t1 (filter ((\<le>) t1) tis);
          batch = if label t1 b > a
            then map (\<lambda>v. (Inl (v, a), Cap t 0)) (filter (\<lambda>v. label t1 v > a) (the (G' t1) b))
            else [];
          os''' = produces os'' batch
     in label_prop_op os''' caps' (List.insert t1 tis) G' (List.union [s, d] vs) label'
  | _ \<Rightarrow> \<oslash>))
  (Read (Some (1 :: 2)) (\<lambda>x. case x of
    Inr (Inl (n, x), t) \<Rightarrow>
      let (caps', os') = mint os caps 0 t;
          (caps'', os'') = mint os' caps' 1 t;
          os''' = consume os'' 1 t 1;
          t1 = myfst t;
          label' = update_label label x n t1 (filter ((\<le>) t1) tis);
          batch = if label t1 n > x
            then map (\<lambda>v. (Inl (v, x), Cap t 0)) (filter (\<lambda>v. label t1 v > x) (the (G t1) n))
            else [];
          os'''' = produces os''' batch
    in label_prop_op os'''' caps'' tis G vs label'
  | _ \<Rightarrow> \<oslash>))
  (let below_caps = [cap \<leftarrow> caps. \<not> frontier_less_equal (front os 1) (time cap)];
       above_caps = [cap \<leftarrow> caps. frontier_less_equal (front os 1) (time cap)];
       output_caps = remdups_f (myfst \<circ> time) below_caps;
       batch = map (\<lambda>cap. let t = myfst (time cap) in
        (Inr (group_by (\<lambda>v u. label t v = label t u) vs), cap)) output_caps;
       os' = produces os batch;
       os'' = drop_caps os' below_caps
  in Silent (label_prop_op os'' above_caps tis G vs label))
  (Choice (cimage (\<lambda>p. case outpu os p of
    x # xs \<Rightarrow> send_output (label_prop_op (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) caps tis G vs label) p x)
    (cfilter (\<lambda>p. outpu os p \<noteq> []) c\<UU>)))
  (let (os', st) = obtain_progress os
  in send_progress (label_prop_op os' caps tis G vs label) st)\<close>

abbreviation inp_op' where
  \<open>inp_op' os n ins \<equiv>
  map_op (case_option (Inl (0 :: 3)) (\<lambda>p. Inr (0, p))) (case_option (Inl (0 :: 3)) (\<lambda>p. Inr (0, p)))
  (ooo_input_top os n ins)\<close>

abbreviation label_op where
  \<open>label_op os caps tis G vs label \<equiv>
  map_op (case_option (Inl (1 :: 3)) (\<lambda>p. Inr (1, p))) (case_option (Inl (1 :: 3)) (\<lambda>p. Inr (1, p)))
  (label_prop_op os caps tis G vs label)\<close>

abbreviation incr_op' where
  \<open>incr_op' incr os \<equiv>
  map_op (case_option (Inl (2 :: 3)) (\<lambda>p. Inr (1, p))) (case_option (Inl (2 :: 3)) (\<lambda>p. Inr (2, p)))
  (increment_top incr os)\<close>

end