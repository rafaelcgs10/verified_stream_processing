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

abbreviation "produces os batch \<equiv> os\<lparr> outpu := (\<lambda> p. outpu os p @ map (\<lambda> (x, cap). (x, capability.time cap)) (filter (\<lambda> (x, cap). out cap = p) batch)), produ := produ os @ map (\<lambda> (x, cap). (out cap, capability.time cap, 1)) batch \<rparr>"

abbreviation \<open>mint os caps p t \<equiv> let cap = Cap t p in
  if cap \<in> set caps then (caps, os) else (caps @ [cap], mint_cap os p t)\<close>

definition update_graph where
  \<open>update_graph E s d t =
  (let f = (\<lambda>E' t'. let g = case_option (\<lambda>_. []) id (E' t') in E'(t' := Some (g(s := g s @ [d], d := g d @ [s]))))
  in foldl f E [t ..< Max (dom E) + 1])\<close>

definition update_label where
  \<open>update_label label a b t n =
  foldl (\<lambda>label' t'. label'(t' := (label' t')(b := min (label' t' b) a))) label [t ..< n]\<close>

primrec remdups_f where
  \<open>remdups_f f [] = []\<close>
| \<open>remdups_f f (x # xs) = (if f x \<in> f ` set xs then remdups_f f xs else x # remdups_f f xs)\<close>

lemma remdups_f_id:
  \<open>remdups_f id xs = remdups xs\<close>
  by (induction xs) simp_all

(* declare [[unify_search_bound = 100]] *)
corec label_prop_op where
  \<open>label_prop_op os caps E label = choice6
  (Read None (\<lambda>st. case st of Inl (Inr f) \<Rightarrow> label_prop_op (os\<lparr>front := f\<rparr>) caps E label | _ \<Rightarrow> \<oslash>))
  (Read (Some (0 :: 2)) (\<lambda>x. case x of
    Inr ((s, d), ts) \<Rightarrow>
      let (caps', os') = mint os caps 0 ts;
          os'' = consume os' 0 ts 1;
          t = myfst ts;
          E' = update_graph E s d t;
          (a, b) = (min s d, max s d);
          label' = update_label label a b t (Max (dom E) + 1);
          batch = if label t b > a
            then map (\<lambda>v. ((v, a), Cap ts 0)) (filter (\<lambda>v. label t v > a) (the (E' t) b))
            else [];
          os''' = produces os'' batch
     in label_prop_op os''' caps' E' label'
  | _ \<Rightarrow> \<oslash>))
  (Read (Some (1 :: 2)) (\<lambda>x. case x of
    Inr ((n, x), ts) \<Rightarrow>
      let (caps', os') = mint os caps 0 ts;
          (caps'', os'') = mint os' caps' 1 ts;
          os''' = consume os'' 1 ts 1;
          t = myfst ts;
          label' = update_label label x n t (Max (dom E) + 1);
          batch = if label t n > x
            then map (\<lambda>v. ((v, x), Cap ts 0)) (filter (\<lambda>v. label t v > x) (the (E t) n))
            else [];
          os'''' = produces os''' batch
    in label_prop_op os'''' caps' E label'
  | _ \<Rightarrow> \<oslash>))
  (let below_caps = [cap \<leftarrow> caps. \<not> frontier_less_equal (front os 1) (capability.time cap)];
       above_caps = [cap \<leftarrow> caps. frontier_less_equal (front os 1) (capability.time cap)];
       output_caps = remdups_f (myfst \<circ> capability.time) below_caps;
       batch = concat (map (\<lambda>cap. let t = myfst (capability.time cap) in map (\<lambda>v. ((v, label t v), cap)) (filter (\<lambda>v. the (E t) v \<noteq> []) undefined)) output_caps);
       os' = produces os batch;
       os'' = drop_caps os' below_caps
  in Silent (label_prop_op os'' above_caps E label))
  (Choice (cimage (\<lambda>p. case outpu os p of
    x # xs \<Rightarrow> send_output (label_prop_op (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) caps E label) p x)
    (cfilter (\<lambda>p. outpu os p \<noteq> []) c\<UU>)))
  (let (os', st) = obtain_progress os
  in send_progress (label_prop_op os' caps E label) st)\<close>

abbreviation inp_op' where
  \<open>inp_op' os n ins \<equiv>
  map_op (case_option (Inl (0 :: 3)) (\<lambda>p. Inr (0, p))) (case_option (Inl (0 :: 3)) (\<lambda>p. Inr (0, p)))
  (ooo_input_top os n ins)\<close>

abbreviation label_op where
  \<open>label_op os caps E label \<equiv>
  map_op (case_option (Inl (1 :: 3)) (\<lambda>p. Inr (1, p))) (case_option (Inl (1 :: 3)) (\<lambda>p. Inr (1, p)))
  (label_prop_op os caps E label)\<close>

abbreviation incr_op' where
  \<open>incr_op' incr os \<equiv>
  map_op (case_option (Inl (2 :: 3)) (\<lambda>p. Inr (1, p))) (case_option (Inl (2 :: 3)) (\<lambda>p. Inr (2, p)))
  (increment_top incr os)\<close>

end