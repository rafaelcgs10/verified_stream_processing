theory ConnectedComponents

imports
  Accumulator
  Input_top
  Dataplane.Timely_Infrastructure
  Dataplane.MyProduct_Instances
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

(* TODO move *)
abbreviation "mint_cap os p t \<equiv> os\<lparr> inter := inter os @ [(p, t, 1)] \<rparr>"
abbreviation "produces os batch \<equiv> os\<lparr> outpu := (\<lambda> p. outpu os p @ map (\<lambda> (x, cap). (x, time cap)) (filter (\<lambda> (x, cap). out cap = p) batch)), produ := produ os @ map (\<lambda> (x, cap). (out cap, time cap, 1)) batch \<rparr>"

corec input_top' where
  \<open>input_top' os n ins = choice3
  (Choice (cimage (\<lambda>p. case ins p of
    LCons (Data ts d) lxs \<Rightarrow>
      let cap = Cap (n p) p;
          os' = if lxs = LNil then drop_cap os cap else delay_cap os cap ts;
          os'' = produce os' (Cap (time cap + ts) p) [d]
      in Silent (input_top' os'' n (ins(p := lxs)))
  | LCons (Watermark ts) lxs \<Rightarrow>
      let cap = Cap (n p) p;
          os' = if lxs = LNil then drop_cap os cap else delay_cap os cap ts
      in Silent (input_top' os' (n(p := n p + ts)) (ins(p := lxs))))
    (cfilter (\<lambda>p. ins p \<noteq> LNil) c\<UU>)))
  (Choice (cimage (\<lambda>p. case outpu os p of
    x # xs \<Rightarrow> send_output (input_top' (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>) n ins) p x)
    (cfilter (\<lambda>p. outpu os p \<noteq> []) c\<UU>)))
  (let (os', st) = obtain_progress os
  in send_progress (input_top' os' n ins) st)\<close>

abbreviation \<open>choice4 op1 op2 op3 op4 \<equiv> choice2 (choice3 op1 op2 op3) op4\<close>
abbreviation \<open>choice5 op1 op2 op3 op4 op5 \<equiv> choice2 (choice4 op1 op2 op3 op4) op5\<close>
abbreviation \<open>choice6 op1 op2 op3 op4 op5 op6 \<equiv> choice2 (choice5 op1 op2 op3 op4 op5) op6\<close>
abbreviation \<open>choice7 op1 op2 op3 op4 op5 op6 op7 \<equiv> choice2 (choice6 op1 op2 op3 op4 op5 op6) op7\<close>

corec plus01_op where
  \<open>plus01_op os = choice3
  (Choice (cimage (\<lambda>p. Read (Some p) (\<lambda>x. case x of
    Inr (d, ts) \<Rightarrow>
      let cap = Cap ts p;
          os' = consume os p ts 1;
          os'' = produce os' (Cap (time cap + MyPair 0 1) p) [d]
      in plus01_op os''
  | _ \<Rightarrow> \<oslash>)) c\<UU>))
  (Choice (cimage (\<lambda>p. case outpu os p of
    x # xs \<Rightarrow> send_output (plus01_op (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>)) p x)
    (cfilter (\<lambda>p. outpu os p \<noteq> []) c\<UU>)))
  (let (os', st) = obtain_progress os
  in send_progress (plus01_op os') st)\<close>

lemma step_plus01_op_Inp_elim:
  assumes \<open>step io (plus01_op os) op\<close>
  obtains p d ts where \<open>io = Inp (Some p) (Inr (d, ts))\<close> \<open>op = plus01_op (produce (consume os p ts 1) (Cap (ts + MyPair 0 1) p) [d])\<close>
  | p x where \<open>io = Inp (Some p) (Inl x)\<close> \<open>op = \<oslash>\<close>
  | p x xs where \<open>io = Out (Some p) (Inr x)\<close> \<open>outpu os p = x # xs\<close> \<open>op = plus01_op (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>)\<close>
  | os' st where \<open>io = Out None (Inl (Inl st))\<close> \<open>obtain_progress os = (os', st)\<close> \<open>op = plus01_op os'\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) plus01_op.code)
  apply (cases io)
  by (auto split: sum.splits list.splits)

declare [[unify_search_bound = 100]]

corec label_prop_op where
  \<open>label_prop_op os caps buf1 E buf2 label = choice7
  (Read None (\<lambda>st. case st of Inl (Inr f) \<Rightarrow> label_prop_op (os\<lparr> front := f \<rparr>) caps buf1 E buf2 label | _ \<Rightarrow> \<oslash>))
  (Read (Some (1 :: 2)) (\<lambda>x. case x of
    Inr ((s, d), ts) \<Rightarrow>
      let cap = Cap ts 1;
          (caps', os') = if cap \<in> set caps then (caps, os) else (caps @ [cap], mint_cap os 1 ts);
          os'' = consume os' 1 ts 1;
          buf1' = buf1(ts := buf1 ts @ [(s, d), (d, s)])
     in label_prop_op os'' (sort_key time caps') buf1' E buf2 label
  | _ \<Rightarrow> \<oslash>))
  (Read (Some (2 :: 2)) (\<lambda>x. case x of
    Inr ((n, x), ts) \<Rightarrow>
      let cap = Cap ts 2;
          (caps', os') = if cap \<in> set caps then (caps, os) else (caps @ [cap], mint_cap os 2 ts);
          os'' = consume os' 1 ts 1;
          buf2' = buf2(ts := buf2 ts @ [(n, x)])
    in label_prop_op os'' (sort_key time caps') buf1 E buf2' label
  | _ \<Rightarrow> \<oslash>))
  (case [cap \<leftarrow> caps. time_below_frontier (time cap) (front os 1) \<and> out cap = 1] of
    [] \<Rightarrow> Silent (label_prop_op os caps buf1 E buf2 label)
  | cap # caps' \<Rightarrow>
      let ts = time cap;
          buf1' = buf1(ts := []);
          E' = E @ buf1 ts;
          vertices = remdups (map fst E' @ map snd E');
          neighbors = (\<lambda>x. remdups [snd e. e \<leftarrow> E', fst e = x]);
          batch = [((n, label v), cap). v \<leftarrow> vertices, n \<leftarrow> neighbors v];
          os' = produces os batch;
          os'' = drop_cap os' cap
      in Silent (label_prop_op os'' caps' buf1' E' buf2 label))
  (case [cap \<leftarrow> caps. time_below_frontier (time cap) (front os 2) \<and> out cap = 2] of
    [] \<Rightarrow> Silent (label_prop_op os caps buf1 E buf2 label)
  | cap # caps' \<Rightarrow>
      let ts = time cap;
          buf2' = buf2(ts := []);
          vertices = remdups (map fst E @ map snd E);
          neighbors = (\<lambda>x. remdups [snd e. e \<leftarrow> E, fst e = x]);
          min_label = (\<lambda>n. Min (set [x. (n, x) \<leftarrow> buf2 ts]));
          updated_vertices = [v. v \<leftarrow> vertices, min_label v < label v];
          label' = foldl (\<lambda>f v. f(v := min_label v)) label updated_vertices;
          batch = [((n, label' v), cap). v \<leftarrow> updated_vertices, n \<leftarrow> neighbors v];
          os' = produces os batch;
          os'' = drop_cap os' cap
      in Silent (label_prop_op os'' caps' buf1 E buf2' label'))
  (Choice (cimage (\<lambda>p. case outpu os p of
    x # xs \<Rightarrow> send_output (label_prop_op (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>) caps buf1 E buf2 label) p x)
    (cfilter (\<lambda>p. outpu os p \<noteq> []) c\<UU>)))
  (let (os', st) = obtain_progress os
  in send_progress (label_prop_op os' caps buf1 E buf2 label) st)\<close>

abbreviation inp_op where
  \<open>inp_op os n ins \<equiv>
  map_op (case_option (Inl (0 :: 2)) (\<lambda>p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda>p. Inr (0, p)))
  (input_top' os n ins)\<close>

abbreviation plus_op where
  \<open>plus_op os \<equiv>
  map_op (case_option (Inl (1 :: 2)) (\<lambda>p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda>p. Inr (1, p)))
  (plus01_op os)\<close>

abbreviation inp_plus_op where
  \<open>inp_plus_op os1 n ins buf1 os2 \<equiv>
  map_op (case_sum id id) (case_sum id id)
  (comp_op [Inr (0 :: 2, 0 :: 1) \<mapsto> Inr (1 :: 2, 0 :: 1)] buf1 (inp_op os1 n ins)
    (plus_op os2))\<close>

abbreviation inp_plus_edges where
  \<open>inp_plus_edges \<equiv> (\<lambda>l. if l = Loc (0 :: 2) (Src (0 :: 1)) then [Loc (1 :: 2) (Trg (0 :: 1))] else [])\<close>

abbreviation inp_plus_summary where
  \<open>inp_plus_summary \<equiv> (\<lambda>l1 l2.
   if l1 = Loc (0 :: 2) (Src (0 :: 1)) \<and> l2 = Loc (1 :: 2)  (Trg (0 :: 1))
   then frontier {#0 :: (nat, nat) myprod#}\<^sub>z
   else if l1 = Loc 0 (Trg 0) \<and> l2 = Loc 0 (Src 0)
   then frontier {#0#}\<^sub>z
   else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
   then frontier {#0#}\<^sub>z
   else {}\<^sub>A)\<close>

lemma
  \<open>edges sg = inp_plus_edges \<Longrightarrow>
  summ sg = inp_plus_summary \<Longrightarrow>
  dataflow_op sg (inp_plus_op os1 n ins buf1 os2)
  \<approx> map_op (\<lambda>p. (1, p)) (\<lambda>p. (1, p)) (source_op ins')\<close>
  oops

abbreviation label_op where
  \<open>label_op os caps buf1 E buf2 label \<equiv>
  map_op (case_option (Inl (1 :: 3)) (\<lambda>p. Inr (1, p))) (case_option (Inl (1 :: 3)) (\<lambda>p. Inr (1, p)))
  (label_prop_op os caps buf1 E buf2 label)\<close>

end