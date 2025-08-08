theory ConnectedComponents

imports
  Accumulator
  Dataplane.Timely_Infrastructure
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

instantiation prod :: (plus, plus) plus
begin
fun plus_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>(x, y) + (u, v) = (x + u, y + v)\<close>
instance ..
end

instantiation prod :: (zero, zero) zero
begin
definition zero_prod :: \<open>'a \<times> 'b\<close> where
  \<open>0 = (0, 0)\<close>
instance ..
end

abbreviation cc_spec where
  \<open>cc_spec \<equiv> accumulator_op (\<lambda>_. (\<union>)) (\<lambda>_. The \<circ> is_ccs) (\<lambda>_. 0)\<close>

(* TODO move *)
abbreviation "send_output op p x \<equiv> Write op (Some p) (Inr x)"
abbreviation "send_progress op st \<equiv> Write op None (Inl (Inl st))"
abbreviation "obtain_progress os \<equiv> (os\<lparr> consu := [], inter := [], produ := [] \<rparr>, \<lparr> cons = consu os, inte = inter os, prod = produ os\<rparr>)"
abbreviation "drop_cap os cap \<equiv> (os\<lparr> inter := inter os @ [(out cap, time cap, -1)] \<rparr>)"
abbreviation "mint_cap os p t \<equiv> os\<lparr> inter := inter os @ [(p, t, 1)] \<rparr>"
abbreviation "produces os batch \<equiv> os\<lparr> outpu := (\<lambda> p. outpu os p @ map (\<lambda> (x, cap). (x, time cap)) (filter (\<lambda> (x, cap). out cap = p) batch)), produ := produ os @ map (\<lambda> (x, cap). (out cap, time cap, 1)) batch \<rparr>"

(* Why use the Silent constructor? Is it to make it easier to reason later about the different possible steps? *)
corec ooo_input_top where
  \<open>ooo_input_top os caps inps = choice3
  (Choice (cimage (\<lambda>p. case inps p of
    LCons (Data ts d) lxs \<Rightarrow>
      let cap = Cap (caps p) p;
          os' = delay_cap os cap ts;
          os'' = produce os' (Cap (time cap + ts) p) [d]
      in Silent (ooo_input_top os'' caps (inps(p := lxs)))
  | LCons (Watermark ts) lxs \<Rightarrow>
      let cap = Cap (caps p) p;
          os' = if lxs = LNil then drop_cap os cap else delay_cap os cap ts
      in Silent (ooo_input_top os' (caps(p := caps p + ts)) (inps(p := lxs))))
    (cfilter (\<lambda>p. inps p \<noteq> LNil) c\<UU>)))
  (Choice (cimage (\<lambda>p. case outpu os p of
    x # xs \<Rightarrow> send_output (ooo_input_top (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>) caps inps) p x)
    (cfilter (\<lambda>p. outpu os p \<noteq> []) c\<UU>)))
  (let (os', st) = obtain_progress os
  in send_progress (ooo_input_top os' caps inps) st)\<close>

abbreviation \<open>choice4 op1 op2 op3 op4 \<equiv> choice2 (choice3 op1 op2 op3) op4\<close>
abbreviation \<open>choice5 op1 op2 op3 op4 op5 \<equiv> choice2 (choice4 op1 op2 op3 op4) op5\<close>
abbreviation \<open>choice6 op1 op2 op3 op4 op5 op6 \<equiv> choice2 (choice5 op1 op2 op3 op4 op5) op6\<close>
abbreviation \<open>choice7 op1 op2 op3 op4 op5 op6 op7 \<equiv> choice2 (choice6 op1 op2 op3 op4 op5 op6) op7\<close>

(* Should this operator use the frontier, or just do +(0, 1) on timestamps without caring? *)
corec plus01_op where
  \<open>plus01_op os caps = choice4
  (Read None (\<lambda>st. case st of Inl (Inr f) \<Rightarrow> plus01_op (os\<lparr> front := f \<rparr>) caps | _ \<Rightarrow> \<oslash>))
  (Choice (cimage (\<lambda>p. Read (Some p) (\<lambda>x. case x of
    Inr (d, ts) \<Rightarrow>
      let cap = Cap ts p;
          (caps', os') = if cap \<in> set caps then (caps, os) else (caps @ [cap], mint_cap os p ts);
          os'' = delay_cap os' cap (0, 1);
          os''' = produce os'' (Cap (time cap + (0, 1)) p) [d]
      in plus01_op os''' caps'
  | _ \<Rightarrow> \<oslash>)) c\<UU>))
  (Choice (cimage (\<lambda>p. case outpu os p of
    x # xs \<Rightarrow> send_output (plus01_op (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>) caps) p x)
    (cfilter (\<lambda>p. outpu os p \<noteq> []) c\<UU>)))
  (let (os', st) = obtain_progress os
  in send_progress (plus01_op os' caps) st)\<close>

corec label_prop_op where
  \<open>label_prop_op os caps buf1 E buf2 lbls = choice7
  (Read None (\<lambda>st. case st of Inl (Inr f) \<Rightarrow> label_prop_op (os\<lparr> front := f \<rparr>) caps buf1 E buf2 lbls | _ \<Rightarrow> \<oslash>))
  (Read (Some (1 :: 2)) (\<lambda>x. case x of
    Inr ((s, d), ts) \<Rightarrow>
      let cap = Cap ts 1;
          (caps', os') = if cap \<in> set caps then (caps, os) else (caps @ [cap], mint_cap os 1 ts);
          buf1' = buf1(ts := buf1 ts @ [(s, d), (d, s)])
     in label_prop_op os' (sort_key time caps') buf1' E buf2 lbls
  | _ \<Rightarrow> \<oslash>))
  (Read (Some (2 :: 2)) (\<lambda>x. case x of
    Inr ((n, x), ts) \<Rightarrow>
      let cap = Cap ts 2;
          (caps', os') = if cap \<in> set caps then (caps, os) else (caps @ [cap], mint_cap os 2 ts);
          buf2' = buf2(ts := buf2 ts @ [(n, x)])
    in label_prop_op os' (sort_key time caps') buf1 E buf2' lbls
  | _ \<Rightarrow> \<oslash>))
  (case [cap \<leftarrow> caps. time_below_frontier (time cap) (front os 1) \<and> out cap = 1] of
    [] \<Rightarrow> Silent (label_prop_op os caps buf1 E buf2 lbls)
  | cap # caps' \<Rightarrow>
      let ts = time cap;
          buf1' = buf1(ts := []);
          E' = E @ buf1 ts;
          vertices = remdups (map fst E' @ map snd E');
          neighbors = (\<lambda>x. remdups [snd e. e \<leftarrow> E', fst e = x]);
          batch = [((n, the (lbls v)), cap). v \<leftarrow> vertices, n \<leftarrow> neighbors v];
          os' = produces os batch;
          os'' = drop_cap os' cap
      in Silent (label_prop_op os'' caps' buf1' E' buf2 lbls))
  (case [cap \<leftarrow> caps. time_below_frontier (time cap) (front os 2) \<and> out cap = 2] of
    [] \<Rightarrow> Silent (label_prop_op os caps buf1 E buf2 lbls)
  | cap # caps' \<Rightarrow>
      let ts = time cap;
          buf2' = buf2(ts := []);
          vertices = remdups (map fst E @ map snd E)
      in undefined)
  (Choice (cimage (\<lambda>p. case outpu os p of
    x # xs \<Rightarrow> send_output (label_prop_op (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>) caps buf1 E buf2 lbls) p x)
    (cfilter (\<lambda>p. outpu os p \<noteq> []) c\<UU>)))
  (let (os', st) = obtain_progress os
  in send_progress (label_prop_op os' caps buf1 E buf2 lbls) st)\<close>

end