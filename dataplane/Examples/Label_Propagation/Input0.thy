theory Input0

imports
  Input1
begin

lemma input_0_fst_label_prop_input0_batched_empty:
  assumes \<open>msgs = input os (0 :: 2)\<close>
  shows \<open>input (fst (label_prop_input0_batched os msgs)) (0 :: 2) = []\<close>
  using assms by simp


lemma filter_label_prop_input0_step_batch_out_neq[simp]:
  assumes \<open>p \<noteq> (1 :: 2)\<close>
  shows \<open>filter (\<lambda>(x, cap). out cap = p) (label_prop_input0_step_batch os d t) = []\<close>
  using assms
  unfolding label_prop_input0_step_batch_def label_prop_edge_batch_def
    label_prop_neighbor_batch_def
  by (auto simp add: filter_empty_conv split: if_splits)


lemma filter_snd_label_prop_input0_batched_out_neq[simp]:
  assumes \<open>p \<noteq> (1 :: 2)\<close>
  shows \<open>filter (\<lambda>(x, cap). out cap = p) (snd (label_prop_input0_batched os msgs)) = []\<close>
  using assms
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  obtain os' batches where rec_eq:
    \<open>label_prop_input0_batched (label_prop_input0_step_state os d t) msgs = (os', batches)\<close>
    by (cases \<open>label_prop_input0_batched (label_prop_input0_step_state os d t) msgs\<close>)
  have rec: \<open>filter (\<lambda>(x, cap). out cap = p) batches = []\<close>
    using Cons.hyps[OF Cons.prems, of \<open>label_prop_input0_step_state os d t\<close>] rec_eq
    by simp
  show ?case
    using Cons.prems rec unfolding msg_eq
    by (simp add: rec_eq)
qed


lemma outpu_0_fst_label_prop_input0_batched[simp]:
  \<open>outpu (fst (label_prop_input0_batched os msgs)) (0 :: 2) = outpu os 0\<close>
  by simp


lemma all_edges_eq_graph_entries:
  assumes inv: \<open>label_prop_upd_inv os\<close>
  shows \<open>all_edges os q = {e. \<exists>t\<in>set (timestamps os). t \<le> q \<and> snd e \<in> set (graph os t (fst e))}\<close>
proof (intro set_eqI iffI)
  fix e
  assume e_in: \<open>e \<in> all_edges os q\<close>
  obtain v w where e: \<open>e = (v, w)\<close>
    by (cases e)
  then obtain t where \<open>t \<in> set (timestamps os)\<close> \<open>t \<le> q\<close> \<open>w \<in> set (graph os t v)\<close>
    using e_in unfolding all_edges_def set_neighbors by auto
  then show \<open>e \<in> {e. \<exists>t\<in>set (timestamps os). t \<le> q \<and> snd e \<in> set (graph os t (fst e))}\<close>
    using e by auto
next
  fix e
  assume e_in: \<open>e \<in> {e. \<exists>t\<in>set (timestamps os). t \<le> q \<and> snd e \<in> set (graph os t (fst e))}\<close>
  then obtain t where t: \<open>t \<in> set (timestamps os)\<close> \<open>t \<le> q\<close>
    and graph_edge: \<open>snd e \<in> set (graph os t (fst e))\<close>
    by auto
  have vertices: \<open>fst e \<in> set (vertices os t)\<close> \<open>snd e \<in> set (vertices os t)\<close>
    using label_prop_upd_inv_graph_edgeD[OF inv graph_edge] by auto
  have all_vertices: \<open>fst e \<in> all_vertices os q\<close> \<open>snd e \<in> all_vertices os q\<close>
    using t vertices unfolding all_vertices_def by auto
  have neighbor: \<open>snd e \<in> set (neighbors os q (fst e))\<close>
    using t graph_edge unfolding set_neighbors by auto
  show \<open>e \<in> all_edges os q\<close>
    using all_vertices neighbor unfolding all_edges_def by (cases e) auto
qed


lemma all_edges_label_prop_input0_step_state_eq:
  assumes INV: \<open>label_prop_upd_inv os\<close>
  shows \<open>all_edges (label_prop_input0_step_state os d t) q =
    all_edges os q \<union>
      (if myfst t \<le> q then
        {(fst (de1 os d), snd (de1 os d)), (snd (de1 os d), fst (de1 os d))}
       else {})\<close>
proof -
  let ?v1 = \<open>fst (de1 os d)\<close>
  let ?v2 = \<open>snd (de1 os d)\<close>
  let ?t1 = \<open>myfst t\<close>
  let ?l1 = \<open>min_label os ?t1 ?v1\<close>
  let ?l2 = \<open>min_label os ?t1 ?v2\<close>
  let ?v = \<open>if ?l1 > ?l2 then ?v1 else ?v2\<close>
  let ?l = \<open>if ?l1 > ?l2 then ?l2 else ?l1\<close>
  let ?G = \<open>(graph os)(?t1 := (graph os ?t1)
    (?v1 := ?v2 # graph os ?t1 ?v1, ?v2 := ?v1 # graph os ?t1 ?v2))\<close>
  let ?V = \<open>(vertices os)(?t1 := [?v1, ?v2] @ vertices os ?t1)\<close>
  let ?os' = \<open>label_prop_edge_record_update (input_tl os 0) ?t1 ?v1 ?v2 ?v ?l\<close>
  have step_edges: \<open>all_edges (label_prop_input0_step_state os d t) q = all_edges ?os' q\<close>
    by simp
  have os'_fields:
    \<open>timestamps ?os' = ?t1 # timestamps os\<close>
    \<open>graph ?os' = ?G\<close>
    \<open>vertices ?os' = ?V\<close>
    by (simp_all add: label_prop_edge_record_update_def input_tl_def)
  have old_edges:
    \<open>all_edges os q = {e. \<exists>t\<in>set (timestamps os). t \<le> q \<and> snd e \<in> set (graph os t (fst e))}\<close>
    by (rule all_edges_eq_graph_entries[OF INV])
  have new_graph_edgeD:
    \<open>\<And>t' e. snd e \<in> set (?G t' (fst e)) \<Longrightarrow> fst e \<in> set (?V t') \<and> snd e \<in> set (?V t')\<close>
  proof -
    fix t' e
    assume graph_edge: \<open>snd e \<in> set (?G t' (fst e))\<close>
    obtain x y where e: \<open>e = (x, y)\<close>
      by (cases e)
    show \<open>fst e \<in> set (?V t') \<and> snd e \<in> set (?V t')\<close>
      using graph_edge label_prop_upd_inv_graph_edgeD[OF INV]
      unfolding e by (auto split: if_splits)
  qed
  have new_edges:
    \<open>all_edges ?os' q = {e. \<exists>t\<in>set (?t1 # timestamps os). t \<le> q \<and> snd e \<in> set (?G t (fst e))}\<close>
  proof (intro set_eqI iffI)
    fix e
    assume e_in: \<open>e \<in> all_edges ?os' q\<close>
    then obtain t' where t': \<open>t' \<in> set (?t1 # timestamps os)\<close> \<open>t' \<le> q\<close>
      and graph_edge: \<open>snd e \<in> set (?G t' (fst e))\<close>
      using os'_fields unfolding all_edges_def set_neighbors by (cases e) auto
    show \<open>e \<in> {e. \<exists>t\<in>set (?t1 # timestamps os). t \<le> q \<and> snd e \<in> set (?G t (fst e))}\<close>
      using t' graph_edge by blast
  next
    fix e
    assume e_in: \<open>e \<in> {e. \<exists>t\<in>set (?t1 # timestamps os). t \<le> q \<and> snd e \<in> set (?G t (fst e))}\<close>
    then obtain t' where t': \<open>t' \<in> set (?t1 # timestamps os)\<close> \<open>t' \<le> q\<close>
      and graph_edge: \<open>snd e \<in> set (?G t' (fst e))\<close>
      by blast
    have vertices: \<open>fst e \<in> set (?V t')\<close> \<open>snd e \<in> set (?V t')\<close>
      using new_graph_edgeD[OF graph_edge] by auto
    have t'_new: \<open>t' \<in> {u \<in> set (timestamps ?os'). u \<le> q}\<close>
      using t' os'_fields(1) by auto
    have vertices_new: \<open>fst e \<in> set (vertices ?os' t')\<close> \<open>snd e \<in> set (vertices ?os' t')\<close>
      using vertices os'_fields(3) by auto
    have all_vertices: \<open>fst e \<in> all_vertices ?os' q\<close> \<open>snd e \<in> all_vertices ?os' q\<close>
      using t'_new vertices_new unfolding all_vertices_def by blast+
    have graph_new: \<open>snd e \<in> set (graph ?os' t' (fst e))\<close>
      using graph_edge os'_fields(2) by auto
    have neighbor: \<open>snd e \<in> set (neighbors ?os' q (fst e))\<close>
      using t'_new graph_new unfolding set_neighbors by blast
    show \<open>e \<in> all_edges ?os' q\<close>
      using all_vertices neighbor unfolding all_edges_def by (cases e) auto
  qed
  have graph_entries:
    \<open>{e. \<exists>t\<in>set (?t1 # timestamps os). t \<le> q \<and> snd e \<in> set (?G t (fst e))} =
      {e. \<exists>t\<in>set (timestamps os). t \<le> q \<and> snd e \<in> set (graph os t (fst e))} \<union>
      (if ?t1 \<le> q then {(?v1, ?v2), (?v2, ?v1)} else {})\<close>
  proof (intro set_eqI iffI)
    fix e
    assume e_in: \<open>e \<in> {e. \<exists>t\<in>set (?t1 # timestamps os). t \<le> q \<and> snd e \<in> set (?G t (fst e))}\<close>
    then obtain t' where t': \<open>t' \<in> set (?t1 # timestamps os)\<close> \<open>t' \<le> q\<close>
      and graph_edge: \<open>snd e \<in> set (?G t' (fst e))\<close>
      by blast
    show \<open>e \<in> {e. \<exists>t\<in>set (timestamps os). t \<le> q \<and> snd e \<in> set (graph os t (fst e))} \<union>
      (if ?t1 \<le> q then {(?v1, ?v2), (?v2, ?v1)} else {})\<close>
    proof (cases \<open>t' = ?t1\<close>)
      case False
      then have \<open>t' \<in> set (timestamps os)\<close>
        using t' by auto
      moreover have \<open>snd e \<in> set (graph os t' (fst e))\<close>
        using graph_edge False by auto
      ultimately show ?thesis
        using t' by auto
    next
      case t1_eq: True
      show ?thesis
      proof (cases \<open>?t1 \<in> set (timestamps os)\<close>)
        case in_ts: True
        have old_or_new:
          \<open>snd e \<in> set (graph os ?t1 (fst e)) \<or>
            (fst e = ?v1 \<and> snd e = ?v2) \<or> (fst e = ?v2 \<and> snd e = ?v1)\<close>
          using graph_edge t1_eq by (cases e) (auto split: if_splits)
        then show ?thesis
          using t' t1_eq in_ts by (cases e) auto
      next
        case not_ts: False
        have empty: \<open>graph os ?t1 (fst e) = []\<close>
          using label_prop_upd_inv_graph_empty_if_not_timestamp[OF INV not_ts, of \<open>fst e\<close>] .
        have new_edge:
          \<open>(fst e = ?v1 \<and> snd e = ?v2) \<or> (fst e = ?v2 \<and> snd e = ?v1)\<close>
          using graph_edge t1_eq empty by (cases e) (auto split: if_splits)
        then show ?thesis
          using t' t1_eq by (cases e) auto
      qed
    qed
  next
    fix e
    assume e_in: \<open>e \<in> {e. \<exists>t\<in>set (timestamps os). t \<le> q \<and> snd e \<in> set (graph os t (fst e))} \<union>
      (if ?t1 \<le> q then {(?v1, ?v2), (?v2, ?v1)} else {})\<close>
    from e_in consider
      (old) t' where \<open>t' \<in> set (timestamps os)\<close> \<open>t' \<le> q\<close> \<open>snd e \<in> set (graph os t' (fst e))\<close>
    | (new) \<open>?t1 \<le> q\<close> \<open>e = (?v1, ?v2) \<or> e = (?v2, ?v1)\<close>
      by (cases \<open>?t1 \<le> q\<close>) auto
    then show \<open>e \<in> {e. \<exists>t\<in>set (?t1 # timestamps os). t \<le> q \<and> snd e \<in> set (?G t (fst e))}\<close>
    proof cases
      case old
      then have \<open>snd e \<in> set (?G t' (fst e))\<close>
        by (cases e) auto
      then show ?thesis
        using old by auto
    next
      case new
      then show ?thesis
        by auto
    qed
  qed
  show ?thesis
    using step_edges old_edges new_edges graph_entries by simp
qed


lemma all_edges_fst_label_prop_input0_batched_prefix_eq:
  assumes input_eq: \<open>input os 0 = msgs @ rest\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>all_edges (fst (label_prop_input0_batched os msgs)) q =
    all_edges os q \<union>
      (\<Union>(d, t)\<in>set msgs. if myfst t \<le> q then
        {(fst (de1 os d), snd (de1 os d)), (snd (de1 os d), fst (de1 os d))}
       else {})\<close>
  using input_eq inv wf_upd
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case
    by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  let ?step = \<open>label_prop_input0_step_state os d t\<close>
  have input0: \<open>input os 0 = (d, t) # (msgs @ rest)\<close>
    using Cons.prems(1) msg_eq by simp
  have input_step: \<open>input ?step 0 = msgs @ rest\<close>
    using input0 by simp
  have inv_step: \<open>label_prop_upd_inv ?step\<close>
    by (rule label_prop_upd_inv_label_prop_input0_step_stateI[OF Cons.prems(2) input0 Cons.prems(3)])
  have wf_step: \<open>wf_label_prop_updates ?step (set (input ?step 1))\<close>
    by (rule wf_label_prop_updates_label_prop_input0_step_stateI[OF Cons.prems(2) Cons.prems(3)])
  have ih:
    \<open>all_edges (fst (label_prop_input0_batched ?step msgs)) q =
      all_edges ?step q \<union>
        (\<Union>(d, t)\<in>set msgs. if myfst t \<le> q then
          {(fst (de1 ?step d), snd (de1 ?step d)), (snd (de1 ?step d), fst (de1 ?step d))}
         else {})\<close>
    by (rule Cons.hyps[OF input_step inv_step wf_step])
  have step_edges:
    \<open>all_edges ?step q = all_edges os q \<union>
      (if myfst t \<le> q then
        {(fst (de1 os d), snd (de1 os d)), (snd (de1 os d), fst (de1 os d))}
       else {})\<close>
    by (rule all_edges_label_prop_input0_step_state_eq[OF Cons.prems(2)])
  show ?case
    using ih step_edges msg_eq
    by (cases \<open>label_prop_input0_batched ?step msgs\<close>)
      (auto simp add: Un_assoc Un_left_commute Un_commute)
qed


lemma all_edges_fst_label_prop_input0_batched_input_eq:
  assumes input_eq: \<open>input os 0 = msgs\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>all_edges (fst (label_prop_input0_batched os msgs)) q =
    all_edges os q \<union>
      (\<Union>(d, t)\<in>set msgs. if myfst t \<le> q then
        {(fst (de1 os d), snd (de1 os d)), (snd (de1 os d), fst (de1 os d))}
       else {})\<close>
  by (rule all_edges_fst_label_prop_input0_batched_prefix_eq[where rest=Nil])
    (use assms in simp_all)




lemma wf_label_prop_updates_label_prop_input0_step_state_monoI:
  assumes H: \<open>wf_label_prop_updates os S\<close>
  shows \<open>wf_label_prop_updates (label_prop_input0_step_state os d t) S\<close>
proof (rule wf_label_prop_updates_os_mono[OF H])
  show \<open>de1 os = de1 (label_prop_input0_step_state os d t)\<close>
    by simp
  show \<open>set (timestamps os) \<subseteq> set (timestamps (label_prop_input0_step_state os d t))\<close>
    by auto
  show \<open>\<forall>t'. set (vertices os t') \<subseteq> set (vertices (label_prop_input0_step_state os d t) t') \<and>
    (\<forall>v. set (graph os t' v) \<subseteq> set (graph (label_prop_input0_step_state os d t) t' v))\<close>
    unfolding label_prop_input0_step_state_def label_prop_edge_record_update_def input_tl_def
    by (auto simp: Let_def split: if_splits)
  show \<open>S = S\<close>
    by simp
qed


lemma wf_label_prop_updates_fst_label_prop_input0_batched_monoI:
  assumes H: \<open>wf_label_prop_updates os S\<close>
  shows \<open>wf_label_prop_updates (fst (label_prop_input0_batched os xs)) S\<close>
  using H
proof (induct xs arbitrary: os)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  obtain d t where x_eq: \<open>x = (d, t)\<close>
    by (cases x)
  have step: \<open>wf_label_prop_updates (label_prop_input0_step_state os d t) S\<close>
    by (rule wf_label_prop_updates_label_prop_input0_step_state_monoI[OF Cons.prems])
  have rec: \<open>wf_label_prop_updates (fst (label_prop_input0_batched (label_prop_input0_step_state os d t) xs)) S\<close>
    by (rule Cons.hyps[OF step])
  show ?case
    using rec unfolding x_eq
    by (cases \<open>label_prop_input0_batched (label_prop_input0_step_state os d t) xs\<close>) simp
qed


lemma labels_inv_fst_label_prop_input0_batched_input_allI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes input_eq: \<open>input os 0 = msgs\<close>
    and labels: \<open>\<forall>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>\<forall>q. labels_inv (all_edges (fst (label_prop_input0_batched os msgs)) q)
    (min_label (fst (label_prop_input0_batched os msgs)) q)\<close>
proof
  fix q
  show \<open>labels_inv (all_edges (fst (label_prop_input0_batched os msgs)) q)
    (min_label (fst (label_prop_input0_batched os msgs)) q)\<close>
    by (rule labels_inv_fst_label_prop_input0_batched_inputI[OF input_eq _ inv wf_upd])
      (use labels in simp)
qed


lemma wf_label_prop_updates_label_prop_input0_step_state_output1_shiftI:
  fixes os :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and d :: \<open>nat \<times> nat + nat set set\<close>
    and t :: \<open>(nat, nat) myprod\<close>
    and rest :: \<open>((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) list\<close>
    and S :: \<open>((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) set\<close>
  assumes input0: \<open>input os (0 :: 2) = (d, t) # rest\<close>
    and EN1: \<open>en1 os = Inl\<close>
    and DE1: \<open>de1 os = projl\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and LABELS: \<open>\<forall>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and WF_input1: \<open>wf_label_prop_updates os (set (input os (1 :: 2)))\<close>
    and WF: \<open>wf_label_prop_updates os
      (S \<union> ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) ` set (outpu os (1 :: 2))))\<close>
  shows \<open>wf_label_prop_updates (label_prop_input0_step_state os d t)
      (S \<union> ((\<lambda>(d, t). (d, t -+- MyPair (0 :: nat) (Suc (0 :: nat)))) `
        set (outpu (label_prop_input0_step_state os d t) (1 :: 2))))\<close>
proof -
  let ?step = \<open>label_prop_input0_step_state os d t\<close>
  let ?v1 = \<open>fst (de1 os d)\<close>
  let ?v2 = \<open>snd (de1 os d)\<close>
  let ?t1 = \<open>myfst t\<close>
  let ?l1 = \<open>min_label os ?t1 ?v1\<close>
  let ?l2 = \<open>min_label os ?t1 ?v2\<close>
  let ?v = \<open>if ?l1 > ?l2 then ?v1 else ?v2\<close>
  let ?l = \<open>if ?l1 > ?l2 then ?l2 else ?l1\<close>
  let ?updated = \<open>label_prop_edge_record_update (input_tl os 0) ?t1 ?v1 ?v2 ?v ?l\<close>
  let ?batch = \<open>label_prop_edge_batch os ?updated ?t1 ?v ?l t\<close>
  let ?shift = \<open>\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))\<close>
  have batch_eq: \<open>label_prop_input0_step_batch os d t = ?batch\<close>
    unfolding label_prop_input0_step_batch_def by (simp add: Let_def)
  have old_wf: \<open>wf_label_prop_updates ?step
      (S \<union> ?shift ` set (outpu os 1))\<close>
    by (rule wf_label_prop_updates_label_prop_input0_step_state_monoI[OF WF])
  have updated_inv: \<open>label_prop_upd_inv ?updated\<close>
  proof (rule label_prop_upd_inv_input0_preserved[OF INV])
    show \<open>timestamps ?updated = ?t1 # timestamps os\<close>
      by (simp add: label_prop_edge_record_update_def input_tl_def)
    show \<open>graph ?updated = (graph os)(?t1 := (graph os ?t1)(?v1 := ?v2 # graph os ?t1 ?v1,
        ?v2 := ?v1 # graph os ?t1 ?v2))\<close>
      by (simp add: label_prop_edge_record_update_def input_tl_def)
    show \<open>vertices ?updated = map_entry ?t1 ((@) [?v1, ?v2]) (vertices os)\<close>
      by (simp add: label_prop_edge_record_update_def input_tl_def)
    show \<open>label ?updated = (label os)(?t1 := (label os ?t1)(?v := ?l))\<close>
      by (simp add: label_prop_edge_record_update_def input_tl_def)
    show \<open>input ?updated 1 = input os 1\<close>
      by (simp add: label_prop_edge_record_update_def input_tl_def)
    show \<open>de1 ?updated = de1 os\<close>
      by (simp add: label_prop_edge_record_update_def input_tl_def)
    show \<open>(?v, ?l) = (if min_label os ?t1 ?v2 < min_label os ?t1 ?v1
        then (?v1, min_label os ?t1 ?v2)
        else (?v2, min_label os ?t1 ?v1))\<close>
      by simp
    show \<open>wf_label_prop_updates os (set (input os 1))\<close>
      by (rule WF_input1)
  qed
  have updated_labels: \<open>\<forall>q. labels_inv (all_edges ?updated q) (min_label ?updated q)\<close>
  proof
    fix q
    show \<open>labels_inv (all_edges ?updated q) (min_label ?updated q)\<close>
    proof (rule labels_inv_input0_preserved[OF _ INV])
      show \<open>\<And>q. labels_inv (all_edges os q) (min_label os q)\<close>
        using LABELS by blast
      show \<open>input ?updated = (input os)(0 := tl (input os 0))\<close>
        by (simp add: label_prop_edge_record_update_def input_tl_def)
      show \<open>timestamps ?updated = ?t1 # timestamps os\<close>
        by (simp add: label_prop_edge_record_update_def input_tl_def)
      show \<open>graph ?updated = (graph os)(?t1 := (graph os ?t1)(?v1 := ?v2 # graph os ?t1 ?v1,
          ?v2 := ?v1 # graph os ?t1 ?v2))\<close>
        by (simp add: label_prop_edge_record_update_def input_tl_def)
      show \<open>vertices ?updated = map_entry ?t1 ((@) [?v1, ?v2]) (vertices os)\<close>
        by (simp add: label_prop_edge_record_update_def input_tl_def)
      show \<open>label ?updated = (label os)(?t1 := (label os ?t1)(?v := ?l))\<close>
        by (simp add: label_prop_edge_record_update_def input_tl_def)
      show \<open>(?v, ?l) = (if min_label os ?t1 ?v2 < min_label os ?t1 ?v1
          then (?v1, min_label os ?t1 ?v2)
          else (?v2, min_label os ?t1 ?v1))\<close>
        by simp
    qed
  qed
  have new_wf: \<open>wf_label_prop_updates ?step
      (?shift ` set (map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = (1 :: 2)) ?batch)))\<close>
    unfolding wf_label_prop_updates_def
  proof (intro ballI)
    fix x
    assume x_in: \<open>x \<in> ?shift ` set (map (\<lambda>(x, cap). (x, capability.time (cap :: (2, (nat, nat) myprod) capability)))
      (filter (\<lambda>(x, cap). out cap = 1) ?batch))\<close>
    obtain y where x_y: \<open>x = ?shift y\<close>
      and y_in: \<open>y \<in> set (map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = (1 :: 2)) ?batch))\<close>
    proof -
      show thesis
        apply (rule imageE[OF x_in])
        subgoal for y
          apply (erule that[of y])
          apply assumption
          done
        done
    qed
    have y_in_image: \<open>y \<in> (\<lambda>(x, cap). (x, capability.time cap)) `
        set (filter (\<lambda>(x, cap). out cap = (1 :: 2)) ?batch)\<close>
      by (rule y_in[unfolded set_map])
    obtain z where y_z:
      \<open>y = (case z of (x, cap) \<Rightarrow> (x, capability.time cap))\<close>
      and z_in: \<open>z \<in> set (filter (\<lambda>(x, cap). out cap = (1 :: 2)) ?batch)\<close>
    proof (rule imageE[OF y_in_image])
      fix z
      assume y_z': \<open>y = (case z of (x, cap) \<Rightarrow> (x, capability.time cap))\<close>
        and z_in': \<open>z \<in> set (filter (\<lambda>(x, cap). out cap = (1 :: 2)) ?batch)\<close>
      show thesis
      proof (rule that)
        show \<open>y = (case z of (x, cap) \<Rightarrow> (x, capability.time cap))\<close>
          by (rule y_z')
        show \<open>z \<in> set (filter (\<lambda>(x, cap). out cap = (1 :: 2)) ?batch)\<close>
          by (rule z_in')
      qed
    qed
    obtain d' cap where z_eq: \<open>z = (d', cap)\<close>
      by (cases z)
    have z_filter: \<open>z \<in> {z \<in> set ?batch. (case z of (x, cap) \<Rightarrow> out cap = 1)}\<close>
      using z_in unfolding set_filter .
    have z_mem_out: \<open>z \<in> set ?batch \<and> (case z of (x, cap) \<Rightarrow> out cap = 1)\<close>
      using z_filter unfolding mem_Collect_eq .
    have z_mem: \<open>z \<in> set ?batch\<close>
      using z_mem_out by (rule conjunct1)
    have z_out: \<open>case z of (x, cap) \<Rightarrow> out cap = 1\<close>
      using z_mem_out by (rule conjunct2)
    have batch_mem: \<open>(d', cap) \<in> set ?batch\<close>
      using z_mem unfolding z_eq .
    have out_cap: \<open>out cap = 1\<close>
      using z_out unfolding z_eq by simp
    have y_eq: \<open>y = (d', capability.time cap)\<close>
      using y_z unfolding z_eq by simp
    have x_eq: \<open>x = (d', capability.time cap -+- MyPair 0 (Suc 0))\<close>
      using x_y y_eq by simp




    have ts: \<open>myfst (capability.time cap) \<in> set (timestamps ?updated)\<close>
      by (rule label_prop_edge_batch_in_timestamps[OF batch_mem])
    have vx: \<open>?v = ?v1 \<or> ?v = ?v2\<close>
      by simp
    have vertex: \<open>fst (de1 os d') \<in> all_vertices ?updated (myfst (capability.time cap))\<close>
      by (rule label_prop_edge_batch_all_vertices[OF refl refl EN1 DE1 updated_inv batch_mem refl refl vx])
    have cc: \<open>snd (de1 os d') \<in> cc_of (all_edges ?updated q) (fst (de1 os d'))\<close>
      if le: \<open>myfst (capability.time cap) \<le> q\<close> for q
    proof -
      have pair: \<open>(fst (de1 os d'), snd (de1 os d')) = de1 os d'\<close>
        by simp
      have vertex_label: \<open>(?v, ?l) = (if min_label os ?t1 ?v2 < min_label os ?t1 ?v1
          then (?v1, min_label os ?t1 ?v2)
          else (?v2, min_label os ?t1 ?v1))\<close>
        by simp
      show ?thesis
        by (rule label_prop_edge_batch_cc_of_all_edges
            [OF refl refl EN1 DE1 updated_inv batch_mem le pair vertex_label LABELS INV])
    qed
    show \<open>case x of (d, t) \<Rightarrow> myfst t \<in> set (timestamps ?step) \<and>
      fst (de1 ?step d) \<in> all_vertices ?step (myfst t) \<and>
      (\<forall>t'\<ge>myfst t. snd (de1 ?step d) \<in> cc_of (all_edges ?step t') (fst (de1 ?step d)))\<close>
      using ts vertex cc x_eq
      unfolding label_prop_input0_step_state_def
      by (auto simp: Let_def)
  qed
  have outpu_step: \<open>set (outpu ?step 1) = set (outpu os 1) \<union>
      set (map (\<lambda>(x, cap). (x, capability.time (cap :: (2, (nat, nat) myprod) capability ))) (filter (\<lambda>(x, cap). out cap = 1) ?batch))\<close>
    by (simp add: batch_eq)
  show ?thesis
    using old_wf new_wf
    unfolding outpu_step image_Un Un_assoc[symmetric]
    by (simp add: wf_label_prop_updates_un)
qed


lemma wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI:
  fixes os :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
  assumes input0: \<open>input os 0 = msgs @ rest\<close>
    and EN1: \<open>en1 os = Inl\<close>
    and DE1: \<open>de1 os = projl\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and LABELS: \<open>\<forall>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and WF_input1: \<open>wf_label_prop_updates os (set (input os 1))\<close>
    and WF: \<open>wf_label_prop_updates os
      (S \<union> ((\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) ` set (outpu os 1)))\<close>
  shows \<open>wf_label_prop_updates (fst (label_prop_input0_batched os msgs))
      (S \<union> ((\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) `
        set (outpu (fst (label_prop_input0_batched os msgs)) 1)))\<close>
  using input0 EN1 DE1 INV LABELS WF_input1 WF
proof (induct msgs arbitrary: os S)
  case Nil
  then show ?case
    by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  have input_step0: \<open>input os 0 = (d, t) # (msgs @ rest)\<close>
    using Cons.prems(1) msg_eq by simp
  let ?step = \<open>label_prop_input0_step_state os d t\<close>
  have step_wf: \<open>wf_label_prop_updates ?step
      (S \<union> ((\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) ` set (outpu ?step 1)))\<close>
    by (rule wf_label_prop_updates_label_prop_input0_step_state_output1_shiftI
        [OF input_step0 Cons.prems(2) Cons.prems(3) Cons.prems(4) Cons.prems(5)
          Cons.prems(6) Cons.prems(7)])
  have input_rec: \<open>input ?step 0 = msgs @ rest\<close>
    using input_step0 by simp
  have EN1_rec: \<open>en1 ?step = Inl\<close>
    using Cons.prems(2) by simp
  have DE1_rec: \<open>de1 ?step = projl\<close>
    using Cons.prems(3) by simp
  have INV_rec: \<open>label_prop_upd_inv ?step\<close>
    by (rule label_prop_upd_inv_label_prop_input0_step_stateI
        [OF Cons.prems(4) input_step0 Cons.prems(6)])
  have labels_os: \<open>labels_inv (all_edges os q) (min_label os q)\<close> for q
    using Cons.prems(5) by (rule spec)
  have LABELS_rec: \<open>\<forall>q. labels_inv (all_edges ?step q) (min_label ?step q)\<close>
  proof
    fix q
    show \<open>labels_inv (all_edges ?step q) (min_label ?step q)\<close>
      by (rule labels_inv_label_prop_input0_step_stateI[OF labels_os Cons.prems(4) input_step0])
  qed
  have WF_input1_rec: \<open>wf_label_prop_updates ?step (set (input ?step 1))\<close>
    by (rule wf_label_prop_updates_label_prop_input0_step_stateI
        [OF Cons.prems(4) Cons.prems(6)])
  have rec: \<open>wf_label_prop_updates (fst (label_prop_input0_batched ?step msgs))
      (S \<union> ((\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) `
        set (outpu (fst (label_prop_input0_batched ?step msgs)) 1)))\<close>
    by (rule Cons.hyps[OF input_rec EN1_rec DE1_rec INV_rec LABELS_rec WF_input1_rec step_wf])
  show ?case
    using rec unfolding msg_eq
    by (cases \<open>label_prop_input0_batched ?step msgs\<close>) simp
qed

end
