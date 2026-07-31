theory Input1

imports
  "../../Correctness/Outputs"
  "../../Correctness/Produces"
  "../../Correctness/Progress"
  "../../Correctness/OCapsReorder"
  "../../Correctness/Consumes"
  "../../Correctness/Init"
  "../../Correctness/Timely_Collections"
  Label_Propagation_op_Correctness_Extras
begin

declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del] 
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]
declare if_cong[cong]
declare list_emb_Nil2[simp del] BULK_BENQ_right_empty[simp del] BULK_BENQ_left_empty[simp del]
  filter_True[simp del] filter_False[simp del]
declare cin.rep_eq[simp del]
declare cin.rep_eq[symmetric, simp]

lemma input_label_prop_input1_step_state[simp]:
  \<open>input (label_prop_input1_step_state os d t) = (input os)(1 := tl (input os 1))\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def input_tl_def)

lemma intsum_label_prop_input1_step_state[simp]:
  \<open>intsum (label_prop_input1_step_state os d t) = intsum os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)

lemma consu_label_prop_input1_step_state[simp]:
  \<open>consu (label_prop_input1_step_state os d t) = consu os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)

lemma front_label_prop_input1_step_state[simp]:
  \<open>front (label_prop_input1_step_state os d t) = front os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)

lemma initia_label_prop_input1_step_state[simp]:
  \<open>initia (label_prop_input1_step_state os d t) = initia os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)

lemma en1_label_prop_input1_step_state[simp]:
  \<open>en1 (label_prop_input1_step_state os d t) = en1 os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)

lemma de1_label_prop_input1_step_state[simp]:
  \<open>de1 (label_prop_input1_step_state os d t) = de1 os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)

lemma is_en1_label_prop_input1_step_state[simp]:
  \<open>is_en1 (label_prop_input1_step_state os d t) = is_en1 os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)

lemma en2_label_prop_input1_step_state[simp]:
  \<open>en2 (label_prop_input1_step_state os d t) = en2 os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)

lemma de2_label_prop_input1_step_state[simp]:
  \<open>de2 (label_prop_input1_step_state os d t) = de2 os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)

lemma is_en2_label_prop_input1_step_state[simp]:
  \<open>is_en2 (label_prop_input1_step_state os d t) = is_en2 os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)

lemma outpu_label_prop_input1_step_state[simp]:
  \<open>outpu (label_prop_input1_step_state os d t) =
    (\<lambda>p. outpu os p @ map (\<lambda>(x, cap). (x, time cap))
      (filter (\<lambda>(x, cap). out cap = p) (label_prop_input1_step_batch os d t)))\<close>
  unfolding label_prop_input1_step_state_def label_prop_input1_step_batch_def
  by (simp add: Let_def fun_eq_iff)

lemma produ_label_prop_input1_step_state[simp]:
  \<open>produ (label_prop_input1_step_state os d t) =
    produ os @ map (\<lambda>(x, cap). (out cap, time cap, 1))
      (label_prop_input1_step_batch os d t)\<close>
  unfolding label_prop_input1_step_state_def label_prop_input1_step_batch_def produces_def
  by (simp add: Let_def)

lemma timestamps_label_prop_input1_step_state[simp]:
  \<open>timestamps (label_prop_input1_step_state os d t) = timestamps os\<close>
  unfolding label_prop_input1_step_state_def label_prop_label_record_update_def input_tl_def
  by (simp add: Let_def)

lemma graph_label_prop_input1_step_state[simp]:
  \<open>label_propagation_state.graph (label_prop_input1_step_state os d t) = label_propagation_state.graph os\<close>
  unfolding label_prop_input1_step_state_def label_prop_label_record_update_def input_tl_def
    produces_def drop_caps_def release_caps_def
  by (simp add: Let_def)

lemma vertices_label_prop_input1_step_state[simp]:
  \<open>vertices (label_prop_input1_step_state os d t) = vertices os\<close>
  unfolding label_prop_input1_step_state_def label_prop_label_record_update_def input_tl_def
  by (simp add: Let_def)

lemma all_vertices_label_prop_input1_step_state[simp]:
  \<open>all_vertices (label_prop_input1_step_state os d t) = all_vertices os\<close>
  unfolding all_vertices_def by simp

lemma neighbors_label_prop_input1_step_state[simp]:
  \<open>neighbors (label_prop_input1_step_state os d t) = neighbors os\<close>
  unfolding neighbors_def by (simp add: fun_eq_iff)

lemma all_edges_label_prop_input1_step_state[simp]:
  \<open>all_edges (label_prop_input1_step_state os d t) = all_edges os\<close>
  unfolding all_edges_def by simp

lemma input_fst_label_prop_input1_batched[simp]:
  \<open>input (fst (label_prop_input1_batched os msgs)) =
    (input os)(1 := drop (length msgs) (input os 1))\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta fun_eq_iff drop_Suc)

lemma intsum_fst_label_prop_input1_batched[simp]:
  \<open>intsum (fst (label_prop_input1_batched os msgs)) = intsum os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)

lemma consu_fst_label_prop_input1_batched[simp]:
  \<open>consu (fst (label_prop_input1_batched os msgs)) = consu os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)

lemma front_fst_label_prop_input1_batched[simp]:
  \<open>front (fst (label_prop_input1_batched os msgs)) = front os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)

lemma initia_fst_label_prop_input1_batched[simp]:
  \<open>initia (fst (label_prop_input1_batched os msgs)) = initia os\<close>
proof (induct msgs arbitrary: os)
  case Nil
  show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg: \<open>msg = (d, t)\<close>
    by (cases msg)
  obtain os' batches where rec:
    \<open>label_prop_input1_batched (label_prop_input1_step_state os d t) msgs = (os', batches)\<close>
    by (cases \<open>label_prop_input1_batched (label_prop_input1_step_state os d t) msgs\<close>)
  have \<open>initia os' = initia (label_prop_input1_step_state os d t)\<close>
    using Cons.hyps[of \<open>label_prop_input1_step_state os d t\<close>] rec
    by simp
  then have os': \<open>initia os' = initia os\<close>
    by simp
  show ?case
    unfolding msg
    using rec os'
    by simp
qed

lemma en1_fst_label_prop_input1_batched[simp]:
  \<open>en1 (fst (label_prop_input1_batched os msgs)) = en1 os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)

lemma de1_fst_label_prop_input1_batched[simp]:
  \<open>de1 (fst (label_prop_input1_batched os msgs)) = de1 os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)

lemma is_en1_fst_label_prop_input1_batched[simp]:
  \<open>is_en1 (fst (label_prop_input1_batched os msgs)) = is_en1 os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)

lemma en2_fst_label_prop_input1_batched[simp]:
  \<open>en2 (fst (label_prop_input1_batched os msgs)) = en2 os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)

lemma de2_fst_label_prop_input1_batched[simp]:
  \<open>de2 (fst (label_prop_input1_batched os msgs)) = de2 os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)

lemma is_en2_fst_label_prop_input1_batched[simp]:
  \<open>is_en2 (fst (label_prop_input1_batched os msgs)) = is_en2 os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)

lemma outpu_fst_label_prop_input1_batched[simp]:
  \<open>outpu (fst (label_prop_input1_batched os msgs)) =
    (\<lambda>p. outpu os p @ map (\<lambda>(x, cap). (x, time cap))
      (filter (\<lambda>(x, cap). out cap = p) (snd (label_prop_input1_batched os msgs))))\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta append_assoc fun_eq_iff)

lemma inter_fst_label_prop_input1_batched:
  \<open>inter (fst (label_prop_input1_batched os msgs)) =
    inter (fold (\<lambda>(d, t) os. label_prop_input1_step_state os d t) msgs os)\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta split: prod.splits)

lemma ocaps_fst_label_prop_input1_batched:
  \<open>ocaps (fst (label_prop_input1_batched os msgs)) =
    ocaps (fold (\<lambda>(d, t) os. label_prop_input1_step_state os d t) msgs os)\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta split: prod.splits)

lemma produ_fst_label_prop_input1_batched[simp]:
  \<open>produ (fst (label_prop_input1_batched os msgs)) =
    produ os @ map (\<lambda>(x, cap). (out cap, time cap, 1))
      (snd (label_prop_input1_batched os msgs))\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta append_assoc)

lemma label_propagation_op_logic_input1I[intro]:
  assumes \<open>input os 1 = (d, t) # xs\<close>
    and \<open>de1 os d = (v, l)\<close>
    and \<open>t1 = myfst t\<close>
    and \<open>os' = input_tl os 1\<close>
    and \<open>l' = min (min_label os t1 v) l\<close>
    and \<open>os'' = label_prop_label_record_update os' t1 v l'\<close>
    and \<open>batch = label_prop_label_batch os os'' t1 v l' t\<close>
    and \<open>os_next = release_caps (drop_caps (produces (add_caps os'' (map snd batch)) batch) (map snd batch)) 1\<close>
  shows \<open>os_next |\<in>| label_propagation_op_logic os\<close>
  using assms unfolding label_propagation_op_logic_def by auto

lemma step_label_propagation_op_input1[intro]:
  assumes \<open>input os 1 = (d, t) # xs\<close>
    and \<open>de1 os d = (v, l)\<close>
    and \<open>t1 = myfst t\<close>
    and \<open>os' = input_tl os 1\<close>
    and \<open>l' = min (min_label os t1 v) l\<close>
    and \<open>os'' = label_prop_label_record_update os' t1 v l'\<close>
    and \<open>batch = label_prop_label_batch os os'' t1 v l' t\<close>
    and \<open>os_next = release_caps (drop_caps (produces (add_caps os'' (map snd batch)) batch) (map snd batch)) 1\<close>
    and \<open>initia os\<close>
    and \<open>op = label_propagation_op os_next\<close>
  shows \<open>step Tau (label_propagation_op os) op\<close>
  using assms by auto

lemma step_label_propagation_op_input1_step_state[intro]:
  assumes inp: \<open>input os 1 = (d, t) # xs\<close>
    and ini: \<open>initia os\<close>
    and op_eq: \<open>op = label_propagation_op (label_prop_input1_step_state os d t)\<close>
  shows \<open>step Tau (label_propagation_op os) op\<close>
proof -
  let ?v = \<open>fst (de1 os d)\<close>
  let ?l = \<open>snd (de1 os d)\<close>
  let ?t1 = \<open>myfst t\<close>
  let ?l' = \<open>min (min_label os ?t1 ?v) ?l\<close>
  let ?os'' = \<open>label_prop_label_record_update (input_tl os 1) ?t1 ?v ?l'\<close>
  let ?batch = \<open>label_prop_label_batch os ?os'' ?t1 ?v ?l' t\<close>
  have vl_eq: \<open>de1 os d = (?v, ?l)\<close> by simp
  have state_eq:
    \<open>label_prop_input1_step_state os d t =
       release_caps (drop_caps (produces (add_caps ?os'' (map snd ?batch)) ?batch)
                                (map snd ?batch)) 1\<close>
    unfolding label_prop_input1_step_state_def Let_def by simp
  show ?thesis
    using op_eq[unfolded state_eq]
    by (rule step_label_propagation_op_input1
            [OF inp vl_eq refl refl refl refl refl refl ini])
qed

lemma step_compower_label_propagation_op_input1[intro]:
  assumes \<open>input os 1 = msgs @ ys\<close>
    and \<open>n = length msgs\<close>
    and \<open>os_next |\<in>| ((\<lambda>oss. cUnion (cimage label_propagation_op_logic
      (cfilter (\<lambda>os. initia os \<and> (\<exists>p. ocaps os p \<noteq> [])) oss))) ^^ n) {|os|}\<close>
    and \<open>op = label_propagation_op os_next\<close>
  shows \<open>(step Tau ^^ n) (label_propagation_op os) op\<close>
  using assms by auto

lemma step_compower_label_propagation_op_input1_eq[intro]:
  assumes \<open>input os 1 = msgs @ ys\<close>
    and   \<open>n = length msgs\<close>
    and   \<open>(os_next, batch) = label_prop_input1_batched os msgs\<close>
    and   \<open>initia os\<close>
    and   \<open>op = label_propagation_op os_next\<close>
  shows \<open>(step Tau ^^ n) (label_propagation_op os) op\<close>
proof -
  have \<open>(step Tau ^^ length msgs) (label_propagation_op os) (label_propagation_op os_next)\<close>
    using assms(1,3,4)
  proof (induct msgs arbitrary: os ys os_next batch)
    case Nil
    then show ?case by auto
  next
    case (Cons m msgs')
    obtain d t where m_def: \<open>m = (d, t)\<close> by (cases m)
    let ?os_step = \<open>label_prop_input1_step_state os d t\<close>
    from Cons.prems(1) m_def have inp: \<open>input os 1 = (d, t) # msgs' @ ys\<close> by simp
    have step1: \<open>step Tau (label_propagation_op os) (label_propagation_op ?os_step)\<close>
      by (rule step_label_propagation_op_input1_step_state[OF inp Cons.prems(3) refl])
    have inp_step: \<open>input ?os_step 1 = msgs' @ ys\<close>
      using inp by simp
    have initia_step: \<open>initia ?os_step\<close>
      using Cons.prems(3) by simp
    show ?case
    proof (cases \<open>label_prop_input1_batched ?os_step msgs'\<close>)
      case (Pair os_final batches)
      from Cons.prems(2) m_def Pair have os_next_eq: \<open>os_next = os_final\<close>
        by (auto split: prod.splits)
      have ih: \<open>(step Tau ^^ length msgs') (label_propagation_op ?os_step) (label_propagation_op os_final)\<close>
        using Cons.hyps[of ?os_step ys os_final batches] inp_step Pair[symmetric] initia_step
        by simp
      from relpowp_Suc_I2[OF step1 ih]
      have \<open>(step Tau ^^ Suc (length msgs')) (label_propagation_op os) (label_propagation_op os_final)\<close> .
      then show ?thesis using os_next_eq m_def by simp
    qed
  qed
  with assms(2,5) show ?thesis by simp
qed

lemma step_compower_label_propagation_op_input1_eq_alt[intro]:
  assumes \<open>input os 1 = msgs @ ys\<close>
    and   \<open>n = length msgs\<close>
    and   \<open>initia os\<close>
    and   \<open>op = label_propagation_op (fst (label_prop_input1_batched os msgs))\<close>
  shows \<open>(step Tau ^^ n) (label_propagation_op os) op\<close>
  apply (rule  step_compower_label_propagation_op_input1_eq[OF assms(1) assms(2) _ assms(3) assms(4)])
  apply (rule prod.collapse)
  done


no_notation shiftr (infixl \<open>>>\<close> 55)
no_syntax (ASCII) "_thenM" :: \<open>['a, 'b] \<Rightarrow> 'c\<close>  (infixl \<open>>>\<close> 54)

(* label_prop_label_record_update only modifies the label field; input, intsum,
   and ocaps are untouched, so input_ocaps_inv transfers trivially. *)

lemma input_ocaps_inv_label_prop_label_record_updateI:
  assumes inv: "input_ocaps_inv os"
  shows "input_ocaps_inv (label_prop_label_record_update os event_t vertex assigned_label)"
  using inv unfolding input_ocaps_inv_def label_prop_label_record_update_def by simp




subsection \<open>Moving pending data through the loop\<close>


definition label_prop_input1_loop_updates where
  \<open>label_prop_input1_loop_updates cbufs os_label_prop os =
    (let
      cbufs' = cbufs((2, 1) := [], (1, 1) := []);
      os_label_prop_consumed =
        CONSUMES 1
          (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
          (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>);
      os_label_prop' =
        fst (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1));
      os2' =
        drop_caps
          (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2))
            (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
          (map (\<lambda>t. Cap t 1)
            (ocaps (os 2) 1 @
              map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
                (cbufs (2, 1) @ outpu os_label_prop 1)))
          \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>;
      os' = os(2 := os2')
     in (cbufs', os_label_prop', os'))\<close>


lemma label_prop_input1_loop_updates_cbufs_11:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>cbufs' (1, 1) = []\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_cbufs_21:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>cbufs' (2, 1) = []\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_input_label_1:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>input os_label_prop' 1 = []\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_input_label_0:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>input os_label_prop' 0 = input os_label_prop 0\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_input_os2_1:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>input (os' 2) 1 = []\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_outpu_os2_1:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>outpu (os' 2) 1 = []\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_initia_label:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>initia os_label_prop' = initia os_label_prop\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_front_label:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>front os_label_prop' = front os_label_prop\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_initia_os2:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>initia (os 2) = initia (os' 2)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_front_os2:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>front (os 2) = front (os' 2)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_intsum_os2:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>intsum (os 2) = intsum (os' 2)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_intsum_label:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>intsum os_label_prop = intsum os_label_prop'\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_en1_label:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>en1 os_label_prop = en1 os_label_prop'\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_en2_label:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>en2 os_label_prop = en2 os_label_prop'\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_de1_label:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>de1 os_label_prop = de1 os_label_prop'\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_de2_label:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>de2 os_label_prop = de2 os_label_prop'\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_en1_os2:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>en1 (os 2) = en1 (os' 2)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_en2_os2:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>en2 (os 2) = en2 (os' 2)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_de1_os2:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>de1 (os 2) = de1 (os' 2)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_de2_os2:
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>de2 (os 2) = de2 (os' 2)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def fold_consumes
  by (auto split: prod.splits)


section \<open>Label-propagation input-1 batch facts\<close>

subsection \<open>Frame facts for input-1 batches\<close>





lemma timestamps_fst_label_prop_input1_batched[simp]:
  \<open>timestamps (fst (label_prop_input1_batched os msgs)) = timestamps os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)


lemma all_edges_fst_label_prop_input1_batched[simp]:
  \<open>all_edges (fst (label_prop_input1_batched os msgs)) = all_edges os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)


subsection \<open>Batch member and non-empty destructors\<close>




lemma label_prop_neighbor_batch_nonemptyD:
  fixes old_os neighbor_os label_os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_neighbor_batch old_os neighbor_os label_os relevant_times vertex new_label event_time \<noteq> []\<close>
  obtains cur_t v' where
    \<open>cur_t \<in> set relevant_times\<close>
    \<open>v' \<in> set (neighbors neighbor_os cur_t vertex)\<close>
    \<open>new_label < min_label old_os cur_t vertex\<close>
    \<open>new_label < min_label label_os cur_t v'\<close>
proof -
  let ?batch_at = \<open>\<lambda>cur_t.
    if min_label old_os cur_t vertex > new_label
    then map (\<lambda>v'. (en1 old_os (v', new_label), Cap (MyPair cur_t (mysnd event_time)) 1))
      (filter (\<lambda>v'. min_label label_os cur_t v' > new_label)
        (neighbors neighbor_os cur_t vertex))
    else []\<close>
  have \<open>\<exists>cur_t\<in>set relevant_times. ?batch_at cur_t \<noteq> []\<close>
    using assms unfolding label_prop_neighbor_batch_def Let_def
    by (auto simp: concat_eq_Nil_conv)
  then obtain cur_t where cur_t_in: \<open>cur_t \<in> set relevant_times\<close>
    and batch_at_nonempty: \<open>?batch_at cur_t \<noteq> []\<close>
    by auto

  then have old_guard: \<open>new_label < min_label old_os cur_t vertex\<close>
    by (auto split: if_splits)
  have filter_nonempty:
    \<open>filter (\<lambda>v'. new_label < min_label label_os cur_t v')
      (neighbors neighbor_os cur_t vertex) \<noteq> []\<close>
    using batch_at_nonempty old_guard by simp
  then obtain v' where filt_in:
    \<open>v' \<in> set (filter (\<lambda>v'. new_label < min_label label_os cur_t v')
      (neighbors neighbor_os cur_t vertex))\<close>
    by (cases \<open>filter (\<lambda>v'. new_label < min_label label_os cur_t v')
      (neighbors neighbor_os cur_t vertex)\<close>) auto
  then have v'_in: \<open>v' \<in> set (neighbors neighbor_os cur_t vertex)\<close>
    and label_guard: \<open>new_label < min_label label_os cur_t v'\<close>
    by auto
  show ?thesis
    using that[OF cur_t_in v'_in old_guard label_guard] .
qed






lemma label_prop_label_batch_nonemptyD:
  fixes old_os updated_os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_label_batch old_os updated_os event_t vertex new_label event_time \<noteq> []\<close>
  obtains cur_t v' where
    \<open>cur_t \<in> set (timestamps old_os)\<close>
    \<open>event_t \<le> cur_t\<close>
    \<open>v' \<in> set (neighbors old_os cur_t vertex)\<close>
    \<open>new_label < min_label old_os cur_t vertex\<close>
    \<open>new_label < min_label updated_os cur_t v'\<close>
proof -
  obtain cur_t v' where cur_t_in: \<open>cur_t \<in> set (filter ((\<le>) event_t) (timestamps old_os))\<close>
    and v'_in: \<open>v' \<in> set (neighbors old_os cur_t vertex)\<close>
    and old_guard: \<open>new_label < min_label old_os cur_t vertex\<close>
    and updated_guard: \<open>new_label < min_label updated_os cur_t v'\<close>
    using assms unfolding label_prop_label_batch_def
    by (elim label_prop_neighbor_batch_nonemptyD)
  have cur_t_ts: \<open>cur_t \<in> set (timestamps old_os)\<close>
    and event_le: \<open>event_t \<le> cur_t\<close>
    using cur_t_in by auto
  show ?thesis
    using that[OF cur_t_ts event_le v'_in old_guard updated_guard] .
qed


lemma label_prop_neighbor_batch_memberD:
  fixes old_os neighbor_os label_os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(x, cap) \<in> set (label_prop_neighbor_batch old_os neighbor_os label_os
    relevant_times vertex new_label event_time)\<close>
  obtains cur_t where
    \<open>cur_t \<in> set relevant_times\<close>
    \<open>cap = Cap (MyPair cur_t (mysnd event_time)) 1\<close>
  using assms unfolding label_prop_neighbor_batch_def
  by (auto simp: Let_def split: if_splits)


lemma label_prop_label_batch_memberD:
  fixes old_os updated_os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(x, cap) \<in> set (label_prop_label_batch old_os updated_os event_t vertex new_label event_time)\<close>
  obtains cur_t where
    \<open>cur_t \<in> set (timestamps old_os)\<close>
    \<open>event_t \<le> cur_t\<close>
    \<open>cap = Cap (MyPair cur_t (mysnd event_time)) 1\<close>
proof -
  obtain cur_t where cur_t_in: \<open>cur_t \<in> set (filter ((\<le>) event_t) (timestamps old_os))\<close>
    and cap_eq: \<open>cap = Cap (MyPair cur_t (mysnd event_time)) 1\<close>
    using assms unfolding label_prop_label_batch_def
    by (elim label_prop_neighbor_batch_memberD)
  show ?thesis
    using that cur_t_in cap_eq by auto
qed


lemma label_prop_input1_step_batch_memberD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(x, cap) \<in> set (label_prop_input1_step_batch os d t)\<close>
  obtains cur_t where
    \<open>cur_t \<in> set (timestamps os)\<close>
    \<open>myfst t \<le> cur_t\<close>
    \<open>cap = Cap (MyPair cur_t (mysnd t)) 1\<close>
proof -
  obtain cur_t where cur_t_in: \<open>cur_t \<in> set (timestamps os)\<close>
    and time_le: \<open>myfst t \<le> cur_t\<close>
    and cap_eq: \<open>cap = Cap (MyPair cur_t (mysnd t)) 1\<close>
    using assms unfolding label_prop_input1_step_batch_def Let_def
    by (elim label_prop_label_batch_memberD)
  show ?thesis
    using that[OF cur_t_in time_le cap_eq] .
qed


lemma label_prop_input1_step_batch_member_payloadD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os d t)\<close>
  obtains v l l' cur_t v' where
    \<open>de1 os d = (v, l)\<close>
    \<open>l' = min (min_label os (myfst t) v) l\<close>
    \<open>cur_t \<in> set (timestamps os)\<close>
    \<open>myfst t \<le> cur_t\<close>
    \<open>v' \<in> set (neighbors os cur_t v)\<close>
    \<open>x = en1 os (v', l')\<close>
    \<open>cap = Cap (MyPair cur_t (mysnd t)) 1\<close>
proof -
  obtain v l where de1_eq: \<open>de1 os d = (v, l)\<close>
    by (cases \<open>de1 os d\<close>)
  show ?thesis
    using member that[of v l \<open>min (min_label os (myfst t) v) l\<close>] de1_eq
    unfolding label_prop_input1_step_batch_def label_prop_label_batch_def
      label_prop_neighbor_batch_def Let_def
    by (auto split: if_splits)
qed



lemma label_prop_input1_step_batch_unfold:
  \<open>label_prop_input1_step_batch os d t =
    label_prop_label_batch os
      (label_prop_label_record_update (input_tl os 1) (myfst t) (fst (de1 os d))
        (min (min_label os (myfst t) (fst (de1 os d))) (snd (de1 os d))))
      (myfst t) (fst (de1 os d)) (min (min_label os (myfst t) (fst (de1 os d))) (snd (de1 os d))) t\<close>
  unfolding label_prop_input1_step_batch_def Let_def by simp


lemma label_prop_input1_step_batch_nonempty_unfoldD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_input1_step_batch os d t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
  shows \<open>label_prop_label_batch os
    (label_prop_label_record_update (input_tl os 1) (myfst t) (fst (de1 os d))
      (min (min_label os (myfst t) (fst (de1 os d))) (snd (de1 os d))))
    (myfst t) (fst (de1 os d)) (min (min_label os (myfst t) (fst (de1 os d))) (snd (de1 os d))) t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
  using assms[unfolded label_prop_input1_step_batch_unfold] by assumption


lemma label_prop_input1_step_batch_nonemptyD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_input1_step_batch os d t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
  obtains v l l' cur_t v' where
    \<open>de1 os d = (v, l)\<close>
    \<open>cur_t \<in> set (timestamps os)\<close>
    \<open>myfst t \<le> cur_t\<close>
    \<open>v' \<in> set (neighbors os cur_t v)\<close>
    \<open>l' = min (min_label os (myfst t) v) l\<close>
    \<open>l' < min_label os cur_t v\<close>
    \<open>l' < min_label
      (label_prop_label_record_update (input_tl os 1) (myfst t) v l')
      cur_t v'\<close>
proof -
  let ?v = \<open>fst (de1 os d)\<close>
  let ?l = \<open>snd (de1 os d)\<close>
  let ?l' = \<open>min (min_label os (myfst t) ?v) ?l\<close>
  let ?updated = \<open>label_prop_label_record_update (input_tl os 1) (myfst t) ?v ?l'\<close>
  have de1_eq: \<open>de1 os d = (?v, ?l)\<close>
    by simp
  have batch_nonempty:
    \<open>label_prop_label_batch os ?updated (myfst t) ?v ?l' t \<noteq> ([] :: ('d \<times> (2, (nat, nat) myprod) capability) list)\<close>
    by (rule label_prop_input1_step_batch_nonempty_unfoldD[OF assms])


  show ?thesis
  proof (rule label_prop_label_batch_nonemptyD[OF batch_nonempty])
    fix cur_t v'
    assume cur_t_in: \<open>cur_t \<in> set (timestamps os)\<close>
      and time_le: \<open>myfst t \<le> cur_t\<close>
      and v'_in: \<open>v' \<in> set (neighbors os cur_t ?v)\<close>
      and old_guard: \<open>?l' < min_label os cur_t ?v\<close>
      and updated_guard: \<open>?l' < min_label ?updated cur_t v'\<close>
    show thesis
      using that[OF de1_eq cur_t_in time_le v'_in refl old_guard updated_guard] .
  qed
qed




lemma label_prop_input1_step_batch_nonempty_strict_updateD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_input1_step_batch os d t \<noteq> []\<close>
    and ts_t: \<open>myfst t \<in> set (timestamps os)\<close>
  obtains v l l' where
    \<open>de1 os d = (v, l)\<close>
    \<open>l' = min (min_label os (myfst t) v) l\<close>
    \<open>l' < min_label os (myfst t) v\<close>
    \<open>min_label
      (label_prop_label_record_update (input_tl os 1) (myfst t) v l')
      (myfst t) v < min_label os (myfst t) v\<close>
proof -
  obtain v l l' cur_t v' where de1_eq: \<open>de1 os d = (v, l)\<close>
    and cur_t_in: \<open>cur_t \<in> set (timestamps os)\<close>
    and time_le: \<open>myfst t \<le> cur_t\<close>
    and v'_in: \<open>v' \<in> set (neighbors os cur_t v)\<close>
    and l': \<open>l' = min (min_label os (myfst t) v) l\<close>
    and strict_cur: \<open>l' < min_label os cur_t v\<close>
    using label_prop_input1_step_batch_nonemptyD[OF assms(1)] by metis
  have mono: \<open>min_label os cur_t v \<le> min_label os (myfst t) v\<close>
    using min_label_mono_time[OF ts_t time_le] .
  have strict_myfst: \<open>l' < min_label os (myfst t) v\<close>
    using strict_cur mono by linarith
  let ?updated = \<open>label_prop_label_record_update (input_tl os 1) (myfst t) v l'\<close>
  have label_eq: \<open>label ?updated = (label os)(myfst t := (label os (myfst t))(v := l'))\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  have ts_eq: \<open>timestamps ?updated = timestamps os\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  have l_in_set: \<open>l' \<in> insert (label ?updated (myfst t) v)
      ((\<lambda>t'. label ?updated t' v) ` {t' \<in> set (timestamps ?updated). t' \<le> myfst t})\<close>
    using label_eq by simp
  have min_le_l: \<open>min_label ?updated (myfst t) v \<le> l'\<close>
    using l_in_set unfolding min_label_def by (intro Min_le) auto
  have strict_update: \<open>min_label ?updated (myfst t) v < min_label os (myfst t) v\<close>
    using min_le_l strict_myfst by linarith
  show ?thesis
    using that[OF de1_eq l' strict_myfst strict_update] .
qed



lemma fst_label_prop_input1_batched_Cons_prefix:
  \<open>fst (label_prop_input1_batched os ((d, t) # pre)) =
    fst (label_prop_input1_batched (label_prop_input1_step_state os d t) pre)\<close>
  by (cases \<open>label_prop_input1_batched (label_prop_input1_step_state os d t) pre\<close>) simp


lemma label_prop_input1_batched_batch_memberD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
  obtains pre d t post os_pre where
    \<open>msgs = pre @ (d, t) # post\<close>
    \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre d t)\<close>
  using assms
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  show ?case
  proof (cases \<open>(x, cap) \<in> set (label_prop_input1_step_batch os d t)\<close>)
    case True
    show ?thesis
      by (rule Cons.prems(1)[of Nil d t msgs os]) (simp_all add: msg_eq True)
  next
    case False
    have tail_member:
      \<open>(x, cap) \<in> set (snd (label_prop_input1_batched (label_prop_input1_step_state os d t) msgs))\<close>
      using Cons.prems(2) False unfolding msg_eq
      by (cases \<open>label_prop_input1_batched (label_prop_input1_step_state os d t) msgs\<close>) simp
    show ?thesis
    proof (rule Cons.hyps[OF _ tail_member])
      fix pre da ta post os_pre
      assume msgs_tail: \<open>msgs = pre @ (da, ta) # post\<close>
        and os_pre_eq: \<open>os_pre = fst (label_prop_input1_batched (label_prop_input1_step_state os d t) pre)\<close>
        and member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre da ta)\<close>
      have msgs_eq: \<open>msg # msgs = (d, t) # pre @ (da, ta) # post\<close>
        using msgs_tail msg_eq by simp
      have os_pre_eq': \<open>os_pre = fst (label_prop_input1_batched os ((d, t) # pre))\<close>
        using os_pre_eq fst_label_prop_input1_batched_Cons_prefix[of os d t pre] by simp
      show thesis
      proof (rule Cons.prems(1)[of \<open>(d, t) # pre\<close> da ta post os_pre])
        show \<open>msg # msgs = ((d, t) # pre) @ (da, ta) # post\<close>
          using msgs_tail msg_eq by simp

        show \<open>os_pre = fst (label_prop_input1_batched os ((d, t) # pre))\<close>
          using os_pre_eq' .
        show \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre da ta)\<close>
          using member .
      qed


    qed
  qed
qed



lemma label_prop_input1_batched_produced_memberD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>(p, pt, n) \<in> set (map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
    (snd (label_prop_input1_batched os msgs)))\<close>
  obtains
    \<open>p = 1\<close>
    \<open>n = 1\<close>
    \<open>myfst pt \<in> set (timestamps os)\<close>
    \<open>MyPair (myfst pt) 0 \<le> pt\<close>
proof -
  obtain x cap where batch_member: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    and triple_eq: \<open>(p, pt, n) = (case cap of Cap t p \<Rightarrow> (p, t, 1))\<close>
    using assms by auto
  obtain pre d t post os_pre where os_pre_eq:
    \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    and step_member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre d t)\<close>
    using batch_member by (elim label_prop_input1_batched_batch_memberD)
  obtain cur_t where cur_t_pre: \<open>cur_t \<in> set (timestamps os_pre)\<close>
    and cap_eq: \<open>cap = Cap (MyPair cur_t (mysnd t)) 1\<close>
    using step_member by (elim label_prop_input1_step_batch_memberD)
  have cur_t: \<open>cur_t \<in> set (timestamps os)\<close>
    using cur_t_pre os_pre_eq by simp
  have fields: \<open>p = 1\<close> \<open>n = 1\<close> \<open>pt = MyPair cur_t (mysnd t)\<close>
    using triple_eq cap_eq by simp_all
  have pt_ts: \<open>myfst pt \<in> set (timestamps os)\<close>
    using fields cur_t by simp
  have pt_ge: \<open>MyPair (myfst pt) 0 \<le> pt\<close>
    using fields by simp
  show ?thesis
    using that[OF fields(1) fields(2) pt_ts pt_ge] .
qed




lemma outpu_fst_label_prop_input1_batched_eq:
  \<open>outpu (fst (label_prop_input1_batched os msgs)) p =
    outpu os p @ map (\<lambda>(x, cap). (x, capability.time cap))
      (filter (\<lambda>(x, cap). out cap = p) (snd (label_prop_input1_batched os msgs)))\<close>
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  let ?step = \<open>label_prop_input1_step_state os d t\<close>
  have step_out: \<open>outpu ?step p = outpu os p @
      map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = p) (label_prop_input1_step_batch os d t))\<close>
    unfolding label_prop_input1_step_state_def label_prop_input1_step_batch_def
    by (simp add: Let_def split: capability.splits)
  obtain os_final batches where tail:
    \<open>label_prop_input1_batched ?step msgs = (os_final, batches)\<close>
    by (cases \<open>label_prop_input1_batched ?step msgs\<close>) auto
  have tail_out: \<open>outpu os_final p = outpu ?step p @
      map (\<lambda>(x, cap). (x, capability.time cap)) (filter (\<lambda>(x, cap). out cap = p) batches)\<close>
    using Cons.hyps[of ?step] tail by simp
  show ?case
    using msg_eq tail step_out tail_out
    by (simp add: append_assoc)
qed


lemma filter_label_prop_input1_step_batch_out_neq[simp]:
  assumes \<open>p \<noteq> (1 :: 2)\<close>
  shows \<open>filter (\<lambda>(x, cap). out cap = p) (label_prop_input1_step_batch os d t) = []\<close>
  using assms
  by (auto simp add: filter_empty_conv elim!: label_prop_input1_step_batch_memberD)


lemma filter_snd_label_prop_input1_batched_out_neq[simp]:
  assumes \<open>p \<noteq> (1 :: 2)\<close>
  shows \<open>filter (\<lambda>(x, cap). out cap = p) (snd (label_prop_input1_batched os msgs)) = []\<close>
  using assms
  by (auto simp add: filter_empty_conv elim!: label_prop_input1_batched_batch_memberD label_prop_input1_step_batch_memberD)


lemma outpu_0_fst_snd_label_prop_input1_loop_updates[simp]:
  \<open>outpu (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) (0 :: 2) =
    outpu os_label_prop 0\<close>
  unfolding label_prop_input1_loop_updates_def Let_def
  by (simp add: fold_consumes)


lemma outpu_fst_label_prop_input1_batched_nonemptyD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>outpu os 1 = []\<close>
    and \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
  obtains x cap where
    \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    \<open>out cap = (1 :: 2)\<close>
proof -
  have filter_nonempty:
    \<open>filter (\<lambda>(x, cap). out cap = (1 :: 2)) (snd (label_prop_input1_batched os msgs)) \<noteq> []\<close>
    using assms by auto
  then obtain pair where pair_in:
    \<open>pair \<in> set (filter (\<lambda>(x, cap). out cap = (1 :: 2))
      (snd (label_prop_input1_batched os msgs)))\<close>
    by (cases \<open>filter (\<lambda>(x, cap). out cap = (1 :: 2))
      (snd (label_prop_input1_batched os msgs))\<close>) auto
  obtain x cap where pair: \<open>pair = (x, cap)\<close>
    by (cases pair)
  have batch_in: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    and cap_out: \<open>out cap = (1 :: 2)\<close>
    using pair_in unfolding pair by auto
  show ?thesis
    using that[OF batch_in cap_out] .
qed




lemma label_prop_input1_batched_outpu_nonempty_strict_updateD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>outpu os 1 = []\<close>
    and \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  obtains pre d t post os_pre v l l' where
    \<open>msgs = pre @ (d, t) # post\<close>
    \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    \<open>de1 os_pre d = (v, l)\<close>
    \<open>myfst t \<in> set (timestamps os)\<close>
    \<open>l' = min (min_label os_pre (myfst t) v) l\<close>
    \<open>l' < min_label os_pre (myfst t) v\<close>
    \<open>min_label
      (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l')
      (myfst t) v < min_label os_pre (myfst t) v\<close>
proof -
  obtain x cap where batch_member: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    and cap_out: \<open>out cap = (1 :: 2)\<close>
    using assms(1,2) by (elim outpu_fst_label_prop_input1_batched_nonemptyD)
  obtain pre d t post os_pre where msgs_eq: \<open>msgs = pre @ (d, t) # post\<close>
    and os_pre_eq: \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    and step_batch_member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre d t)\<close>
    using batch_member by (elim label_prop_input1_batched_batch_memberD)
  have step_batch_nonempty: \<open>label_prop_input1_step_batch os_pre d t \<noteq> []\<close>
    using step_batch_member by auto
  have dt_in_msgs: \<open>(d, t) \<in> set msgs\<close>
    using msgs_eq by simp
  have dt_in_input: \<open>(d, t) \<in> set (input os 1)\<close>
    using dt_in_msgs msgs_input by auto
  have ts_t_os: \<open>myfst t \<in> set (timestamps os)\<close>
    using dt_in_input wf_upd unfolding wf_label_prop_updates_def by fast
  have ts_t_pre: \<open>myfst t \<in> set (timestamps os_pre)\<close>
    using ts_t_os os_pre_eq by simp
  obtain v l l' where de1_eq: \<open>de1 os_pre d = (v, l)\<close>
    and l': \<open>l' = min (min_label os_pre (myfst t) v) l\<close>
    and strict: \<open>l' < min_label os_pre (myfst t) v\<close>
    and update_strict:
    \<open>min_label (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l')
        (myfst t) v < min_label os_pre (myfst t) v\<close>
    using step_batch_nonempty ts_t_pre
    by (elim label_prop_input1_step_batch_nonempty_strict_updateD)
  show ?thesis
    using that[OF msgs_eq os_pre_eq de1_eq ts_t_os l' strict update_strict] .
qed


subsection \<open>Label minima and invariant preservation\<close>


lemma min_label_label_prop_label_record_update_le:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes l_le: \<open>l \<le> min_label os t v\<close>
  shows \<open>min_label (label_prop_label_record_update (input_tl os 1) t v l) q x \<le> min_label os q x\<close>
proof -
  let ?os' = \<open>label_prop_label_record_update (input_tl os 1) t v l\<close>
  have ts_eq: \<open>timestamps ?os' = timestamps os\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  have label_eq: \<open>label ?os' = (label os)(t := (label os t)(v := l))\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  show ?thesis
  proof (cases \<open>x = v\<close>)
    case False
    have \<open>\<And>t'. label ?os' t' x = label os t' x\<close>
      using False label_eq by (auto simp: fun_upd_def)
    then show ?thesis
      unfolding min_label_def using ts_eq by simp
  next
    case True
    have l_le_label_t: \<open>l \<le> label os t v\<close>
    proof -
      have \<open>min_label os t v \<le> label os t v\<close>
        unfolding min_label_def by (intro Min_le) auto
      then show ?thesis using l_le by simp
    qed
    let ?S = \<open>insert (label os q v) ((\<lambda>t'. label os t' v) ` {t' \<in> set (timestamps os). t' \<le> q})\<close>
    let ?S' = \<open>insert (label ?os' q v) ((\<lambda>t'. label ?os' t' v) ` {t' \<in> set (timestamps ?os'). t' \<le> q})\<close>
    have S'_eq: \<open>?S' = insert (label ?os' q v) ((\<lambda>t'. label ?os' t' v) ` {t' \<in> set (timestamps os). t' \<le> q})\<close>
      using ts_eq by simp
    have fin_S: \<open>finite ?S\<close> by auto
    have fin_S': \<open>finite ?S'\<close> by auto
    have ne_S: \<open>?S \<noteq> {}\<close> by auto
    have bound: \<open>Min ?S' \<le> Min ?S\<close>
    proof (rule Min.boundedI[OF fin_S ne_S])
      fix y assume y_in: \<open>y \<in> ?S\<close>
      then consider (q_lbl) \<open>y = label os q v\<close>
        | (t_lbl) t' where \<open>t' \<in> set (timestamps os)\<close> \<open>t' \<le> q\<close> \<open>y = label os t' v\<close>
        by blast
      then show \<open>Min ?S' \<le> y\<close>
      proof cases
        case q_lbl
        show ?thesis
        proof (cases \<open>q = t\<close>)
          case True
          have \<open>label ?os' q v = l\<close> using True label_eq by simp
          then have \<open>l \<in> ?S'\<close> by auto
          then have \<open>Min ?S' \<le> l\<close> using fin_S' by (intro Min_le) auto
          also have \<open>l \<le> y\<close> using l_le_label_t q_lbl True by simp
          finally show ?thesis .
        next
          case False
          have \<open>label ?os' q v = label os q v\<close>
            using False label_eq by simp
          then have \<open>y \<in> ?S'\<close> using q_lbl by auto
          then show ?thesis using fin_S' by (intro Min_le) auto
        qed
      next
        case (t_lbl t')
        show ?thesis
        proof (cases \<open>t' = t\<close>)
          case True
          have lbl_t: \<open>label ?os' t v = l\<close> using label_eq by simp
          have t_mem: \<open>t \<in> {t'' \<in> set (timestamps ?os'). t'' \<le> q}\<close>
            using ts_eq t_lbl(1,2) True by simp
          have \<open>l \<in> ?S'\<close>
            using lbl_t t_mem image_eqI[where x=t and f=\<open>\<lambda>t'. label ?os' t' v\<close>] by auto
          then have \<open>Min ?S' \<le> l\<close> using fin_S' by (intro Min_le) auto
          also have \<open>l \<le> y\<close> using l_le_label_t t_lbl(3) True by simp
          finally show ?thesis .
        next
          case False
          have lbl_eq: \<open>label ?os' t' v = label os t' v\<close>
            using False label_eq by (simp add: fun_upd_def)
          have t'_mem: \<open>t' \<in> {t'' \<in> set (timestamps ?os'). t'' \<le> q}\<close>
            using ts_eq t_lbl(1,2) by simp
          have \<open>y \<in> ?S'\<close>
            using lbl_eq t'_mem t_lbl(3) image_eqI[where x=t' and f=\<open>\<lambda>t''. label ?os' t'' v\<close>] by auto
          then show ?thesis using fin_S' by (intro Min_le) auto
        qed
      qed
    qed
    have \<open>min_label ?os' q v = Min ?S'\<close>
      unfolding min_label_def by simp
    moreover have \<open>min_label os q v = Min ?S\<close>
      unfolding min_label_def by simp
    ultimately show ?thesis using bound True by simp
  qed
qed


lemma min_label_label_prop_input1_step_state_le:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  shows \<open>min_label (label_prop_input1_step_state os d t) q x \<le> min_label os q x\<close>
proof -
  let ?v = \<open>fst (de1 os d)\<close>
  let ?l = \<open>snd (de1 os d)\<close>
  let ?t1 = \<open>myfst t\<close>
  let ?new = \<open>min (min_label os ?t1 ?v) ?l\<close>
  let ?os'' = \<open>label_prop_label_record_update (input_tl os 1) ?t1 ?v ?new\<close>
  let ?batch = \<open>label_prop_label_batch os ?os'' ?t1 ?v ?new t\<close>
  have step_eq:
    \<open>label_prop_input1_step_state os d t =
       release_caps (drop_caps (produces (add_caps ?os'' (map snd ?batch)) ?batch) (map snd ?batch)) 1\<close>
    unfolding label_prop_input1_step_state_def Let_def by simp
  have new_le: \<open>?new \<le> min_label os ?t1 ?v\<close>
    by simp
  have \<open>min_label (label_prop_input1_step_state os d t) q x = min_label ?os'' q x\<close>
    unfolding step_eq by simp
  also have \<open>\<dots> \<le> min_label os q x\<close>
    using min_label_label_prop_label_record_update_le[OF new_le] .
  finally show ?thesis .
qed


lemma min_label_fst_label_prop_input1_batched_le:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  shows \<open>min_label (fst (label_prop_input1_batched os msgs)) q x \<le> min_label os q x\<close>
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons a ms)
  obtain d t where a_eq: \<open>a = (d, t)\<close> by (cases a) auto
  have unfold:
    \<open>fst (label_prop_input1_batched os (a # ms)) =
       fst (label_prop_input1_batched (label_prop_input1_step_state os d t) ms)\<close>
    using a_eq fst_label_prop_input1_batched_Cons_prefix[of os d t ms] by simp
  have ih: \<open>min_label (fst (label_prop_input1_batched (label_prop_input1_step_state os d t) ms)) q x
             \<le> min_label (label_prop_input1_step_state os d t) q x\<close>
    using Cons.hyps[of \<open>label_prop_input1_step_state os d t\<close>] by simp
  also have \<open>\<dots> \<le> min_label os q x\<close>
    using min_label_label_prop_input1_step_state_le[of os d t q x] .
  finally show ?case using unfold by simp
qed



lemma labels_inv_label_prop_input1_step_stateI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes labels: \<open>\<And>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and input1: \<open>input os 1 = (d, t) # xs\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>labels_inv (all_edges (label_prop_input1_step_state os d t) q)
    (min_label (label_prop_input1_step_state os d t) q)\<close>
proof -
  obtain v l where de1_eq: \<open>de1 os d = (v, l)\<close>
    by (cases \<open>de1 os d\<close>)
  let ?t1 = \<open>myfst t\<close>
  let ?l' = \<open>min (min_label os ?t1 v) l\<close>
  let ?os'' = \<open>label_prop_label_record_update (input_tl os 1) ?t1 v ?l'\<close>
  have step_eq: \<open>label_prop_input1_step_state os d t =
    release_caps (drop_caps (produces (add_caps ?os''
      (map snd (label_prop_label_batch os ?os'' ?t1 v ?l' t)))
      (label_prop_label_batch os ?os'' ?t1 v ?l' t))
      (map snd (label_prop_label_batch os ?os'' ?t1 v ?l' t))) 1\<close>
    using de1_eq unfolding label_prop_input1_step_state_def Let_def by simp
  have \<open>labels_inv (all_edges ?os'' q) (min_label ?os'' q)\<close>
    by (rule labels_inv_input1_preserved_record_update_tl[OF labels inv _ de1_eq refl refl wf_upd])
      (use input1 in simp)
  then show ?thesis
    unfolding step_eq by simp
qed


lemma label_prop_upd_inv_label_prop_input1_step_stateI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes inv: \<open>label_prop_upd_inv os\<close>
    and input1: \<open>input os 1 = (d, t) # xs\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>label_prop_upd_inv (label_prop_input1_step_state os d t)\<close>
proof -
  obtain v l where de1_eq: \<open>de1 os d = (v, l)\<close>
    by (cases \<open>de1 os d\<close>)
  let ?t1 = \<open>myfst t\<close>
  let ?l' = \<open>min (min_label os ?t1 v) l\<close>
  let ?os'' = \<open>label_prop_label_record_update (input_tl os 1) ?t1 v ?l'\<close>
  have step_eq: \<open>label_prop_input1_step_state os d t =
    release_caps (drop_caps (produces (add_caps ?os''
      (map snd (label_prop_label_batch os ?os'' ?t1 v ?l' t)))
      (label_prop_label_batch os ?os'' ?t1 v ?l' t))
      (map snd (label_prop_label_batch os ?os'' ?t1 v ?l' t))) 1\<close>
    using de1_eq unfolding label_prop_input1_step_state_def Let_def by simp
  have os''_inv: \<open>label_prop_upd_inv ?os''\<close>
    by (rule label_prop_upd_inv_input1_preserved[OF inv input1 _ de1_eq refl _ _ _ _ _ wf_upd])
      (use input1 in \<open>simp_all add: label_prop_label_record_update_def input_tl_def\<close>)

  then show ?thesis
    unfolding step_eq by simp
qed


lemma wf_label_prop_updates_label_prop_input1_step_stateI:
  assumes input1: \<open>input os 1 = (d, t) # xs\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>wf_label_prop_updates (label_prop_input1_step_state os d t)
    (set (input (label_prop_input1_step_state os d t) 1))\<close>
proof -
  let ?step = \<open>label_prop_input1_step_state os d t\<close>
  have input_step: \<open>input ?step 1 = xs\<close>
    using input1 by simp
  have subset: \<open>set xs \<subseteq> set (input os 1)\<close>
    using input1 by auto
  show ?thesis
    using wf_upd subset
    unfolding wf_label_prop_updates_def input_step by auto
qed


lemma label_prop_upd_inv_fst_label_prop_input1_batched_prefixI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes input_eq: \<open>input os 1 = msgs @ rest\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>label_prop_upd_inv (fst (label_prop_input1_batched os msgs))\<close>
  using input_eq inv wf_upd
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close> by (cases msg)
  have input1: \<open>input os 1 = (d, t) # (msgs @ rest)\<close>
    using Cons.prems(1) msg_eq by simp
  let ?step = \<open>label_prop_input1_step_state os d t\<close>
  have inv_step: \<open>label_prop_upd_inv ?step\<close>
    by (rule label_prop_upd_inv_label_prop_input1_step_stateI[OF Cons.prems(2) input1 Cons.prems(3)])
  have wf_step: \<open>wf_label_prop_updates ?step (set (input ?step 1))\<close>
    by (rule wf_label_prop_updates_label_prop_input1_step_stateI[OF input1 Cons.prems(3)])
  have input_step: \<open>input ?step 1 = msgs @ rest\<close>
    using input1 by simp
  have ih: \<open>label_prop_upd_inv (fst (label_prop_input1_batched ?step msgs))\<close>
    by (rule Cons.hyps[OF input_step inv_step wf_step])
  then show ?case
    using msg_eq by (cases \<open>label_prop_input1_batched ?step msgs\<close>) simp
qed


lemma labels_inv_fst_label_prop_input1_batched_prefixI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes input_eq: \<open>input os 1 = msgs @ rest\<close>
    and labels: \<open>\<And>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>labels_inv (all_edges (fst (label_prop_input1_batched os msgs)) q)
    (min_label (fst (label_prop_input1_batched os msgs)) q)\<close>
  using input_eq labels inv wf_upd
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  have input1: \<open>input os 1 = (d, t) # (msgs @ rest)\<close>
    using Cons.prems(1) msg_eq by simp
  let ?step = \<open>label_prop_input1_step_state os d t\<close>
  have labels_step: \<open>\<And>q. labels_inv (all_edges ?step q) (min_label ?step q)\<close>
    by (rule labels_inv_label_prop_input1_step_stateI[OF Cons.prems(2) Cons.prems(3) input1 Cons.prems(4)])
  have inv_step: \<open>label_prop_upd_inv ?step\<close>
    by (rule label_prop_upd_inv_label_prop_input1_step_stateI[OF Cons.prems(3) input1 Cons.prems(4)])
  have wf_step: \<open>wf_label_prop_updates ?step (set (input ?step 1))\<close>
    by (rule wf_label_prop_updates_label_prop_input1_step_stateI[OF input1 Cons.prems(4)])
  have input_step: \<open>input ?step 1 = msgs @ rest\<close>
    using input1 by simp
  have ih: \<open>labels_inv (all_edges (fst (label_prop_input1_batched ?step msgs)) q)
    (min_label (fst (label_prop_input1_batched ?step msgs)) q)\<close>
    by (rule Cons.hyps[OF input_step labels_step inv_step wf_step])
  then show ?case
    using msg_eq
    by (cases \<open>label_prop_input1_batched ?step msgs\<close>) simp

qed


lemma labels_inv_fst_label_prop_input1_batched_inputI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes labels: \<open>\<And>q. labels_inv (all_edges os q) (min_label os q)\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>labels_inv (all_edges (fst (label_prop_input1_batched os (input os 1))) q)
    (min_label (fst (label_prop_input1_batched os (input os 1))) q)\<close>
  by (rule labels_inv_fst_label_prop_input1_batched_prefixI[where rest=Nil])
    (use assms in simp_all)


lemma labels_stable_label_prop_input1_step_stateI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes stable: \<open>labels_stable (all_edges os q) (min_label os q)\<close>
    and time_not_le: \<open>\<not> myfst t \<le> q\<close>
  shows \<open>labels_stable (all_edges (label_prop_input1_step_state os d t) q)
    (min_label (label_prop_input1_step_state os d t) q)\<close>
proof -
  let ?v = \<open>fst (de1 os d)\<close>
  let ?l = \<open>snd (de1 os d)\<close>
  let ?t1 = \<open>myfst t\<close>
  let ?l' = \<open>min (min_label os ?t1 ?v) ?l\<close>
  let ?os'' = \<open>label_prop_label_record_update (input_tl os 1) ?t1 ?v ?l'\<close>
  let ?batch = \<open>label_prop_label_batch os ?os'' ?t1 ?v ?l' t\<close>
  have step_eq:
    \<open>label_prop_input1_step_state os d t =
      release_caps (drop_caps (produces (add_caps ?os'' (map snd ?batch)) ?batch)
        (map snd ?batch)) 1\<close>
    unfolding label_prop_input1_step_state_def Let_def by simp
  have stable': \<open>labels_stable (all_edges os q) (min_label ?os'' q)\<close>
    by (rule labels_stable_input1_preserved_record_update_tl[OF stable time_not_le])
  show ?thesis
    using stable' unfolding step_eq by simp
qed


lemma labels_stable_fst_label_prop_input1_batchedI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes stable: \<open>labels_stable (all_edges os q) (min_label os q)\<close>
    and time_not_le: \<open>\<forall>(d, t)\<in>set msgs. \<not> myfst t \<le> q\<close>
  shows \<open>labels_stable (all_edges (fst (label_prop_input1_batched os msgs)) q)
    (min_label (fst (label_prop_input1_batched os msgs)) q)\<close>
  using stable time_not_le
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  have step_stable:
    \<open>labels_stable (all_edges (label_prop_input1_step_state os d t) q)
      (min_label (label_prop_input1_step_state os d t) q)\<close>
    by (rule labels_stable_label_prop_input1_step_stateI)
      (use Cons.prems msg_eq in auto)
  have tail_not_le: \<open>\<forall>(d, t)\<in>set msgs. \<not> myfst t \<le> q\<close>
    using Cons.prems(2) msg_eq by auto
  have rec:
    \<open>labels_stable (all_edges (fst (label_prop_input1_batched
        (label_prop_input1_step_state os d t) msgs)) q)
      (min_label (fst (label_prop_input1_batched
        (label_prop_input1_step_state os d t) msgs)) q)\<close>
    by (rule Cons.hyps[OF step_stable tail_not_le])
  show ?case
    using rec msg_eq
    by (cases \<open>label_prop_input1_batched (label_prop_input1_step_state os d t) msgs\<close>) simp
qed


lemma label_prop_input1_batched_batch_time_not_leD:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes time_not_le: \<open>\<forall>(d, t)\<in>set msgs. \<not> myfst t \<le> q\<close>
    and member: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
  shows \<open>\<not> myfst (time cap) \<le> q\<close>
proof -
  obtain pre d t post os_pre where msgs_eq: \<open>msgs = pre @ (d, t) # post\<close>
    and step_member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre d t)\<close>
    using member by (elim label_prop_input1_batched_batch_memberD)
  obtain cur_t where time_le: \<open>myfst t \<le> cur_t\<close>
    and cap_eq: \<open>cap = Cap (MyPair cur_t (mysnd t)) (1 :: 2)\<close>
    using step_member by (elim label_prop_input1_step_batch_memberD)
  have msg_not_le: \<open>\<not> myfst t \<le> q\<close>
    using time_not_le msgs_eq by auto
  show ?thesis
    using msg_not_le time_le cap_eq by auto
qed




lemma label_prop_label_batch_empty_neighborD:
  fixes os updated_os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes batch_empty: \<open>label_prop_label_batch os updated_os event_t v l event_time = []\<close>
    and cur_t_in: \<open>cur_t \<in> set (timestamps os)\<close>
    and event_le: \<open>event_t \<le> cur_t\<close>
    and neighbor: \<open>v' \<in> set (neighbors os cur_t v)\<close>
  shows \<open>min_label os cur_t v \<le> l \<or> min_label updated_os cur_t v' \<le> l\<close>
proof (rule ccontr)
  assume not_thesis: \<open>\<not> (min_label os cur_t v \<le> l \<or> min_label updated_os cur_t v' \<le> l)\<close>
  then have old_gt: \<open>l < min_label os cur_t v\<close>
    and updated_gt: \<open>l < min_label updated_os cur_t v'\<close>
    by auto
  have filter_nonempty:
    \<open>filter (\<lambda>v'. l < min_label updated_os cur_t v') (neighbors os cur_t v) \<noteq> []\<close>
  proof -
    have \<open>v' \<in> set (filter (\<lambda>v'. l < min_label updated_os cur_t v')
        (neighbors os cur_t v))\<close>
      using neighbor updated_gt by simp
    then show ?thesis
      by (cases \<open>filter (\<lambda>v'. l < min_label updated_os cur_t v')
          (neighbors os cur_t v)\<close>) auto
  qed
  have nonempty: \<open>label_prop_label_batch os updated_os event_t v l event_time \<noteq> []\<close>
    unfolding label_prop_label_batch_def label_prop_neighbor_batch_def
    using cur_t_in event_le old_gt filter_nonempty
    by (auto simp add: concat_eq_Nil_conv)
  show False
    using batch_empty nonempty by blast
qed


lemma labels_stable_label_prop_label_record_update_visibleI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes INV: \<open>label_prop_upd_inv os\<close>
    and stable: \<open>labels_stable (all_edges os q) (min_label os q)\<close>
    and t1_le_q: \<open>t1 \<le> q\<close>
    and t1_in: \<open>t1 \<in> set (timestamps os)\<close>
    and new_le: \<open>l \<le> min_label os t1 v\<close>
    and batch_empty:
    \<open>label_prop_label_batch os (label_prop_label_record_update (input_tl os 1) t1 v l)
        t1 v l event_time = []\<close>
  shows \<open>labels_stable
    (all_edges (label_prop_label_record_update (input_tl os 1) t1 v l) q)
    (min_label (label_prop_label_record_update (input_tl os 1) t1 v l) q)\<close>
proof -
  let ?os' = \<open>label_prop_label_record_update (input_tl os 1) t1 v l\<close>
  have ts_eq: \<open>timestamps ?os' = timestamps os\<close>
    by simp
  have label_eq: \<open>label ?os' = (label os)(t1 := (label os t1)(v := l))\<close>
    unfolding label_prop_label_record_update_def input_tl_def by simp
  have min_cases:
    \<open>min_label ?os' r x = min_label os r x \<or>
      (x = v \<and> min_label ?os' r x = l)\<close> for r x
    by (rule min_label_label_update_v_cases[OF ts_eq label_eq new_le])
  have min_eq_not_v: \<open>x \<noteq> v \<Longrightarrow> min_label ?os' r x = min_label os r x\<close> for r x
    using min_cases[of r x] by blast
  have min_le_old: \<open>min_label ?os' q x \<le> min_label os q x\<close> for x
    using min_label_label_prop_label_record_update_le[OF new_le, of q x] by simp
  have sym_edges: \<open>sym (all_edges os q)\<close>
    by (rule all_edges_sym[OF INV])
  show ?thesis
    unfolding labels_stable_def
  proof (intro allI impI)
    fix a b
    assume edge_union: \<open>(a, b) \<in> all_edges ?os' q \<union> (all_edges ?os' q)\<inverse>\<close>
    then have edge_union_old: \<open>(a, b) \<in> all_edges os q \<union> (all_edges os q)\<inverse>\<close>
      by simp
    have ab_edge: \<open>(a, b) \<in> all_edges os q\<close>
      using edge_union_old sym_edges unfolding sym_def by auto
    have ba_edge: \<open>(b, a) \<in> all_edges os q\<close>
      using ab_edge sym_edges unfolding sym_def by auto
    have old_ab: \<open>min_label os q a \<le> min_label os q b\<close>
      using stable edge_union_old unfolding labels_stable_def by auto

    show \<open>min_label ?os' q a \<le> min_label ?os' q b\<close>
    proof (cases \<open>min_label ?os' q b = min_label os q b\<close>)
      case True
      then show ?thesis
        using min_le_old[of a] old_ab by linarith
    next
      case False
      then have b_v: \<open>b = v\<close> and min_b: \<open>min_label ?os' q b = l\<close>
        using min_cases[of q b] by auto
      show ?thesis
      proof (cases \<open>a = v\<close>)
        case True
        then show ?thesis
          using b_v by simp
      next
        case a_ne_v: False
        have min_a: \<open>min_label ?os' q a = min_label os q a\<close>
          using min_eq_not_v[OF a_ne_v] .
        have va_edge: \<open>(v, a) \<in> all_edges os q\<close>
          using ba_edge b_v by simp
        then have a_neigh_q: \<open>a \<in> set (neighbors os q v)\<close>
          unfolding all_edges_def by auto
        obtain s where s_in: \<open>s \<in> set (timestamps os)\<close>
          and s_le_q: \<open>s \<le> q\<close>
          and a_graph_s: \<open>a \<in> set (graph os s v)\<close>
          using a_neigh_q unfolding set_neighbors by auto

        have old_a_le_l: \<open>min_label os q a \<le> l\<close>
        proof (cases \<open>s \<le> t1\<close>)
          case True
          have a_neigh_t1: \<open>a \<in> set (neighbors os t1 v)\<close>
            using s_in True a_graph_s unfolding set_neighbors by auto
          have emptyD:
            \<open>min_label os t1 v \<le> l \<or> min_label ?os' t1 a \<le> l\<close>
            by (rule label_prop_label_batch_empty_neighborD[OF batch_empty t1_in le_refl a_neigh_t1])
          then show ?thesis
          proof
            assume \<open>min_label os t1 v \<le> l\<close>
            moreover have \<open>min_label os q a \<le> min_label os q v\<close>
              using old_ab b_v by simp
            moreover have \<open>min_label os q v \<le> min_label os t1 v\<close>
              by (rule min_label_mono_time[OF t1_in t1_le_q])
            ultimately show ?thesis by linarith
          next
            assume upd_a: \<open>min_label ?os' t1 a \<le> l\<close>
            have \<open>min_label os q a \<le> min_label os t1 a\<close>
              by (rule min_label_mono_time[OF t1_in t1_le_q])
            also have \<open>\<dots> = min_label ?os' t1 a\<close>
              using min_eq_not_v[OF a_ne_v, of t1] by simp
            also have \<open>\<dots> \<le> l\<close>
              by (rule upd_a)
            finally show ?thesis .
          qed
        next
          case False
          then have t1_le_s: \<open>t1 \<le> s\<close>
            by linarith
          have a_neigh_s: \<open>a \<in> set (neighbors os s v)\<close>
            using s_in a_graph_s unfolding set_neighbors by auto
          have emptyD:
            \<open>min_label os s v \<le> l \<or> min_label ?os' s a \<le> l\<close>
            by (rule label_prop_label_batch_empty_neighborD[OF batch_empty s_in t1_le_s a_neigh_s])
          then show ?thesis
          proof
            assume \<open>min_label os s v \<le> l\<close>
            moreover have \<open>min_label os q a \<le> min_label os q v\<close>
              using old_ab b_v by simp
            moreover have \<open>min_label os q v \<le> min_label os s v\<close>
              by (rule min_label_mono_time[OF s_in s_le_q])
            ultimately show ?thesis by linarith
          next
            assume upd_a: \<open>min_label ?os' s a \<le> l\<close>


            have \<open>min_label os q a \<le> min_label os s a\<close>
              by (rule min_label_mono_time[OF s_in s_le_q])
            also have \<open>\<dots> = min_label ?os' s a\<close>
              using min_eq_not_v[OF a_ne_v, of s] by simp
            also have \<open>\<dots> \<le> l\<close>
              by (rule upd_a)
            finally show ?thesis .
          qed
        qed
        show ?thesis
          using min_a min_b old_a_le_l by simp
      qed
    qed
  qed
qed


lemma labels_stable_label_prop_input1_step_state_visibleI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes INV: \<open>label_prop_upd_inv os\<close>
    and stable: \<open>labels_stable (all_edges os q) (min_label os q)\<close>
    and time_le: \<open>myfst t \<le> q\<close>
    and time_in: \<open>myfst t \<in> set (timestamps os)\<close>
    and batch_empty: \<open>label_prop_input1_step_batch os d t = []\<close>
  shows \<open>labels_stable (all_edges (label_prop_input1_step_state os d t) q)
    (min_label (label_prop_input1_step_state os d t) q)\<close>
proof -
  let ?v = \<open>fst (de1 os d)\<close>
  let ?l = \<open>snd (de1 os d)\<close>
  let ?t1 = \<open>myfst t\<close>
  let ?l' = \<open>min (min_label os ?t1 ?v) ?l\<close>
  let ?os'' = \<open>label_prop_label_record_update (input_tl os 1) ?t1 ?v ?l'\<close>
  let ?batch = \<open>label_prop_label_batch os ?os'' ?t1 ?v ?l' t\<close>
  have new_le: \<open>?l' \<le> min_label os ?t1 ?v\<close>
    by simp
  have stable': \<open>labels_stable (all_edges ?os'' q) (min_label ?os'' q)\<close>
    using batch_empty
    unfolding label_prop_input1_step_batch_def Let_def
    by (rule labels_stable_label_prop_label_record_update_visibleI
        [OF INV stable time_le time_in new_le])
  show ?thesis
    using stable' unfolding label_prop_input1_step_state_def Let_def by simp
qed


lemma snd_label_prop_input1_batched_empty_if_filter_out1_empty:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes filter_empty:
    \<open>filter (\<lambda>(x, cap). out cap = (1 :: 2))
      (snd (label_prop_input1_batched os msgs)) = []\<close>
  shows \<open>snd (label_prop_input1_batched os msgs) = []\<close>
proof (cases \<open>snd (label_prop_input1_batched os msgs)\<close>)
  case Nil
  then show ?thesis by simp
next
  case (Cons a xs)
  obtain x cap where a_eq: \<open>a = (x, cap)\<close>
    by (cases a)
  have member: \<open>(x, cap) \<in> set (snd (label_prop_input1_batched os msgs))\<close>
    using Cons a_eq by simp
  obtain pre d t post os_pre where
    \<open>msgs = pre @ (d, t) # post\<close>
    \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    and step_member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os_pre d t)\<close>
    using member by (elim label_prop_input1_batched_batch_memberD)
  obtain cur_t where cap_eq: \<open>cap = Cap (MyPair cur_t (mysnd t)) (1 :: 2)\<close>
    using step_member by (elim label_prop_input1_step_batch_memberD)
  have \<open>out cap = (1 :: 2)\<close>
    using cap_eq by simp
  then have \<open>(x, cap) \<in> set (filter (\<lambda>(x, cap). out cap = (1 :: 2))
      (snd (label_prop_input1_batched os msgs)))\<close>
    using member by simp
  then show ?thesis
    using filter_empty by simp
qed


lemma labels_stable_fst_label_prop_input1_batched_emptyI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes input_eq: \<open>input os 1 = msgs @ rest\<close>
    and inv: \<open>label_prop_upd_inv os\<close>
    and stable: \<open>labels_stable (all_edges os q) (min_label os q)\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
    and batch_empty: \<open>snd (label_prop_input1_batched os msgs) = []\<close>
  shows \<open>labels_stable (all_edges (fst (label_prop_input1_batched os msgs)) q)
    (min_label (fst (label_prop_input1_batched os msgs)) q)\<close>
  using input_eq inv stable wf_upd batch_empty
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  have input1: \<open>input os 1 = (d, t) # (msgs @ rest)\<close>
    using Cons.prems(1) msg_eq by simp
  let ?step = \<open>label_prop_input1_step_state os d t\<close>
  have head_empty: \<open>label_prop_input1_step_batch os d t = []\<close>
    using Cons.prems(5) msg_eq
    by (cases \<open>label_prop_input1_batched ?step msgs\<close>) simp
  have tail_empty: \<open>snd (label_prop_input1_batched ?step msgs) = []\<close>
    using Cons.prems(5) msg_eq
    by (cases \<open>label_prop_input1_batched ?step msgs\<close>) simp
  have time_in: \<open>myfst t \<in> set (timestamps os)\<close>
    using input1 Cons.prems(4)
    unfolding wf_label_prop_updates_def by fastforce
  have step_stable:
    \<open>labels_stable (all_edges ?step q) (min_label ?step q)\<close>
  proof (cases \<open>myfst t \<le> q\<close>)
    case True
    show ?thesis
      by (rule labels_stable_label_prop_input1_step_state_visibleI
          [OF Cons.prems(2) Cons.prems(3) True time_in head_empty])
  next
    case False
    show ?thesis
      by (rule labels_stable_label_prop_input1_step_stateI[OF Cons.prems(3) False])
  qed
  have inv_step: \<open>label_prop_upd_inv ?step\<close>
    by (rule label_prop_upd_inv_label_prop_input1_step_stateI[OF Cons.prems(2) input1 Cons.prems(4)])
  have wf_step: \<open>wf_label_prop_updates ?step (set (input ?step 1))\<close>
    by (rule wf_label_prop_updates_label_prop_input1_step_stateI[OF input1 Cons.prems(4)])
  have input_step: \<open>input ?step 1 = msgs @ rest\<close>
    using input1 by simp
  have rec:
    \<open>labels_stable (all_edges (fst (label_prop_input1_batched ?step msgs)) q)
      (min_label (fst (label_prop_input1_batched ?step msgs)) q)\<close>
    by (rule Cons.hyps[OF input_step inv_step step_stable wf_step tail_empty])
  show ?case
    using rec msg_eq
    by (cases \<open>label_prop_input1_batched ?step msgs\<close>) simp
qed


lemma labels_stable_fst_label_prop_input1_batched_input_emptyI:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes inv: \<open>label_prop_upd_inv os\<close>
    and stable: \<open>labels_stable (all_edges os q) (min_label os q)\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
    and batch_empty: \<open>snd (label_prop_input1_batched os (input os 1)) = []\<close>
  shows \<open>labels_stable (all_edges (fst (label_prop_input1_batched os (input os 1))) q)
    (min_label (fst (label_prop_input1_batched os (input os 1))) q)\<close>
  by (rule labels_stable_fst_label_prop_input1_batched_emptyI[where rest=Nil])
    (use assms in simp_all)



lemma fst_label_prop_input1_batched_append:
  \<open>fst (label_prop_input1_batched os (xs @ ys)) =
   fst (label_prop_input1_batched (fst (label_prop_input1_batched os xs)) ys)\<close>
proof (induct xs arbitrary: os)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  obtain d t where a_eq: \<open>a = (d, t)\<close> by (cases a)
  have step_eq:
    \<open>fst (label_prop_input1_batched os ((d, t) # (xs @ ys))) =
     fst (label_prop_input1_batched (label_prop_input1_step_state os d t) (xs @ ys))\<close>
    using fst_label_prop_input1_batched_Cons_prefix[of os d t \<open>xs @ ys\<close>] by simp
  have step_eq2:
    \<open>fst (label_prop_input1_batched os ((d, t) # xs)) =
     fst (label_prop_input1_batched (label_prop_input1_step_state os d t) xs)\<close>
    using fst_label_prop_input1_batched_Cons_prefix[of os d t xs] by simp
  show ?case
    using a_eq step_eq step_eq2
      Cons.hyps[of \<open>label_prop_input1_step_state os d t\<close>]
    by simp
qed

(* preservation lemma for label_prop_upd_inv through batched *)

lemma label_prop_upd_inv_fst_label_prop_input1_batched_preserved:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>label_prop_upd_inv os\<close>
  shows \<open>label_prop_upd_inv (fst (label_prop_input1_batched os msgs))\<close>
  oops


lemma min_label_fst_label_prop_input1_batched_strict_if_output_nonempty:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes \<open>outpu os 1 = []\<close>
    and \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
  obtains q v where
    \<open>v \<in> edge_vertices (all_edges os q)\<close>
    \<open>min_label (fst (label_prop_input1_batched os msgs)) q v < min_label os q v\<close>
  oops



lemma min_label_fst_label_prop_input1_batched_strict_timestamped_if_output_nonempty:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes out_empty: \<open>outpu os 1 = []\<close>
    and out_nonempty: \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  obtains q v where
    \<open>q \<in> set (timestamps os)\<close>
    \<open>v \<in> edge_vertices (all_edges os q)\<close>
    \<open>min_label (fst (label_prop_input1_batched os msgs)) q v < min_label os q v\<close>
proof -
  obtain pre d t post os_pre v l l' where
    msgs_eq: \<open>msgs = pre @ (d, t) # post\<close>
    and os_pre_eq: \<open>os_pre = fst (label_prop_input1_batched os pre)\<close>
    and de1_pre_eq: \<open>de1 os_pre d = (v, l)\<close>
    and l': \<open>l' = min (min_label os_pre (myfst t) v) l\<close>
    and strict_pre: \<open>l' < min_label os_pre (myfst t) v\<close>
    and update_strict:
    \<open>min_label (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v l') (myfst t) v
        < min_label os_pre (myfst t) v\<close>
    apply (rule label_prop_input1_batched_outpu_nonempty_strict_updateD[OF out_empty out_nonempty, OF INV msgs_input wf_upd])
    apply simp
    done   
  have de1_os_eq: \<open>de1 os d = (v, l)\<close>
    using de1_pre_eq os_pre_eq by simp
  have dt_in_msgs: \<open>(d, t) \<in> set msgs\<close>
    using msgs_eq by simp
  have dt_in_input: \<open>(d, t) \<in> set (input os 1)\<close>
    using dt_in_msgs msgs_input by auto
  have ts_t: \<open>myfst t \<in> set (timestamps os)\<close>
    and v_vertex_raw: \<open>fst (de1 os d) \<in> all_vertices os (myfst t)\<close>
    using dt_in_input wf_upd unfolding wf_label_prop_updates_def by fast+
  have v_in_all: \<open>v \<in> all_vertices os (myfst t)\<close>
    using v_vertex_raw de1_os_eq by simp
  have v_in_edge: \<open>v \<in> edge_vertices (all_edges os (myfst t))\<close>
    using v_in_all edge_vertices_all_edges[OF INV] by simp

  let ?step = \<open>label_prop_input1_step_state os_pre d t\<close>
  let ?new = \<open>min (min_label os_pre (myfst t) v) l\<close>
  have new_eq_l: \<open>?new = l'\<close> by (rule sym[OF l'])
  have step_min:
    \<open>min_label ?step (myfst t) v =
       min_label (label_prop_label_record_update (input_tl os_pre 1) (myfst t) v ?new) (myfst t) v\<close>
    unfolding label_prop_input1_step_state_def Let_def
    using de1_pre_eq by simp
  have step_strict_pre:
    \<open>min_label ?step (myfst t) v < min_label os_pre (myfst t) v\<close>
    using step_min new_eq_l update_strict by simp

  have fst_unfold:
    \<open>fst (label_prop_input1_batched os msgs) =
     fst (label_prop_input1_batched ?step post)\<close>
    using msgs_eq os_pre_eq
      fst_label_prop_input1_batched_append[of os pre \<open>(d, t) # post\<close>]
      fst_label_prop_input1_batched_Cons_prefix[of os_pre d t post]
    by simp

  have step_le_os:
    \<open>min_label os_pre (myfst t) v \<le> min_label os (myfst t) v\<close>
    using os_pre_eq min_label_fst_label_prop_input1_batched_le[of os pre \<open>myfst t\<close> v]
    by simp

  have tail_le_step:
    \<open>min_label (fst (label_prop_input1_batched ?step post)) (myfst t) v
       \<le> min_label ?step (myfst t) v\<close>
    using min_label_fst_label_prop_input1_batched_le[of ?step post \<open>myfst t\<close> v] .

  have strict_full:
    \<open>min_label (fst (label_prop_input1_batched os msgs)) (myfst t) v < min_label os (myfst t) v\<close>
  proof -
    have \<open>min_label (fst (label_prop_input1_batched os msgs)) (myfst t) v
            = min_label (fst (label_prop_input1_batched ?step post)) (myfst t) v\<close>
      using fst_unfold by simp
    also have \<open>\<dots> \<le> min_label ?step (myfst t) v\<close>
      using tail_le_step .
    also have \<open>\<dots> < min_label os_pre (myfst t) v\<close>
      using step_strict_pre .
    also have \<open>\<dots> \<le> min_label os (myfst t) v\<close>
      using step_le_os .
    finally show ?thesis .
  qed

  show ?thesis
    using that[OF ts_t v_in_edge strict_full] .
qed


subsection \<open>Measure decrease\<close>


lemma labels_measure_strict_decrease_if_pointwise_le_and_less:
  fixes A :: \<open>(nat \<times> nat) set\<close>
    and l l' :: \<open>nat \<Rightarrow> nat\<close>
  assumes finite_edges: \<open>finite (edge_vertices A)\<close>
    and labels: \<open>labels_inv A l\<close>
    and labels': \<open>labels_inv A l'\<close>
    and le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> l' v \<le> l v\<close>
    and strict: \<open>\<exists>v\<in>edge_vertices A. l' v < l v\<close>
  shows \<open>labels_measure A l' < labels_measure A l\<close>
proof -
  have rank_le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> rank A (l' v) \<le> rank A (l v)\<close>
    using le finite_edges
    unfolding rank_def
    by (intro card_mono; force)

  obtain v where v_in: \<open>v \<in> edge_vertices A\<close> and strict_v: \<open>l' v < l v\<close>
    using strict by auto
  have l'_in: \<open>l' v \<in> edge_vertices A\<close>
    using labels' v_in unfolding labels_inv_def cc_of_def by auto
  have rank_strict: \<open>rank A (l' v) < rank A (l v)\<close>
  proof -
    let ?S' = \<open>{y \<in> edge_vertices A. y < l' v}\<close>
    let ?S = \<open>{y \<in> edge_vertices A. y < l v}\<close>
    have subset: \<open>?S' \<subset> ?S\<close>
      using l'_in strict_v by auto
    moreover have \<open>finite ?S\<close>
      using finite_edges by auto
    ultimately show ?thesis
      unfolding rank_def by (simp add: psubset_card_mono)
  qed
  show ?thesis
    unfolding labels_measure_def
    by (rule sum_strict_mono_ex1[OF finite_edges]) (auto intro: rank_le v_in rank_strict)
qed



lemma labels_measure_strict_decrease_if_pointwise_le_and_less_same_edges:
  fixes A A' :: \<open>(nat \<times> nat) set\<close>
    and l l' :: \<open>nat \<Rightarrow> nat\<close>
  assumes finite_edges: \<open>finite (edge_vertices A)\<close>
    and labels: \<open>labels_inv A l\<close>
    and labels': \<open>labels_inv A l'\<close>
    and edges_eq: \<open>A' = A\<close>
    and le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> l' v \<le> l v\<close>
    and strict: \<open>\<exists>v\<in>edge_vertices A. l' v < l v\<close>
  shows \<open>labels_measure A' l' < labels_measure A l\<close>
  using labels_measure_strict_decrease_if_pointwise_le_and_less
    [OF finite_edges labels labels' le strict]
    edges_eq by simp





lemma labels_measure_le_if_pointwise_le_same_edges:
  fixes A A' :: \<open>(nat \<times> nat) set\<close>
    and l l' :: \<open>nat \<Rightarrow> nat\<close>
  assumes finite_edges: \<open>finite (edge_vertices A)\<close>
    and edges_eq: \<open>A' = A\<close>
    and le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> l' v \<le> l v\<close>
  shows \<open>labels_measure A' l' \<le> labels_measure A l\<close>
proof -
  have rank_le: \<open>\<And>v. v \<in> edge_vertices A \<Longrightarrow> rank A (l' v) \<le> rank A (l v)\<close>
    using le finite_edges
    unfolding rank_def
    by (intro card_mono; force)
  have \<open>(\<Sum>v\<in>edge_vertices A. rank A (l' v)) \<le> (\<Sum>v\<in>edge_vertices A. rank A (l v))\<close>
    by (rule sum_mono) (auto intro: rank_le)
  then show ?thesis
    using edges_eq unfolding labels_measure_def by simp

qed



lemma labels_measure_fst_label_prop_input1_batched_le_at_timestamp:
  fixes os os' :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and msgs :: \<open>('d \<times> (nat, nat) myprod) list\<close>
  assumes os'_def: \<open>os' = fst (label_prop_input1_batched os msgs)\<close>
  shows \<open>labels_measure (all_edges os' t) (min_label os' t)
      \<le> labels_measure (all_edges os t) (min_label os t)\<close>
proof -
  have edges_eq: \<open>all_edges os' t = all_edges os t\<close>
    using os'_def by simp
  have finite_edges: \<open>finite (edge_vertices (all_edges os t))\<close>
    by (rule finite_edge_vertices_all_edges)
  have pointwise:
    \<open>\<And>v. v \<in> edge_vertices (all_edges os t) \<Longrightarrow> min_label os' t v \<le> min_label os t v\<close>
    using os'_def min_label_fst_label_prop_input1_batched_le[of os msgs t]
    by simp
  show ?thesis
    by (rule labels_measure_le_if_pointwise_le_same_edges
        [OF finite_edges edges_eq pointwise])
qed



lemma labels_measure_fst_label_prop_input1_batched_strict_at_some_timestamp_if_output_nonempty:
  fixes os os' :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and msgs :: \<open>('d \<times> (nat, nat) myprod) list\<close>
  assumes os'_def: \<open>os' = fst (label_prop_input1_batched os msgs)\<close>
    and out_empty: \<open>outpu os 1 = []\<close>
    and out_nonempty: \<open>outpu os' 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
    and labels_os: \<open>\<And>t. labels_inv (all_edges os t) (min_label os t)\<close>
    and labels_os': \<open>\<And>t. labels_inv (all_edges os' t) (min_label os' t)\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  obtains q where
    \<open>q \<in> set (timestamps os)\<close>
    \<open>labels_measure (all_edges os' q) (min_label os' q)
      < labels_measure (all_edges os q) (min_label os q)\<close>
proof -
  have out_batch: \<open>outpu (fst (label_prop_input1_batched os msgs)) 1 \<noteq> []\<close>
    using os'_def out_nonempty by simp
  obtain q v where q_in: \<open>q \<in> set (timestamps os)\<close>
    and v_in: \<open>v \<in> edge_vertices (all_edges os q)\<close>
    and strict_v: \<open>min_label (fst (label_prop_input1_batched os msgs)) q v < min_label os q v\<close>
    using min_label_fst_label_prop_input1_batched_strict_timestamped_if_output_nonempty
      [OF out_empty out_batch INV msgs_input wf_upd]
    by blast
  have pointwise:
    \<open>\<And>v. v \<in> edge_vertices (all_edges os q) \<Longrightarrow> min_label os' q v \<le> min_label os q v\<close>
    using os'_def min_label_fst_label_prop_input1_batched_le[of os msgs q]
    by simp
  have strict_ex:
    \<open>\<exists>v\<in>edge_vertices (all_edges os q). min_label os' q v < min_label os q v\<close>
    using os'_def v_in strict_v by auto
  have edges_eq: \<open>all_edges os' q = all_edges os q\<close>
    using os'_def by simp
  have finite_edges: \<open>finite (edge_vertices (all_edges os q))\<close>
    by (rule finite_edge_vertices_all_edges)
  have labels: \<open>labels_inv (all_edges os q) (min_label os q)\<close>
    using labels_os .
  have labels': \<open>labels_inv (all_edges os q) (min_label os' q)\<close>
    using labels_os'[of q] edges_eq by simp
  have strict_measure:
    \<open>labels_measure (all_edges os' q) (min_label os' q)
      < labels_measure (all_edges os q) (min_label os q)\<close>
    by (rule labels_measure_strict_decrease_if_pointwise_le_and_less_same_edges
        [OF finite_edges labels labels' edges_eq pointwise strict_ex])
  show ?thesis
    using that[OF q_in strict_measure] .
qed




lemma labels_measure_sum_fst_label_prop_input1_batched_decreases_if_output_nonempty:
  fixes os os' :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and msgs :: \<open>('d \<times> (nat, nat) myprod) list\<close>
  assumes os'_def: \<open>os' = fst (label_prop_input1_batched os msgs)\<close>
    and out_empty: \<open>outpu os 1 = []\<close>
    and out_nonempty: \<open>outpu os' 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os\<close>
    and msgs_input: \<open>set msgs \<subseteq> set (input os 1)\<close>
    and labels_os: \<open>\<And>t. labels_inv (all_edges os t) (min_label os t)\<close>
    and labels_os': \<open>\<And>t. labels_inv (all_edges os' t) (min_label os' t)\<close>
    and wf_upd: \<open>wf_label_prop_updates os (set (input os 1))\<close>
  shows \<open>sum_list (map (\<lambda>t. labels_measure (all_edges os' t) (min_label os' t))
          (timestamps os'))
      < sum_list (map (\<lambda>t. labels_measure (all_edges os t) (min_label os t))
          (timestamps os))\<close>
proof -
  have ts_eq: \<open>timestamps os' = timestamps os\<close>
    using os'_def by simp
  have pointwise:
    \<open>\<And>t. t \<in> set (timestamps os) \<Longrightarrow>
      labels_measure (all_edges os' t) (min_label os' t)
        \<le> labels_measure (all_edges os t) (min_label os t)\<close>
    using labels_measure_fst_label_prop_input1_batched_le_at_timestamp[OF os'_def]
    by simp
  obtain q where q_in: \<open>q \<in> set (timestamps os)\<close>
    and strict_q: \<open>labels_measure (all_edges os' q) (min_label os' q)
      < labels_measure (all_edges os q) (min_label os q)\<close>
    using labels_measure_fst_label_prop_input1_batched_strict_at_some_timestamp_if_output_nonempty
      [OF os'_def out_empty out_nonempty INV msgs_input labels_os labels_os' wf_upd]
    by blast
  have strict_ex:
    \<open>\<exists>t\<in>set (timestamps os). labels_measure (all_edges os' t) (min_label os' t)
      < labels_measure (all_edges os t) (min_label os t)\<close>
    using q_in strict_q by blast
  have \<open>sum_list (map (\<lambda>t. labels_measure (all_edges os' t) (min_label os' t))
          (timestamps os))
      < sum_list (map (\<lambda>t. labels_measure (all_edges os t) (min_label os t))
          (timestamps os))\<close>
    by (rule sum_list_strict_mono_ex1[OF pointwise strict_ex])
  then show ?thesis
    using ts_eq by simp
qed


subsection \<open>Loop-update termination driver\<close>


lemma labels_inv_label_prop_input1_loop_updatesI:
  fixes os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes UPDATES: \<open>(cbufs', os_label_prop', os') =
      label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and labels_os: \<open>\<And>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and wf_upd: \<open>wf_label_prop_updates os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  shows \<open>labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
proof -
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?base = \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>\<close>
  let ?consumed = \<open>CONSUMES 1 ?msgs ?base\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?consumed (input ?consumed 1))\<close>
    using UPDATES
    unfolding label_prop_input1_loop_updates_def Let_def
    by (auto split: prod.splits)
  have wf_base_msgs: \<open>wf_label_prop_updates ?base (set ?msgs)\<close>
    using wf_upd[unfolded wf_label_prop_updates_un]
    unfolding wf_label_prop_updates_def by simp
  have inv_consumed: \<open>label_prop_upd_inv ?consumed\<close>
    by (rule label_prop_upd_inv_CONSUMES_port1I[OF _ wf_base_msgs])
      (use INV in simp)
  have labels_consumed: \<open>\<And>t. labels_inv (all_edges ?consumed t) (min_label ?consumed t)\<close>
    using labels_os by simp
  have wf_consumed: \<open>wf_label_prop_updates ?consumed (set (input ?consumed 1))\<close>
    using wf_upd
    unfolding wf_label_prop_updates_def by (simp add: input_CONSUMES Un_commute)
  show ?thesis
    using os_label_prop'_eq labels_inv_fst_label_prop_input1_batched_inputI
      [OF labels_consumed inv_consumed wf_consumed, of t]
    by simp
qed


lemma labels_stable_label_prop_input1_loop_updates_emptyI:
  fixes os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes UPDATES: \<open>(cbufs', os_label_prop', os') =
      label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and stable: \<open>labels_stable (all_edges os_label_prop q) (min_label os_label_prop q)\<close>
    and wf_upd: \<open>wf_label_prop_updates os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and out_empty: \<open>outpu os_label_prop' 1 = []\<close>
  shows \<open>labels_stable (all_edges os_label_prop' q) (min_label os_label_prop' q)\<close>
proof -
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?base = \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>\<close>
  let ?consumed = \<open>CONSUMES 1 ?msgs ?base\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?consumed (input ?consumed 1))\<close>
    using UPDATES
    unfolding label_prop_input1_loop_updates_def Let_def
    by (auto split: prod.splits)
  have wf_base_msgs: \<open>wf_label_prop_updates ?base (set ?msgs)\<close>
    using wf_upd[unfolded wf_label_prop_updates_un]
    unfolding wf_label_prop_updates_def by simp
  have inv_consumed: \<open>label_prop_upd_inv ?consumed\<close>
    by (rule label_prop_upd_inv_CONSUMES_port1I[OF _ wf_base_msgs])
      (use INV in simp)
  have stable_consumed: \<open>labels_stable (all_edges ?consumed q) (min_label ?consumed q)\<close>
    using stable by simp
  have wf_consumed: \<open>wf_label_prop_updates ?consumed (set (input ?consumed 1))\<close>
    using wf_upd
    unfolding wf_label_prop_updates_def by (simp add: input_CONSUMES Un_commute)
  have consumed_out_empty: \<open>outpu ?consumed 1 = []\<close>
    by (simp add: fold_consumes)
  have filter_empty:
    \<open>filter (\<lambda>(x, cap). out cap = (1 :: 2))
      (snd (label_prop_input1_batched ?consumed (input ?consumed 1))) = []\<close>
    using out_empty os_label_prop'_eq consumed_out_empty
    by (simp add: outpu_fst_label_prop_input1_batched_eq)
  have batch_empty:
    \<open>snd (label_prop_input1_batched ?consumed (input ?consumed 1)) = []\<close>
    by (rule snd_label_prop_input1_batched_empty_if_filter_out1_empty[OF filter_empty])
  have stable_final:
    \<open>labels_stable
      (all_edges (fst (label_prop_input1_batched ?consumed (input ?consumed 1))) q)
      (min_label (fst (label_prop_input1_batched ?consumed (input ?consumed 1))) q)\<close>
    by (rule labels_stable_fst_label_prop_input1_batched_input_emptyI
        [OF inv_consumed stable_consumed wf_consumed batch_empty])
  show ?thesis
    using os_label_prop'_eq stable_final by simp
qed


lemma labels_stable_label_prop_input1_loop_updatesI:
  fixes os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes UPDATES: \<open>(cbufs', os_label_prop', os') =
      label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and stable: \<open>labels_stable (all_edges os_label_prop q) (min_label os_label_prop q)\<close>
    and time_not_le: \<open>\<forall>(d, t)\<in>set (input os_label_prop 1) \<union>
        set (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)).
      \<not> myfst t \<le> q\<close>
  shows \<open>labels_stable (all_edges os_label_prop' q) (min_label os_label_prop' q)\<close>
proof -
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?base = \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>\<close>
  let ?consumed = \<open>CONSUMES 1 ?msgs ?base\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?consumed (input ?consumed 1))\<close>
    using UPDATES
    unfolding label_prop_input1_loop_updates_def Let_def
    by (auto split: prod.splits)
  have stable_consumed: \<open>labels_stable (all_edges ?consumed q) (min_label ?consumed q)\<close>
    using stable by simp
  have time_not_le_consumed:
    \<open>\<forall>(d, t)\<in>set (input ?consumed 1). \<not> myfst t \<le> q\<close>
    using time_not_le by (simp add: input_CONSUMES Un_commute)
  have stable_batched:
    \<open>labels_stable
      (all_edges (fst (label_prop_input1_batched ?consumed (input ?consumed 1))) q)
      (min_label (fst (label_prop_input1_batched ?consumed (input ?consumed 1))) q)\<close>
    by (rule labels_stable_fst_label_prop_input1_batchedI[OF stable_consumed time_not_le_consumed])
  show ?thesis
    using os_label_prop'_eq stable_batched by simp
qed


lemma label_prop_input1_loop_updates_sum_measure_decrease_if_label_output_nonempty:
  fixes os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes UPDATES: \<open>(cbufs', os_label_prop', os') =
      label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and out_nonempty: \<open>outpu os_label_prop' 1 \<noteq> []\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and wf_upd: \<open>wf_label_prop_updates os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
    and labels_os: \<open>\<And>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
  shows \<open>sum_list (map (\<lambda>t. labels_measure (all_edges os_label_prop' t) (min_label os_label_prop' t))
          (timestamps os_label_prop'))
      < sum_list (map (\<lambda>t. labels_measure (all_edges os_label_prop t) (min_label os_label_prop t))
          (timestamps os_label_prop))\<close>
proof -
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?base = \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>\<close>
  let ?consumed = \<open>CONSUMES 1 ?msgs ?base\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?consumed (input ?consumed 1))\<close>
    using UPDATES
    unfolding label_prop_input1_loop_updates_def Let_def
    by (auto split: prod.splits)
  have consumed_outpu: \<open>outpu ?consumed 1 = []\<close>
    unfolding fold_consumes by simp
  have msgs_input_self: \<open>set (input ?consumed 1) \<subseteq> set (input ?consumed 1)\<close>
    by simp
  have wf_base_msgs: \<open>wf_label_prop_updates ?base (set ?msgs)\<close>
    using wf_upd[unfolded wf_label_prop_updates_un]
    unfolding wf_label_prop_updates_def by simp
  have inv_consumed: \<open>label_prop_upd_inv ?consumed\<close>
    by (rule label_prop_upd_inv_CONSUMES_port1I[OF _ wf_base_msgs])
      (use INV in simp)
  have wf_consumed: \<open>wf_label_prop_updates ?consumed (set (input ?consumed 1))\<close>
    using wf_upd
    unfolding wf_label_prop_updates_def by (simp add: input_CONSUMES Un_commute)
  have labels_consumed: \<open>\<And>t. labels_inv (all_edges ?consumed t) (min_label ?consumed t)\<close>
    using labels_os by simp
  have labels_os': \<open>\<And>t. labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
    by (rule labels_inv_label_prop_input1_loop_updatesI[OF UPDATES INV labels_os wf_upd])
  have consumed_decrease:
    \<open>sum_list (map (\<lambda>t. labels_measure (all_edges os_label_prop' t) (min_label os_label_prop' t))
        (timestamps os_label_prop'))
      < sum_list (map (\<lambda>t. labels_measure (all_edges ?consumed t) (min_label ?consumed t))
        (timestamps ?consumed))\<close>
    using labels_measure_sum_fst_label_prop_input1_batched_decreases_if_output_nonempty
      [of os_label_prop' ?consumed \<open>input ?consumed 1\<close>]
      os_label_prop'_eq consumed_outpu out_nonempty inv_consumed msgs_input_self
      labels_consumed labels_os' wf_consumed
    by simp
  have consumed_same:
    \<open>sum_list (map (\<lambda>t. labels_measure (all_edges ?consumed t) (min_label ?consumed t))
        (timestamps ?consumed)) =
      sum_list (map (\<lambda>t. labels_measure (all_edges os_label_prop t) (min_label os_label_prop t))
        (timestamps os_label_prop))\<close>
    unfolding fold_consumes min_label_def all_edges_def all_vertices_def neighbors_def
    by simp
  show ?thesis
    using consumed_decrease consumed_same by simp
qed



lemma label_prop_input1_loop_updates_timestmaps:
  "label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os') \<Longrightarrow>
   timestamps os_label_prop' = timestamps os_label_prop"
  unfolding label_prop_input1_loop_updates_def
  by clarsimp

subsection \<open>Frame facts for label_prop_input1_loop_updates\<close>


lemma fst_label_prop_input1_loop_updates[simp]:
  \<open>fst (label_prop_input1_loop_updates cbufs os_label_prop os) =
   cbufs((2, 1) := [], (1, 1) := [])\<close>
  unfolding label_prop_input1_loop_updates_def Let_def by simp


lemma filter_cap_out_map_neq[simp]:
  assumes \<open>p \<noteq> q\<close>
  shows \<open>filter (\<lambda>cap. out cap = p) (map (\<lambda>t. Cap t q) xs) = []\<close>
  using assms by (induct xs) auto


lemma filter_cap_out_map_image_neq[simp]:
  assumes \<open>p \<noteq> q\<close>
  shows \<open>filter (\<lambda>cap. out cap = p) (map (\<lambda>x. Cap (f x) q) xs) = []\<close>
  using assms by (induct xs) auto


lemma filter_snd_label_prop_label_batch_out_neq[simp]:
  assumes \<open>p \<noteq> (1 :: 2)\<close>
  shows \<open>filter (\<lambda>cap. out cap = p)
    (map snd (label_prop_label_batch old_os updated_os event_t v l t)) = []\<close>
proof -
  have aux:
    \<open>filter (\<lambda>cap. out cap = p)
      (map snd (concat (map (\<lambda>cur_t.
        if l < min_label old_os cur_t v then
          map (\<lambda>v'. (en1 old_os (v', l), Cap (MyPair cur_t (mysnd t)) 1))
            (filter (\<lambda>v'. l < min_label updated_os cur_t v') (neighbors old_os cur_t v))
        else []) ts))) = []\<close> for ts
    using assms by (induct ts) (auto simp: comp_def)

  show ?thesis
    unfolding label_prop_label_batch_def label_prop_neighbor_batch_def Let_def
    using aux by simp
qed





lemma ocaps_1_label_prop_input1_step_state_empty:
  assumes input0_empty: \<open>input os (0 :: 2) = []\<close>
    and input1_single: \<open>input os (1 :: 2) = [(d, t)]\<close>
  shows \<open>ocaps (label_prop_input1_step_state os d t) (1 :: 2) = []\<close>
  unfolding label_prop_input1_step_state_def Let_def
  apply (rule ocaps_release_caps_empty_inputs)
  subgoal for p' s
    using input0_empty input1_single
    by (cases p' rule: num2_cases) (simp_all add: input_tl_def)
  done


lemma ocaps_1_fst_label_prop_input1_batched_empty:
  assumes input0_empty: \<open>input os (0 :: 2) = []\<close>
    and msgs_eq: \<open>msgs = input os (1 :: 2)\<close>
    and nonempty_or_empty: \<open>msgs \<noteq> [] \<or> ocaps os (1 :: 2) = []\<close>
  shows \<open>ocaps (fst (label_prop_input1_batched os msgs)) (1 :: 2) = []\<close>
  using assms
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg) simp
  define os' where \<open>os' = label_prop_input1_step_state os d t\<close>
  have input1_os: \<open>input os (1 :: 2) = (d, t) # msgs\<close>
    using Cons.prems(2) msg_eq by simp
  have input0_os': \<open>input os' (0 :: 2) = []\<close>
    using Cons.prems(1) by (simp add: os'_def)
  have msgs_os': \<open>msgs = input os' (1 :: 2)\<close>
    using input1_os by (simp add: os'_def)
  have nonempty_or_empty': \<open>msgs \<noteq> [] \<or> ocaps os' (1 :: 2) = []\<close>
  proof (cases \<open>msgs = []\<close>)
    case True
    then have \<open>ocaps os' (1 :: 2) = []\<close>
      using ocaps_1_label_prop_input1_step_state_empty[OF Cons.prems(1), of d t]
        input1_os
      by (simp add: os'_def)
    then show ?thesis by simp
  next
    case False
    then show ?thesis by simp
  qed
  have rec: \<open>ocaps (fst (label_prop_input1_batched os' msgs)) (1 :: 2) = []\<close>
    by (rule Cons.hyps[OF input0_os' msgs_os' nonempty_or_empty'])
  show ?case
    using msg_eq rec
    by (cases \<open>label_prop_input1_batched os' msgs\<close>) (simp add: os'_def)
qed


lemma ocaps_1_fst_snd_label_prop_input1_loop_updates_empty:
  assumes input0_empty: \<open>input os_label_prop (0 :: 2) = []\<close>
    and no_stale:
    \<open>input os_label_prop (1 :: 2) @
        cbufs (1, 1) @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1) = [] \<Longrightarrow>
        ocaps os_label_prop (1 :: 2) = []\<close>
  shows \<open>ocaps (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) (1 :: 2) = []\<close>
proof -
  let ?incoming = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?consumed = \<open>CONSUMES 1 ?incoming
    (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  have input0_consumed: \<open>input ?consumed (0 :: 2) = []\<close>
    using input0_empty by (simp add: input_CONSUMES)
  have nonempty_or_empty: \<open>input ?consumed (1 :: 2) \<noteq> [] \<or> ocaps ?consumed (1 :: 2) = []\<close>
  proof (cases \<open>input ?consumed (1 :: 2) = []\<close>)
    case False
    then show ?thesis by simp
  next
    case True
    have stale: \<open>ocaps os_label_prop (1 :: 2) = []\<close>
      using True no_stale by (simp add: input_CONSUMES fold_consumes)
    show ?thesis
      using True stale by (simp add: input_CONSUMES fold_consumes)
  qed
  have batch:
    \<open>ocaps (fst (label_prop_input1_batched ?consumed (input ?consumed (1 :: 2)))) (1 :: 2) = []\<close>
    by (rule ocaps_1_fst_label_prop_input1_batched_empty
        [OF input0_consumed refl nonempty_or_empty])
  show ?thesis
    using batch
    unfolding label_prop_input1_loop_updates_def Let_def
    by simp
qed







lemma ocaps_0_label_prop_input1_step_state[simp]:
  \<open>ocaps (label_prop_input1_step_state os d t) (0 :: 2) = ocaps os 0\<close>
  unfolding label_prop_input1_step_state_def release_caps_def drop_caps_def add_caps_def
    produces_def input_tl_def
  by (simp add: Let_def)





lemma ocaps_0_fst_label_prop_input1_batched[simp]:
  \<open>ocaps (fst (label_prop_input1_batched os msgs)) (0 :: 2) = ocaps os 0\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta split: prod.splits)


lemma intsum_fst_snd_label_prop_input1_loop_updates[simp]:
  \<open>intsum (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) =
    intsum os_label_prop\<close>
  unfolding label_prop_input1_loop_updates_def Let_def
  by clarsimp


lemma ocaps_0_fst_snd_label_prop_input1_loop_updates[simp]:
  assumes H: \<open>intsum os_label_prop (1 :: 2) (0 :: 2) = []\<close>
  shows \<open>ocaps (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) 0 =
    ocaps os_label_prop 0\<close>
  using H
  unfolding label_prop_input1_loop_updates_def Let_def
  by (clarsimp simp add: fold_consumes)


lemma ocaps_1_snd_snd_label_prop_input1_loop_updates_empty:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes H: \<open>intsum (os (2 :: 3)) (1 :: 2) (1 :: 2) = [MyPair 0 (Suc 0)]\<close>
  shows \<open>ocaps ((snd (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) 2) (1 :: 2) = []\<close>
proof -
  have cap_times:
    \<open>map time (filter (\<lambda>cap. out cap = (1 :: 2)) (map (\<lambda>t. Cap t (1 :: 2)) xs)) = xs\<close> for xs
    by (induct xs) simp_all
  have concat_shift:
    \<open>concat (map (\<lambda>(d, t). [t -+- MyPair 0 (Suc 0)]) xs) =
      map (\<lambda>(d, t). t -+- MyPair 0 (Suc 0)) xs\<close>
    for xs :: \<open>('d \<times> (nat, nat) myprod) list\<close>
    by (induct xs) auto
  show ?thesis
    using H
    unfolding label_prop_input1_loop_updates_def Let_def
    by (simp add: drop_caps_def produces_def fold_consumes cap_times concat_shift
        flip: list_diff_append map_append filter_append)
qed





lemma timestamps_fst_snd_label_prop_input1_loop_updates[simp]:
  \<open>timestamps (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) =
    timestamps os_label_prop\<close>
  unfolding label_prop_input1_loop_updates_def Let_def
  by clarsimp


subsection \<open>Produced progress for label_prop_input1_loop_updates\<close>


lemma produ_fst_snd_label_prop_input1_loop_updates:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os_label_prop_consumed :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes os_label_prop_consumed_def:
    \<open>os_label_prop_consumed =
      CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  shows \<open>produ (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) =
    produ os_label_prop @
      map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
        (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1)))\<close>
  using os_label_prop_consumed_def
  unfolding label_prop_input1_loop_updates_def Let_def
  by (simp add: fold_consumes split_beta split: capability.splits)


subsection \<open>Operational normal forms for label_prop_input1_loop_updates\<close>


lemma label_prop_input1_loop_updates_os2_state:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
  shows \<open>os' 2 =
    drop_caps
      (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2))
        (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
      (map (\<lambda>t. Cap t 1)
        (ocaps (os 2) 1 @
          map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
            (cbufs (2, 1) @ outpu os_label_prop 1)))
      \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>\<close>
  using step[symmetric]
  unfolding label_prop_input1_loop_updates_def Let_def
  by (simp split: prod.splits)


lemma label_prop_input1_loop_updates_consu_os2:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
  shows \<open>consu (os' 2) = consu (os 2) @
    map (\<lambda>(d, t). ((1 :: 2), t, (1 :: int))) (cbufs (2, 1) @ outpu os_label_prop 1)\<close>
proof -
  have os2_eq: \<open>os' 2 =
    drop_caps
      (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2))
        (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
      (map (\<lambda>t. Cap t 1)
        (ocaps (os 2) 1 @
          map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
            (cbufs (2, 1) @ outpu os_label_prop 1)))
      \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>\<close>
    by (rule label_prop_input1_loop_updates_os2_state[OF step])
  show ?thesis
    unfolding os2_eq
    by (simp add: produces_def drop_caps_def fold_consumes split_beta)
qed


lemma label_prop_input1_loop_updates_produ_os2:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
  shows \<open>produ (os' 2) = produ (os 2) @
    map (\<lambda>(d, t). ((1 :: 2), t -+- MyPair 0 (Suc 0), (1 :: int)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
proof -
  have os2_eq: \<open>os' 2 =
    drop_caps
      (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2))
        (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
      (map (\<lambda>t. Cap t 1)
        (ocaps (os 2) 1 @
          map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
            (cbufs (2, 1) @ outpu os_label_prop 1)))
      \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>\<close>
    by (rule label_prop_input1_loop_updates_os2_state[OF step])
  show ?thesis
    unfolding os2_eq
    by (simp add: produces_def drop_caps_def fold_consumes split_beta)
qed


lemma label_prop_input1_loop_updates_inter_os2:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
  shows \<open>inter (os' 2) = inter (os 2) @
    concat (map (\<lambda>(d, t). concat (map (\<lambda>p'. map (\<lambda>t'. ((p' :: 2), t + t', (1 :: int)))
      (intsum (os 2) 1 p')) enum_class.enum))
      (cbufs (2, 1) @ outpu os_label_prop 1)) @
    map (\<lambda>t. ((1 :: 2), t, -(1 :: int))) (ocaps (os 2) 1) @
    map (\<lambda>(d, t). ((1 :: 2), t -+- MyPair 0 (Suc 0), -(1 :: int)))
      (cbufs (2, 1) @ outpu os_label_prop 1)\<close>
proof -
  have os2_eq: \<open>os' 2 =
    drop_caps
      (produces (CONSUMES 1 (cbufs (2, 1) @ outpu os_label_prop 1) (os 2))
        (map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))
      (map (\<lambda>t. Cap t 1)
        (ocaps (os 2) 1 @
          map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
            (cbufs (2, 1) @ outpu os_label_prop 1)))
      \<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>\<close>
    by (rule label_prop_input1_loop_updates_os2_state[OF step])
  show ?thesis
    unfolding os2_eq
    by (simp add: produces_def drop_caps_def fold_consumes split_beta)
qed


lemma label_prop_input1_loop_updates_label_batched:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os_label_prop_consumed :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
    and consumed_def: \<open>os_label_prop_consumed =
      CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  shows \<open>os_label_prop' =
    fst (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))\<close>
  using step[symmetric] consumed_def
  unfolding label_prop_input1_loop_updates_def Let_def
  by (auto split: prod.splits)


lemma label_prop_input1_loop_updates_outpu_label_1_batched:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os_label_prop_consumed :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
    and consumed_def: \<open>os_label_prop_consumed =
      CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  shows \<open>outpu os_label_prop' 1 =
    map (\<lambda>(x, cap). (x, capability.time cap))
      (filter (\<lambda>(x, cap). out cap = (1 :: 2))
        (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))))\<close>
proof -
  have batched: \<open>os_label_prop' =
    fst (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))\<close>
    by (rule label_prop_input1_loop_updates_label_batched[OF step consumed_def])
  have consumed_out_empty: \<open>outpu os_label_prop_consumed 1 = []\<close>
    using consumed_def by (simp add: fold_consumes)
  show ?thesis
    using batched consumed_out_empty
    by (simp add: outpu_fst_label_prop_input1_batched_eq)
qed


lemma label_prop_input1_loop_updates_produ_label:
  fixes os :: \<open>3 \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
    and os_label_prop :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os_label_prop_consumed :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ('d \<times> (nat, nat) myprod) buf\<close>
  assumes step: \<open>label_prop_input1_loop_updates cbufs os_label_prop os = (cbufs', os_label_prop', os')\<close>
    and consumed_def: \<open>os_label_prop_consumed =
      CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  shows \<open>produ os_label_prop' = produ os_label_prop @
    map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
      (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1)))\<close>
proof -
  have \<open>produ (fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))) = produ os_label_prop @
    map (\<lambda>(x, cap). case cap of Cap t p \<Rightarrow> (p, t, 1))
      (snd (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1)))\<close>
    using consumed_def
    by (rule produ_fst_snd_label_prop_input1_loop_updates
        [where os_label_prop_consumed = os_label_prop_consumed
          and cbufs = cbufs
          and os_label_prop = os_label_prop
          and os = os])
  then show ?thesis
    using step by simp
qed


lemma fst_label_prop_input1_loop_updates_update[simp]:
  \<open>fst (label_prop_input1_loop_updates cbufs os_label_prop (os(n := X))) =
    fst (label_prop_input1_loop_updates cbufs os_label_prop os)\<close>
  unfolding label_prop_input1_loop_updates_def
  by clarsimp


lemma fst_snd_label_prop_input1_loop_updates_update[simp]:
  assumes n2: \<open>n \<noteq> (2 :: 3)\<close>
  shows \<open>fst (snd (label_prop_input1_loop_updates cbufs os_label_prop (os(n := X)))) =
    fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))\<close>
  using n2
  unfolding label_prop_input1_loop_updates_def
  by clarsimp


lemma snd_snd_label_prop_input1_loop_updates_unchanged[simp]:
  assumes n2: \<open>n \<noteq> (2 :: 3)\<close>
  shows \<open>snd (snd (label_prop_input1_loop_updates cbufs os_label_prop os)) n = os n\<close>
  using n2
  unfolding label_prop_input1_loop_updates_def
  by clarsimp




lemma snd_snd_label_prop_input1_loop_updates_update[simp]:
  assumes nm: \<open>n \<noteq> m\<close>
  shows \<open>snd (snd (label_prop_input1_loop_updates cbufs os_label_prop (os(n := X)))) m =
    snd (snd (label_prop_input1_loop_updates cbufs os_label_prop os)) m\<close>
  using nm
  unfolding label_prop_input1_loop_updates_def
  by clarsimp


lemma fst_label_prop_input1_loop_updates_cbufs_cleared[simp]:
  assumes k: \<open>k = (((1 :: 3), (1 :: 2))) \<or> k = (((2 :: 3), (1 :: 2)))\<close>
  shows \<open>fst (label_prop_input1_loop_updates (cbufs(k := X)) os_label_prop os) =
    fst (label_prop_input1_loop_updates cbufs os_label_prop os)\<close>
  using k
  unfolding label_prop_input1_loop_updates_def
  by (auto simp add: fun_upd_twist)



lemma fst_snd_label_prop_input1_loop_updates_cbufs_irrelevant[simp]:
  assumes k11: \<open>k \<noteq> (((1 :: 3), (1 :: 2)))\<close>
    and k21: \<open>k \<noteq> (((2 :: 3), (1 :: 2)))\<close>
  shows \<open>fst (snd (label_prop_input1_loop_updates (cbufs(k := X)) os_label_prop os)) =
    fst (snd (label_prop_input1_loop_updates cbufs os_label_prop os))\<close>
  using k11 k21
  unfolding label_prop_input1_loop_updates_def
  by clarsimp


lemma snd_snd_label_prop_input1_loop_updates_cbufs_irrelevant[simp]:
  assumes k21: \<open>k \<noteq> (((2 :: 3), (1 :: 2)))\<close>
  shows \<open>snd (snd (label_prop_input1_loop_updates (cbufs(k := X)) os_label_prop os)) =
    snd (snd (label_prop_input1_loop_updates cbufs os_label_prop os))\<close>
  using k21
  unfolding label_prop_input1_loop_updates_def
  by clarsimp




section \<open>Dataplane invariant transfer lemmas\<close>


lemma dataplane_tracker_inv_outpu_then_fold_consumes:
  fixes os :: \<open>'nid :: {linorder,enum} \<Rightarrow> ('p :: {linorder,enum}, 'd, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) operator_state\<close>
    and cbufs :: \<open>'nid \<times> 'p \<Rightarrow> ('d \<times> 't) buf\<close>
    and sg :: \<open>('nid, 'p, 't) subgraph\<close>
  assumes Inv: \<open>dataplane_tracker_inv os cbufs sg\<close>
    and D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and GR: \<open>graph_summar_nt (summ sg) (nxt sg) os\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and edge: \<open>summ sg (Loc nid_up (Src p_up)) (Loc nid_dn (Trg p_dn)) \<noteq> {}\<^sub>A\<close>
    and nid_neq: \<open>nid_up \<noteq> nid_dn\<close>
  shows
    \<open>dataplane_tracker_inv
       (os(nid_up := (os nid_up)\<lparr>outpu := (outpu (os nid_up))(p_up := [])\<rparr>,
           nid_dn := fold (\<lambda>(d, t) s. consumes s p_dn t d)
                       (cbufs (nid_dn, p_dn) @ outpu (os nid_up) p_up)
                       (os nid_dn)))
       (cbufs((nid_dn, p_dn) := []))
       sg\<close>
proof -
  let ?os1 = "os(nid_up := (os nid_up)\<lparr>outpu := (outpu (os nid_up))(p_up := [])\<rparr>)"
  let ?cb1 = "cbufs((nid_dn, p_dn) := cbufs (nid_dn, p_dn) @ outpu (os nid_up) p_up)"
  have outpu_split: "outpu (os nid_up) p_up = outpu (os nid_up) p_up @ []"
    by simp
  have os1_eq: "?os1 = os(nid_up := (os nid_up)\<lparr>outpu :=
                 (\<lambda>p'. if p' = p_up then [] else outpu (os nid_up) p')\<rparr>)"
    by (auto simp: fun_upd_def)
  have inv1: "dataplane_tracker_inv ?os1 ?cb1 sg"
    apply (rule dataplane_tracker_inv_update_outputs
        [where nid=nid_up and p=p_up and xs="outpu (os nid_up) p_up" and ys="[]"
          and nid'=nid_dn and p'=p_dn])
    apply (rule Inv)
    apply (rule outpu_split)
    apply (simp add: fun_upd_def)
    apply simp
    apply (rule edge)
    apply (rule GR)
    done
  have GR1: "graph_summar_nt (summ sg) (nxt sg) ?os1"
    using GR by (auto simp: graph_summar_nt_def)
  let ?L = "cbufs (nid_dn, p_dn) @ outpu (os nid_up) p_up"
  let ?os2 = "?os1(nid_dn := fold (\<lambda>(d, t) s. consumes s p_dn t d) ?L (?os1 nid_dn))"
  let ?cb2 = "(\<lambda>(nid', p'). if nid' = nid_dn \<and> p' = p_dn then drop (length ?L) (?cb1 (nid_dn, p_dn))
                            else ?cb1 (nid', p'))"
  have len_le: "length ?L \<le> length (?cb1 (nid_dn, p_dn))"
    by simp
  have inv2: "dataplane_tracker_inv ?os2 ?cb2 sg"
    apply (rule dataplane_tracker_inv_fold_consumes
        [where os="?os1" and cbufs="?cb1" and nid=nid_dn and p=p_dn and n="length ?L"])
    apply (rule inv1)
    apply (rule D)
    apply (rule GR1)
    apply (rule len_le)
    apply (rule refl)
    apply simp
    done
  have take_all_eq: "take (length ?L) (?cb1 (nid_dn, p_dn)) = ?L"
    by (simp add: take_all)
  have drop_all_eq: "drop (length ?L) (?cb1 (nid_dn, p_dn)) = []"
    by simp
  have cb2_eq: "?cb2 = cbufs((nid_dn, p_dn) := [])"
    using drop_all_eq nid_neq
    by (auto simp: fun_eq_iff fun_upd_def split: prod.splits)
  have os1_dn: "?os1 nid_dn = os nid_dn"
    using nid_neq by simp
  have os2_eq: "?os2 = os(nid_up := (os nid_up)\<lparr>outpu := (outpu (os nid_up))(p_up := [])\<rparr>,
                          nid_dn := fold (\<lambda>(d, t) s. consumes s p_dn t d) ?L (os nid_dn))"
    using os1_dn by (simp add: fun_upd_def fun_eq_iff)
  show ?thesis
    using inv2 unfolding os2_eq cb2_eq .
qed


lemma dataplane_tracker_inv_produces_drops_dropcaps_shape:
  fixes caps_to_drop :: \<open>('p :: {enum,linorder}, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) capability list\<close>
  assumes D: \<open>dataflow_topology (summ sg) (-+-)\<close>
  shows
    \<open>noutput = (\<lambda>p. outpu (os nid) p @ oputs p) \<Longrightarrow>
     nocaps = (\<lambda>p. list_diff (ocaps (os nid) p)
                              (map capability.time (filter (\<lambda>c. out c = p) caps_to_drop))) \<Longrightarrow>
     ninput = (\<lambda>p. filter (\<lambda>(_, t). t \<notin> set (map capability.time (filter (\<lambda>c. out c = p) caps_to_drop)))
                          (input (os nid) p)) \<Longrightarrow>
     nprodu = produ (os nid) @ produs \<Longrightarrow>
     ninter = operator_state.inter (os nid)
              @ map (\<lambda>cap. (out cap, capability.time cap, - 1)) caps_to_drop \<Longrightarrow>
     (\<forall>p'. mset (map capability.time (filter (\<lambda>c. out c = p') caps_to_drop))
            \<subseteq># mset (ocaps (os nid) p')) \<Longrightarrow>
     (\<forall>(p, t, m) \<in> set produs. m > 0 \<and> t \<in> set (ocaps (os nid) p)) \<Longrightarrow>
     (\<forall>p. snd ` set (oputs p) \<subseteq> set (ocaps (os nid) p)) \<Longrightarrow>
     (\<forall>p. to_zmset (map snd (oputs p)) = zmset (map snd (filter (\<lambda>x. p = fst x) produs))) \<Longrightarrow>
     graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
     nxt sg = graph_to_nxt (summ sg) \<Longrightarrow>
     dataplane_tracker_inv os cbufs sg \<Longrightarrow>
     dataplane_tracker_inv (os(nid := os nid \<lparr>outpu := noutput, ocaps := nocaps,
        input := ninput, produ := nprodu, inter := ninter\<rparr>)) cbufs sg\<close>
proof -
  assume NOut: "noutput = (\<lambda>p. outpu (os nid) p @ oputs p)"
  assume NOcaps: "nocaps = (\<lambda>p. list_diff (ocaps (os nid) p)
                                  (map capability.time (filter (\<lambda>c. out c = p) caps_to_drop)))"
  assume NInput: "ninput = (\<lambda>p. filter (\<lambda>(_, t). t \<notin> set (map capability.time
                                          (filter (\<lambda>c. out c = p) caps_to_drop)))
                                       (input (os nid) p))"
  assume NProdu: "nprodu = produ (os nid) @ produs"
  assume NInter: "ninter = operator_state.inter (os nid)
                          @ map (\<lambda>cap. (out cap, capability.time cap, - 1)) caps_to_drop"
  assume Drops: "\<forall>p'. mset (map capability.time (filter (\<lambda>c. out c = p') caps_to_drop))
                       \<subseteq># mset (ocaps (os nid) p')"
  assume Produs: "\<forall>(p, t, m) \<in> set produs. m > 0 \<and> t \<in> set (ocaps (os nid) p)"
  assume Oputs: "\<forall>p. snd ` set (oputs p) \<subseteq> set (ocaps (os nid) p)"
  assume OPZ: "\<forall>p. to_zmset (map snd (oputs p)) = zmset (map snd (filter (\<lambda>x. p = fst x) produs))"
  assume G: "graph_summar_nt (summ sg) (nxt sg) os"
  assume Nxt: "nxt sg = graph_to_nxt (summ sg)"
  assume Inv: "dataplane_tracker_inv os cbufs sg"

  define drops :: "'p \<Rightarrow> 't list"
    where "drops = (\<lambda>p. map capability.time (filter (\<lambda>c. out c = p) caps_to_drop))"

  let ?ninter_concat = "operator_state.inter (os nid)
                        @ concat (map (\<lambda>p. map (\<lambda>t. (p, t, - 1 :: int)) (drops p)) Enum.enum)"

  let ?osPD = "os(nid := (os nid)\<lparr>outpu := noutput, ocaps := nocaps,
                                   input := ninput, produ := nprodu, inter := ?ninter_concat\<rparr>)"

  have NOcaps': "nocaps = (\<lambda>p. list_diff (ocaps (os nid) p) (drops p))"
    using NOcaps by (simp add: drops_def)
  have NInput': "ninput = (\<lambda>p. filter (\<lambda>(_, t). t \<notin> set (drops p)) (input (os nid) p))"
    using NInput by (simp add: drops_def)
  have Drops': "\<forall>p. mset (drops p) \<subseteq># mset (ocaps (os nid) p)"
    using Drops by (simp add: drops_def)

  have inv_PD: "dataplane_tracker_inv ?osPD cbufs sg"
    by (rule dataplane_tracker_inv_produces_drops[OF D NOut NOcaps' NInput' NProdu refl
          Drops' Produs Oputs OPZ G Nxt Inv])

  have group_caps:
    "mset (concat (map (\<lambda>p. map (\<lambda>t. (p, t, - 1 :: int))
                           (map capability.time (filter (\<lambda>c. out c = p) cs))) Enum.enum)) =
     mset (map (\<lambda>cap. (out cap, capability.time cap, - 1)) cs)" for cs :: "('p, 't) capability list"
  proof (induct cs)
    case Nil
    show ?case by simp
  next
    case (Cons c cs)
    let ?f = "\<lambda>p. map (\<lambda>t. (p, t, - 1 :: int)) (map capability.time (filter (\<lambda>c'. out c' = p) cs))"
    have rewrite:
      "concat (map (\<lambda>p. map (\<lambda>t. (p, t, - 1 :: int))
                            (map capability.time (filter (\<lambda>c'. out c' = p) (c # cs)))) Enum.enum)
       = concat (map (\<lambda>p. (if out c = p then [(p, capability.time c, - 1 :: int)] else []) @ ?f p)
                      Enum.enum)"
      by (rule arg_cong[where f=concat], rule map_cong[OF refl], simp)
    have enum_pick:
      "mset (concat (map (\<lambda>p :: 'p. if out c = p then [(p, capability.time c, - 1 :: int)] else [])
                          Enum.enum))
       = {#(out c, capability.time c, - 1)#}"
    proof -
      have aux: "distinct ps \<Longrightarrow> out c \<in> set ps \<Longrightarrow>
        mset (concat (map (\<lambda>p :: 'p. if out c = p then [(p, capability.time c, - 1 :: int)] else []) ps))
        = {#(out c, capability.time c, - 1)#}" for ps
        by (induct ps) auto
      show ?thesis
        by (rule aux[OF Enum.enum_class.enum_distinct Enum.enum_class.in_enum])
    qed
    show ?case
    proof -
      have split_mset_aux:
        "mset (concat (map (\<lambda>p. A p @ B p) ps)) =
         mset (concat (map A ps)) + mset (concat (map B ps))" for A B and ps :: "'p list"
        by (induct ps) simp_all
      have split_mset:
        "mset (concat (map (\<lambda>p. (if out c = p then [(p, capability.time c, - 1 :: int)] else []) @ ?f p) Enum.enum)) =
         mset (concat (map (\<lambda>p. if out c = p then [(p, capability.time c, - 1 :: int)] else []) Enum.enum)) +
         mset (concat (map ?f Enum.enum))"
        by (rule split_mset_aux)

      have "mset (concat (map (\<lambda>p. map (\<lambda>t. (p, t, - 1 :: int))
                            (map capability.time (filter (\<lambda>c'. out c' = p) (c # cs)))) Enum.enum)) =
        mset (concat (map (\<lambda>p. (if out c = p then [(p, capability.time c, - 1 :: int)] else []) @ ?f p)
                      Enum.enum))"
        using rewrite by simp
      also have "... = {#(out c, capability.time c, - 1)#} +
        mset (map (\<lambda>cap. (out cap, capability.time cap, - 1)) cs)"
        using split_mset enum_pick Cons.hyps by simp
      also have "... = mset (map (\<lambda>cap. (out cap, capability.time cap, - 1)) (c # cs))"
        by simp
      finally show ?thesis .
    qed


  qed

  have inter_mset_eq:
    "mset (operator_state.inter (?osPD nid)) = mset (operator_state.inter (?osPD nid \<lparr>inter := ninter\<rparr>))"
    using group_caps[of caps_to_drop] NInter by (simp add: drops_def)

  let ?osTarget = "os(nid := (os nid)\<lparr>outpu := noutput, ocaps := nocaps,
                                       input := ninput, produ := nprodu, inter := ninter\<rparr>)"

  have all_fields_match:
    "\<forall>nid'. intsum (?osTarget nid') = intsum (?osPD nid') \<and>
            ocaps (?osTarget nid') = ocaps (?osPD nid') \<and>
            consu (?osTarget nid') = consu (?osPD nid') \<and>
            mset (operator_state.inter (?osTarget nid')) = mset (operator_state.inter (?osPD nid')) \<and>
            produ (?osTarget nid') = produ (?osPD nid') \<and>
            outpu (?osTarget nid') = outpu (?osPD nid') \<and>
            front (?osTarget nid') = front (?osPD nid')"
    apply (intro allI conjI)
    subgoal for nid' by simp
    subgoal for nid' by simp
    subgoal for nid' by simp
    subgoal for nid' using group_caps[of caps_to_drop] NInter
      by (cases "nid' = nid") (simp_all add: drops_def)
    subgoal for nid' by simp
    subgoal for nid' by simp
    subgoal for nid' by simp
    done

  show ?thesis
    using inv_PD dataplane_tracker_inv_clean_reorder_inter[OF all_fields_match]
    by blast
qed


lemma dataplane_tracker_inv_produces_drop:
  fixes os :: \<open>'nid :: {linorder,enum} \<Rightarrow> ('p :: {linorder,enum}, 'd, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) operator_state\<close>
    and cbufs :: \<open>'nid \<times> 'p \<Rightarrow> ('d \<times> 't) buf\<close>
    and sg :: \<open>('nid, 'p, 't) subgraph\<close>
  assumes Inv: \<open>dataplane_tracker_inv (os(nid := s1)) cbufs sg\<close>
    and D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and GR: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := s1))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and batch_caps_exact:
    \<open>\<And>x cap. (x, cap) \<in> set batch \<Longrightarrow>
        capability.time cap \<in> set (ocaps s1 (out cap))\<close>
    and drops_subset_per_port:
    \<open>\<And>p'. mset (map capability.time (filter (\<lambda>c. out c = p') caps_to_drop)) \<subseteq>#
            mset (ocaps s1 p')\<close>
    and drops_disjoint_input:
    \<open>\<And>p'. set (map capability.time (filter (\<lambda>c. out c = p') caps_to_drop)) \<inter>
            snd ` set (input s1 p') = {}\<close>
  shows
    \<open>dataplane_tracker_inv
       (os(nid := drop_caps (produces s1 batch) caps_to_drop))
       cbufs sg\<close>
proof -
  let ?os0 = \<open>os(nid := s1)\<close>
  let ?oputs = \<open>\<lambda>p. map (\<lambda>(x, cap). (x, capability.time cap))
    (filter (\<lambda>(x, cap). out cap = p) batch)\<close>
  let ?produs = \<open>map (\<lambda>(x, cap). (out cap, capability.time cap, 1 :: int)) batch\<close>
  let ?drop_times = \<open>\<lambda>p. map capability.time (filter (\<lambda>c. out c = p) caps_to_drop)\<close>

  have input_filter:
    \<open>input s1 = (\<lambda>p. filter (\<lambda>(_, t). t \<notin> set (?drop_times p)) (input s1 p))\<close>
  proof (rule ext)
    fix p
    have all_not: \<open>\<forall>x\<in>set (input s1 p). case x of (_, t) \<Rightarrow> t \<notin> set (?drop_times p)\<close>
      using drops_disjoint_input[of p]
      by auto
    show \<open>input s1 p = filter (\<lambda>(_, t). t \<notin> set (?drop_times p)) (input s1 p)\<close>
      by (rule sym, subst filter_id_conv) (use all_not in auto)
  qed

  have Produs: \<open>\<forall>(p, t, m) \<in> set ?produs. m > 0 \<and> t \<in> set (ocaps (?os0 nid) p)\<close>
    using batch_caps_exact
    by (auto split: prod.splits capability.splits)

  have Oputs: \<open>\<forall>p. snd ` set (?oputs p) \<subseteq> set (ocaps (?os0 nid) p)\<close>
    using batch_caps_exact
    by (auto split: prod.splits capability.splits)

  have OPZ:
    \<open>\<forall>p. to_zmset (map snd (?oputs p)) =
      zmset (map snd (filter (\<lambda>x. p = fst x) ?produs))\<close>
  proof
    fix p
    have rhs:
      \<open>map snd (filter (\<lambda>x. p = fst x) ?produs) =
        map (\<lambda>(x, cap). (capability.time cap, 1 :: int))
          (filter (\<lambda>(x, cap). out cap = p) batch)\<close>
      by (induct batch) (auto simp: split_beta)
    have lhs_to:
      \<open>to_zmset (map snd (?oputs p)) =
        to_zmset (map (\<lambda>(x, cap). capability.time cap)
          (filter (\<lambda>(x, cap). out cap = p) batch))\<close>
      by (induct batch) (auto simp: split_beta)
    have zm:
      \<open>zmset (map (\<lambda>(x, cap). (capability.time cap, 1 :: int))
          (filter (\<lambda>(x, cap). out cap = p) batch)) =
        to_zmset (map (\<lambda>(x, cap). capability.time cap)
          (filter (\<lambda>(x, cap). out cap = p) batch))\<close>
      by (induct \<open>filter (\<lambda>(x, cap). out cap = p) batch\<close>) (auto simp: split_beta)
    show \<open>to_zmset (map snd (?oputs p)) =
      zmset (map snd (filter (\<lambda>x. p = fst x) ?produs))\<close>
      using lhs_to rhs zm by simp
  qed

  have inv_shape:
    \<open>dataplane_tracker_inv
      (?os0(nid := (?os0 nid)\<lparr>
        outpu := (\<lambda>p. outpu (?os0 nid) p @ ?oputs p),
        ocaps := (\<lambda>p. list_diff (ocaps (?os0 nid) p) (?drop_times p)),
        input := input s1,
        produ := produ (?os0 nid) @ ?produs,
        inter := operator_state.inter (?os0 nid) @
          map (\<lambda>cap. (out cap, capability.time cap, - 1)) caps_to_drop\<rparr>))
      cbufs sg\<close>
    apply (rule dataplane_tracker_inv_produces_drops_dropcaps_shape[OF D])
    apply (rule refl)
    apply (rule refl)
    apply (subst fun_upd_same)
    apply (rule input_filter)
    apply (rule refl)
    apply (rule refl)
    apply (rule allI)
    apply (subst fun_upd_same)
    apply (rule drops_subset_per_port)
    apply (rule Produs)
    apply (rule Oputs)
    apply (rule OPZ)
    apply (rule GR)
    apply (rule Nxt)
    apply (rule Inv)
    done

  have target_eq:
    \<open>os(nid := drop_caps (produces s1 batch) caps_to_drop) =
     ?os0(nid := (?os0 nid)\<lparr>
        outpu := (\<lambda>p. outpu (?os0 nid) p @ ?oputs p),
        ocaps := (\<lambda>p. list_diff (ocaps (?os0 nid) p) (?drop_times p)),
        input := input s1,
        produ := produ (?os0 nid) @ ?produs,
        inter := operator_state.inter (?os0 nid) @
          map (\<lambda>cap. (out cap, capability.time cap, - 1)) caps_to_drop\<rparr>)\<close>
    unfolding drop_caps_def produces_def
    by (cases s1) simp

  show ?thesis
    using inv_shape target_eq by simp
qed


section \<open>Base-state projection\<close>


subsection \<open>Input capability preservation for input-1 batches\<close>


lemma label_prop_input1_step_batch_caps:
  fixes os :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
  assumes IOC: \<open>input_ocaps_inv os\<close>
    and zero: \<open>0 \<in> set (intsum os 1 1)\<close>
    and input: \<open>(d, t) \<in> set (input os 1)\<close>
    and member: \<open>(x, cap) \<in> set (label_prop_input1_step_batch os d t)\<close>
  shows \<open>\<exists>t'\<in>set (ocaps os (out cap)). t' \<le> capability.time cap\<close>
  using member input IOC zero
  unfolding label_prop_input1_step_batch_def label_prop_label_batch_def
    label_prop_neighbor_batch_def input_ocaps_inv_def
  apply (auto simp add: zero_myprod_def less_eq_myprod_def split: if_splits)
  subgoal for cur_t v
    apply (rule bexI[where x=t])
    apply (cases t; simp add: less_eq_myprod_def)
    apply force
    done
  done


lemma input_ocaps_inv_label_prop_input1_step_stateI:
  assumes \<open>input_ocaps_inv os\<close>
  shows \<open>input_ocaps_inv (label_prop_input1_step_state os d t)\<close>
  unfolding label_prop_input1_step_state_def Let_def
  apply (rule input_ocaps_inv_release_capsI)
  apply (rule input_ocaps_inv_drop_produces_add_capsI)
  apply (rule input_ocaps_inv_label_prop_label_record_updateI)
  apply (rule input_ocaps_inv_input_tlI)
  apply (rule assms)
  done


lemma input_ocaps_inv_fst_label_prop_input1_batchedI:
  assumes \<open>input_ocaps_inv os\<close>
  shows \<open>input_ocaps_inv (fst (label_prop_input1_batched os msgs))\<close>
  using assms
proof (induct msgs arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons msg msgs)
  obtain d t where msg_eq: \<open>msg = (d, t)\<close>
    by (cases msg)
  have step_inv: \<open>input_ocaps_inv (label_prop_input1_step_state os d t)\<close>
    by (rule input_ocaps_inv_label_prop_input1_step_stateI[OF Cons.prems])
  obtain os_final batches where rec:
    \<open>label_prop_input1_batched (label_prop_input1_step_state os d t) msgs = (os_final, batches)\<close>
    by (cases \<open>label_prop_input1_batched (label_prop_input1_step_state os d t) msgs\<close>)
  show ?case
    using Cons.hyps[OF step_inv] msg_eq rec
    by simp

qed



subsection \<open>Dataplane preservation for input-1 batches\<close>


lemma dataplane_tracker_inv_input_update:
  assumes \<open>dataplane_tracker_inv os cbufs sg\<close>
  shows \<open>dataplane_tracker_inv (os(nid := (os nid)\<lparr>input := inp\<rparr>)) cbufs sg\<close>
proof -
  have fields: \<open>\<forall>nid'. intsum (os nid') = intsum ((os(nid := (os nid)\<lparr>input := inp\<rparr>)) nid') \<and>
    ocaps (os nid') = ocaps ((os(nid := (os nid)\<lparr>input := inp\<rparr>)) nid') \<and>
    consu (os nid') = consu ((os(nid := (os nid)\<lparr>input := inp\<rparr>)) nid') \<and>
    operator_state.inter (os nid') = operator_state.inter ((os(nid := (os nid)\<lparr>input := inp\<rparr>)) nid') \<and>
    produ (os nid') = produ ((os(nid := (os nid)\<lparr>input := inp\<rparr>)) nid') \<and>
    outpu (os nid') = outpu ((os(nid := (os nid)\<lparr>input := inp\<rparr>)) nid') \<and>
    front (os nid') = front ((os(nid := (os nid)\<lparr>input := inp\<rparr>)) nid')\<close>
    by (auto split: if_splits)
  show ?thesis
    using iffD1[OF dataplane_tracker_inv_clean_input[OF fields] assms] .
qed


lemma dataplane_tracker_inv_label_prop_input1_step_state:
  fixes ls :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>'nid :: {enum, linorder} \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
  assumes D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and Inv: \<open>dataplane_tracker_inv (os(nid := op_state_base ls)) cbufs sg\<close>
    and G: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and IOC: \<open>input_ocaps_inv ls\<close>
    and zero: \<open>0 \<in> set (intsum ls 1 1)\<close>
    and input: \<open>input ls 1 = (d, t) # xs\<close>
  shows \<open>dataplane_tracker_inv (os(nid := op_state_base (label_prop_input1_step_state ls d t))) cbufs sg\<close>
proof -
  let ?ls1 = \<open>input_tl ls 1\<close>
  let ?ls2 = \<open>label_prop_label_record_update ?ls1 (myfst t) (fst (de1 ls d))
    (min (min_label ls (myfst t) (fst (de1 ls d))) (snd (de1 ls d)))\<close>
  let ?batch = \<open>label_prop_input1_step_batch ls d t\<close>
  have inv_base2: \<open>dataplane_tracker_inv (os(nid := op_state_base ?ls2)) cbufs sg\<close>
  proof -
    have fields: \<open>\<forall>nid'. intsum ((os(nid := op_state_base ls)) nid') = intsum ((os(nid := op_state_base ?ls2)) nid') \<and>
      ocaps ((os(nid := op_state_base ls)) nid') = ocaps ((os(nid := op_state_base ?ls2)) nid') \<and>
      consu ((os(nid := op_state_base ls)) nid') = consu ((os(nid := op_state_base ?ls2)) nid') \<and>
      inter ((os(nid := op_state_base ls)) nid') = inter ((os(nid := op_state_base ?ls2)) nid') \<and>
      produ ((os(nid := op_state_base ls)) nid') = produ ((os(nid := op_state_base ?ls2)) nid') \<and>
      outpu ((os(nid := op_state_base ls)) nid') = outpu ((os(nid := op_state_base ?ls2)) nid') \<and>
      front ((os(nid := op_state_base ls)) nid') = front ((os(nid := op_state_base ?ls2)) nid')\<close>
      by (auto simp add: op_state_base_def input_tl_def label_prop_label_record_update_def)
    show ?thesis
      using iffD1[OF dataplane_tracker_inv_clean_input[OF fields] Inv] .
  qed
  have G_base2: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls2))\<close>
  proof -
    have geq: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls2)) =
      graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
      by (rule graph_summar_nt_intsum_cong) (simp add: op_state_base_def input_tl_def label_prop_label_record_update_def)
    show ?thesis
      using geq G by simp
  qed
  have input_member: \<open>(d, t) \<in> set (input ls 1)\<close>
    using input by simp
  have batch_caps: \<open>\<And>x cap. (x, cap) \<in> set ?batch \<Longrightarrow>
    \<exists>t'\<in>set (ocaps (op_state_base ?ls2) (out cap)). t' \<le> capability.time cap\<close>
    using label_prop_input1_step_batch_caps[OF IOC zero input_member]
    by (simp add: op_state_base_def input_tl_def label_prop_label_record_update_def)
  have inv_drop:
    \<open>dataplane_tracker_inv
      (os(nid := drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch)))
      cbufs sg\<close>
    by (rule dataplane_tracker_inv_add_caps_produces_drop_caps_update[OF D inv_base2 G_base2 Nxt batch_caps])
  have G_drop:
    \<open>graph_summar_nt (summ sg) (nxt sg)
      (os(nid := drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch)))\<close>
  proof -
    have geq: \<open>graph_summar_nt (summ sg) (nxt sg)
      (os(nid := drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch))) =
      graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls2))\<close>
      by (rule graph_summar_nt_intsum_cong) (simp add: drop_caps_def produces_def add_caps_def)
    show ?thesis
      using geq G_base2 by simp
  qed
  have inv_release:
    \<open>dataplane_tracker_inv
      (os(nid := release_caps (drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch)) 1))
      cbufs sg\<close>
    by (rule dataplane_tracker_inv_release_caps_update[OF D inv_drop G_drop Nxt])
  have step_base:
    \<open>op_state_base (label_prop_input1_step_state ls d t) =
      release_caps (drop_caps (produces (add_caps (op_state_base ?ls2) (map snd ?batch)) ?batch) (map snd ?batch)) 1\<close>
    unfolding label_prop_input1_step_state_def label_prop_input1_step_batch_def Let_def
    by simp
  show ?thesis
    using inv_release by (simp add: step_base)
qed

lemma dataplane_tracker_inv_label_prop_input1_batched:
  fixes ls :: \<open>('d, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>'nid :: {enum, linorder} \<Rightarrow> (2, 'd, (nat, nat) myprod) operator_state\<close>
  assumes D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and Inv: \<open>dataplane_tracker_inv (os(nid := op_state_base ls)) cbufs sg\<close>
    and G: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and IOC: \<open>input_ocaps_inv ls\<close>
    and zero: \<open>0 \<in> set (intsum ls 1 1)\<close>
  shows \<open>dataplane_tracker_inv
    (os(nid := op_state_base (fst (label_prop_input1_batched ls (input ls 1))))) cbufs sg\<close>
proof -
  have aux:
    \<open>msgs = input ls 1 \<Longrightarrow>
      dataplane_tracker_inv (os(nid := op_state_base ls)) cbufs sg \<Longrightarrow>
      graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls)) \<Longrightarrow>
      input_ocaps_inv ls \<Longrightarrow>
      0 \<in> set (intsum ls 1 1) \<Longrightarrow>
      dataplane_tracker_inv
        (os(nid := op_state_base (fst (label_prop_input1_batched ls (input ls 1))))) cbufs sg\<close>
    for msgs ls
  proof (induct msgs arbitrary: ls)
    case Nil
    then show ?case by simp
  next
    case (Cons msg msgs)
    obtain d t where msg_eq: \<open>msg = (d, t)\<close>
      by (cases msg)
    have input_eq: \<open>input ls 1 = (d, t) # msgs\<close>
      using Cons.prems(1) msg_eq by simp
    let ?ls' = \<open>label_prop_input1_step_state ls d t\<close>
    have inv_step: \<open>dataplane_tracker_inv (os(nid := op_state_base ?ls')) cbufs sg\<close>
      by (rule dataplane_tracker_inv_label_prop_input1_step_state[OF D Cons.prems(2) Cons.prems(3) Nxt Cons.prems(4) Cons.prems(5) input_eq])
    have G_step: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls'))\<close>
    proof -
      have geq: \<open>graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ?ls')) =
        graph_summar_nt (summ sg) (nxt sg) (os(nid := op_state_base ls))\<close>
        by (rule graph_summar_nt_intsum_cong) (simp add: label_prop_input1_step_state_def Let_def op_state_base_def)
      show ?thesis
        using geq Cons.prems(3) by simp
    qed
    have IOC_step: \<open>input_ocaps_inv ?ls'\<close>
      by (rule input_ocaps_inv_label_prop_input1_step_stateI[OF Cons.prems(4)])
    have zero_step: \<open>0 \<in> set (intsum ?ls' 1 1)\<close>
      using Cons.prems(5) by simp
    have input_step: \<open>msgs = input ?ls' 1\<close>
      using input_eq by simp
    have rec: \<open>dataplane_tracker_inv
      (os(nid := op_state_base (fst (label_prop_input1_batched ?ls' (input ?ls' 1))))) cbufs sg\<close>
      by (rule Cons.hyps[OF input_step inv_step G_step IOC_step zero_step])
    obtain ls_final batches where rec_eq:
      \<open>label_prop_input1_batched ?ls' msgs = (ls_final, batches)\<close>
      by (cases \<open>label_prop_input1_batched ?ls' msgs\<close>)
    show ?case
      using rec input_eq msg_eq rec_eq by (simp add: fun_upd_def)
  qed
  show ?thesis
    by (rule aux[OF refl Inv G IOC zero])
qed

subsection \<open>Dataplane preservation for input-0 batches\<close>


lemma label_prop_input1_loop_updates_preserves_dataplane_tracker_inv:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and sg :: \<open>(3, 2, (nat, nat) myprod) subgraph\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  assumes step:
    \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and GR: \<open>graph_summar_nt (summ sg) (nxt sg) os\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and Inv: \<open>dataplane_tracker_inv os cbufs sg\<close>
    and label_prop_extension:
    \<open>os_label_prop = operator_state.extend (os 1) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
    and Summ: \<open>summ sg = antichain_from_list \<circ>\<circ> raw_summary\<close>
    and Intsum: \<open>\<forall>n. intsum (os n) = (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    and IOC1: \<open>input_ocaps_inv (os 1)\<close>
    and IOC2: \<open>input_ocaps_inv (os 2)\<close>
  shows \<open>dataplane_tracker_inv (os'(1 := op_state_base os_label_prop')) cbufs' sg\<close>

proof -
  define b1 where "b1 = cbufs (1, 1)"

  define b21 where "b21 = cbufs (2, 1)"

  define out1 where "out1 = outpu os_label_prop 1"

  define in21 where "in21 = input (os 2) 1"

  define inc where "inc = MyPair (0 :: nat) (Suc 0)"
  define ts_caps2_extra where "ts_caps2_extra = map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- inc) (b21 @ out1)"

  define ts_drop where "ts_drop = ocaps (os 2) 1 @ ts_caps2_extra"

  define batch where "batch = map (\<lambda>x. (fst x, Cap (snd x -+- inc) (1 :: 2))) (in21 @ b21 @ out1)"

  define os2_consumed where "os2_consumed = CONSUMES 1 (b21 @ out1) (os 2)"

  define os2_after_prod where "os2_after_prod = produces os2_consumed batch"

  define os2_after_drop where "os2_after_drop = drop_caps os2_after_prod (map (\<lambda>t. Cap t 1) ts_drop)"

  define os2' where
    "os2' = os2_after_drop\<lparr>outpu := (outpu (os 2))(1 := []), input := (input (os 2))(1 := [])\<rparr>"


  have cbufs'_eq: "cbufs' = cbufs((2, 1) := [], (1, 1) := [])"
    and os'_eq: "os' = os(2 := os2')"
    using step
    unfolding label_prop_input1_loop_updates_def Let_def
      os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
      ts_drop_def ts_caps2_extra_def batch_def
      b21_def out1_def in21_def inc_def
    by (simp_all split: prod.splits)

  define os_label_prop_consumed where
    "os_label_prop_consumed = CONSUMES 1
      (b1 @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- inc)) (in21 @ b21 @ out1))
      (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)"


  have base_label_prop: "op_state_base os_label_prop = os 1"
    using label_prop_extension
    unfolding op_state_base_def
    by (simp add: operator_state.defs)

  have IOC_label_prop: "input_ocaps_inv os_label_prop"
    using IOC1 label_prop_extension
    unfolding input_ocaps_inv_def
    by (simp add: operator_state.defs)

  have zero_label_prop: "0 \<in> set (intsum os_label_prop 1 1)"
    using Intsum label_prop_extension
    by (simp add: raw_summary_def zero_myprod_def operator_state.defs)

  have out1_eq: "out1 = outpu (os 1) 1"
    using label_prop_extension by (simp add: out1_def operator_state.defs)

  have edge12: "summ sg (Loc (1 :: 3) (Src (1 :: 2))) (Loc (2 :: 3) (Trg (1 :: 2))) \<noteq> {}\<^sub>A"
    using Summ
    by (simp add: raw_summary_def antichain_from_list_singleton)

  have edge21: "summ sg (Loc (2 :: 3) (Src (1 :: 2))) (Loc (1 :: 3) (Trg (1 :: 2))) \<noteq> {}\<^sub>A"
    using Summ
    by (simp add: raw_summary_def antichain_from_list_singleton)

  define osA where
    "osA = os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>,
               2 := os2_consumed)"

  define cbufsA where "cbufsA = cbufs((2, 1) := [])"


  have invA: "dataplane_tracker_inv osA cbufsA sg"
  proof -
    have raw: "dataplane_tracker_inv
      (os(1 := (os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>,
          2 := CONSUMES 1 (cbufs (2, 1) @ outpu (os 1) 1) (os 2)))
      (cbufs((2, 1) := [])) sg"
      by (rule dataplane_tracker_inv_outpu_then_fold_consumes
          [where nid_up=1 and p_up=1 and nid_dn=2 and p_dn=1,
            OF Inv D GR Nxt edge12]) simp
    show ?thesis
      using raw out1_eq
      by (simp add: osA_def cbufsA_def os2_consumed_def b21_def)
  qed

  have GA: "graph_summar_nt (summ sg) (nxt sg) osA"
  proof -
    have "graph_summar_nt (summ sg) (nxt sg) osA = graph_summar_nt (summ sg) (nxt sg) os"
      by (rule graph_summar_nt_intsum_cong)
        (simp add: osA_def os2_consumed_def fold_consumes)
    then show ?thesis
      using GR by simp
  qed

  define msgsA where "msgsA = b1 @ outpu (os 2) 1"

  define osB where
    "osB = osA(2 := (osA 2)\<lparr>outpu := (outpu (osA 2))(1 := [])\<rparr>,
                1 := CONSUMES 1 msgsA (osA 1))"

  define cbufsB where "cbufsB = cbufsA((1, 1) := [])"


  have invB: "dataplane_tracker_inv osB cbufsB sg"
  proof -
    have raw: "dataplane_tracker_inv
      (osA(2 := (osA 2)\<lparr>outpu := (outpu (osA 2))(1 := [])\<rparr>,
             1 := CONSUMES 1 (cbufsA (1, 1) @ outpu (osA 2) 1) (osA 1)))
      (cbufsA((1, 1) := [])) sg"
      by (rule dataplane_tracker_inv_outpu_then_fold_consumes
          [where nid_up=2 and p_up=1 and nid_dn=1 and p_dn=1,
            OF invA D GA Nxt edge21]) simp
    show ?thesis
      using raw
      by (simp add: osB_def cbufsB_def msgsA_def b1_def
          cbufsA_def osA_def os2_consumed_def fold_consumes)
  qed

  have GB: "graph_summar_nt (summ sg) (nxt sg) osB"
  proof -
    have "graph_summar_nt (summ sg) (nxt sg) osB = graph_summar_nt (summ sg) (nxt sg) os"
      by (rule graph_summar_nt_intsum_cong)
        (simp add: osB_def osA_def os2_consumed_def fold_consumes)
    then show ?thesis
      using GR by simp
  qed

  define caps_drop where "caps_drop = map (\<lambda>t. Cap t (1 :: 2)) ts_drop"

  define produs where "produs = map (\<lambda>(x, cap). (out cap, capability.time cap, 1 :: int)) batch"

  define oputs where "oputs = (\<lambda>p. map (\<lambda>(x, cap). (x, capability.time cap)) (filter (\<lambda>(x, cap). out cap = p) batch))"



  have concat_shift:
    "concat (map (\<lambda>(d, t). [t -+- inc]) xs) = map (\<lambda>(d :: nat \<times> nat + nat set set, t). t -+- inc) xs" for xs
    by (induct xs) auto
  have osB2_ocaps1:
    "ocaps (osB 2) 1 = ocaps (os 2) 1 @ map (\<lambda>(d, t). t -+- inc) (b21 @ out1)"
    using Intsum unfolding concat_shift[symmetric]
    by (simp add: osB_def osA_def os2_consumed_def fold_consumes raw_summary_def inc_def)

  have input_caps2:
    "\<And>d t. (d, t) \<in> set in21 \<Longrightarrow> t -+- inc \<in> set (ocaps (os 2) 1)"
  proof -
    fix d t
    assume mem: "(d, t) \<in> set in21"
    have inc: "inc \<in> set (intsum (os 2) 1 1)"
      using Intsum by (simp add: inc_def raw_summary_def)
    show "t -+- inc \<in> set (ocaps (os 2) 1)"
      using IOC2 mem inc unfolding input_ocaps_inv_def in21_def by fastforce
  qed

  have shifted_caps_B:
    "\<And>d t. (d, t) \<in> set (in21 @ b21 @ out1) \<Longrightarrow> t -+- inc \<in> set (ocaps (osB 2) 1)"
    using input_caps2 osB2_ocaps1 by auto

  have prod_caps_B: "\<forall>(p, t, m) \<in> set produs. m > 0 \<and> t \<in> set (ocaps (osB 2) p)"
  proof (rule ballI)
    fix y :: "2 \<times> (nat, nat) myprod \<times> int"

    assume y: "y \<in> set produs"
    then obtain x where x_mem: "x \<in> set (in21 @ b21 @ out1)"
      and y_eq: "y = (1, snd x -+- inc, 1)"
      unfolding produs_def batch_def by auto
    obtain d t where x_eq: "x = (d, t)"
      by (cases x)
    show "case y of (p, t, m) \<Rightarrow> 0 < m \<and> t \<in> set (ocaps (osB 2) p)"
      using shifted_caps_B[of d t] x_mem x_eq y_eq by simp
  qed

  have ts_drop_subset_B: "mset ts_drop \<subseteq># mset (ocaps (osB 2) 1)"
    using osB2_ocaps1 by (simp add: split_beta ts_drop_def ts_caps2_extra_def)

  have drops_subset_B:
    "\<forall>p'. mset (map capability.time (filter (\<lambda>c. out c = p') caps_drop)) \<subseteq># mset (ocaps (osB 2) p')"
    unfolding caps_drop_def
    by (rule cap_times_filter_single_port_subset[OF ts_drop_subset_B])

  have oputs_caps_B: "\<forall>p. snd ` set (oputs p) \<subseteq> set (ocaps (osB 2) p)"
    unfolding oputs_def
    by (rule produced_oputs_caps_from_produs[OF prod_caps_B[unfolded produs_def]])

  have oputs_produs_B:
    "\<forall>p. to_zmset (map snd (oputs p)) = zmset (map snd (filter (\<lambda>x. p = fst x) produs))"
    unfolding oputs_def produs_def
    by (rule produced_oputs_produs_zmset)

  define drop_times where "drop_times = (\<lambda>p. map capability.time (filter (\<lambda>c. out c = p) caps_drop))"

  define os2C_abs where
    "os2C_abs = (osB 2)\<lparr>
    outpu := (\<lambda>p. outpu (osB 2) p @ oputs p),
    ocaps := (\<lambda>p. list_diff (ocaps (osB 2) p) (drop_times p)),
    input := (\<lambda>p. filter (\<lambda>(_, t). t \<notin> set (drop_times p)) (input (osB 2) p)),
    produ := produ (osB 2) @ produs,
    inter := operator_state.inter (osB 2) @ map (\<lambda>cap. (out cap, capability.time cap, - 1)) caps_drop\<rparr>"

  define osC_abs where "osC_abs = osB(2 := os2C_abs)"


  have invC_abs: "dataplane_tracker_inv osC_abs cbufsB sg"
    unfolding osC_abs_def os2C_abs_def drop_times_def
    by (rule dataplane_tracker_inv_produces_drops_dropcaps_shape
        [OF D refl refl refl refl refl drops_subset_B prod_caps_B oputs_caps_B oputs_produs_B GB Nxt invB])

  have GC_abs: "graph_summar_nt (summ sg) (nxt sg) osC_abs"
  proof -
    have "graph_summar_nt (summ sg) (nxt sg) osC_abs = graph_summar_nt (summ sg) (nxt sg) osB"
      by (rule graph_summar_nt_intsum_cong) (simp add: osC_abs_def os2C_abs_def)
    then show ?thesis
      using GB by simp
  qed

  define osD where
    "osD = osC_abs(2 := (osC_abs 2)\<lparr>outpu := (outpu (osC_abs 2))(1 := [])\<rparr>,
                   1 := CONSUMES 1 (cbufsB (1, 1) @ outpu (osC_abs 2) 1) (osC_abs 1))"


  have invD: "dataplane_tracker_inv osD (cbufsB((1, 1) := [])) sg"
    unfolding osD_def
    by (rule dataplane_tracker_inv_outpu_then_fold_consumes
        [where nid_up=2 and p_up=1 and nid_dn=1 and p_dn=1,
          OF invC_abs D GC_abs Nxt edge21]) simp

  have oputs1_map:
    "map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = 1)
          (map (\<lambda>x. (fst x, Cap (snd x -+- inc) 1)) xs)) =
      map (\<lambda>(d, t). (d, t -+- inc)) xs" for xs
    by (induct xs) (auto split: prod.splits)

  have oputs1_eq:
    "oputs 1 = map (\<lambda>(d, t). (d, t -+- inc)) (in21 @ b21 @ out1)"
    unfolding oputs_def batch_def
    by (simp add: oputs1_map)

  have out_label_prop: "outpu os_label_prop = outpu (os 1)"
    using label_prop_extension by (simp add: operator_state.defs)

  have base_clear:
    "op_state_base (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>) =
      (os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>"
    using base_label_prop out_label_prop by simp

  have osB1:
    "osB 1 = CONSUMES 1 msgsA ((os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>)"
    by (simp add: osB_def osA_def)

  have osC_abs_1: "osC_abs 1 = osB 1"
    by (simp add: osC_abs_def)

  have osC_abs_out2_1: "outpu (osC_abs 2) 1 = oputs 1"
    by (simp add: osC_abs_def os2C_abs_def osB_def osA_def os2_consumed_def fold_consumes)

  have osD_to_B: "osD 1 = CONSUMES 1 (oputs 1) (osB 1)"
  proof -
    have raw: "osD 1 = CONSUMES 1 (cbufsB (1, 1) @ outpu (osC_abs 2) 1) (osC_abs 1)"
      by (simp add: osD_def)
    have msgs: "cbufsB (1, 1) @ outpu (osC_abs 2) 1 = oputs 1"
      using osC_abs_out2_1 by (simp add: cbufsB_def cbufsA_def)
    show ?thesis
      apply (subst raw)
      apply (subst msgs)
      apply (subst osC_abs_1)
      apply (rule refl)
      done
  qed

  have osD_to_base:
    "osD 1 = CONSUMES 1 (msgsA @ oputs 1) ((os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>)"
    apply (subst osD_to_B)
    apply (subst osB1)
    apply (rule CONSUMES_CONSUMES)
    done

  have msgs_oputs_eq:
    "msgsA @ oputs 1 =
      b1 @ outpu (os 2) 1 @ map (\<lambda>(d, t). (d, t -+- inc)) (in21 @ b21 @ out1)"
    using oputs1_eq by (simp add: msgsA_def)

  have label_prop_consumed_base:
    "op_state_base os_label_prop_consumed =
      CONSUMES 1 (msgsA @ oputs 1) ((os 1)\<lparr>outpu := (outpu (os 1))(1 := [])\<rparr>)"
    unfolding os_label_prop_consumed_def
    apply (simp only: op_state_base_CONSUMES)
    apply (subst base_clear)
    apply (subst msgs_oputs_eq)
    apply (rule refl)
    done

  have osD_slot1: "osD 1 = op_state_base os_label_prop_consumed"
    apply (subst osD_to_base)
    apply (subst label_prop_consumed_base)
    apply (rule refl)
    done

  define osE :: "3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state"
    where "osE = osD(2 := (osD 2)\<lparr>input := (input (os 2))(1 := [])\<rparr>)"


  have invE: "dataplane_tracker_inv osE (cbufsB((1, 1) := [])) sg"
    unfolding osE_def
    by (rule dataplane_tracker_inv_input_update
        [where nid=2 and inp="(input (os 2))(1 := [])", OF invD])


  have oputs_other_map:
    "p \<noteq> 1 \<Longrightarrow>
      map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = p)
          (map (\<lambda>x. (fst x, Cap (snd x -+- inc) 1)) xs)) = []" for p :: 2 and xs
    by (induct xs) (auto split: prod.splits)

  have oputs_other: "p \<noteq> 1 \<Longrightarrow> oputs p = []" for p :: 2
    unfolding oputs_def batch_def
    by (rule oputs_other_map)

  have osB2_eq: "osB 2 = os2_consumed\<lparr>outpu := (outpu (os 2))(1 := [])\<rparr>"
    by (simp add: osB_def osA_def os2_consumed_def fold_consumes)

  have osE2_outpu: "outpu (osE 2) = outpu os2'"
  proof (rule ext)
    fix p :: 2
    show "outpu (osE 2) p = outpu os2' p"
    proof (cases "p = 1")
      case True
      then show ?thesis
        by (simp add: osE_def osD_def os2'_def drop_caps_def produces_def)
    next
      case False
      then show ?thesis
        using oputs_other[OF False]
        by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
            os2'_def drop_caps_def produces_def)
    qed
  qed

  have osE2_eq: "osE 2 = os2'"
  proof (rule operator_state_eqI)
    show "intsum (osE 2) = intsum os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          fold_consumes drop_caps_def produces_def)
    show "consu (osE 2) = consu os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          fold_consumes drop_caps_def produces_def)
    show "operator_state.inter (osE 2) = operator_state.inter os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          caps_drop_def
          fold_consumes drop_caps_def produces_def)
    show "produ (osE 2) = produ os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          produs_def
          fold_consumes drop_caps_def produces_def)
    show "input (osE 2) = input os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          fold_consumes drop_caps_def produces_def)
    show "outpu (osE 2) = outpu os2'"
      by (rule osE2_outpu)
    show "front (osE 2) = front os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          fold_consumes drop_caps_def produces_def)
    show "ocaps (osE 2) = ocaps os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          drop_times_def caps_drop_def
          fold_consumes drop_caps_def produces_def)
    show "initia (osE 2) = initia os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          fold_consumes drop_caps_def produces_def)
    show "operator_state.more (osE 2) = operator_state.more os2'"
      by (simp add: osE_def osD_def osC_abs_def os2C_abs_def osB2_eq
          os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
          fold_consumes drop_caps_def produces_def)
  qed

  have osE_eq: "osE = os(2 := os2', 1 := op_state_base os_label_prop_consumed)"
  proof (rule ext)
    fix nid'
    show "osE nid' = (os(2 := os2', 1 := op_state_base os_label_prop_consumed)) nid'"
    proof (cases "nid' = 1")
      case True
      then show ?thesis
        using osD_slot1 by (simp add: osE_def)
    next
      case False
      then show ?thesis
      proof (cases "nid' = 2")
        case True
        then show ?thesis
          using osE2_eq False by simp
      next
        case False2: False
        then show ?thesis
          using False
          by (simp add: osE_def osD_def osC_abs_def osB_def osA_def)
      qed
    qed
  qed

  have intsum_os2': "intsum os2' = intsum (os 2)"
    by (simp add: os2'_def os2_after_drop_def os2_after_prod_def os2_consumed_def
        fold_consumes drop_caps_def produces_def)

  have intsum_consumed_base:
    "intsum (op_state_base os_label_prop_consumed) = intsum (os 1)"
  proof -
    have "intsum (op_state_base os_label_prop_consumed) =
      intsum (op_state_base (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>))"
      by (simp add: os_label_prop_consumed_def intsum_consumes_fold)
    also have "... = intsum ((op_state_base os_label_prop)\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)"
      by simp
    also have "... = intsum (op_state_base os_label_prop)"
      by simp
    also have "... = intsum (os 1)"
      using base_label_prop by simp
    finally show ?thesis .
  qed

  have intsum_label_base: "intsum (op_state_base os_label_prop) = intsum (os 1)"
    using base_label_prop by simp


  have GE: "graph_summar_nt (summ sg) (nxt sg) osE"
  proof -
    have geq:
      "graph_summar_nt (summ sg) (nxt sg)
        (os(2 := os2', 1 := op_state_base os_label_prop_consumed)) =
       graph_summar_nt (summ sg) (nxt sg) os"
      by (rule graph_summar_nt_intsum_cong)
        (simp add: intsum_os2' intsum_consumed_base intsum_label_base)
    have "graph_summar_nt (summ sg) (nxt sg) osE = graph_summar_nt (summ sg) (nxt sg) os"
      apply (subst osE_eq)
      apply (rule geq)
      done
    then show ?thesis
      using GR by simp
  qed

  have IOC_consumed: "input_ocaps_inv os_label_prop_consumed"
  proof -
    have "input_ocaps_inv (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)"
      using IOC_label_prop unfolding input_ocaps_inv_def by simp
    then show ?thesis
      unfolding os_label_prop_consumed_def
      by (rule input_ocaps_inv_CONSUMES)
  qed

  have zero_consumed: "0 \<in> set (intsum os_label_prop_consumed 1 1)"
    using zero_label_prop
    by (simp add: os_label_prop_consumed_def intsum_consumes_fold)

  have upd: "osE(1 := op_state_base os_label_prop_consumed) = osE"
    apply (subst osE_eq)
    apply (subst osE_eq)
    apply simp
    done

  have invE_base:
    "dataplane_tracker_inv (osE(1 := op_state_base os_label_prop_consumed))
      (cbufsB((1, 1) := [])) sg"
    apply (subst upd)
    apply (rule invE)
    done

  have GE_base:
    "graph_summar_nt (summ sg) (nxt sg)
      (osE(1 := op_state_base os_label_prop_consumed))"
    apply (subst upd)
    apply (rule GE)
    done



  have invFinal:
    "dataplane_tracker_inv
      (osE(1 := op_state_base (fst (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1)))))
      (cbufsB((1, 1) := [])) sg"
    by (rule dataplane_tracker_inv_label_prop_input1_batched
        [OF D invE_base GE_base Nxt IOC_consumed zero_consumed])







  have os_label_prop'_eq:
    "os_label_prop' = fst (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))"
    using step
    unfolding label_prop_input1_loop_updates_def Let_def
      os_label_prop_consumed_def b1_def in21_def b21_def out1_def inc_def
    by (simp split: prod.splits)

  have os_final_eq:
    "os'(1 := op_state_base os_label_prop') =
      osE(1 := op_state_base (fst (label_prop_input1_batched os_label_prop_consumed (input os_label_prop_consumed 1))))"
    apply (subst os'_eq)
    apply (subst os_label_prop'_eq)
    apply (subst osE_eq)
    apply simp
    done

  have cbufs_final_eq: "cbufs' = cbufsB((1, 1) := [])"
    using cbufs'_eq by (simp add: cbufsB_def cbufsA_def)

  show ?thesis
    apply (subst os_final_eq)
    apply (subst cbufs_final_eq)
    apply (rule invFinal)
    done

qed


subsection \<open>Loop-update bridge and frame facts\<close>


lemma input_ocaps_inv_op_state_base:
  \<open>input_ocaps_inv (op_state_base os) = input_ocaps_inv os\<close>
  unfolding input_ocaps_inv_def op_state_base_def
  by simp


lemma label_prop_input1_loop_updates_corrected_os:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows
    \<open>(cbufs', os_label_prop', os'(1 := op_state_base os_label_prop)) =
      label_prop_input1_loop_updates cbufs os_label_prop (os(1 := op_state_base os_label_prop))\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def
  by (simp add: fun_upd_twist split: prod.splits)


subsection \<open>State extension and graph frame facts\<close>


lemma graph_produces[simp]:
  \<open>graph (produces os batch) = graph os\<close>
  unfolding produces_def by simp


lemma label_propagation_state_extend_decompose:
  fixes os :: \<open>('d, 'v::linorder, 't1, 't2) label_propagation_state\<close>
  shows \<open>os = operator_state.extend (op_state_base os)
    \<lparr>en1 = en1 os, de1 = de1 os, is_en1 = is_en1 os,
      en2 = en2 os, de2 = de2 os, is_en2 = is_en2 os,
      timestamps = timestamps os, graph = graph os,
      vertices = vertices os, label = label os\<rparr>\<close>
  by (simp add: op_state_base_def operator_state.defs)


lemma label_prop_input1_step_state_graph[simp]:
  \<open>graph (label_prop_input1_step_state os d t) = graph os\<close>
  unfolding label_prop_input1_step_state_def
  by (simp add: Let_def)




lemma graph_fst_label_prop_input1_batched[simp]:
  \<open>graph (fst (label_prop_input1_batched os msgs)) = graph os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)


lemma vertices_fst_label_prop_input1_batched[simp]:
  \<open>vertices (fst (label_prop_input1_batched os msgs)) = vertices os\<close>
  by (induct msgs arbitrary: os) (auto simp: case_prod_beta)


lemma label_prop_input1_loop_updates_extension:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and ext: \<open>os_label_prop = operator_state.extend (op_state_base os_label_prop)
      \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr,
        timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
  shows \<open>os_label_prop' = operator_state.extend (op_state_base os_label_prop')
      \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr,
        timestamps = T, graph = G, vertices = V, label = label os_label_prop'\<rparr>\<close>
proof -
  let ?cons = \<open>CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?cons (input ?cons 1))\<close>
    using step unfolding label_prop_input1_loop_updates_def Let_def
    by (simp split: prod.splits)
  have en1_os: \<open>en1 os_label_prop = Inl\<close>
    by (subst ext) (simp add: operator_state.defs)
  have de1_os: \<open>de1 os_label_prop = projl\<close>
    by (subst ext) (simp add: operator_state.defs)
  have is_en1_os: \<open>is_en1 os_label_prop = isl\<close>
    by (subst ext) (simp add: operator_state.defs)
  have en2_os: \<open>en2 os_label_prop = Inr\<close>
    by (subst ext) (simp add: operator_state.defs)
  have de2_os: \<open>de2 os_label_prop = projr\<close>
    by (subst ext) (simp add: operator_state.defs)
  have is_en2_os: \<open>is_en2 os_label_prop = isr\<close>
    by (subst ext) (simp add: operator_state.defs)
  have timestamps_os: \<open>timestamps os_label_prop = T\<close>
    by (subst ext) (simp add: operator_state.defs)
  have graph_os: \<open>graph os_label_prop = G\<close>
    by (subst ext) (simp add: operator_state.defs)
  have vertices_os: \<open>vertices os_label_prop = V\<close>
    by (subst ext) (simp add: operator_state.defs)
  have en1_eq: \<open>en1 os_label_prop' = Inl\<close>
    unfolding os_label_prop'_eq using en1_os by simp
  have de1_eq: \<open>de1 os_label_prop' = projl\<close>
    unfolding os_label_prop'_eq using de1_os by simp
  have is_en1_eq: \<open>is_en1 os_label_prop' = isl\<close>
    unfolding os_label_prop'_eq using is_en1_os by simp
  have en2_eq: \<open>en2 os_label_prop' = Inr\<close>
    unfolding os_label_prop'_eq using en2_os by simp
  have de2_eq: \<open>de2 os_label_prop' = projr\<close>
    unfolding os_label_prop'_eq using de2_os by simp
  have is_en2_eq: \<open>is_en2 os_label_prop' = isr\<close>
    unfolding os_label_prop'_eq using is_en2_os by simp
  have timestamps_eq: \<open>timestamps os_label_prop' = T\<close>
    unfolding os_label_prop'_eq using timestamps_os by simp
  have graph_eq: \<open>graph os_label_prop' = G\<close>
    unfolding os_label_prop'_eq using graph_os by simp
  have vertices_eq: \<open>vertices os_label_prop' = V\<close>
    unfolding os_label_prop'_eq using vertices_os by simp
  have decomp: \<open>os_label_prop' = operator_state.extend (op_state_base os_label_prop')
      \<lparr>en1 = en1 os_label_prop', de1 = de1 os_label_prop', is_en1 = is_en1 os_label_prop',
        en2 = en2 os_label_prop', de2 = de2 os_label_prop', is_en2 = is_en2 os_label_prop',
        timestamps = timestamps os_label_prop', graph = graph os_label_prop',
        vertices = vertices os_label_prop', label = label os_label_prop'\<rparr>\<close>
    by (rule label_propagation_state_extend_decompose)
  show ?thesis
    using decomp en1_eq de1_eq is_en1_eq en2_eq de2_eq is_en2_eq timestamps_eq graph_eq vertices_eq
    by simp
qed

subsection \<open>Raw-summary preservation for loop updates\<close>


lemma label_prop_input1_loop_updates_intsum_corrected:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  shows \<open>\<forall>n. intsum ((os'(1 := op_state_base os_label_prop')) n) =
    intsum ((os(1 := op_state_base os_label_prop)) n)\<close>
  using step
  unfolding label_prop_input1_loop_updates_def Let_def op_state_base_def drop_caps_def produces_def
  by (auto split: prod.splits if_splits)


lemma graph_summar_nt_label_prop_input1_loop_updates_corrected:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and GR: \<open>graph_summar_nt (summ sg) (nxt sg) (os(1 := op_state_base os_label_prop))\<close>
  shows \<open>graph_summar_nt (summ sg) (nxt sg) (os'(1 := op_state_base os_label_prop'))\<close>
proof -
  have intsum_eq: \<open>\<And>n. intsum ((os'(1 := op_state_base os_label_prop')) n) =
      intsum ((os(1 := op_state_base os_label_prop)) n)\<close>
    using label_prop_input1_loop_updates_intsum_corrected[OF step] by blast
  have \<open>graph_summar_nt (summ sg) (nxt sg) (os'(1 := op_state_base os_label_prop')) =
        graph_summar_nt (summ sg) (nxt sg) (os(1 := op_state_base os_label_prop))\<close>
    by (rule graph_summar_nt_intsum_cong) (rule intsum_eq)
  then show ?thesis using GR by simp
qed

subsection \<open>Input capability preservation for loop updates\<close>


lemma input_ocaps_inv_label_prop_input1_loop_updates_label:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and IOC: \<open>input_ocaps_inv os_label_prop\<close>
  shows \<open>input_ocaps_inv os_label_prop'\<close>
proof -
  let ?cons = \<open>CONSUMES 1
        (cbufs (1, 1) @ outpu (os 2) 1 @
          map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
            (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1))
        (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?cons (input ?cons 1))\<close>
    using step unfolding label_prop_input1_loop_updates_def Let_def
    by (simp split: prod.splits)
  have outpu_upd: \<open>input_ocaps_inv (os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>)\<close>
    using IOC by (simp add: input_ocaps_inv_def)
  hence \<open>input_ocaps_inv ?cons\<close>
    by (rule input_ocaps_inv_CONSUMES)
  hence \<open>input_ocaps_inv (fst (label_prop_input1_batched ?cons (input ?cons 1)))\<close>
    by (rule input_ocaps_inv_fst_label_prop_input1_batchedI)
  thus ?thesis unfolding os_label_prop'_eq .
qed


lemma input_ocaps_inv_label_prop_input1_loop_updates_os2:
  fixes os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and IOC: \<open>input_ocaps_inv (os 2)\<close>
    and Intsum: \<open>\<forall>n. intsum ((os(1 := op_state_base os_label_prop)) n) =
      (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
  shows \<open>input_ocaps_inv (os' 2)\<close>
proof -
  let ?buf = \<open>cbufs (2, 1) @ outpu os_label_prop 1\<close>
  let ?outpu_batch = \<open>map (\<lambda>x. (fst x, Cap (snd x -+- MyPair 0 (Suc 0)) 1))
        (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?drops = \<open>map (\<lambda>t. Cap t 1)
        (ocaps (os 2) 1 @
          map (\<lambda>a. case a of (d, t) \<Rightarrow> t -+- MyPair 0 (Suc 0))
            (cbufs (2, 1) @ outpu os_label_prop 1))\<close>
  let ?intermediate = \<open>drop_caps (produces (CONSUMES 1 ?buf (os 2)) ?outpu_batch) ?drops\<close>
  have os2'_eq:
    \<open>os' 2 = ?intermediate\<lparr>outpu := (outpu (os 2))(1 := []),
                            input := (input (os 2))(1 := [])\<rparr>\<close>
    using step unfolding label_prop_input1_loop_updates_def Let_def
    by (simp split: prod.splits)
  have intsum_2_0_1: \<open>intsum (os 2) 0 1 = []\<close>
    using Intsum[unfolded raw_summary_def, rule_format, of \<open>2 :: 3\<close>, simplified]
    using num2_neq(1) by force
  have intsum_2_1_0: \<open>intsum (os 2) 1 0 = []\<close>
    using Intsum[unfolded raw_summary_def, rule_format, of \<open>2 :: 3\<close>, simplified]
    using num2_neq(1) by force

  show ?thesis
    unfolding os2'_eq input_ocaps_inv_def
  proof (intro allI ballI)
    fix p p' t s
    assume t_in: \<open>t \<in> snd ` set (input
       (?intermediate\<lparr>outpu := (outpu (os 2))(1 := []),
                       input := (input (os 2))(1 := [])\<rparr>) p)\<close>
      and s_in: \<open>s \<in> set (intsum
       (?intermediate\<lparr>outpu := (outpu (os 2))(1 := []),
                       input := (input (os 2))(1 := [])\<rparr>) p p')\<close>
    have p_ne1: \<open>p \<noteq> 1\<close>
      using t_in by (auto split: if_splits)
    have p_eq0: \<open>p = (0 :: 2)\<close>
      using p_ne1 num2_neq(2) by blast
    have t_in_os2: \<open>t \<in> snd ` set (input (os 2) p)\<close>
      using t_in p_ne1
      by (auto simp: drop_caps_def produces_def input_CONSUMES split: if_splits)
    have s_in_os2: \<open>s \<in> set (intsum (os 2) p p')\<close>
      using s_in by (simp add: drop_caps_def produces_def)
    have orig: \<open>t -+- s \<in> set (ocaps (os 2) p')\<close>
      using IOC t_in_os2 s_in_os2 unfolding input_ocaps_inv_def by blast
    have p'_eq0: \<open>p' = (0 :: 2)\<close>
    proof (rule ccontr)
      assume \<open>p' \<noteq> 0\<close>
      hence \<open>p' = 1\<close> using num2_neq(1) by blast
      thus False using s_in_os2 intsum_2_0_1 p_eq0 by simp
    qed
    have ocaps_unchanged: \<open>ocaps ?intermediate 0 = ocaps (os 2) 0\<close>
    proof -
      have ocaps_drop_p0:
        \<open>ocaps (drop_caps (produces (CONSUMES 1 ?buf (os 2)) ?outpu_batch) ?drops) 0
       = ocaps (produces (CONSUMES 1 ?buf (os 2)) ?outpu_batch) 0\<close>
        unfolding drop_caps_def by (simp add: filter_False)

      have ocaps_produces_p0:
        \<open>ocaps (produces (CONSUMES 1 ?buf (os 2)) ?outpu_batch) 0
       = ocaps (CONSUMES (1 :: 2) ?buf (os 2)) 0\<close>
        unfolding produces_def by simp
      have ocaps_cons_p0: \<open>ocaps (CONSUMES (1 :: 2) ?buf (os 2)) 0 = ocaps (os 2) 0\<close>
        by (rule ocaps_CONSUMES_other_port[OF intsum_2_1_0])
      show ?thesis
        using ocaps_drop_p0 ocaps_produces_p0 ocaps_cons_p0 by simp
    qed
    show \<open>t -+- s \<in> set (ocaps
       (?intermediate\<lparr>outpu := (outpu (os 2))(1 := []),
                       input := (input (os 2))(1 := [])\<rparr>) p')\<close>
      using orig ocaps_unchanged p'_eq0 by simp
  qed
qed


subsection \<open>Label-update invariant preservation for loop updates\<close>


lemma label_prop_upd_inv_label_prop_input1_loop_updatesI:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and wf_upd: \<open>wf_label_prop_updates os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  shows \<open>label_prop_upd_inv os_label_prop'\<close>
proof -
  let ?os_reset = \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>\<close>
  let ?buf = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
        map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
          (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?cons = \<open>CONSUMES 1 ?buf ?os_reset\<close>
  have os_label_prop'_eq:
    \<open>os_label_prop' = fst (label_prop_input1_batched ?cons (input ?cons 1))\<close>
    using step unfolding label_prop_input1_loop_updates_def Let_def
    by (simp split: prod.splits)
  have inv_reset: \<open>label_prop_upd_inv ?os_reset\<close>
    using INV by simp
  have wf_reset_buf: \<open>wf_label_prop_updates ?os_reset (set ?buf)\<close>
    using wf_upd[unfolded wf_label_prop_updates_un]
    unfolding wf_label_prop_updates_def by simp
  have inv_cons: \<open>label_prop_upd_inv ?cons\<close>
    by (rule label_prop_upd_inv_CONSUMES_port1I[OF inv_reset wf_reset_buf])
  have wf_cons: \<open>wf_label_prop_updates ?cons (set (input ?cons 1))\<close>
    using wf_upd
    unfolding wf_label_prop_updates_def by (simp add: input_CONSUMES Un_commute)
  show ?thesis
    unfolding os_label_prop'_eq
    by (rule label_prop_upd_inv_fst_label_prop_input1_batched_prefixI
        [where rest=Nil, OF _ inv_cons wf_cons])
      simp
qed


lemma labels_inv_label_prop_input1_loop_updates_allI:
  fixes os_label_prop os_label_prop' :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os os' :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs cbufs' :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>

assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
  and INV: \<open>label_prop_upd_inv os_label_prop\<close>
  and wf_upd: \<open>wf_label_prop_updates os_label_prop
      (set (input os_label_prop 1) \<union>
       set (cbufs (1, 1) @ outpu (os 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
shows \<open>\<forall>t. labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
proof
  fix t
  show \<open>labels_inv (all_edges os_label_prop' t) (min_label os_label_prop' t)\<close>
    by (rule labels_inv_label_prop_input1_loop_updatesI[
          where cbufs = cbufs and os_label_prop = os_label_prop and os = os
            and cbufs' = cbufs' and os_label_prop' = os_label_prop'
            and os' = os' and t = t])
        (use step INV wf_upd LABELS in auto)
qed



subsection \<open>Pending-message payload preservation for loop updates\<close>


lemma label_prop_input1_loop_updates_msgs_invI:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and EN1: \<open>en1 os_label_prop = Inl\<close>
    and DE1: \<open>de1 os_label_prop = projl\<close>
    and INV: \<open>label_prop_upd_inv os_label_prop\<close>
    and LABELS: \<open>\<forall>t. labels_inv (all_edges os_label_prop t) (min_label os_label_prop t)\<close>
    and wf_upd: \<open>wf_label_prop_updates os_label_prop
        (set (input os_label_prop 1) \<union>
         set (cbufs (1, 1) @ outpu (os 2) 1 @
              map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
                (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)))\<close>
  shows \<open>wf_label_prop_updates os_label_prop'
      (set (cbufs' (1, 1) @ outpu (os' 2) 1 @
            map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
              (input (os' 2) 1 @ cbufs' (2, 1) @ outpu os_label_prop' 1)))\<close>
proof -
  let ?msgs = \<open>cbufs (1, 1) @ outpu (os 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os 2) 1 @ cbufs (2, 1) @ outpu os_label_prop 1)\<close>
  let ?base = \<open>os_label_prop\<lparr>outpu := (outpu os_label_prop)(1 := [])\<rparr>\<close>
  let ?consumed = \<open>CONSUMES 1 ?msgs ?base\<close>
  let ?full = \<open>input ?consumed 1\<close>

  have os'_eq: \<open>os_label_prop' = fst (label_prop_input1_batched ?consumed ?full)\<close>
    using step
    unfolding label_prop_input1_loop_updates_def Let_def
    by (auto split: prod.splits)

  have wf_base_msgs: \<open>wf_label_prop_updates ?base (set ?msgs)\<close>
    using wf_upd[unfolded wf_label_prop_updates_un]
    unfolding wf_label_prop_updates_def by simp
  have inv_consumed: \<open>label_prop_upd_inv ?consumed\<close>
    by (rule label_prop_upd_inv_CONSUMES_port1I[OF _ wf_base_msgs])
      (use INV in simp)
  have wf_consumed: \<open>wf_label_prop_updates ?consumed (set (input ?consumed 1))\<close>
    using wf_upd
    unfolding wf_label_prop_updates_def by (simp add: input_CONSUMES Un_commute)

  have all_edges_final: \<open>\<And>q. all_edges os_label_prop' q = all_edges ?consumed q\<close>
    using os'_eq by simp

  let ?msgs' = \<open>cbufs' (1, 1) @ outpu (os' 2) 1 @
    map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0)))
      (input (os' 2) 1 @ cbufs' (2, 1) @ outpu os_label_prop' 1)\<close>

  have per_msg: \<open>\<And>d t. (d, t) \<in> set ?msgs' \<Longrightarrow>
      myfst t \<in> set (timestamps os_label_prop') \<and>
      fst (de1 os_label_prop' d) \<in> all_vertices os_label_prop' (myfst t) \<and>
      (\<forall>q. myfst t \<le> q \<longrightarrow>
        snd (de1 os_label_prop' d) \<in> cc_of (all_edges os_label_prop' q) (fst (de1 os_label_prop' d)))\<close>
  proof -
    fix d t
    assume member: \<open>(d, t) \<in> set ?msgs'\<close>

    have shifted_member:
      \<open>(d, t) \<in> set (map (\<lambda>(d, t). (d, t -+- MyPair 0 (Suc 0))) (outpu os_label_prop' 1))\<close>
      using member step 
      by (simp add: label_prop_input1_loop_updates_cbufs_11 label_prop_input1_loop_updates_cbufs_21 label_prop_input1_loop_updates_input_os2_1 label_prop_input1_loop_updates_outpu_os2_1)
    then obtain d0 t0 where out_member: \<open>(d0, t0) \<in> set (outpu os_label_prop' 1)\<close>
      and d_eq: \<open>d = d0\<close>
      and t_eq: \<open>t = t0 -+- MyPair 0 (Suc 0)\<close>
      by auto

    have consumed_out_empty: \<open>outpu ?consumed 1 = []\<close>
      by (simp add: fold_consumes)
    have outpu_eq:
      \<open>outpu os_label_prop' 1 =
      map (\<lambda>(x, cap). (x, capability.time cap))
        (filter (\<lambda>(x, cap). out cap = 1) (snd (label_prop_input1_batched ?consumed ?full)))\<close>
      using os'_eq consumed_out_empty
      by (simp add: outpu_fst_label_prop_input1_batched_eq)
    obtain cap where batch_member:
      \<open>(d0, cap) \<in> set (snd (label_prop_input1_batched ?consumed ?full))\<close>
      and out_cap: \<open>out cap = 1\<close>
      and t0_eq: \<open>t0 = capability.time cap\<close>
      using out_member outpu_eq by auto

    obtain pre d_in t_in post os_pre where full_eq: \<open>?full = pre @ (d_in, t_in) # post\<close>
      and os_pre_eq: \<open>os_pre = fst (label_prop_input1_batched ?consumed pre)\<close>
      and step_member: \<open>(d0, cap) \<in> set (label_prop_input1_step_batch os_pre d_in t_in)\<close>
      using batch_member by (elim label_prop_input1_batched_batch_memberD)

    obtain v l l' cur_t v' where de1_pre: \<open>de1 os_pre d_in = (v, l)\<close>
      and l'_def: \<open>l' = min (min_label os_pre (myfst t_in) v) l\<close>
      and cur_t_ts_pre: \<open>cur_t \<in> set (timestamps os_pre)\<close>
      and event_le_cur: \<open>myfst t_in \<le> cur_t\<close>
      and neigh: \<open>v' \<in> set (neighbors os_pre cur_t v)\<close>
      and d0_eq: \<open>d0 = en1 os_pre (v', l')\<close>
      and cap_eq: \<open>cap = Cap (MyPair cur_t (mysnd t_in)) 1\<close>
      using step_member by (elim label_prop_input1_step_batch_member_payloadD)

    have inv_pre: \<open>label_prop_upd_inv os_pre\<close>
    proof -
      have \<open>label_prop_upd_inv (fst (label_prop_input1_batched ?consumed pre))\<close>
        by (rule label_prop_upd_inv_fst_label_prop_input1_batched_prefixI
            [where rest = \<open>(d_in, t_in) # post\<close>, OF _ inv_consumed wf_consumed])
          (use full_eq in simp)
      then show ?thesis
        using os_pre_eq by simp
    qed

    have in_full: \<open>(d_in, t_in) \<in> set (input ?consumed 1)\<close>
      using full_eq by simp
    have de1_consumed: \<open>de1 ?consumed d_in = (v, l)\<close>
      using de1_pre os_pre_eq by simp
    have pending_consumed:
      \<open>myfst t_in \<in> set (timestamps ?consumed) \<and>
      fst (de1 ?consumed d_in) \<in> all_vertices ?consumed (myfst t_in) \<and>
      (\<forall>q. myfst t_in \<le> q \<longrightarrow> snd (de1 ?consumed d_in) \<in> cc_of (all_edges ?consumed q) (fst (de1 ?consumed d_in)))\<close>
      using wf_consumed in_full unfolding wf_label_prop_updates_def by blast
    have l_cc_consumed: \<open>\<And>q. myfst t_in \<le> q \<Longrightarrow> l \<in> cc_of (all_edges ?consumed q) v\<close>
      using pending_consumed de1_consumed by simp

    have verts_pre: \<open>v \<in> all_vertices os_pre cur_t \<and> v' \<in> all_vertices os_pre cur_t\<close>
      by (rule label_prop_upd_inv_neighborsD[OF inv_pre neigh])
    have edge_cur_pre: \<open>(v, v') \<in> all_edges os_pre cur_t\<close>
      using verts_pre neigh unfolding all_edges_def by auto
    have all_edges_pre: \<open>\<And>q. all_edges os_pre q = all_edges ?consumed q\<close>
      using os_pre_eq by simp
    have edge_final: \<open>\<And>q. cur_t \<le> q \<Longrightarrow> (v, v') \<in> all_edges os_label_prop' q\<close>
    proof -
      fix q
      assume cur_t_le_q: \<open>cur_t \<le> q\<close>
      have \<open>(v, v') \<in> all_edges os_pre q\<close>
        using edge_cur_pre all_edges_mono[OF cur_t_le_q, of os_pre] by blast
      then show \<open>(v, v') \<in> all_edges os_label_prop' q\<close>
        using all_edges_pre[of q] all_edges_final[of q] by simp
    qed

    have t0_cur: \<open>t0 = MyPair cur_t (mysnd t_in)\<close>
      using t0_eq cap_eq by simp
    have t_fst: \<open>myfst t = cur_t\<close>
      using t_eq t0_cur by simp
    have decode: \<open>de1 os_label_prop' d = (v', l')\<close>
      using d_eq d0_eq os_pre_eq os'_eq EN1 DE1 by simp
    have ts_final: \<open>myfst t \<in> set (timestamps os_label_prop')\<close>
      using cur_t_ts_pre os_pre_eq os'_eq t_fst by simp
    have vertex_final: \<open>fst (de1 os_label_prop' d) \<in> all_vertices os_label_prop' (myfst t)\<close>
      using edge_final[OF order_refl, unfolded all_edges_def] decode t_fst by auto
    have labels_inv_consumed: \<open>\<And>q. labels_inv (all_edges ?consumed q) (min_label ?consumed q)\<close>
      using LABELS by simp
    have labels_inv_pre: \<open>\<And>q. labels_inv (all_edges os_pre q) (min_label os_pre q)\<close>
      unfolding os_pre_eq
      by (rule labels_inv_fst_label_prop_input1_batched_prefixI
          [where rest = \<open>(d_in, t_in) # post\<close>, OF _ labels_inv_consumed inv_consumed wf_consumed])
        (use full_eq in simp)
    have v_in_vertices_pre: \<open>v \<in> all_vertices os_pre (myfst t_in)\<close>
      using pending_consumed de1_consumed os_pre_eq
      unfolding all_vertices_def by simp
    have v_in_edge_vertices_pre: \<open>v \<in> edge_vertices (all_edges os_pre (myfst t_in))\<close>
      using v_in_vertices_pre edge_vertices_all_edges[OF inv_pre] by simp
    have min_label_pre_cc:
      \<open>min_label os_pre (myfst t_in) v \<in> cc_of (all_edges os_pre (myfst t_in)) v\<close>
      using labels_inv_pre[of \<open>myfst t_in\<close>] v_in_edge_vertices_pre
      unfolding labels_inv_def by blast
    have cc_final: \<open>\<And>q. myfst t \<le> q \<Longrightarrow>
    snd (de1 os_label_prop' d) \<in> cc_of (all_edges os_label_prop' q) (fst (de1 os_label_prop' d))\<close>
    proof -
      fix q
      assume t_le_q: \<open>myfst t \<le> q\<close>
      have cur_t_le_q: \<open>cur_t \<le> q\<close>
        using t_le_q t_fst by simp
      have event_le_q: \<open>myfst t_in \<le> q\<close>
        using event_le_cur cur_t_le_q by simp
      have l_cc_final_v: \<open>l \<in> cc_of (all_edges os_label_prop' q) v\<close>
        using l_cc_consumed[OF event_le_q] all_edges_final[of q] by simp
      have min_label_cc_final_v:
        \<open>min_label os_pre (myfst t_in) v \<in> cc_of (all_edges os_label_prop' q) v\<close>
        using min_label_pre_cc all_edges_pre[of \<open>myfst t_in\<close>] all_edges_final[of q]
          all_edges_mono[OF event_le_q, of ?consumed] cc_of_mono
        by metis
      have l'_cc_final_v: \<open>l' \<in> cc_of (all_edges os_label_prop' q) v\<close>
        using l'_def l_cc_final_v min_label_cc_final_v by (auto simp: min_def)
      have reach: \<open>reachable (all_edges os_label_prop' q) v v'\<close>
        using edge_final[OF cur_t_le_q] unfolding reachable_def by auto
      have cc_eq: \<open>cc_of (all_edges os_label_prop' q) v = cc_of (all_edges os_label_prop' q) v'\<close>
        by (rule cc_of_eq_if_reachable[OF reach])
      show \<open>snd (de1 os_label_prop' d) \<in> cc_of (all_edges os_label_prop' q) (fst (de1 os_label_prop' d))\<close>
        using decode l'_cc_final_v cc_eq by simp
    qed

    show \<open>myfst t \<in> set (timestamps os_label_prop') \<and>
    fst (de1 os_label_prop' d) \<in> all_vertices os_label_prop' (myfst t) \<and>
    (\<forall>q. myfst t \<le> q \<longrightarrow>
      snd (de1 os_label_prop' d) \<in> cc_of (all_edges os_label_prop' q) (fst (de1 os_label_prop' d)))\<close>
      using ts_final vertex_final cc_final by blast
  qed
  show ?thesis
    unfolding wf_label_prop_updates_def
    by (intro ballI) (clarify, rule per_msg, simp)
qed



lemma label_prop_input1_loop_updates_preserves_dataplane_tracker_inv_corrected:
  fixes os_label_prop :: \<open>(nat \<times> nat + nat set set, nat, nat, nat) label_propagation_state\<close>
    and os :: \<open>3 \<Rightarrow> (2, nat \<times> nat + nat set set, (nat, nat) myprod) operator_state\<close>
    and cbufs :: \<open>3 \<times> 2 \<Rightarrow> ((nat \<times> nat + nat set set) \<times> (nat, nat) myprod) buf\<close>
    and sg :: \<open>(3, 2, (nat, nat) myprod) subgraph\<close>
    and T :: \<open>nat list\<close>
    and G :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close>
    and V :: \<open>nat \<Rightarrow> nat list\<close>
    and L :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  assumes step: \<open>(cbufs', os_label_prop', os') = label_prop_input1_loop_updates cbufs os_label_prop os\<close>
    and D: \<open>dataflow_topology (summ sg) (-+-)\<close>
    and GR: \<open>graph_summar_nt (summ sg) (nxt sg) (os(1 := op_state_base os_label_prop))\<close>
    and Nxt: \<open>nxt sg = graph_to_nxt (summ sg)\<close>
    and Inv: \<open>dataplane_tracker_inv (os(1 := op_state_base os_label_prop)) cbufs sg\<close>
    and label_prop_extension:
    \<open>os_label_prop = operator_state.extend (op_state_base os_label_prop) \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
          en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
    and Summ: \<open>summ sg = antichain_from_list \<circ>\<circ> raw_summary\<close>
    and Intsum: \<open>\<forall>n. intsum ((os(1 := op_state_base os_label_prop)) n) =
      (\<lambda>p1 p2. raw_summary (Loc n (Trg p1)) (Loc n (Src p2)))\<close>
    and IOC1: \<open>input_ocaps_inv os_label_prop\<close>
    and IOC2: \<open>input_ocaps_inv (os 2)\<close>
  shows \<open>dataplane_tracker_inv (os'(1 := op_state_base os_label_prop')) cbufs' sg\<close>
proof -
  have step':
    \<open>(cbufs', os_label_prop', os'(1 := op_state_base os_label_prop)) =
      label_prop_input1_loop_updates cbufs os_label_prop (os(1 := op_state_base os_label_prop))\<close>
    by (rule label_prop_input1_loop_updates_corrected_os[OF step])
  have label_prop_extension':
    \<open>os_label_prop = operator_state.extend ((os(1 := op_state_base os_label_prop)) 1)
      \<lparr>en1 = Inl, de1 = projl, is_en1 = isl,
        en2 = Inr, de2 = projr, is_en2 = isr, timestamps = T, graph = G, vertices = V, label = L\<rparr>\<close>
    using label_prop_extension by simp
  have IOC1': \<open>input_ocaps_inv ((os(1 := op_state_base os_label_prop)) 1)\<close>
    using IOC1 by (simp add: input_ocaps_inv_op_state_base)
  have IOC2': \<open>input_ocaps_inv ((os(1 := op_state_base os_label_prop)) 2)\<close>
    using IOC2 by simp
  have inv':
    \<open>dataplane_tracker_inv
      ((os'(1 := op_state_base os_label_prop))(1 := op_state_base os_label_prop')) cbufs' sg\<close>
    by (rule label_prop_input1_loop_updates_preserves_dataplane_tracker_inv
        [OF step' D GR Nxt Inv label_prop_extension' Summ Intsum IOC1' IOC2'])

  then show ?thesis
    by simp
qed


section \<open>loop_updates\<close>

subsection \<open>Recursive function\<close>



lemma label_prop_edge_batch_all_vertices:
  assumes \<open>updated_os = label_prop_edge_record_update (input_tl old_os 0) (event_t :: _ :: {plus, order}) v1 v2 vertex new_label\<close>
    \<open>batch = label_prop_edge_batch old_os updated_os event_t vertex new_label event_time\<close>
    \<open>en1 old_os = Inl\<close> \<open>de1 old_os = projl\<close> \<open>label_prop_upd_inv updated_os\<close> \<open>(d, cap) \<in> set batch\<close>
    \<open>t = myfst (capability.time cap)\<close> \<open>v = fst (de1 old_os d)\<close>
    \<open>vertex = v1 \<or> vertex = v2\<close>
  shows \<open>v \<in> all_vertices updated_os t\<close>
proof -
  have t_in: \<open>t \<in> set (timestamps updated_os)\<close> \<open>event_t \<le> t\<close>
    using assms(2,6,7) unfolding label_prop_edge_batch_def Let_def by auto
  have \<open>v = vertex \<or> v \<in> set (neighbors updated_os t vertex)\<close>
    using assms(2-4,6,7,8) by (auto simp add: label_prop_edge_batch_def Let_def split: if_splits)
  then show ?thesis
  proof
    assume \<open>v = vertex\<close>
    then show ?thesis
      using assms(1,9) t_in unfolding all_vertices_def
      by (force simp add: label_prop_edge_record_update_def input_tl_def)
  next
    assume \<open>v \<in> set (neighbors updated_os t vertex)\<close>
    then obtain t' where t': \<open>t' \<in> set (timestamps updated_os)\<close> \<open>t' \<le> t\<close>
      \<open>v \<in> set (graph updated_os t' vertex)\<close> unfolding neighbors_def by auto
    then have \<open>v \<in> set (vertices updated_os t')\<close>
      using label_prop_upd_inv_graph_edgeD[OF assms(5)] by blast
    then show ?thesis unfolding all_vertices_def using t'(1,2) by blast
  qed
qed

lemma label_prop_label_batch_all_vertices:
  assumes \<open>updated_os = label_prop_label_record_update old_os event_t vertex assigned_label\<close>
    \<open>batch = label_prop_label_batch old_os updated_os event_t vertex new_label event_time\<close>
    \<open>en1 old_os = Inl\<close> \<open>de1 old_os = projl\<close> \<open>label_prop_upd_inv old_os\<close> \<open>(d, cap) \<in> set batch\<close>
    \<open>t = myfst (capability.time cap)\<close> \<open>v = fst (de1 old_os d)\<close>
  shows \<open>v \<in> all_vertices updated_os t\<close>
proof -
  have \<open>v \<in> set (neighbors old_os t vertex)\<close>
    using assms(2-4,6,7,8) by (force simp add: label_prop_label_batch_def label_prop_neighbor_batch_def)
  then obtain t' where t': \<open>t' \<in> set (timestamps old_os)\<close> \<open>t' \<le> t\<close>
    \<open>v \<in> set (graph old_os t' vertex)\<close> unfolding neighbors_def by auto
  hence \<open>v \<in> set (vertices old_os t')\<close>
    using label_prop_upd_inv_graph_edgeD[OF assms(5)] by blast
  hence \<open>v \<in> all_vertices old_os t\<close> unfolding all_vertices_def using t'(1,2) by blast
  thus ?thesis by (simp add: assms(1) label_prop_label_record_update_def all_vertices_def)
qed

lemma label_prop_edge_batch_cc_of_all_edges:
  assumes UPD: \<open>updated_os = label_prop_edge_record_update (input_tl old_os 0) (myfst (t :: _ :: {plus, order})) v1 v2 vertex new_label\<close>
    and BATCH: \<open>batch = label_prop_edge_batch old_os updated_os (myfst t) vertex new_label t\<close>
    and EN1: \<open>en1 old_os = Inl\<close> and DE1: \<open>de1 old_os = projl\<close>
    and INV_UPD: \<open>label_prop_upd_inv updated_os\<close>
    and MEM: \<open>(d, cap) \<in> set batch\<close>
    and T'_GE: \<open>myfst (capability.time cap) \<le> t'\<close>
    and VW: \<open>(v, w) = de1 old_os d\<close>
    and CHOICE: \<open>(vertex, new_label) = (if min_label old_os (myfst t) v2 < min_label old_os (myfst t) v1
      then (v1, min_label old_os (myfst t) v2)
      else (v2, min_label old_os (myfst t) v1))\<close>
    and LABELS_OLD: \<open>\<forall>q. labels_inv (all_edges old_os q) (min_label old_os q)\<close>
    and INV_OLD: \<open>label_prop_upd_inv old_os\<close>
  shows \<open>w \<in> cc_of (all_edges updated_os t') v\<close>
proof -
  let ?t0 = \<open>myfst (capability.time cap)\<close>
  let ?E = \<open>all_edges updated_os ?t0\<close>
  let ?ns = \<open>neighbors updated_os ?t0 vertex\<close>
  have v_eq: \<open>v = fst (de1 old_os d)\<close> and w_eq': \<open>w = snd (de1 old_os d)\<close>
    using VW by (metis fst_conv, metis VW snd_conv)
  have t0_in: \<open>?t0 \<in> set (timestamps updated_os)\<close> and t0_ge: \<open>myfst t \<le> ?t0\<close>
    using BATCH MEM unfolding label_prop_edge_batch_def Let_def by auto
  have v_cases: \<open>v = vertex \<or> v \<in> set ?ns\<close>
    using BATCH EN1 DE1 MEM v_eq
    by (auto simp add: label_prop_edge_batch_def Let_def split: if_splits)
  have w_eq: \<open>w = fold min (map (min_label old_os ?t0) ?ns) (min (min_label old_os ?t0 vertex) new_label)\<close>
    using BATCH EN1 DE1 MEM w_eq'
    by (auto simp add: label_prop_edge_batch_def Let_def split: if_splits)
  have vx12: \<open>vertex = v1 \<or> vertex = v2\<close>
    using CHOICE by (auto split: if_splits)
  obtain vo where vo12: \<open>vo = v1 \<or> vo = v2\<close>
    and nl_eq: \<open>new_label = min_label old_os (myfst t) vo\<close>
    using CHOICE by (cases \<open>min_label old_os (myfst t) v2 < min_label old_os (myfst t) v1\<close>) auto
  have mt_ts: \<open>myfst t \<in> set (timestamps updated_os)\<close>
    using UPD by (simp add: label_prop_edge_record_update_def input_tl_def)
  have v12_av: \<open>v1 \<in> all_vertices updated_os ?t0\<close> \<open>v2 \<in> all_vertices updated_os ?t0\<close>
    using UPD mt_ts t0_ge unfolding all_vertices_def
    by (force simp add: label_prop_edge_record_update_def input_tl_def)+
  have v12_nb: \<open>v2 \<in> set (neighbors updated_os ?t0 v1)\<close> \<open>v1 \<in> set (neighbors updated_os ?t0 v2)\<close>
    using UPD mt_ts t0_ge unfolding set_neighbors
    by (force simp add: label_prop_edge_record_update_def input_tl_def)+
  have edge_new: \<open>(v1, v2) \<in> ?E\<close> \<open>(v2, v1) \<in> ?E\<close>
    using v12_av v12_nb unfolding all_edges_def by auto
  have edges_sub: \<open>all_edges old_os q \<subseteq> all_edges updated_os q\<close> for q
    using UPD unfolding all_edges_def all_vertices_def set_neighbors
    by (fastforce simp add: label_prop_edge_record_update_def input_tl_def split: if_splits)
  have vertex_ev: \<open>vertex \<in> edge_vertices ?E\<close>
    using vx12 edge_new unfolding edge_vertices_def by (auto simp add: Field_def)
  have nb_edge: \<open>x \<in> set ?ns \<Longrightarrow> (vertex, x) \<in> ?E\<close> for x
    using label_prop_upd_inv_graph_edgeD[OF INV_UPD] vx12 v12_av
    unfolding all_edges_def all_vertices_def set_neighbors by blast
  have nb_ev: \<open>x \<in> set ?ns \<Longrightarrow> x \<in> edge_vertices ?E\<close> for x
    using nb_edge unfolding edge_vertices_def by (auto simp add: Field_def)
  have cand_x: \<open>min_label old_os ?t0 x \<in> cc_of ?E x\<close>
    if x_ev: \<open>x \<in> edge_vertices ?E\<close> for x
  proof (cases \<open>x \<in> all_vertices old_os ?t0\<close>)
    case True
    then have \<open>x \<in> edge_vertices (all_edges old_os ?t0)\<close>
      using edge_vertices_all_edges[OF INV_OLD] by simp
    then have \<open>min_label old_os ?t0 x \<in> cc_of (all_edges old_os ?t0) x\<close>
      using LABELS_OLD unfolding labels_inv_def by blast
    then show ?thesis
      using cc_of_mono edges_sub by blast
  next
    case False
    then have \<open>min_label old_os ?t0 x = x\<close>
      using min_label_eq_self_if_not_all_vertices'[OF INV_OLD] by blast
    then show ?thesis
      using cc_of_self x_ev by fastforce
  qed
  have cand_nl: \<open>new_label \<in> cc_of ?E vertex\<close>
  proof -
    have vo_ev: \<open>vo \<in> edge_vertices ?E\<close>
      using vo12 edge_new unfolding edge_vertices_def by (auto simp add: Field_def)
    have \<open>new_label \<in> cc_of ?E vo\<close>
    proof (cases \<open>vo \<in> all_vertices old_os (myfst t)\<close>)
      case True
      then have \<open>new_label \<in> cc_of (all_edges old_os (myfst t)) vo\<close>
        using LABELS_OLD nl_eq edge_vertices_all_edges[OF INV_OLD]
        unfolding labels_inv_def by auto
      then have \<open>new_label \<in> cc_of (all_edges updated_os (myfst t)) vo\<close>
        using cc_of_mono edges_sub by blast
      then show ?thesis
        using cc_of_mono all_edges_mono[OF t0_ge] by blast
    next
      case False
      then have \<open>new_label = vo\<close>
        using min_label_eq_self_if_not_all_vertices'[OF INV_OLD] nl_eq by blast
      then show ?thesis
        using cc_of_self vo_ev by fastforce
    qed
    moreover have \<open>cc_of ?E vo = cc_of ?E vertex\<close>
      using vx12 vo12 edge_new cc_of_eq_if_reachable
      unfolding reachable_def by (metis UnCI r_into_rtrancl)
    ultimately show ?thesis by simp
  qed
  have w_vertex: \<open>w \<in> cc_of ?E vertex\<close>
  proof -
    have \<open>w \<in> insert (min (min_label old_os ?t0 vertex) new_label)
        (set (map (min_label old_os ?t0) ?ns))\<close>
      unfolding w_eq fold_min_Min by (rule Min_in) auto
    then consider (init) \<open>w = min (min_label old_os ?t0 vertex) new_label\<close>
      | (nb) x where \<open>x \<in> set ?ns\<close> \<open>w = min_label old_os ?t0 x\<close>
      by auto
    then show ?thesis
    proof cases
      case init
      then have \<open>w = min_label old_os ?t0 vertex \<or> w = new_label\<close>
        by (simp add: min_def)
      then show ?thesis
        using cand_x[OF vertex_ev] cand_nl by auto
    next
      case nb
      then have \<open>w \<in> cc_of ?E x\<close>
        using cand_x[OF nb_ev] by blast
      moreover have \<open>cc_of ?E x = cc_of ?E vertex\<close>
        using nb_edge[OF nb(1)] cc_of_eq_if_reachable
        unfolding reachable_def by (metis UnCI r_into_rtrancl)
      ultimately show ?thesis by simp
    qed
  qed
  have \<open>w \<in> cc_of (all_edges updated_os t') vertex\<close>
    using w_vertex cc_of_mono all_edges_mono[OF T'_GE] by blast
  moreover have \<open>cc_of (all_edges updated_os t') vertex = cc_of (all_edges updated_os t') v\<close>
  proof -
    have \<open>reachable (all_edges updated_os t') vertex v\<close>
      using v_cases
    proof
      assume \<open>v = vertex\<close>
      then show ?thesis by (simp add: reachable_refl)
    next
      assume \<open>v \<in> set ?ns\<close>
      then have \<open>(vertex, v) \<in> ?E\<close> by (rule nb_edge)
      then have \<open>(vertex, v) \<in> all_edges updated_os t'\<close>
        using all_edges_mono[OF T'_GE] by blast
      then show ?thesis
        unfolding reachable_def by (metis UnCI r_into_rtrancl)
    qed
    then show ?thesis by (rule cc_of_eq_if_reachable)
  qed
  ultimately show ?thesis by simp
qed
end
