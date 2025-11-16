theory Timely_Infrastructure

imports
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.BNA_Operators
  Progress_Tracking.Propagate
  Nondeterministic_Dataflow.Eval
  "HOL-Library.While_Combinator"
  "../propagation_extras/Executable"
  Zero_Cyc_Check
  Locations
  Operators_Utils
  DataplaneUtils
  Containers.Collection_Order
begin 

declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]

(*
  TODO:
  Correctness of max_top
  Correctness of dataflow compilation
  Loops
  collatz_op
  Correctness of collatz_op
  unordered_input_top
  wcc_op: https://timelydataflow.github.io/differential-dataflow/chapter_4/chapter_4_1.html
  Correctness of wcc_op
  Scopes (change timestamp type, maybe not now)
  Type inference for locations (if it is not so hard)
  Nominal wiring (if it is not so hard)
  Provide operator builders
*)


(* FIXME: move me *)
fun rmdups where
  "rmdups S [] = []"
| "rmdups S (x # xs) = (if x \<in> S then rmdups S xs else x # (rmdups (insert x S) xs))"

lemma set_rmdups[simp]:
  "set (rmdups S xs) = set xs - S"
  by (induct xs arbitrary: S) auto

lemma rmdups_rmdups[simp]:
  "rmdups S1 (rmdups S2 xs) = rmdups (S1 \<union> S2) xs"
  by (induct xs arbitrary: S1 S2) (auto simp add: insert_absorb)

lemma rmdups_append[simp]:
  "rmdups S (xs @ ys) = rmdups S xs @ rmdups (S \<union> set xs) ys"
  by (induct xs arbitrary: S ys) (auto simp add: insert_absorb)

lemma rmdups_cong:
  "A \<inter> set xs = B \<inter> set xs \<Longrightarrow>
   rmdups A xs = rmdups B xs"
  apply (induct xs arbitrary: A B)
   apply simp
  apply (smt (verit, best) Diff_Diff_Int Diff_iff Int_insert_left_if1 insert_absorb inter_eq_subsetI list.inject list.set(2) list.set_intros(1) rmdups.simps(2) set_subset_Cons)
  done

lemma rmdups_NilI:
  "(set xs \<subseteq> A \<and> xs \<noteq> []) \<or> xs = [] \<Longrightarrow>
   rmdups A xs = []"
  apply (induct xs arbitrary: A)
   apply simp_all
  done

lemma rmdups_insert_NilI:
  "(set xs = {a} \<and> xs \<noteq> []) \<or> xs = [] \<Longrightarrow>
   rmdups (insert a A) xs = []"
  apply (induct xs arbitrary: A)
   apply auto
  done

definition "DEBUG = False"

definition "trace = (if DEBUG then Debug.tracing else (\<lambda> x y. y))"

lemma trace_simp[simp]:
  "trace x = id"
  by (auto simp add: trace_def)

(* Inspired by timely/src/progress/change_batch.rs:12 *)
type_synonym 'a change_batch = "'a list"

(* Inspired by timely/src/progress/subgraph.rs:237 *)
record ('id, 'p, 't) subgraph =
  pt_tr :: "(('id, 'p) location, 't) configuration"
  edges :: "('id, 'p) location \<Rightarrow> ('id, 'p) location list"
  summ :: "('id, 'p) location \<Rightarrow> ('id, 'p) location \<Rightarrow> 't antichain"

datatype ('id, 'p, 's, 'd, 't) dataflow_tree = 
  "apply": Logic "('p option, 'p option, 's + 'd) op" "'p port \<Rightarrow> 'p port \<Rightarrow> 't antichain"
  | Comp "'id \<times> 'p \<Rightarrow> ('id \<times> 'p) option" "('id, 'p, 's, 'd, 't) dataflow_tree" "('id, 'p, 's, 'd, 't) dataflow_tree"

fun compile_dataflow_tree_aux :: "'id :: {minus, plus, one, ord} \<Rightarrow> ('id, 'p, 's, 'd, 't :: {zero, order}) dataflow_tree \<Rightarrow>
    'id \<times> (('id, 'p) location \<Rightarrow> ('id, 'p) location \<Rightarrow> 't antichain) \<times> ('id + 'id \<times> 'p, 'id + 'id \<times> 'p, 's + 'd) op" where
  "compile_dataflow_tree_aux n (Logic op su) = (n + 1,
    (\<lambda> l1 l2. 
    if n = node l1 \<and> n = node l2 \<and> is_Trg (port l1) \<and> is_Src (port l2) 
    then su (port l1) (port l2)
    else frontier {#}\<^sub>z),
    map_op (case_option (Inl n) (\<lambda> p. Inr (n, p))) (case_option (Inl n) (\<lambda> p. Inr (n, p))) op)"
| "compile_dataflow_tree_aux n (Comp wire dt1 dt2) = (
    let (n', summary1, op1) = compile_dataflow_tree_aux n dt1 in
    let (n'', summary2, op2) = compile_dataflow_tree_aux n' dt2 in
    (n'', \<lambda> l1 l2. 
     if node l1 \<ge> n \<and> node l1 < n' \<and> node l2 \<ge> n' \<and> is_Src (port l1) \<and> is_Trg (port l2)
     then (case wire (node l1 - n, idp (port l1)) of 
             None \<Rightarrow> frontier {#}\<^sub>z 
           | Some (offset, q) \<Rightarrow> (if node l2 = n' + offset \<and> q = idp (port l2) then frontier (abs_zmultiset (mset [0], {#})) else frontier {#}\<^sub>z )) 
     else summary1 l1 l2 + summary2 l1 l2,
     map_op (case_sum id id) (case_sum id id)
     (comp_op (case_sum (\<lambda> _. None) ((case_option None (Some o Inr)) o (\<lambda> (nid, p). case wire (nid - n, p) of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (n' + offset, q)))) (\<lambda> _. []) op1 op2))
   )"

(* value  "(fst o snd) (compile_dataflow_tree_aux (0 :: 4)
       (Comp [ (1, 0) \<mapsto> (3, 0) ]
         (Comp (\<lambda> l. None) (Logic \<oslash>) (Logic \<oslash>))
         (Comp (\<lambda> l. None) (Logic \<oslash>) (Logic \<oslash>))))
      (Loc 1 (Src 1)) (Loc 3 (Trg (1 :: 1)))" *)

definition "compile_dataflow_tree df = (
  let (_, s, op) = compile_dataflow_tree_aux 0 df in
  if \<not> has_zero_cyc s \<and>
     no_self_loop_checker s \<and>
     implementation_graph_checker (weights_to_graph_fun (remove_non_zero_weights s))
  then (s, op)
  else Code.abort (STR ''Control plane could not be build'') (\<lambda> _. (\<lambda> _ _. frontier {#}\<^sub>z, \<oslash>)))"

abbreviation "df_ex1 \<equiv> (Comp [ (1, 0) \<mapsto> (1, 0) ]
         (Comp (\<lambda> l. None) (Logic \<oslash> (\<lambda>_ _. frontier {#0#}\<^sub>z)) (Logic \<oslash> (\<lambda>_ _. frontier {#0#}\<^sub>z)))
         (Comp (\<lambda> l. None) (Logic \<oslash> (\<lambda>_ _. frontier {#0#}\<^sub>z)) (Logic \<oslash> (\<lambda>_ _. frontier {#0#}\<^sub>z)))) :: (4, 4, unit, nat, nat) dataflow_tree"

(* value "fst (compile_dataflow_tree
       df_ex1)
       (Loc 1 (Src 0)) (Loc 3 (Trg 0))"
 *)

lemma compile_dataflow_tree_aux_same_loc:
  "(n'', summar, op) = compile_dataflow_tree_aux n df \<Longrightarrow>
   summar loc loc = {}\<^sub>A"
  apply (induct df arbitrary: n n'' op summar)
  subgoal
    by (cases loc; simp add: frontier_empty_zmset split: port.splits if_splits)
  subgoal for wire dt1 dt2 n n''
    apply (cases "compile_dataflow_tree_aux n dt1")
    subgoal for n' summar'
      apply (cases "compile_dataflow_tree_aux n' dt2")
      subgoal for n''' summar''
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec[of _ n'])
        apply (drule meta_spec[of _ n'])
        apply (drule meta_spec[of _ n''])
        apply (drule meta_spec)
        apply (drule meta_spec[of _ summar'])
        apply (drule meta_spec)
        apply (drule meta_spec[of _ summar''])
        apply (drule meta_mp)
        apply simp
        apply (drule meta_mp)
        apply simp
        apply (simp split: if_splits)
        apply safe
        subgoal
          by (auto 0 0 simp add: frontier_empty_zmset port.case_eq_if split: if_splits option.splits)
        done
      done
    done
  done

lemma enum_dataflow_topology_compile_dataflow[simp]:
  "enum_dataflow_topology (fst (compile_dataflow_tree (df :: (_, _, _, _, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le}) dataflow_tree))) (+)"
  apply standard
       apply (simp_all add: add_mono_thms_linordered_semiring(1) Groups.add_ac(1))
  subgoal
    unfolding compile_dataflow_tree_def Let_def
    apply (cases "compile_dataflow_tree_aux 0 df"; simp)
    using compile_dataflow_tree_aux_same_loc frontier_empty_zmset apply metis
    done
  subgoal
    unfolding compile_dataflow_tree_def Let_def
    apply (cases "compile_dataflow_tree_aux 0 df")
    apply (simp add: no_self_loop_checker_is_graph_checker split: if_splits)
    subgoal
      apply (rule decide_graph_construction[where t=0, simplified, rotated])
      apply assumption+
      done
    subgoal
      apply (rule empty_graph_no_zero_cyc)
      apply assumption+
      apply simp_all
      apply standard
        apply (simp_all add: add_mono_thms_linordered_semiring(1) frontier_empty_zmset)
      done
    done
  done

global_interpretation dataflow_topology_from_tree: enum_dataflow_topology "fst (compile_dataflow_tree (df :: (_, _, _, _, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le}) dataflow_tree))" "(+)"
  for df
  defines take_step' = "enum_dataflow_topology.take_step (fst (compile_dataflow_tree df)) (+)"
    and after_summary = "dataflow_topology.after_summary (+) :: 't zmultiset \<Rightarrow> 't antichain \<Rightarrow> 't zmultiset"
  by simp

notation dataflow_topology_from_tree.followed_by (infixl \<open>-+-\<close> 65)

definition take_step_locale where
  "take_step_locale df = take_step' df cless"

fun take_step where
  "take_step summary (CM loc t delta) c =
  (let c_pointstamps_old = c_pts c loc; c_pointstamps_new = (c_pts c)(loc := update_zmultiset (c_pts c loc) t delta)
   in c\<lparr>c_pts := c_pointstamps_new, c_work := (c_work c)(loc := c_work c loc + frontier_change_code c_pointstamps_old (c_pointstamps_new loc))\<rparr>)"
| "take_step summary PR c =
   (let (t, loc) = mymin_code (t_loc_pairs c); c_implications_old = c_imp c loc; c_implications_new = (c_imp c)(loc := c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#});
    c_worklist_removed_loc = map_entry loc (filter_zmset (\<lambda>t'. t' \<noteq> t)) (c_work c)
    in c\<lparr>c_work := \<lambda>loc'. c_worklist_removed_loc loc' + after_summary (frontier_change_code c_implications_old (c_implications_new loc)) (summary loc loc'),
        c_imp := c_implications_new\<rparr>)"

definition "propagate_all_locale summary df c0 = (while_option (Not o (worklist_is_empty summary))
                                           (take_step_locale df PR) c0)"

abbreviation empty_conf where
  "empty_conf \<equiv> \<lparr>c_work = (\<lambda> _.  {#}\<^sub>z), c_pts = (\<lambda> _.  {#}\<^sub>z), c_imp = (\<lambda> _. {#}\<^sub>z)\<rparr>"

definition "propagate_all summary c0 = (while_option (Not o (worklist_is_empty summary))
                                        (take_step summary PR) c0)"

lemma take_step_fast_code[simp]:
  "take_step_locale df x = take_step (fst (compile_dataflow_tree df)) x"
  unfolding take_step_locale_def
  apply (cases x)
  apply (auto simp add: fun_eq_iff mymin_code_def)
  done

lemma propagate_all_locale_eq_propagate_all:
  "propagate_all_locale (fst (compile_dataflow_tree df)) df c = propagate_all (fst (compile_dataflow_tree df)) c"
  unfolding propagate_all_locale_def Let_def propagate_all_def by (auto split: prod.splits)

abbreviation "show_frontier x \<equiv> let f = Max_antichain x in if f = 42 then STR ''{}'' else STR ''{ '' + show_nat (Max_antichain x) + STR '' }''" 

abbreviation "print_frontier x \<equiv> trace ((STR ''Frontier: '') + show_frontier x)" 

abbreviation "show_frontiers impf \<equiv> show_list (show_prod show_loc show_frontier) (map (\<lambda> l. (l, frontier (impf l))) enum_location_inst.enum_location)"

(* Inspired by timely/src/progress/subgraph.rs:453 *)
(* First migrate all change batches to the worklist, then call propagate_all_locale *)
definition "change_multiplicities summary xs conf = fold (\<lambda> (l, t, m) c. take_step summary (CM l t m) c) xs conf"

definition "propagate_pointstamps summary conf cbs = propagate_all summary (change_multiplicities summary cbs conf)"

abbreviation "init_subgraph summary \<equiv>
   \<lparr> pt_tr = the (propagate_pointstamps summary empty_conf (concat (map (\<lambda> nid. map (\<lambda> p. (Loc nid (Src p), 0, 1)) enum_class.enum) enum_class.enum))),
   edges = (\<lambda> l1. [l2 \<leftarrow> enum_class.enum. \<not> is_empty_antichain (summary l1 l2) \<and> is_Src (port l1) \<and> is_Trg (port l2) ]),
   summ = summary \<rparr>"


(* Inspired by timely/src/dataflow/operators/generic/builder_rc.rs:29 and timely/src/progress/operate.rs:63 *)
(* This is the shared that the operator exposes to the subgraph *)
record ('p, 't) shared_state =
  cons :: "('p \<times> 't \<times> int) change_batch"
  inte :: "('p \<times> 't \<times> int) change_batch"
  prod :: "('p \<times> 't \<times> int) change_batch"

(* Inspired by timely/src/progress/subgraph.rs:759 *)
definition extract_progress where
  "extract_progress nid edg st =
    map (\<lambda> (p, t, m). (Loc nid (Trg p), t, -m)) (cons st) @ 
    map (\<lambda> (p, t, m). (Loc nid (Src p), t, m)) (inte st) @
    concat (map (\<lambda> (p, t, m). map (\<lambda> l. (l, t, m)) (edg (Loc nid (Src p)))) (prod st))"

term "((o) frontier) ` imp_fron"

(* Inspired by timely/src/dataflow/operators/capability.rs:62 *)
datatype ('p, 't) capability = Cap (time: "'t :: plus") (out: 'p)

corec dataflow_op where
  "dataflow_op sg op = Choice (cimage (\<lambda> op. case op of 
     Read (Inl nid) f \<Rightarrow> (case propagate_all (summ sg) (pt_tr sg) of
         Some conf' \<Rightarrow> let sg' = sg\<lparr> pt_tr := conf' \<rparr> in
         let imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) in Silent (dataflow_op sg' (f (Inl (Inr (frontier o imp_fron))))))
   | Read (Inr (nid, p)) f \<Rightarrow> Read (nid, p) (\<lambda> x. dataflow_op sg (f (Inr x)))
   | Write op' (Inr (nid, p)) (Inr x) \<Rightarrow> Write (dataflow_op sg op') (nid, p) x
   | Silent op' \<Rightarrow> Silent (dataflow_op sg op')
   | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow> Silent (dataflow_op (sg\<lparr> pt_tr := (change_multiplicities (summ sg) (extract_progress nid (edges sg) st) (pt_tr sg)) \<rparr>) op')
   | _ \<Rightarrow> Code.abort (STR ''Operator in dataflow_op breaks contract'') (\<lambda> _. \<oslash>)) (choices op))"

lemma propagate_all_terminates[simp]:
  "propagate_all a b \<noteq> None"
  sorry

lemma change_multiplicities_terminates[simp]:
  "propagate_pointstamps summary conf cbs \<noteq> None"
  apply (induct cbs arbitrary: conf) 
  apply (auto simp add: propagate_pointstamps_def)
  done

lemma step_dataflow_op_elim:
  assumes "step io (dataflow_op sg op) op'"
  obtains
    nid p op'' x where "io = Inp (nid, p) x" "op' = dataflow_op sg op''" "step (Inp (Inr (nid, p)) (Inr x)) op op''"
  | nid p op'' x where "io = Out (nid, p) x" "op' = dataflow_op sg op''" "step (Out (Inr (nid, p)) (Inr x)) op op''"
  | op'' where "io = Tau" "op' = dataflow_op sg op''" "step Tau op op''"
  | nid op'' st where "io = Tau" "op' = dataflow_op (sg\<lparr> pt_tr := (change_multiplicities (summ sg) (extract_progress nid (edges sg) st) (pt_tr sg)) \<rparr>) op''" "step (Out (Inl nid) (Inl (Inl st))) op op''"
  | nid op'' imp_fron sg' where "io = Tau" "sg' = (case propagate_all (summ sg) (pt_tr sg) of Some conf' \<Rightarrow> sg\<lparr> pt_tr := conf' \<rparr>)"
    "imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p)))" "op' = dataflow_op sg' op''" "step (Inp (Inl nid) (Inl (Inr (frontier o imp_fron)))) op op''"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) dataflow_op.code)
  apply (simp split: if_splits)
  apply (elim stepChoiceE)
  subgoal for op'
    apply (auto del: disjCI split: op.splits sum.splits option.splits)
           apply fastforce+
    done
  done

lemma step_Tau_dataflow_op_Inp_Inl_intro[intro]:
  "step (Inp (Inl nid) (Inl (Inr (frontier o imp_fron)))) op op' \<Longrightarrow>
   conf' = the (propagate_all(summ sg) (pt_tr sg)) \<Longrightarrow>
   sg' = sg\<lparr> pt_tr := conf' \<rparr> \<Longrightarrow>
   imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) \<Longrightarrow>
   step Tau (dataflow_op sg op) (dataflow_op sg' op')"
  apply (subst dataflow_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Tau_dataflow_op_Out_Inl_intro[intro]:
  "step (Out (Inl nid) (Inl (Inl st))) op op' \<Longrightarrow>
   sg' = sg\<lparr> pt_tr := (change_multiplicities (summ sg) (extract_progress nid (edges sg) st) (pt_tr sg)) \<rparr> \<Longrightarrow>
   step Tau (dataflow_op sg op) (dataflow_op sg' op')"
  apply (subst dataflow_op.code)
  apply (force elim: step_choicesE split: sum.splits option.splits)
  done


lemma step_Tau_dataflow_op_Tau_intro[intro]:
  "step Tau op op' \<Longrightarrow>
   step Tau (dataflow_op sg op) (dataflow_op sg op')"
  apply (subst dataflow_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Out_dataflow_op_Out_Inr_intro[intro!]:
  "step (Out (Inr (nid, p)) (Inr x)) op op' \<Longrightarrow>
   step (Out (nid, p) x) (dataflow_op sg op) (dataflow_op sg op')"
  apply (subst dataflow_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Inp_dataflow_op_Inp_Inr_intro[intro!]:
  "step (Inp (Inr (nid, p)) (Inr x)) op op' \<Longrightarrow>
   step (Inp (nid, p) x) (dataflow_op sg op) (dataflow_op sg op')"
  apply (subst dataflow_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma dataflow_op_end_op:
  "dataflow_op sg \<oslash> = \<oslash>"
  apply (subst dataflow_op.code)
  apply simp
  done

lemma steps_Tau_dataflow_op_Tau_intro[intro]:
  "steps (replicate n Tau) op op' \<Longrightarrow>
   (step Tau ^^ n) (dataflow_op sg op) (dataflow_op sg op')"
  apply (induct n arbitrary: op op' sg)
   apply clarsimp+
  apply (metis (no_types, lifting) relcompp_apply relpowp_commute step_Tau_dataflow_op_Tau_intro)
  done

lemma step_Taus_dataflow_op_Taus_intro[intro]:
  "(step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow>
   (step Tau)\<^sup>*\<^sup>*  (dataflow_op sg op) (dataflow_op sg op')"
  apply (induct op' rule: rtranclp_induct)
   apply force
  apply (meson rtranclp.intros(2) step_Tau_dataflow_op_Tau_intro)
  done


lemma step_tau_pow_dataflow_op[intro]:
  "(step Tau ^^ n) op op' \<Longrightarrow>
   (step Tau ^^ n) (dataflow_op sg op) (dataflow_op sg op')"
  by (induct n arbitrary:  op') auto

lemma step_tau_pow_map_op[intro]:
  "(step Tau ^^ n) op op' \<Longrightarrow> (step Tau ^^ n) (map_op f g op) (map_op f g op')"
  apply (induct n arbitrary: op op')
   apply simp_all
  subgoal for n op op'
    apply (elim relcomppE)
    apply (intro relcomppI)
     apply blast
    apply auto
    done
  done

lemma dataflow_op_simps[simp]:
  "\<not> is_Read (dataflow_op sg op)"
  "\<not> is_Write (dataflow_op sg op)"
  "\<not> is_Silent (dataflow_op sg op)"
  "is_Choice (dataflow_op sg op)"
  by (subst dataflow_op.code; simp)+

definition "compile_dataflow dt = (let (summary, op) = compile_dataflow_tree dt in
                                    let sg = init_subgraph summary in
                                    dataflow_op sg op)"

(* Inspired by timely/src/dataflow/channels/pushers/counter.rs:25 and timely/src/dataflow/channels/mod.rs:49 *)
(* writes maybe could support multiple different ports, then this one also would *)
abbreviation "push op p batch \<equiv> 
  writes op (trace (STR ''Pushing data!'') Some p) (map (\<lambda> (x, c). Inr (x, time c)) batch)"

abbreviation "delayed_cap c t \<equiv>
  (Cap (time c + abs t) (out c),
  \<lambda> op. Write op None 
     (Inl (Inl \<lparr> cons = [],
            inte = [(out c, time c, -1), (out c, time c + abs t, 1)],
            prod = [] \<rparr>)))"

(* The minted capability must depend on the internal wiring *)
abbreviation "pull i f \<equiv> (Read ((trace (STR ''Reading data'') Some) i)
  (\<lambda> x. case x of
    (Inr (d, t)) \<Rightarrow> Write (f (d, Cap t 0)) None (Inl (Inl \<lparr>  cons = [(i, t, 1)], inte = [(i, t, 1)], prod = [] \<rparr>))
   | _ \<Rightarrow> \<oslash>))"

definition
  "frontier_less_equal ft t = (\<not> is_empty_antichain (filter_antichain (\<lambda> f. f \<le> t) ft))"


lemma change_multiplicities_append:
  "change_multiplicities su (xs @ ys) = (\<lambda> c. change_multiplicities su ys (change_multiplicities su xs c))"
  unfolding change_multiplicities_def 
  apply (rule ext)
  apply simp
  done

lemma change_multiplicities_append_alt:
  "change_multiplicities su (xs @ ys) c = change_multiplicities su ys (change_multiplicities su xs c)"
  using change_multiplicities_append by metis

lemma change_multiplicities_append_comp:
  "change_multiplicities su (xs @ ys) = change_multiplicities su ys o change_multiplicities su xs"
  unfolding change_multiplicities_def
  apply simp
  done

lemma take_step_comm:
  "(take_step su (CM l2 t2 m2) \<circ>\<circ>\<circ> take_step) su (CM l1 t1 m1) = (take_step su (CM l1 t1 m1) \<circ>\<circ>\<circ> take_step) su (CM l2 t2 m2)"
  apply (rule ext)
  apply (auto simp add: fun_upd_twist update_zmultiset_comm)
  done

lemma take_step_plus[simp]:
  "take_step su (CM l t m) (take_step su (CM l t n) c) = take_step su (CM l t (m + n)) c"
  by (cases c; auto simp add: add.commute)

lemma change_multiplicitie_rev[simp]:
  "change_multiplicities su (rev xs) c = change_multiplicities su xs c"
  unfolding change_multiplicities_def
  apply (subst fold_rev)
  apply (clarsimp simp add: take_step_comm)+
  done

lemma change_multiplicities_comm:
  "change_multiplicities su (xs @ ys) c = change_multiplicities su (ys @ xs) c"
  unfolding change_multiplicities_def
  by (metis (mono_tags, lifting) change_multiplicitie_rev change_multiplicities_append change_multiplicities_def rev_append)

lemma change_multiplicities_simps[simp]:
  "change_multiplicities su [] c = c"
  "change_multiplicities su ((l, t, m) # xs) c = change_multiplicities su xs (take_step summary (CM l t m) c)"
  unfolding change_multiplicities_def by simp+

lemma change_multiplicities_simp_alt:
  "change_multiplicities su ((l, t, m) # xs) c = take_step su (CM l t m) (change_multiplicities su xs c)"
proof -
  have "change_multiplicities su ((l, t, m) # xs) c = change_multiplicities su (rev ((l, t, m) # xs)) c" using change_multiplicitie_rev by metis
  also have "\<dots> = take_step su (CM l t m) (change_multiplicities su (rev xs) c)" by (simp add: change_multiplicities_def foldr_conv_fold)
  ultimately show ?thesis by (metis change_multiplicitie_rev)
qed

lemma change_multiplicities_same_pointstamps_aux:
  "(\<forall> x \<in> set xs. \<forall> y \<in> set xs. fst x = fst y \<and> (fst o snd) x = (fst o snd) y) \<Longrightarrow>
   change_multiplicities su xs c = fold (\<lambda> m c. take_step su (CM ((fst o hd) xs) ((fst o snd o hd) xs) m) c) (map (snd o snd) xs) c"
  unfolding change_multiplicities_def
  apply (induct xs arbitrary: c)
  apply simp
  subgoal premises prems for a xs c
    using prems(2-) apply -
    apply (cases a; clarsimp)
    subgoal using prems(1) by (smt (verit) List.fold_cong fold_map fun_comp_eq_conv list.sel(1) list.set_cases list.set_intros(1))
    done
  done

lemma change_multiplicities_same_pointstamps:
  "(\<forall> x \<in> set xs. \<forall> y \<in> set xs. fst x = l \<and> (fst o snd) x = t) \<Longrightarrow>
   m = sum_list (map (snd o snd) xs) \<Longrightarrow>
   change_multiplicities su xs c = take_step su (CM l t m) c"
  apply (induct xs arbitrary: c m)
  apply simp
  subgoal premises prems for x xs c m
    using prems(2-) apply -
    apply hypsubst_thin
    apply (cases x)
    subgoal for l t m
      apply (simp only: change_multiplicities_simp_alt)
      apply (subst prems(1))
      apply force
      apply (rule refl)
      apply clarsimp
      apply (intro conjI impI)
      subgoal by (metis (no_types) group_cancel.sub1 uminus_add_add_uminus update_zmultiset_comm update_zmultiset_plus)
      subgoal
        by blast 
      done
    done
  done

record ('p, 'd, 't) operator_state =
  consu :: "('p \<times> 't \<times> int) list"
  inter :: "('p \<times> 't \<times> int) list"              
  produ :: "('p \<times> 't \<times> int) list"
  input :: "'p \<Rightarrow> ('d \<times> 't) list"
  outpu :: "'p \<Rightarrow> ('d \<times> 't) list"
  front :: "'p \<Rightarrow> 't antichain"
  ocaps :: "'p \<Rightarrow> 't list"

abbreviation "delay_cap os cap incr \<equiv> (os\<lparr> inter := inter os @ [(out cap, time cap, -1), (out cap, time cap + incr, 1)] \<rparr>)"

definition "produce os cap batch = (if batch = [] then os else os\<lparr> outpu := (outpu os)(out cap := outpu os (out cap) @ map (\<lambda> x. (x, time cap)) batch), produ := produ os @ [(out cap, time cap, length batch)] \<rparr>)"

abbreviation "consume os p t len \<equiv> (if len = 0 then os else os\<lparr> consu := consu os @ [(p, t, len)] \<rparr>)"

abbreviation "choice4 op1 op2 op3 op4 \<equiv> choice2 (choice2 op1 op2) (choice2 op3 op4)"

abbreviation "choice5 op1 op2 op3 op4 op5 \<equiv> choice3 (choice2 op1 op2) (choice2 op3 op4) op5"

abbreviation "mint_cap os p t \<equiv> os\<lparr> inter := inter os @ [(p, t, 1)] \<rparr>"
abbreviation \<open>mint os caps p t \<equiv> if t \<in> set (caps p) then (caps, os) else (caps(p := caps p @ [t]), mint_cap os p t)\<close>


abbreviation "produces os batch \<equiv> os\<lparr> outpu := (\<lambda> p. outpu os p @ map (\<lambda> (x, cap). (x, time cap)) (filter (\<lambda> (x, cap). out cap = p) batch)), produ := produ os @ map (\<lambda> (x, cap). (out cap, time cap, 1)) batch \<rparr>"

abbreviation "drop_caps_old os caps \<equiv> (os\<lparr> inter := inter os @ map (\<lambda> cap. (out cap, time cap, -1)) caps \<rparr>)"

abbreviation "send_output op p x \<equiv> Write op (Some p) (Inr x)"
abbreviation "send_progress op st \<equiv> Write op None (Inl (Inl st))"

abbreviation "obtain_progress os \<equiv> (os\<lparr> consu := [], inter := [], produ := [] \<rparr>, \<lparr> cons = consu os, inte = inter os, prod = produ os\<rparr>)"

fun remove_last where
  "remove_last x [] = []"
| "remove_last x xs = (if last xs = x then butlast xs else remove_last x (butlast xs) @ [last xs])"

abbreviation "drop_cap os cap \<equiv> os\<lparr> inter := inter os @ [(out cap, time cap, -1)], ocaps := (ocaps os) ((out cap) := remove_last (time cap) (ocaps os (out cap))) \<rparr>"

abbreviation "drop_caps os caps \<equiv> os\<lparr> inter := inter os @ map (\<lambda> cap. (out cap, time cap, -1)) caps, ocaps := (\<lambda> p. ocaps os p) \<rparr>"

abbreviation "add_cap os p t \<equiv> os\<lparr> inter := inter os @ [(p, t, 1)], ocaps := (ocaps os) (p := ocaps os p @ [t])  \<rparr>"

abbreviation "consumes os p t d \<equiv> add_cap (os\<lparr> consu := consu os @ [(p, t, 1)], input := BENQ p (d, t) (input os) \<rparr>) p t"



corec builder_op where
  \<open>builder_op ips ops fips fops os logic = choice5
  (Choice (cimage (\<lambda> os. Silent (builder_op ips ops fips fops os logic)) (logic os)))
  (Choice (cimage (\<lambda>p. case outpu os p of
    x # xs \<Rightarrow> send_output (builder_op ips ops fips fops (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>) logic) p x)
    (cfilter (\<lambda>p. outpu os p \<noteq> []) ops)))
  (let (os', st) = obtain_progress os
  in send_progress (builder_op ips ops fips fops os' logic) st)
  (Read None (\<lambda> st. if isl st \<and> isr (projl st) then builder_op ips ops fips fops (os\<lparr> front := projr (projl st) \<rparr>) logic else \<oslash>))
  (Choice (cimage (\<lambda>p. Read (Some p) (\<lambda> x. case x of Inl _ \<Rightarrow> \<oslash> | Inr (d, t) \<Rightarrow> builder_op ips ops fips fops (consumes os p t d) logic)) ips))\<close>

definition notifier_op where
  "notifier_op ips ops fips fops os logic = builder_op ips ops fips fops os 
   (\<lambda> os. logic os (\<lambda> p. filter (\<lambda> t. \<not> frontier_less_equal (front os p) t) (ocaps os p)))"


end