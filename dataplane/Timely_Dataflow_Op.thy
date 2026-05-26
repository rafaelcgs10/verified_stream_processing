theory Timely_Dataflow_Op

imports
  Timely_Progress
  Operators_Utils
begin

section \<open>Dataflow Wrapper Operator\<close>

text \<open>
  The corecursive wrapper couples operator transitions with control-plane propagation.
  The following lemmas characterize the induced transition system and lifting rules.
\<close>

corec dataflow_op where
  "dataflow_op sg op = Choice (cimage (\<lambda> op. case op of
     Read (Inl nid) f \<Rightarrow> (case propagate_all (summ sg) (pt_tr sg) of
         Some conf' \<Rightarrow> let sg' = sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr> in
         let imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) in Silent (dataflow_op sg' (f (Inl (Inr (frontier o imp_fron)))))
      | None \<Rightarrow> \<oslash>)
   | Read (Inr (nid, p)) f \<Rightarrow> Read (nid, p) (\<lambda> x. dataflow_op sg (f (Inr x)))
   | Write op' (Inr (nid, p)) (Inr x) \<Rightarrow> Write (dataflow_op sg op') (nid, p) x
   | Silent op' \<Rightarrow> Silent (dataflow_op sg op')
   | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow> Silent (dataflow_op (sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr>) op')
   | _ \<Rightarrow> Code.abort (STR ''Operator in dataflow_op breaks contract'') (\<lambda> _. \<oslash>))
   (choices op)
   )"

lemma dataflow_op_code[code]:
  "dataflow_op sg op = Choice (cimage (\<lambda> op. case op of
     Read (Inl nid) f \<Rightarrow> (case propagate_all (summ sg) (pt_tr sg) of
         Some conf' \<Rightarrow> let sg' = sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr> in
         let imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) in Silent (dataflow_op sg' (f (Inl (Inr (frontier o imp_fron)))))
      | None \<Rightarrow> \<oslash>)
   | Read (Inr (nid, p)) f \<Rightarrow>  (Read (nid, p) (\<lambda> x. dataflow_op sg (f (Inr x))))
   | Write op' (Inr (nid, p)) (Inr x) \<Rightarrow> (Write (dataflow_op sg op') (nid, p) x)
   | Silent op' \<Rightarrow> Silent (dataflow_op sg op')
   | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow>
      (Silent (dataflow_op (sg\<lparr> upfro := (\<lambda> _. True), pt_tr :=change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr>) op'))
   | _ \<Rightarrow> Code.abort (STR ''Operator in dataflow_op breaks contract'') (\<lambda> _. \<oslash>))
   (let ops = delay_cset (not_nop sg) 10000 (choices op) in
    let ops2 = delay_cset (is_Silent) 10000 ops in
    ops2)
   )"
  apply (simp only: delay_cset_def trace_simp id_def)
  apply (subst dataflow_op.code)
  apply auto
  done

subsection \<open>Transition Rules for @{const dataflow_op}\<close>

lemma step_dataflow_op_elim:
  assumes "step io (dataflow_op sg op) op'"
  obtains
    nid p op'' x where "io = Inp (nid, p) x" "op' = dataflow_op sg op''" "step (Inp (Inr (nid, p)) (Inr x)) op op''"
  | nid p op'' x where "io = Out (nid, p) x" "op' = dataflow_op sg op''" "step (Out (Inr (nid, p)) (Inr x)) op op''"
  | op'' where "io = Tau" "op' = dataflow_op sg op''" "step Tau op op''"
  | nid op'' st where "io = Tau" "op' = dataflow_op (sg\<lparr> upfro := (\<lambda> _. True), pt_tr := (change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg)) \<rparr>) op''" "step (Out (Inl nid) (Inl (Inl st))) op op''"
  | nid op'' imp_fron sg' where "io = Tau" "sg' = (case propagate_all (summ sg) (pt_tr sg) of Some conf' \<Rightarrow> sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr>)"
    "imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p)))" "op' = dataflow_op sg' op''" "step (Inp (Inl nid) (Inl (Inr (frontier o imp_fron)))) op op''"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) dataflow_op.code)
  apply (simp split: if_splits)
  apply (elim stepChoiceE)
  subgoal for op'
    apply (auto del: disjCI split: op.splits sum.splits option.splits simp flip: cin.rep_eq)
    subgoal by fastforce
    subgoal by fastforce
    subgoal by fastforce
    subgoal by fastforce
    subgoal by fastforce
    done
  done

lemma step_Tau_dataflow_op_Inp_Inl_intro[intro]:
  "step (Inp (Inl nid) (Inl (Inr (frontier o imp_fron)))) op op' \<Longrightarrow>
   propagate_all(summ sg) (pt_tr sg) = Some conf' \<Longrightarrow>
   sg' = sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr> \<Longrightarrow>
   imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) \<Longrightarrow>
   step Tau (dataflow_op sg op) (dataflow_op sg' op')"
  apply (subst dataflow_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Tau_dataflow_op_Out_Inl_intro[intro]:
  "step (Out (Inl nid) (Inl (Inl st))) op op' \<Longrightarrow>
   sg' = sg\<lparr> upfro := (\<lambda> _. True), pt_tr := (change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg)) \<rparr> \<Longrightarrow>
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

lemma steps_Tau_dataflow_op_Tau_intro[intro]:
  "steps (replicate n Tau) op op' \<Longrightarrow>
   (step Tau ^^ n) (dataflow_op sg op) (dataflow_op sg op')"
  apply (induct n arbitrary: op op' sg)
   apply clarsimp+
  apply (metis (no_types, lifting) relcompp_apply relpowp_commute step_Tau_dataflow_op_Tau_intro)
  done

lemma steps_Tau_dataflow_op_steps_Out_intro[intro]:
  "steps (map (\<lambda> x. Out (Inr (nid, p)) (Inr x)) xs) op op' \<Longrightarrow>
   ys = map (\<lambda> x. Out (nid, p) x) xs \<Longrightarrow>
   (steps ys) (dataflow_op sg op) (dataflow_op sg op')"
  apply hypsubst_thin
  apply (induct xs arbitrary: op op' sg rule: rev_induct)
   apply clarsimp+
  apply fastforce
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


abbreviation init_conf where
  "init_conf summary \<equiv> the (propagate_all summary initial_conf)"

definition "init_subgraph summary =
   \<lparr> pt_tr = init_conf summary,
   nxt = graph_to_nxt summary,
   summ = summary, upfro = (\<lambda> _. True) \<rparr>"

definition "compile_dataflow chns dt = (let summary = antichain_from_list oo (dataflow_tree_to_graph dt) in
                                    let op = dataflow_tree_to_operator chns dt in
                                    let sg = init_subgraph summary in
                                    dataflow_op sg op)"



fun get_nid where
  "get_nid (Read (Inl nid) f) = Some nid"
| "get_nid (Read (Inr (nid, p)) f) = Some nid"
| "get_nid (Write op (Inr (nid, p)) (Inr x)) = Some nid"
| "get_nid (Write op (Inl nid) (Inl (Inl st))) = Some nid"
| "get_nid _ = None"

definition "is_busy sg op = (case get_nid op of None \<Rightarrow> True 
 | Some nid \<Rightarrow> 
    (\<forall> p. frontier (c_imp (pt_tr sg) (Loc nid (Trg p))) \<noteq> {}\<^sub>A \<or>
          frontier (c_imp (pt_tr sg) (Loc nid (Src p))) \<noteq> {}\<^sub>A))"

corec opt_dataflow_op where
  "opt_dataflow_op sg op = Choice (cimage (\<lambda> op. case op of
     Read (Inl nid) f \<Rightarrow> (case propagate_all (summ sg) (pt_tr sg) of
         Some conf' \<Rightarrow> let sg' = sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr> in
         let imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) in Silent (opt_dataflow_op sg' (f (Inl (Inr (frontier o imp_fron)))))
      | None \<Rightarrow> \<oslash>)
   | Read (Inr (nid, p)) f \<Rightarrow> Read (nid, p) (\<lambda> x. opt_dataflow_op sg (f (Inr x)))
   | Write op' (Inr (nid, p)) (Inr x) \<Rightarrow> Write (opt_dataflow_op sg op') (nid, p) x
   | Silent op' \<Rightarrow> Silent (opt_dataflow_op sg op')
   | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow> Silent (opt_dataflow_op (sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr>) op')
   | _ \<Rightarrow> Code.abort (STR ''Operator in opt_dataflow_op breaks contract'') (\<lambda> _. \<oslash>))
   (cfilter (\<lambda> op. is_busy sg op \<and> not_nop sg op)
   (choices op))
   )"


end
