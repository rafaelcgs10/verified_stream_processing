theory Dataflow_Op

imports
  Propagation_Exec
  Operator_State
  "../Lib/Operators_Utils"
begin

section \<open>Dataflow Wrapper Operator\<close>

corec dataflow_op where
  "dataflow_op sg op = Choice (cimage (\<lambda> op. case op of
     Read (Inl nid) f \<Rightarrow> (case propagate_all (summ sg) (pt_tr sg) of
         Some conf' \<Rightarrow> let sg' = sg\<lparr> pt_tr := conf' \<rparr> in
         let imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) in Silent (dataflow_op sg' (f (Inl (Inr (frontier o imp_fron)))))
      | None \<Rightarrow> \<oslash>)
   | Read (Inr (nid, p)) f \<Rightarrow> Read (nid, p) (\<lambda> x. dataflow_op sg (f (Inr x)))
   | Write op' (Inr (nid, p)) (Inr x) \<Rightarrow> Write (dataflow_op sg op') (nid, p) x
   | Silent op' \<Rightarrow> Silent (dataflow_op sg op')
   | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow> Silent (dataflow_op (sg\<lparr> pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) \<rparr>) op')
   | _ \<Rightarrow> Code.abort (STR ''Operator in dataflow_op breaks contract'') (\<lambda> _. \<oslash>))
   (choices op)
   )"

lemmas dataflow_op_code[code] = dataflow_op.code

subsection \<open>Transition Rules for @{const dataflow_op}\<close>

lemma step_dataflow_op_elim:
  assumes "step io (dataflow_op sg op) op'"
  obtains
    nid p op'' x where "io = Inp (nid, p) x" "op' = dataflow_op sg op''" "step (Inp (Inr (nid, p)) (Inr x)) op op''"
  | nid p op'' x where "io = Out (nid, p) x" "op' = dataflow_op sg op''" "step (Out (Inr (nid, p)) (Inr x)) op op''"
  | op'' where "io = Tau" "op' = dataflow_op sg op''" "step Tau op op''"
  | nid op'' st where "io = Tau" "op' = dataflow_op (sg\<lparr> pt_tr := (change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg)) \<rparr>) op''" "step (Out (Inl nid) (Inl (Inl st))) op op''"
  | nid op'' imp_fron sg' where "io = Tau" "sg' = (case propagate_all (summ sg) (pt_tr sg) of Some conf' \<Rightarrow> sg\<lparr> pt_tr := conf' \<rparr>)"
    "imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p)))" "op' = dataflow_op sg' op''" "step (Inp (Inl nid) (Inl (Inr (frontier o imp_fron)))) op op''"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) dataflow_op.code)
  apply (simp split: if_splits)
  apply (elim stepChoiceE)
  subgoal for op'
    apply (auto del: disjCI split: op.splits sum.splits option.splits simp flip: cin.rep_eq)
    apply fastforce+
    done
  done

lemma step_Tau_dataflow_op_Inp_Inl_intro[intro]:
  "step (Inp (Inl nid) (Inl (Inr (frontier o imp_fron)))) op op' \<Longrightarrow>
   propagate_all(summ sg) (pt_tr sg) = Some conf' \<Longrightarrow>
   sg' = sg\<lparr> pt_tr := conf' \<rparr> \<Longrightarrow>
   imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) \<Longrightarrow>
   step Tau (dataflow_op sg op) (dataflow_op sg' op')"
  apply (subst dataflow_op.code)
  apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Tau_dataflow_op_Out_Inl_intro[intro]:
  "step (Out (Inl nid) (Inl (Inl st))) op op' \<Longrightarrow>
   sg' = sg\<lparr> pt_tr := (change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg)) \<rparr> \<Longrightarrow>
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

lemma dataflow_op_simps[simp]:
  "\<not> is_Read (dataflow_op sg op)"
  "\<not> is_Write (dataflow_op sg op)"
  "\<not> is_Silent (dataflow_op sg op)"
  "is_Choice (dataflow_op sg op)"
  by (subst dataflow_op.code; simp)+


section \<open>Compilation Entry Points\<close>

abbreviation init_conf where
  "init_conf summary \<equiv> the (propagate_all summary initial_conf)"

definition "init_subgraph summary =
   \<lparr> pt_tr = init_conf summary,
   nxt = graph_to_nxt summary,
   summ = summary \<rparr>"

definition "compile_dataflow chns dt = (let summary = antichain_from_list oo (dataflow_tree_to_graph dt) in
                                    let op = dataflow_tree_to_operator chns dt in
                                    let sg = init_subgraph summary in
                                    dataflow_op sg op)"


abbreviation tscomp_op ( "_ \<sqdot>\<^bsub>_\<^esub> _" [81, 80, 80] 80) where
  "tscomp_op dt1 p dt2 \<equiv> Comp (\<lambda> (nid, p'). if nid = 0 \<and> p' = p then Some (0, p) else None) dt1 dt2"

abbreviation loop_back ("_ \<hookleftarrow>\<^bsub>_\<^esub>" [81, 0] 81) where
  "loop_back dt p \<equiv> Loop [(of_nat (nodes_count dt - 1), p) \<mapsto> (0, p)] dt"

text \<open>The wire function written by the sequential composition notation and the
  map literal are the same function. The equation is deliberately not a simp
  rule: proof search tactics such as fastforce degrade when it is in the
  default simpset. Proofs that need to move between the two forms unfold it
  explicitly.\<close>

lemma tscomp_op_wire_eq:
  "(\<lambda> (nid, p'). if nid = 0 \<and> p' = p then Some (0, p) else None) = [(0, p) \<mapsto> (0, p)]"
  by (rule ext) (auto split: prod.splits)

end
