theory Set_op

imports
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.CSet_LList_Impl
begin

corec set_op :: "('a \<times> 'b) cset \<Rightarrow> ('a \<times> 'b) cset \<Rightarrow> ('c, 'a, 'b) op \<Rightarrow> ('c, 'a, 'b) op" where
  "set_op S S' op = choice2
  (Choice (cimage (\<lambda> op. case op of
     Write op p x \<Rightarrow> Silent (set_op (cinsert (p, x) S) S' op) 
   | Silent op \<Rightarrow> Silent (set_op S S' op)
   | Read _ _ \<Rightarrow> Code.abort (STR ''Set_op can only output'') (\<lambda> _. \<oslash>)
   ) (choices op))
   )
  (Choice (cimage (\<lambda> (p, x). Write (set_op S (cinsert (p, x) S') op) p x) (S - S')))"

lemma step_set_op_elim:
  assumes "step io (set_op S S' op) op'"
  obtains p x where "io = Out p x" "(p, x) |\<in>| S" "\<not> (p, x) |\<in>| S'"
    "op' = set_op S (cinsert (p, x) S') op"
  | op'' where "io = Tau" "step Tau op op''" "op' = set_op S S' op''"
  | p x op'' where "io = Tau" "step (Out p x) op op''" "op' = set_op (cinsert (p, x) S) S' op''"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) set_op.code)
  apply (auto del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
    apply fastforce+
  done

lemma step_set_op_intro_Out[intro]:
  "io = Out p x \<Longrightarrow>
   (p, x) |\<in>| S \<Longrightarrow>
   \<not> (p, x) |\<in>| S' \<Longrightarrow>
   op' = set_op S (cinsert (p, x) S') op \<Longrightarrow>
   step io (set_op S S' op) op'"
  apply (subst set_op.code)
  apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
  apply fast
  done

lemma step_set_op_intro_Tau_1[intro]:
  "step (Out p x) op op'' \<Longrightarrow>
   io = Tau \<Longrightarrow>
   op' = set_op (cinsert (p, x) S) S' op'' \<Longrightarrow>
   step io (set_op S S' op) op'"
  apply (subst set_op.code)
  apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
  apply (smt (verit) IO.distinct(1,5) IO.inject(2) SC Silent_in_choices_step String.Literal'_def cDiff_cancel cDiff_cinsert2
      cDiff_cinsert_absorb choices_Silent cimage_eqI cinsert_absorb cinsert_cDiff1 cinsert_cDiff_if cinsert_cDiff_single cinsert_commute
      cinsert_not_cempty csingleton_iff internal_case_prod_def op.simps(18) step.simps step_choicesE)
  done

lemma step_set_op_intro_Tau_2[intro]:
  "io = Tau \<Longrightarrow>
   step Tau op op'' \<Longrightarrow>
   op' = set_op S S' op'' \<Longrightarrow>
   step io (set_op S S' op) op'"
  apply (subst set_op.code)
  apply (subst set_op.code)
  apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
  apply (metis (no_types, lifting) IO.distinct(5) IO.simps(6) cimageI cinsertI1 op.simps(20) step.simps step_choicesE)
  done


lemma step_Taus_set_op[intro]:
  "(step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow>
   op'' = set_op S S' op' \<Longrightarrow>
   (step Tau)\<^sup>*\<^sup>* (set_op S S' op) op''"
  apply (induct op arbitrary: S S' rule: converse_rtranclp_induct)
   apply clarsimp+
  apply (metis converse_rtranclp_into_rtranclp step_set_op_intro_Tau_2)
  done

lemma wstep_Out_set_op[intro]:
  "wstep (Out p x) op op' \<Longrightarrow>
   \<not> (p, x) |\<in>| S' \<Longrightarrow>
   op'' = set_op (cinsert (p, x) S) (cinsert (p, x) S') op' \<Longrightarrow>
   wstep (Out p x) (set_op S S' op) op''"
  unfolding wstep_def
  apply (clarsimp  simp flip: cin.rep_eq)
  apply hypsubst_thin+
  apply (intro "relcomppI")
    prefer 3
  apply (rule step_Taus_set_op[rotated])
     apply (rule refl)+
    prefer 3
      apply (rule step_set_op_intro_Out)
  apply (rule refl)
    defer
      defer
      apply (rule refl)
     defer
  apply (rule rtranclp.intros(2)[rotated])
      apply (rule step_set_op_intro_Tau_1)
        apply assumption
  apply simp
      apply (rule refl)
     apply auto
  done

find_consts "_ llist \<Rightarrow> _ cset"

lemma
  " wtraced (set_op S S' op) vios"



end

lemma
  "wtraced op vios \<Longrightarrow>
   (\<forall> vio \<in> lset vios. \<not> is_VInp vio \<and> \<not> vio |\<in>| cimage (\<lambda> (p, x). VOut p x) S') \<Longrightarrow>
   cset_of_llist vios = cimage (\<lambda> (p, x). VOut p x) S' \<Longrightarrow>
   wtraced (set_op S S' op) vios"
  apply (coinduction arbitrary: vios op S S')
  subgoal for vios
    apply (erule wtraced.cases)
    subgoal for op
      apply simp
      sorry
    subgoal for vio opa op' lxs
      apply clarsimp
      apply (cases vio; simp)
      subgoal for p x
        apply hypsubst_thin
        apply (intro conjI exI)
         apply (rule wstep_Out_set_op)
           apply assumption
          apply force
         apply (rule refl)
        apply (intro conjI exI disjI1)
          apply (rule refl)
         apply simp_all
        apply (auto 0 0)
        apply (drule spec)
        apply (elim conjE)
        apply (drule mp)
        apply (rule refl)
        apply (drule mp)
         apply assumption
          apply simp_all
        
        

end
      apply (intro exI conjI)
      apply (rule wtraced.Step[rotated, of "set_op _ _ _" _ vio'])
        apply simp_all
      apply (cases vio'; simp)
      apply hypsubst_thin


(* lemma
  "wtraces (set_op op) = (wtraces op)"
  unfolding wtraces_def
  apply auto
  subgoal for vios
    oops
 *)
end