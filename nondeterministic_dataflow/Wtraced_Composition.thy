theory Wtraced_Composition

imports
  "BNA_Operators"
begin

inductive visible_cause for wire where
  "visible_cause wire buf (LCons (VInp (Inl p) x) ios) (LCons (VInp p x) ios1) ios2 buf ios ios1 ios2"
| "visible_cause wire buf (LCons (VOut (Inr p) x) ios) ios1 (LCons (VOut p x) ios2) buf ios ios1 ios2"
| "wire p = None \<Longrightarrow> visible_cause wire buf (LCons (VOut (Inl p) x) ios) (LCons (VOut p x) ios1) ios2 buf ios ios1 ios2"
| "p \<notin> ran wire \<Longrightarrow> visible_cause wire buf (LCons (VInp (Inr p) x) ios) ios1 (LCons (VInp p x) ios2) buf ios ios1 ios2"
| "visible_cause wire buf ios ios1 ios2 buf' ios ios1' ios2' \<Longrightarrow>
   wire p = Some q \<Longrightarrow> visible_cause wire buf ios (LCons (VOut p x) ios1) ios2 (BENQ q x buf') ios ios1' ios2'"
| "visible_cause wire buf ios ios1 ios2 buf' ios ios1' ios2' \<Longrightarrow>
   p \<in> ran wire \<Longrightarrow> buf' p \<noteq> [] \<Longrightarrow> BHD p buf' = x \<Longrightarrow>
   visible_cause wire buf ios ios1 (LCons (VInp p x) ios2) (BTL p buf') ios' ios1' ios2'"

coinductive causal for wire where
 "causal wire buf' ios' ios1' ios2' \<Longrightarrow> visible_cause wire buf ios ios1 ios2 buf' ios' ios1' ios2' \<Longrightarrow> causal wire buf ios ios1 ios2"
(* | "causal wire buf ios1 ios2 \<Longrightarrow> wire p = None \<Longrightarrow> causal wire buf (LCons (VOut p x) ios1) ios2"
| "causal wire (BENQ q x buf) ios1 ios2 \<Longrightarrow> wire p = Some q \<Longrightarrow> causal wire buf (LCons (VOut p x) ios1) ios2"
| "causal wire buf ios1 ios2 \<Longrightarrow> causal wire buf ios1 (LCons (VOut p y) ios2)"
| "causal wire buf ios1 ios2 \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> causal wire buf ios1 (LCons (VInp p y) ios2)"
| "causal wire (BTL p buf) ios1 ios2 \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> y = BHD p buf \<Longrightarrow> p \<in> ran wire \<Longrightarrow> causal wire buf ios1 (LCons (VInp p y) ios2)" *)
(* 

abbreviation "VIO_Inls ios \<equiv>
  lmap (case_VIO (case_sum VInp VInp) (case_sum VOut VOut)) (lfilter (case_VIO (case_sum \<top> \<bottom>) (case_sum \<top> \<bottom>)) ios)"

abbreviation "VIO_Inrs ios \<equiv>
  lmap (case_VIO (case_sum VInp VInp) (case_sum VOut VOut)) (lfilter (case_VIO (case_sum \<bottom> \<top>) (case_sum \<bottom> \<top>)) ios)"

abbreviation visible_VIO where "visible_VIO wire io \<equiv> case_VIO (\<lambda>p _. case_sum (\<lambda> _. True) (\<lambda> q. q \<notin> ran wire) p) (\<lambda> p _. case_sum (\<lambda> q. q \<notin> dom wire) (\<lambda> _. True) p) io" 

lemma causal_LCons_VInp_Inl:
  "causal wire buf (LCons (VInp p x) ios1) ios2 \<Longrightarrow>
   causal wire buf ios1 ios2"
  apply (coinduction arbitrary: buf ios1 ios2 rule: causal.coinduct)
  subgoal for buf ios1 ios2
    apply (erule causal.cases)
          apply simp_all
    apply hypsubst_thin
    apply (smt (verit) causal.cases)
    done
  done

lemma causal_LCons_VOut_Inr:
  "causal wire buf ios (LCons (VOut p x) ios2) \<Longrightarrow>
   causal wire buf ios1 ios2"
  apply (coinduction arbitrary: buf ios1 ios2 rule: causal.coinduct)
  subgoal for buf ios1 ios2
    apply (erule causal.cases)
          apply simp_all
    apply hypsubst_thin
    oops *)

lemma visible_cause_VInp_Inl_LNil_False:
  "visible_cause wire buf (LCons (VInp (Inl lp) x) ios) ios1 ios2 buf' ios' ios1' ios2' \<Longrightarrow>
   ios1 = LNil \<Longrightarrow>
   False"
  apply (induct buf "LCons (VInp (Inl lp) x) ios" ios1 ios2 buf' ios' ios1' ios2' pred: visible_cause)
    apply auto
  done


lemma
  "wtraced (comp_op wire buf op1 op2) ios = 
   (\<exists> ios1 ios2. wtraced op1 ios1 \<and> wtraced op2 ios2 \<and> causal wire buf ios ios1 ios2)"
  apply (rule iffI)
  subgoal
    sorry
  subgoal
    apply (elim exE conjE)
    subgoal for ios1 ios2
      apply (coinduction arbitrary: buf op1 op2 ios ios1 ios2 rule: wtraced.coinduct)
      subgoal for buf op1 op2 ios ios1 ios2
        apply (cases ios)
        subgoal
          apply (simp add: lfilter_eq_LNil)
          apply hypsubst_thin
          sorry
        subgoal for io ios
          apply (cases io)
          subgoal for p x
            apply (cases p)
            subgoal for lp
              apply (simp split: if_splits)
              apply hypsubst_thin
              apply (erule wtraced.cases)
              subgoal
              apply (erule causal.cases)
                apply auto
                apply hypsubst_thin
                using visible_cause_VInp_Inl_LNil_False apply fast
                done
              subgoal
                apply hypsubst_thin
         apply (erule causal.cases)
                apply auto
                sorry
              done
            subgoal for rp
         apply (simp split: if_splits)
              apply hypsubst_thin
              apply rotate_tac
              apply (erule wtraced.cases)
              subgoal sorry
              subgoal
                apply hypsubst_thin
    apply (erule causal.cases)
                apply auto

end
                by simp
              subgoal for vio op op' ios1'
                apply (simp split: if_splits)
                subgoal
                 apply hypsubst_thin
                  apply (drule causal_LCons_VInp_Inl)
                    apply (intro exI conjI)
                     apply (rule wstep_comp_op_L_Inp)
                       apply assumption
                      apply (rule refl)+
                    apply blast
                  done
                subgoal
                 apply hypsubst_thin
                  apply (simp split: VIO.splits)
                  subgoal for p x
                  apply (intro exI conjI)
                     apply (rule wstep_trans(2)[of _ "comp_op wire (BENQ p x buf) op' op2"])
                    unfolding wstep_def
                    subgoal sorry
              

                    find_theorems wtraced wstep


end
                  apply (rule step_Tau_comp_op_L)

                  find_theorems wstep name: trans



end


                  subgoal for ios2 p y
                    apply hypsubst_thin
                    apply (intro exI conjI)
                     apply (rule wstep_comp_op_L_Inp)
                       apply assumption
                      apply (rule refl)+
                    apply (rule disjI1)
                    apply (intro exI conjI)
                      apply (rule refl)+
                        apply assumption+
                     apply fastforce
                    apply (rule causal.intros(5)) 
                    apply (rule causal_LCons_VInp_Inl)
                    apply force
                    done
                  subgoal for ios2 p y
                    apply hypsubst_thin
                    sledgehammer             

                    find_theorems "ldropWhile _ _ = LCons _ _"

        find_theorems lfilter LNil

  oops


end