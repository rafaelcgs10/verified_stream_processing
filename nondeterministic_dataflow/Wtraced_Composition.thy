theory Wtraced_Composition

imports
  "BNA_Operators"
begin


coinductive causal for wire where
  "causal wire buf LNil LNil"
| "causal wire buf ios1 ios2 \<Longrightarrow> causal wire buf (LCons (VInp p x) ios1) ios2"
| "causal wire buf ios1 ios2 \<Longrightarrow> wire p = None \<Longrightarrow> causal wire buf (LCons (VOut p x) ios1) ios2"
| "causal wire (BENQ q x buf) ios1 ios2 \<Longrightarrow> wire p = Some q \<Longrightarrow> causal wire buf (LCons (VOut p x) ios1) ios2"
| "causal wire buf ios1 ios2 \<Longrightarrow> causal wire buf ios1 (LCons (VOut p y) ios2)"
| "causal wire buf ios1 ios2 \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> causal wire buf ios1 (LCons (VInp p y) ios2)"
| "causal wire (BTL p buf) ios1 ios2 \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> y = BHD p buf \<Longrightarrow> p \<in> ran wire \<Longrightarrow> causal wire buf ios1 (LCons (VInp p y) ios2)"

abbreviation "VIO_Inls ios \<equiv>
  lmap (case_VIO (case_sum VInp undefined) (case_sum VOut undefined)) (lfilter (case_VIO (case_sum \<top> \<bottom>) (case_sum \<top> \<bottom>)) ios)"

abbreviation "VIO_Inrs ios \<equiv>
  lmap (case_VIO (case_sum undefined VInp) (case_sum undefined VOut)) (lfilter (case_VIO (case_sum \<bottom> \<top>) (case_sum \<bottom> \<top>)) ios)"

abbreviation visible_VIO where "visible_VIO wire io \<equiv> case_VIO (\<lambda>p _. case_sum (\<lambda> _. True) (\<lambda> q. q \<notin> ran wire) p) (\<lambda> p _. case_sum (\<lambda> q. q \<notin> dom wire) (\<lambda> _. True) p) io" 

inductive_cases causal_VInpInlE[elim]: "causal wire buf (LCons (VInp p x) ios1') ios2"


lemma
  "wtraced (comp_op wire buf op1 op2) ios = 
   (\<exists> ios1 ios2. wtraced op1 ios1 \<and> wtraced op2 ios2 \<and>
    lfilter (case_VIO \<top> (\<lambda> p _. p \<notin> ran wire)) ios1 = VIO_Inls ios \<and>
    lfilter (case_VIO (\<lambda> p _. p \<notin> dom wire) \<top>) ios2 = VIO_Inrs ios \<and>
    causal wire buf ios1 ios2)"
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
                by simp
              subgoal for vio op op' ios1'
                apply (simp split: if_splits)
                 apply hypsubst_thin
                subgoal
                  apply (erule causal_VInpInlE)
                        apply auto
                     apply hypsubst_thin
                  subgoal
                    apply (intro exI conjI)
                     apply (rule wstep_comp_op_L_Inp)
                       apply assumption
                      apply (rule refl)+
                    apply blast
                    done
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

        find_theorems lfilter LNil

  oops


end