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

lemma
  "wtraced (comp_op wire buf op1 op2) ios = 
   (\<exists> ios1 ios2. wtraced op1 ios1 \<and> wtraced op2 ios2 \<and>
    VIO_Inls ios = lfilter (case_VIO \<top> (\<lambda> p _. p \<notin> ran wire)) ios1 \<and>
    VIO_Inrs ios = lfilter (case_VIO (\<lambda> p _. p \<notin> dom wire) \<top>) ios2 \<and>
    causal wire buf ios1 ios2)"
  oops


end