theory Cycles_XI
  imports
    Coinductive.Coinductive_List
    Coinductive.Coinductive_Nat
    "HOL-Library.BNF_Corec"
    "HOL-Library.Code_Lazy"
    "HOL-Library.Numeral_Type"
    "HOL-Library.Code_Cardinality"
    "HOL-Library.Simps_Case_Conv"
    "HOL-Library.Debug"
begin

code_lazy_type llist
print_theorems 

datatype (discs_sels) 'd observation = Observed (obs: 'd) | EOB | EOS
codatatype (inputs: 'ip, outputs: 'op, dead 'd) op =
    Read 'ip "'d observation \<Rightarrow> ('ip, 'op, 'd) op"
  | Write "('ip, 'op, 'd) op" 'op 'd
  | End

type_synonym 'd channel = "'d llist"

code_lazy_type op
 
fun chd where
  "chd LNil = EOS"
| "chd (LCons x lxs) = Observed x"

abbreviation ctl :: "'d channel \<Rightarrow> 'd channel" where "ctl \<equiv> ltl"

abbreviation CHD :: "'a \<Rightarrow> ('a \<Rightarrow> 'd channel) \<Rightarrow> 'd observation" where "CHD p lxs \<equiv> chd (lxs p)"
abbreviation CTL :: "'a \<Rightarrow> ('a \<Rightarrow> 'd channel) \<Rightarrow> ('a \<Rightarrow> 'd channel)" where "CTL p lxs \<equiv> lxs(p := ctl (lxs p))"

inductive loud for p where
  Write_same: "loud p (Write op p x) lxs"
| Write_other: "p \<noteq> p' \<Longrightarrow> loud p op' lxs \<Longrightarrow> loud p (Write op' p' x) lxs"
| Read: "loud p (f (CHD p' lxs)) (CTL p' lxs) \<Longrightarrow> loud p (Read p' f) lxs"
| ReadEOB: "loud p (f EOB) lxs \<Longrightarrow> loud p (Read p' f) lxs"

inductive_cases loud_EndE[elim!]: "loud p End lxs"
inductive_cases loud_WriteE[elim!]: "loud p (Write op p' x) lxs"
inductive_cases loud_ReadE[elim!]: "loud p (Read p' f) lxs"

coinductive mute for p where
  End[simp, intro!]: "mute p End lxs"
| Write: "p \<noteq> p' \<Longrightarrow> mute p op' lxs \<Longrightarrow> mute p (Write op' p' x) lxs"
| Read: "mute p (f EOB) lxs \<Longrightarrow> mute p (f (CHD p' lxs)) (CTL p' lxs) \<Longrightarrow> mute p (Read p' f) lxs"

inductive_cases mute_EndE[elim!]: "mute p End lxs"
inductive_cases mute_WriteE[elim!]: "mute p (Write op p' x) lxs"
inductive_cases mute_ReadE[elim!]: "mute p (Read p' f) lxs"

lemma loud_not_mute: "loud p op lxs \<Longrightarrow> \<not> mute p op lxs"
  by (induct op lxs pred: loud) (auto simp: fun_upd_def)

lemma not_loud_mute: "\<not> loud p op lxs \<Longrightarrow> mute p op lxs"
  apply (coinduction arbitrary: op lxs)
  subgoal for op lxs
    apply (cases op)
      apply (auto simp: fun_upd_def intro: loud.intros)
    done
  done

lemma not_mute_iff_loud: "\<not> mute p op lxs \<longleftrightarrow> loud p op lxs"
  by (metis not_loud_mute loud_not_mute)

inductive wary for p where
  Read_same: "wary p (Read p f) lxs"
| Write: "wary p op' lxs \<Longrightarrow> wary p (Write op' p' x) lxs"
| Read_other: "p \<noteq> p' \<Longrightarrow> wary p (f (CHD p' lxs)) (CTL p' lxs) \<Longrightarrow> wary p (Read p' f) lxs"
| ReadEOB: "wary p (f EOB) lxs \<Longrightarrow> wary p (Read p' f) lxs"

inductive_cases wary_EndE[elim!]: "wary p End lxs"
inductive_cases wary_WriteE[elim!]: "wary p (Write op p' x) lxs"
inductive_cases wary_ReadE[elim!]: "wary p (Read p' f) lxs"

coinductive deaf for p where
  End[simp, intro!]: "deaf p End lxs"
| Write: "deaf p op' lxs \<Longrightarrow> deaf p (Write op' p' x) lxs"
| Read: "p \<noteq> p' \<Longrightarrow> deaf p (f EOB) lxs \<Longrightarrow> deaf p (f (CHD p' lxs)) (CTL p' lxs) \<Longrightarrow> deaf p (Read p' f) lxs"

inductive_cases deaf_EndE[elim!]: "deaf p End lxs"
inductive_cases deaf_WriteE[elim!]: "deaf p (Write op p' x) lxs"
inductive_cases deaf_ReadE[elim!]: "deaf p (Read p' f) lxs"

lemma wary_not_deaf: "wary p op lxs \<Longrightarrow> \<not> deaf p op lxs"
  by (induct op lxs pred: wary) (auto simp: fun_upd_def)

lemma not_wary_deaf: "\<not> wary p op lxs \<Longrightarrow> deaf p op lxs"
  apply (coinduction arbitrary: op lxs)
  subgoal for op lxs
    apply (cases op)
      apply (auto intro: wary.intros)
    done
  done

lemma not_deaf_iff_wary: "\<not> deaf p op lxs \<longleftrightarrow> wary p op lxs"
  by (metis not_wary_deaf wary_not_deaf)

abbreviation deafened where
  "deafened op lxs \<equiv> (\<forall>p. deaf p op lxs \<longrightarrow> lxs p = LNil)"

definition muted where
  "muted op lxs lys \<equiv> (\<forall>p. mute p op lxs \<longrightarrow> lys p = LNil)"

lemma
  muted_ReadEOB[simp,intro]: "muted (f EOB) lxs lys \<Longrightarrow> muted (Read p f) lxs lys" and
  muted_Read[simp,intro]: "muted (f (CHD p lxs)) (CTL p lxs) lys \<Longrightarrow> muted (Read p f) lxs lys" and
  muted_Write[simp,intro]: "muted op lxs (CTL p' lys) \<Longrightarrow> muted (Write op p' x) lxs lys" and
  muted_End[iff]: "muted End lxs lys \<longleftrightarrow> (\<forall>p. lys p = LNil)"
  by (auto simp: muted_def)

coinductive produced where
  Read: "muted (f (CHD p lxs)) (CTL p lxs) lys \<Longrightarrow> produced (fuel(p := n)) (f (CHD p lxs)) (CTL p lxs) lys \<Longrightarrow> produced fuel (Read p f) lxs lys"
| ReadEOB: "muted (f EOB) lxs lys \<Longrightarrow> fuel p = Suc n \<Longrightarrow> produced (fuel(p := n)) (f EOB) lxs lys \<Longrightarrow> produced fuel (Read p f) lxs lys"
| Write: "muted op lxs lys \<Longrightarrow> produced fuel op lxs lys \<Longrightarrow> produced fuel (Write op p x) lxs (lys(p := LCons x (lys p)))"
| End: "produced fuel End lxs (\<lambda>_. LNil)"


coinductive traced where
  Read: "traced (fuel(p := n)) (f (Observed x)) lxs \<Longrightarrow> traced fuel (Read p f) (LCons (Inl p, Observed x) lxs)"
| ReadEOS: "traced (fuel(p := n)) (f EOS) lxs \<Longrightarrow> traced fuel (Read p f) (LCons (Inl p, EOS) lxs)"
| ReadEOB: "fuel p = Suc n \<Longrightarrow> traced (fuel(p := n)) (f EOB) lxs \<Longrightarrow> traced fuel (Read p f) (LCons (Inl p, EOB) lxs)"
| Write: "traced fuel op lxs \<Longrightarrow> traced fuel (Write op p x) (LCons (Inr p, Observed x) lxs)"
| End: "traced fuel End LNil"

inductive_cases traced_EndE[elim!]: "traced m End lxs"
inductive_cases traced_WriteE[elim!]: "traced m (Write op p' x) lxs"
inductive_cases traced_ReadE[elim!]: "traced m (Read p' f) lxs"

definition "traces m op = {lxs. traced m op lxs}"

lemma traces_Read[simp]:
  "traces m (Read p f) = (\<Union>x. LCons (Inl p, Observed x) ` (\<Union>n. traces (m(p := n)) (f (Observed x)))) \<union>
                       LCons (Inl p, EOB) ` (case m p of Suc n \<Rightarrow> traces (m(p := n)) (f EOB) | _ \<Rightarrow> {}) \<union>
                       LCons (Inl p, EOS) ` (\<Union>n. traces (m(p := n)) (f EOS))"
  by (auto simp: traces_def image_iff intro: traced.intros split: nat.splits)

lemma traces_Write[simp]:
  "traces m (Write op p x) = LCons (Inr p, Observed x) ` traces m op"
  by (auto simp: traces_def intro: traced.intros)

lemma traces_End[simp]:
  "traces m End = {LNil}"
  by (auto simp: traces_def intro: traced.intros)

corec traced_wit where
  "traced_wit op = (case op of
    Read p f \<Rightarrow> LCons (Inl p, EOS) (traced_wit (f EOS))
  | Write op' p' x \<Rightarrow> LCons (Inr p', Observed x) (traced_wit op')
  | End \<Rightarrow> LNil)"

lemma lset_traced_wit: "t \<in> lset (traced_wit op) \<Longrightarrow> (\<exists>p \<in> inputs op. t = (Inl p, EOS)) \<or> (\<exists>q \<in> outputs op. \<exists>x. t = (Inr q, Observed x))"
  apply (induction t "traced_wit op" arbitrary: op rule: llist.set_induct)
  apply (subst (asm) traced_wit.code)
  apply (auto split: op.splits) []
  apply (subst (asm) (2) traced_wit.code)
  apply (fastforce split: op.splits) []
  done

coinductive cleaned where
  cleaned_Read[intro]: "p \<notin> inputs (f EOS) \<Longrightarrow> (\<And>x. cleaned (f x)) \<Longrightarrow>  cleaned (Read p f)"
| cleaned_Write[intro]: "cleaned op \<Longrightarrow> cleaned (Write op q x)"
| cleaned_End[iff]: "cleaned End"

inductive_cases cleaned_ReadE[elim!]: "cleaned (Read p f)"
inductive_cases cleaned_WriteE[elim!]: "cleaned (Write op q x)"
inductive_cases cleaned_EndE[elim!]: "cleaned End"

inductive cleaned_cong for R where
  cc_base: "R op \<Longrightarrow> cleaned_cong R op"
| cc_cleaned: "cleaned op \<Longrightarrow> cleaned_cong R op"
| cc_read: "p \<notin> inputs (f EOS) \<Longrightarrow> (\<And>x. cleaned_cong R (f x)) \<Longrightarrow> cleaned_cong R (Read p f)"
| cc_write: "cleaned_cong R op \<Longrightarrow> cleaned_cong R (Write op q x)"

lemma cleaned_coinduct_upto: "X op \<Longrightarrow>
  (\<And>op. X op \<Longrightarrow> (\<exists>p f. op = Read p f \<and> p \<notin> inputs (f EOS) \<and> (\<forall>x. cleaned_cong X (f x))) \<or> (\<exists>op' q x. op = Write op' q x \<and> (cleaned_cong X op')) \<or> op = End) \<Longrightarrow>
  cleaned op"
  apply (rule cleaned.coinduct[where X="cleaned_cong X"])
   apply (erule cleaned_cong.intros)
  apply (erule thin_rl)
  subgoal premises prems for op
    using prems(2)
    apply (induct op rule: cleaned_cong.induct)
    subgoal for op
      by (auto dest: prems(1))
    subgoal for op
      by (cases op) auto
    subgoal for f p
      by auto
    subgoal for f p
      by auto
    done
  done

lemma traced_traced_wit: "traced m op (traced_wit op)"
  apply (coinduction arbitrary: op m)
  apply (subst (1 3 5 7) traced_wit.code)
  apply (auto split: op.splits dest: lset_traced_wit simp: traced_wit.code[where op=End])
  done

lemma traces_nonempty: "traces m op \<noteq> {}"
  by (auto simp: traces_def intro!: traced_traced_wit)

lemma non_input_traces: "t \<in> lset lxs \<Longrightarrow> t = (Inl p, y) \<Longrightarrow> p \<notin> inputs op \<Longrightarrow> lxs \<in> traces m op \<Longrightarrow> False"
  apply (induct t lxs arbitrary: m op rule: llist.set_induct)
  subgoal for t lxs m op
    apply (cases op; auto)
    done
  subgoal for t lxs x m op
    apply (cases op; auto split: nat.splits)
    done
  done

lemma traces_op_eqI: "(\<Union>m. traces m op) = (\<Union>m. traces m op') \<Longrightarrow> op = op'"
  apply (coinduction arbitrary: op op')
  subgoal for op op'
    apply (cases op; cases op')
            apply (simp_all add: rel_fun_def set_eq_iff split: nat.splits)
    subgoal for p f p' f'
      apply (rule context_conjI)
      subgoal
        apply (drule spec[of _ "LCons (Inl p, EOS) (traced_wit (f EOS))"])
        apply simp
        apply (drule iffD1)
         apply (rule exI[of _ "\<lambda>_. 0"])
         apply simp
        apply (rule disjI2)
         apply (rule imageI)
         apply (auto dest: lset_traced_wit simp: traces_def traced_traced_wit) []
        apply (erule exE disjE conjE)+
         apply (simp_all add: gr0_conv_Suc image_iff)
        done
      subgoal
        apply safe
        subgoal for x lxs m
          apply (drule spec[of _ "LCons (Inl p, x) lxs"])
          apply (drule iffD1)
          apply (rule exI[of _ "m(p := Suc (m p))"])
           apply (cases x; auto simp: image_iff dest: non_input_traces intro: exI[of _ "m p"]) []
          apply (erule exE conjE disjE)+
           apply (auto simp add: gr0_conv_Suc image_iff)
          done
        subgoal for x lxs m
          apply (drule spec[of _ "LCons (Inl p', x) lxs"])
          apply (drule iffD2)
          apply (rule exI[of _ "m(p' := Suc (m p'))"])
           apply (cases x; auto simp: image_iff dest: non_input_traces intro: exI[of _ "m p'"]) []
          apply (erule exE conjE disjE)+
           apply (auto simp add: gr0_conv_Suc image_iff)
          done
        done
      done
    subgoal
      apply (auto simp: set_eq_iff image_iff)
      apply (metis llist.inject mem_Collect_eq old.sum.distinct(2) prod.inject traced_traced_wit traces_def)
      done
    subgoal
      apply (auto dest!: spec[of _ LNil] simp: gr0_conv_Suc)
      done
    subgoal
      apply (auto simp: set_eq_iff image_iff)
      apply (metis llist.inject mem_Collect_eq old.sum.distinct(2) prod.inject traced_traced_wit traces_def)
      done
    subgoal for op1 p1 x1 op2 p2 x2
      apply auto
      subgoal for lxs m
        apply (drule spec[of _ "LCons (Inr p1, Observed x1) lxs"])
        apply auto
        done
      subgoal for lxs m
        apply (drule spec[of _ "LCons (Inr p2, Observed x2) lxs"])
        apply auto
        done
      subgoal
        apply (drule spec[of _ "LCons (Inr p1, Observed x1) (traced_wit op1)"])
        apply (auto simp: traced_traced_wit traces_def)
        done
      subgoal
        apply (drule spec[of _ "LCons (Inr p1, Observed x1) (traced_wit op1)"])
        apply (auto simp: traced_traced_wit traces_def)
        done
      done
    subgoal
      apply (auto simp: set_eq_iff image_iff)
      done
    subgoal
      apply (auto dest!: spec[of _ LNil] simp: gr0_conv_Suc)
      done
    subgoal
      apply (auto simp: set_eq_iff image_iff)
      done
    done
  done

definition agree :: "('l \<Rightarrow> 'l' \<Rightarrow> bool) \<Rightarrow> ('l \<times> 'c) llist \<Rightarrow> ('l' \<times> 'c) llist \<Rightarrow> bool" where
  "agree R lxs lys = llist_all2 (rel_prod R (=)) (lfilter (Domainp R o fst) lxs) (lfilter (Rangep R o fst) lys)"

definition semantics ("\<lbrakk>_\<rbrakk>") where
  "semantics op lxs lys = (\<exists>m. produced m op lxs lys)"

inductive_cases produced_EndE[elim!]: "produced m End lxs lys"
inductive_cases produced_WriteE[elim!]: "produced m (Write op p' x) lxs lys"
inductive_cases produced_ReadE[elim!]: "produced m (Read p' f) lxs lys"

lemma mute_cong[cong]: "p = q \<Longrightarrow> op = op' \<Longrightarrow> (\<And>q. q \<in> inputs op' \<Longrightarrow> lxs q = lxs' q) \<Longrightarrow> mute p op lxs = mute q op' lxs'"
  apply hypsubst_thin
  apply (rule iffI)
  subgoal premises prems
    using prems(2,1)
    apply (coinduction arbitrary: op' lxs lxs')
    subgoal for op lxs lxs'
      apply (erule mute.cases)
         apply (auto 0 0)
       apply blast
       apply blast
      apply (metis fun_upd_apply)
      done
    done
  subgoal premises prems
    using prems(2,1)
    apply (coinduction arbitrary: op' lxs lxs')
    subgoal for op lxs lxs'
      apply (erule mute.cases)
         apply (auto 0 0)
       apply blast
       apply blast
      apply (metis fun_upd_apply)
      done
    done
  done

lemma muted_cong: "muted op lxs lys \<Longrightarrow>
   (\<forall>p \<in> inputs op. lxs p = lxs' p) \<Longrightarrow> (\<And>p. lys p = LNil \<Longrightarrow> lys' p = LNil) \<Longrightarrow> muted op lxs' lys'"
  by (auto cong: mute_cong simp: muted_def)

lemma produced_cong: "produced m op lxs lys \<Longrightarrow>
   (\<forall>p \<in> inputs op. m p = m' p) \<Longrightarrow>
   (\<forall>p \<in> inputs op. lxs p = lxs' p) \<Longrightarrow>
   (\<forall>p. mute p op lxs \<or> lys p = lys' p) \<Longrightarrow>
   (\<And>p. lys p = LNil \<Longrightarrow> lys' p = LNil) \<Longrightarrow> produced m' op lxs' lys'"
  apply (coinduction arbitrary: m op lxs lys m' lxs' lys')
  subgoal for m op lxs lys m' lxs' lys'
    apply (cases op)
      apply (auto 3 0 simp del: fun_upd_apply simp: muted_def split: if_splits)
            apply (smt (verit) fun_upd_apply mute_ReadE mute_cong)
    subgoal for p f n q
      apply (rule exI[of _ n])
      apply (rule disjI1)
      apply (rule exI[of _ "m(p := n)"])
      apply (smt (verit) fun_upd_apply mute_ReadE mute_cong)
      done
          apply (smt (verit) fun_upd_apply mute_ReadE mute_cong)
         apply (smt (verit) fun_upd_apply mute_ReadE mute_cong)
        apply (smt (verit) fun_upd_apply mute_ReadE mute_cong)
       apply (smt (verit) fun_upd_apply mute_ReadE mute_cong)
      apply (smt (verit) fun_upd_apply mute_ReadE mute_cong)
     apply (smt (verit) fun_upd_apply mute_ReadE mute_cong)
    subgoal for op' p' x lzs
      apply (rule exI[of _ "\<lambda>q. if \<not> mute q op' lxs \<or> q = p' then lzs q else lys' q"])
      apply (auto 3 0 simp: fun_eq_iff) []
         apply (metis mute_WriteE)
        apply (metis mute_WriteE mute_cong)
       apply (metis mute_WriteE)
      apply blast
      done
    done
  done

lemma produced_Write[intro]:
  "muted op lxs lys \<Longrightarrow> produced m op lxs lys \<Longrightarrow> lzs = lys(p := LCons x (lys p)) \<Longrightarrow> produced m (Write op p x) lxs lzs"
  by (simp add: produced.Write)

lemma produced_End[intro!]:
  assumes "(\<And>p. lzs p = LNil)"
  shows "produced m End lxs lzs"
proof -
  from assms have "(\<lambda>a. LNil) = lzs"
    by (simp add: fun_eq_iff)
  then show ?thesis
    using produced.intros(4) by blast
qed

lemma semantics_Read[intro]:
  "muted (f (CHD p lxs)) (CTL p lxs) lys \<Longrightarrow> semantics (f (CHD p lxs)) (CTL p lxs) lys \<Longrightarrow> semantics (Read p f) lxs lys"
  unfolding semantics_def
  by (metis fun_upd_triv produced.Read)


lemma semantics_ReadEOB[intro]:
  "muted (f EOB) lxs lys \<Longrightarrow> semantics (f EOB) lxs lys \<Longrightarrow> semantics (Read p f) lxs lys"
  unfolding semantics_def
  by (metis fun_upd_idem_iff fun_upd_upd produced.ReadEOB)

lemma semantics_Write[intro!]:
  "muted op lxs lys \<Longrightarrow> semantics op lxs lys \<Longrightarrow> lzs = lys(p := LCons x (lys p)) \<Longrightarrow> semantics (Write op p x) lxs lzs"
  unfolding semantics_def
  by (metis produced_Write)

lemma semantics_End[intro]:
  "(\<And>p. lys p = LNil) \<Longrightarrow> semantics End lxs lys"
  unfolding semantics_def
  by (metis produced_End)

inductive produced_cong for R where
  produced: "produced fuel op lxs lys \<Longrightarrow> produced_cong R fuel op lxs lys"
| base: "R fuel op lxs lys \<Longrightarrow> produced_cong R fuel op lxs lys"
| "write": "produced_cong R fuel op' lxs lys' \<Longrightarrow> lys = lys'(p := LCons x (lys' p)) \<Longrightarrow> produced_cong R fuel (Write op' p x) lxs lys"
| read: "(\<And>n. fuel p = Suc n \<Longrightarrow> produced_cong R (fuel(p := n)) (f EOB) lxs lys) \<Longrightarrow>
    (fuel p = 0 \<Longrightarrow> produced_cong R (fuel(p := n)) (f (CHD p lxs)) (CTL p lxs) lys) \<Longrightarrow>
    produced_cong R fuel (Read p f) lxs lys"

inductive_cases produced_cong_WriteE: "produced_cong R fuel (Write op' p x) lxs lys"
inductive_cases produced_cong_ReadE: "produced_cong R fuel (Read p f) lxs lys"
inductive_cases produced_cong_EndE: "produced_cong R fuel End lxs lys"

lemma produced_coinduct_upto:
  assumes R: "R fuel op lxs lys"
    and CIH: "\<And>fuel op lxs lys.
    R fuel op lxs lys \<Longrightarrow>
    (\<exists>p n f.
        op = Read p f \<and>
        muted (f (CHD p lxs)) (CTL p lxs) lys \<and>
        produced_cong R (fuel(p := n)) (f (CHD p lxs)) (CTL p lxs) lys) \<or>
    (\<exists>p n f.
        op = Read p f \<and>
        fuel p = Suc n \<and>
        muted (f EOB) lxs lys \<and>
        produced_cong R (fuel(p := n)) (f EOB) lxs lys) \<or>
    (\<exists>op' lys' p x.
        op = Write op' p x \<and>
        muted op' lxs lys' \<and>
        lys = lys'(p := LCons x (lys' p)) \<and>
        produced_cong R fuel op' lxs lys') \<or>
    op = End \<and> lys = (\<lambda>_. LNil)"
  shows "produced fuel op lxs lys"
  apply (rule produced.coinduct[of "produced_cong R"])
   apply (rule base, rule R)
  subgoal for fuel op lxs lys
    supply [[unify_search_bound = 100]]
    apply (induct fuel op lxs lys rule: produced_cong.induct)
    subgoal for fuel op lxs lys
      by (erule produced.cases) (auto simp del: fun_upd_apply)
    subgoal for fuel op lxs lys
      by (drule CIH) (fastforce simp del: fun_upd_apply simp add: fun_upd_other)+
    subgoal for fuel op' lxs lys' lys p x
      by (auto simp del: fun_upd_apply simp add: fun_upd_other fun_upd_same)
    subgoal for fuel p f lxs lys n
      apply (cases "fuel p"; auto simp del: fun_upd_apply simp add: fun_upd_other fun_upd_same)
      done
    done
  done

inductive mute_cong for p R where
  mute: "mute p op lxs \<Longrightarrow> mute_cong p R op lxs"
| base: "R op lxs \<Longrightarrow> mute_cong p R op lxs"
| "write": "p \<noteq> p' \<Longrightarrow> mute_cong p R op' lxs \<Longrightarrow> mute_cong p R (Write op' p' x) lxs"
| read: "mute_cong p R (f EOB) lxs \<Longrightarrow> mute_cong p R (f (CHD p' lxs)) (CTL p' lxs) \<Longrightarrow> mute_cong p R (Read p' f) lxs"

lemma mute_coinduct_upto:
  assumes "R op lxs"
  and "(\<And>op lxs.
    R op lxs \<Longrightarrow>
    (op = End) \<or>
    (\<exists>p' op' x. op = Write op' p' x \<and> p \<noteq> p' \<and> mute_cong p R op' lxs) \<or>
    (\<exists>f p'. op = Read p' f \<and> mute_cong p R (f (CHD p' lxs)) (CTL p' lxs) \<and> mute_cong p R (f EOB) lxs))"
  shows "mute p op lxs"
  apply (rule mute.coinduct[where X = "mute_cong p R"])
   apply (rule mute_cong.intros, rule assms(1))
  subgoal for op lxs
    apply (induct op lxs pred: mute_cong)
    subgoal
      by (erule mute.cases) (auto simp del: fun_upd_apply)
    subgoal for op lxs
      by (drule assms) (auto simp del: fun_upd_apply)
    subgoal for p' op' lxs x
      by blast
    subgoal for f lxs p'
      by blast
    done
  done

corec fairmerge :: "bool \<Rightarrow> bool \<Rightarrow> (2, 1, nat) op" where
  "fairmerge e1 e2 = (case (e1, e2) of
      (True, True) \<Rightarrow> End
    | (True, False) \<Rightarrow> Read 2 (case_observation (Write (fairmerge e1 e2) 1) (fairmerge e1 e2) End)
    | (False, True) \<Rightarrow> Read 1 (case_observation (Write (fairmerge e1 e2) 1) (fairmerge e1 e2) End)
    | (False, False) \<Rightarrow>
      Read 1 (case_observation (Write (Read 2 (case_observation (Write (fairmerge e1 e2) 1) (fairmerge e1 e2) (fairmerge e1 True))) 1)
     (Read 2 (case_observation (Write (fairmerge e1 e2) 1) (fairmerge e1 e2) (fairmerge e1 True))) (fairmerge True e2)))"

corec (friend) lshift :: "'a list \<Rightarrow> 'a llist \<Rightarrow> 'a llist" (infixr \<open>@@-\<close> 65) where
  "lshift xs ys = (case xs of [] \<Rightarrow> (case ys of LNil \<Rightarrow> LNil | LCons y' ys' \<Rightarrow> LCons y' ys') | x#xs \<Rightarrow> LCons x (lshift xs ys))"

lemma lshift_simps[simp]:
  "lshift [] lxs = lxs"
  "lshift (x#xs) lxs = LCons x (lshift xs lxs)"
  by (subst lshift.code; auto split: llist.splits)+

lemma lshift_append[simp]: "(xs @ ys) @@- ws = xs @@- ys @@- ws"
  by (induct xs) auto

lemma lshift_snoc[simp]: "(xs @ [x]) @@- ws = xs @@- LCons x ws"
  by (induct xs) auto

lemma lshift_LNil_iff:
  "LNil = xs @@- lxs \<longleftrightarrow> xs = [] \<and> lxs = LNil"
  "xs @@- lxs = LNil \<longleftrightarrow> xs = [] \<and> lxs = LNil"
  by (cases xs; auto)+

coinductive merged where
  "merged LNil lxs lxs"
| "merged lxs LNil lxs"
| "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> merged lxs lys lzs \<Longrightarrow>
   merged (xs @@- lxs) (ys @@- lys) (xs @@- ys @@- lzs)"
| "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> merged lxs lys lzs \<Longrightarrow>
   merged (xs @@- lxs) (ys @@- lys) (ys @@- xs @@- lzs)"

coinductive mergedL where
  "mergedL LNil lxs lxs"
| "mergedL lxs LNil lxs"
| "xs \<noteq> [] \<Longrightarrow> mergedL lys lxs lzs \<Longrightarrow> mergedL (xs @@- lxs) lys (xs @@- lzs)"

inductive_cases mergedL_LNil1E[elim!]: "mergedL LNil lys lzs"
inductive_cases mergedL_LNil2E[elim!]: "mergedL lxs LNil lzs"

lemma mergedL_merged: "mergedL lxs lys lzs \<Longrightarrow> merged lxs lys lzs"
  apply (coinduction arbitrary: lxs lys lzs)
  subgoal for lxs lys lzs
    apply (erule mergedL.cases)
      apply simp
    apply simp
    apply (erule mergedL.cases)
      apply simp
     apply simp
     apply (metis lshift_simps(1) lshift_simps(2) mergedL.intros(1) neq_LNil_conv)
    apply metis
    done
  done

lemma mergedRL_merged: "mergedL lys lxs lzs \<Longrightarrow> merged lxs lys lzs"
  apply (coinduction arbitrary: lxs lys lzs)
  subgoal for lxs lys lzs
    apply (erule mergedL.cases)
      apply simp
    apply simp
    apply (erule mergedL.cases)
      apply simp
     apply simp
     apply (metis lshift_simps(1) lshift_simps(2) mergedL.intros(1) neq_LNil_conv)
    apply metis
    done
  done

lemma merged_lappend1: "merged lxs lys lzs \<Longrightarrow> merged (xs @@- lxs) lys (xs @@- lzs)"
  apply (coinduction arbitrary: xs lxs lys lzs)
  apply (erule merged.cases)
     apply (metis llist.exhaust list.simps(3) lshift_simps(1) lshift_simps(2) merged.intros(1))
    apply metis
   apply (smt (verit) append_is_Nil_conv lshift_append)
  apply (metis lshift_simps(1))
  done

lemma merged_lappend2: "merged lxs lys lzs \<Longrightarrow> merged lxs (ys @@- lys) (ys @@- lzs)"
  apply (coinduction arbitrary: ys lxs lys lzs)
  apply (erule merged.cases)
     apply metis
    apply (metis llist.exhaust list.simps(3) lshift_simps(1) lshift_simps(2) merged.intros(2))
   apply (metis lshift_simps(1))
  apply (smt (verit) append_is_Nil_conv lshift_append)
  done

lemma merged_LCons1: "merged lxs lys lzs \<Longrightarrow> merged (LCons x lxs) lys (LCons x lzs)"
  by (metis lshift_simps(1) lshift_simps(2) merged_lappend1)

lemma merged_LCons2: "merged lxs lys lzs \<Longrightarrow> merged lxs (LCons y lys) (LCons y lzs)"
  by (metis lshift_simps(1) lshift_simps(2) merged_lappend2)

lemma merged_commute: "merged lxs lys lzs \<Longrightarrow> merged lys lxs lzs"
  apply (coinduction arbitrary: lxs lys lzs)
  subgoal for lxs lys lzs
    apply (erule merged.cases)
       apply (fastforce intro: merged.intros)+
    done
  done

lemma merged_mergedL: "merged lxs lys lzs \<Longrightarrow> mergedL lxs lys lzs \<or> mergedL lys lxs lzs"
  apply (erule merged.cases)
     apply (metis mergedL.intros(1))
    apply (metis mergedL.intros(1))
   apply (rule disjI1)
   apply hypsubst_thin
  subgoal for xs ys lxs lys lzs
    apply (coinduction arbitrary: xs ys lxs lys lzs)
    subgoal for xs ys lxs lys lzs
      apply (erule merged.cases)
         apply (metis mergedL.intros(2))
        apply (metis mergedL.intros(2) mergedL.intros(3))
       apply (metis merged_commute merged_lappend1)
      apply (metis (full_types) append_is_Nil_conv lshift_append merged_commute)
      done
    done
   apply (rule disjI2)
   apply hypsubst_thin
  subgoal for xs ys lxs lys lzs
    apply (coinduction arbitrary: xs ys lxs lys lzs)
    subgoal for xs ys lxs lys lzs
      apply (erule merged.cases)
         apply (metis mergedL.intros(2) mergedL.intros(3))
        apply (metis mergedL.intros(2))
       apply (metis (full_types) append_is_Nil_conv lshift_append merged_commute)
      apply (metis merged_commute merged_lappend1)
      done
    done
  done

lemma merged_alt: "merged lxs lys lzs \<longleftrightarrow> mergedL lxs lys lzs \<or> mergedL lys lxs lzs"
  using mergedL_merged mergedRL_merged merged_mergedL by blast

coinductive mergedL_fueled where
  "mergedL_fueled LNil LNil lxs lxs"
| "mergedL_fueled LNil lxs LNil lxs"
| "length xs = n \<Longrightarrow> n > 0 \<Longrightarrow> mergedL_fueled lns lys lxs lzs \<Longrightarrow> mergedL_fueled (LCons n lns) (xs @@- lxs) lys (xs @@- lzs)"

corec fuel_of_mergedL where
  "fuel_of_mergedL lxs lys lzs = (if lxs = LNil \<or> lys = LNil then LNil else
     (let (xs, lxs', lzs') = (SOME (xs, lxs', lzs'). xs \<noteq> [] \<and> mergedL lys lxs' lzs' \<and> lxs = xs @@- lxs' \<and> lzs = xs @@- lzs')
     in LCons (length xs) (fuel_of_mergedL lys lxs' lzs')))"

lemma mergedL_mergedL_fueled: 
  "mergedL lxs lys lzs \<Longrightarrow> mergedL_fueled (fuel_of_mergedL lxs lys lzs) lxs lys lzs"
  apply (coinduction arbitrary: lxs lys lzs)
  subgoal for lxs lys lzs
    apply (erule mergedL.cases)
    apply (simp add: fuel_of_mergedL.code)
     apply (simp add: fuel_of_mergedL.code)
    apply (cases "lys = LNil")
     apply (auto simp add: fuel_of_mergedL.code lshift_LNil_iff elim: mergedL.cases) []
    apply (rule disjI2)+
    apply hypsubst_thin
    apply (subst fuel_of_mergedL.code)
    apply (rule someI2)
    apply (rule case_prodI conjI refl | assumption)+
    apply (force simp: lshift_LNil_iff)
    done
  done

lemma mergedL_fueled_mergedL: 
  "mergedL_fueled lns lxs lys lzs \<Longrightarrow> mergedL lxs lys lzs"
  apply (coinduction arbitrary: lns lxs lys lzs)
  apply (erule mergedL_fueled.cases)
    apply force+
  done

lemma mergedL_alt: "mergedL lxs lys lzs \<longleftrightarrow> (\<exists>lns. mergedL_fueled lns lxs lys lzs)"
  using mergedL_fueled_mergedL mergedL_mergedL_fueled by blast

coinductive mergedL1_fueled where
  "mergedL1_fueled LNil LNil lxs lxs"
| "mergedL1_fueled LNil lxs LNil lxs"
| "mergedL1_fueled (if n = 0 then lns else LCons n lns) (if n = 0 then lys else lxs) (if n = 0 then lxs else lys) lzs \<Longrightarrow>
   mergedL1_fueled (LCons (Suc n) lns) (LCons x lxs) lys (LCons x lzs)"

lemma mergedL_fueled_mergedL1_fueled: "mergedL_fueled lns lxs lys lzs \<Longrightarrow> mergedL1_fueled lns lxs lys lzs"
  apply (coinduction arbitrary: lns lxs lys lzs)
  apply (erule mergedL_fueled.cases)
  apply simp
   apply simp
  apply hypsubst_thin
  apply simp
  subgoal for xs lns lxs lys lzs
    apply (induct xs arbitrary: lxs lzs)
     apply simp
    subgoal for x xs lxs lzs
      apply (cases xs)
       apply(auto intro: mergedL_fueled.intros)
      apply (metis length_Cons lshift_simps(2) mergedL_fueled.intros(3) zero_less_Suc)
      done
    done
  done

lemma mergedL1_fueled_mergedL_fueled: "mergedL1_fueled lns lxs lys lzs \<Longrightarrow> mergedL_fueled lns lxs lys lzs"
  apply (coinduction arbitrary: lns lxs lys lzs)
  subgoal for lns lxs lys lzs
    apply (cases lns)
     apply (auto elim: mergedL1_fueled.cases) []
    subgoal for n lns'
      apply hypsubst_thin
      apply (rule disjI2)+
      apply simp
    apply (induct n arbitrary: lns lxs lzs)
       apply (auto elim: mergedL1_fueled.cases) []
      apply (erule mergedL1_fueled.cases)
        apply (auto split: if_splits)
       apply (metis length_Cons list.size(3) lshift_simps(1) lshift_simps(2))
      apply (metis length_Cons lshift_simps(2))
      done
    done
  done

lemma mergedL_fueled_alt: "mergedL_fueled lns lxs lys lzs \<longleftrightarrow> mergedL1_fueled lns lxs lys lzs"
  using mergedL_fueled_mergedL1_fueled mergedL1_fueled_mergedL_fueled by blast

lemma produced_fairmerge_True_True: "produced m (fairmerge True True) lxs lzs \<longleftrightarrow> lzs = (\<lambda>_. LNil)"
  by (fastforce simp: fun_eq_iff fairmerge.code intro!: exI[of _ "\<lambda>_. 0"])

lemma fairmerge_True_True: "\<lbrakk>fairmerge True True\<rbrakk> lxs lzs \<longleftrightarrow> lzs = (\<lambda>_. LNil)"
  unfolding semantics_def produced_fairmerge_True_True by simp

lemma mute_fairmerge_True_False[simp]: "mute 1 (fairmerge True False) lxs \<longleftrightarrow> lxs 2 = LNil"
  apply (rule iffI)
  subgoal
    apply (subst (asm) fairmerge.code)
    apply (auto split: observation.splits  elim!: chd.elims)
    done
  subgoal
    apply (coinduction arbitrary: lxs rule: mute_coinduct_upto)
    apply (intro disjI2)
    apply (subst fairmerge.code)
    apply (auto intro: mute_cong.intros)
    done
  done

lemma mute_fairmerge_False_True[simp]: "mute 1 (fairmerge False True) lxs \<longleftrightarrow> lxs 1 = LNil"
  apply (rule iffI)
  subgoal
    apply (subst (asm) fairmerge.code)
    apply (auto split: observation.splits  elim!: chd.elims)
    done
  subgoal
    apply (coinduction arbitrary: lxs rule: mute_coinduct_upto)
    apply (intro disjI2)
    apply (subst fairmerge.code)
    apply (auto intro: mute_cong.intros)
    done
  done

lemma mute_fairmerge_False_False[simp]: "mute 1 (fairmerge False False) lxs \<longleftrightarrow> lxs 1 = LNil \<and> lxs 2 = LNil"
  apply (rule iffI)
  subgoal
    apply (subst (asm) fairmerge.code)
    apply (auto split: observation.splits  elim!: chd.elims)
    done
  subgoal
    apply (coinduction arbitrary: lxs rule: mute_coinduct_upto)
    apply (intro disjI2)
    apply (subst fairmerge.code)
    apply (auto intro!: mute_cong.read intro: mute_cong.base mute_cong.mute)
    done
  done

lemma produced_muted: "produced m op lxs lys \<Longrightarrow> muted op lxs lys"
  by (erule produced.cases) auto

lemma produced_fairmerge_True_False: "produced m (fairmerge True False) lxs lzs \<longleftrightarrow> lzs = (\<lambda>_. lxs 2)"
  unfolding fun_eq_iff semantics_def
  apply safe
   apply (subst num1_eq1)
   apply (coinduction arbitrary: m lzs lxs)
   apply safe
  subgoal for m lzs lxs
  proof (induct "m 2" arbitrary: m lxs)
    case 0
    then show ?case 
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  next
    case (Suc n)
    from Suc(2-) Suc(1)[of "m(2 := n)"] show ?case
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  qed
  subgoal for m lzs lxs
    by (auto dest!: produced_muted simp: muted_def)
  subgoal for m lzs lxs
  proof (induct "m 2" arbitrary: m lxs)
    case 0
    then show ?case 
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  next
    case (Suc n)
    from Suc(2-) Suc(1)[of "m(2 := n)"] show ?case
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  qed
  subgoal for m lzs lxs
  proof (induct "m 2" arbitrary: m lxs)
    case 0
    then show ?case 
      apply (subst (asm) fairmerge.code)
      apply (auto split: observation.splits elim!: chd.elims)
       apply (metis fun_upd_same)
      done
  next
    case (Suc n)
    from Suc(2-) Suc(1)[of "m(2 := n)"] show ?case
      apply (subst (asm) fairmerge.code)
      apply (auto split: observation.splits elim!: chd.elims)
       apply (metis fun_upd_same)
      done
  qed
  apply (coinduction arbitrary: m lxs lzs rule: produced_coinduct_upto)
  apply (rule disjI1)
  apply (subst fairmerge.code)
  apply (auto simp: fun_upd_def[where 'b=nat] muted_def split: observation.splits elim!: chd.elims
      intro!: exI[of _ 0])
   apply (rule produced_cong.write) 
    apply (rule produced_cong.base)
    apply (rule conjI refl)+
   apply (simp add: fun_eq_iff)
  apply (rule produced_cong.produced)
  apply (rule produced_End)
  apply (metis (full_types) num1_eq1)
  done

lemma fairmerge_True_False: "\<lbrakk>fairmerge True False\<rbrakk> lxs lzs \<longleftrightarrow> lzs = (\<lambda>_. lxs 2)"
  unfolding semantics_def produced_fairmerge_True_False by simp

lemma produced_fairmerge_False_True: "produced m (fairmerge False True) lxs lzs \<longleftrightarrow> lzs = (\<lambda>_. lxs 1)"
  unfolding fun_eq_iff semantics_def
  apply safe
   apply (subst num1_eq1)
   apply (coinduction arbitrary: m lzs lxs)
   apply safe
  subgoal for m lzs lxs
  proof (induct "m 1" arbitrary: m lxs)
    case 0
    then show ?case 
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  next
    case (Suc n)
    from Suc(2-) Suc(1)[of "m(1 := n)"] show ?case
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  qed
  subgoal for m lzs lxs
    by (auto dest!: produced_muted simp: muted_def)
  subgoal for m lzs lxs
  proof (induct "m 1" arbitrary: m lxs)
    case 0
    then show ?case 
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  next
    case (Suc n)
    from Suc(2-) Suc(1)[of "m(1 := n)"] show ?case
      by (subst (asm) fairmerge.code)
        (auto split: observation.splits elim!: chd.elims)
  qed
  subgoal for m lzs lxs
  proof (induct "m 1" arbitrary: m lxs)
    case 0
    then show ?case 
      apply (subst (asm) fairmerge.code)
      apply (auto split: observation.splits elim!: chd.elims)
       apply (metis fun_upd_same)
      done
  next
    case (Suc n)
    from Suc(2-) Suc(1)[of "m(1 := n)"] show ?case
      apply (subst (asm) fairmerge.code)
      apply (auto split: observation.splits elim!: chd.elims)
       apply (metis fun_upd_same)
      done
  qed
  apply (coinduction arbitrary: m lxs lzs rule: produced_coinduct_upto)
  apply (rule disjI1)
  apply (subst fairmerge.code)
  apply (auto simp: fun_upd_def[where 'b=nat] muted_def split: observation.splits elim!: chd.elims
      intro!: exI[of _ 0])
   apply (rule produced_cong.write) 
    apply (rule produced_cong.base)
    apply (rule conjI refl)+
   apply (simp add: fun_eq_iff)
  apply (rule produced_cong.produced)
  apply (rule produced_End)
  apply (metis (full_types) num1_eq1)
  done

lemma fairmerge_False_True: "\<lbrakk>fairmerge False True\<rbrakk> lxs lzs \<longleftrightarrow> lzs = (\<lambda>_. lxs 1)"
  unfolding semantics_def produced_fairmerge_False_True by simp

lemma "\<lbrakk>fairmerge False False\<rbrakk> (\<lambda>x. if x = 1 then llist_of [1, 2, 3] else llist_of [4, 5]) (\<lambda>_. llist_of [4,1,2,3,5])"
  unfolding semantics_def
  apply (rule exI[of _ "\<lambda>x. 3"])
  apply (subst fairmerge.code; simp)
  apply (rule produced.ReadEOB; auto 0 0 simp: muted_def)
  apply (rule produced.Read[where n=3]; auto 0 0 simp: muted_def)
  apply (rule produced_Write; (auto simp: muted_def)?)
  apply (subst fairmerge.code; simp)
  apply (rule produced.Read[where n=3]; auto 0 0  simp: muted_def)
  apply (rule produced_Write; (auto simp: muted_def)?)
  apply (rule produced.ReadEOB; auto 0 0 simp: muted_def)
  apply (subst fairmerge.code; simp)
  apply (rule produced.Read[where n=3]; auto 0 0 simp: muted_def)
  apply (rule produced_Write; (auto simp: muted_def)?)
  apply (rule produced.ReadEOB; auto 0 0 simp: muted_def)
  apply (subst fairmerge.code; simp)
  apply (rule produced.Read[where n=3]; auto 0 0 simp: muted_def)
  apply (rule produced_Write; (auto simp: muted_def)?)
  apply (rule produced.ReadEOB; auto 0 0 simp: muted_def)
  apply (subst fairmerge.code; simp)
  apply (rule produced.ReadEOB; auto 0 0 simp: muted_def)
  apply (rule produced.Read[where n=3]; auto 0 0 simp: muted_def)
  apply (rule produced_Write; (auto simp: muted_def)?)
  apply (subst fairmerge.code; simp)
  apply (rule produced.Read[where n=3]; auto 0 0 simp: muted_def)
  apply (subst fairmerge.code; simp)
  apply (rule produced.Read[where n=3]; auto 0 0)
  done

lemma fairmerge_False_False_Read:
  "fairmerge False False = Read p f \<longleftrightarrow> p = 1 \<and> f = (case_observation (Write (Read 2 (case_observation (Write (fairmerge False False) 1) (fairmerge False False) (fairmerge False True))) 1)
     (Read 2 (case_observation (Write (fairmerge False False) 1) (fairmerge False False) (fairmerge False True))) (fairmerge True False))"
  by (subst fairmerge.code; auto)+

lemma fairmerge_False_False_NoRead:
  "fairmerge False False = Write op' p' x = False"
  "fairmerge False False = End = False"
  by (subst fairmerge.code; auto)+

lemma inputs_fairmerge_False_TrueD: "p \<in> inputs op \<Longrightarrow> op = fairmerge False True \<or> (\<exists>x. op = Write (fairmerge False True) 1 x) \<Longrightarrow> p = 1"
  apply (induct p op rule: op.set_induct(1))
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  done

lemma inputs_fairmerge_False_True[simp]: "inputs (fairmerge False True) = {1}"
  apply (auto dest: inputs_fairmerge_False_TrueD)
  apply (subst fairmerge.code; auto split: observation.splits elim!: chd.elims)
  done

lemma inputs_fairmerge_True_FalseD: "p \<in> inputs op \<Longrightarrow> op = fairmerge True False \<or> (\<exists>x. op = Write (fairmerge True False) 1 x) \<Longrightarrow> p = 2"
  apply (induct p op rule: op.set_induct(1))
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  done

lemma inputs_fairmerge_True_False[simp]: "inputs (fairmerge True False) = {2}"
  apply (auto dest: inputs_fairmerge_True_FalseD)
  apply (subst fairmerge.code; auto split: observation.splits elim!: chd.elims)
  done

lemma inputs_fairmerge_False_FalseD: "p \<in> inputs op \<Longrightarrow>
  op = fairmerge False False \<or>
  op = Read 2 (case_observation (Write (fairmerge False False) 1) (fairmerge False False) (fairmerge False True)) \<or>
  (\<exists>x. op = Write (Read 2 (case_observation (Write (fairmerge False False) 1) (fairmerge False False) (fairmerge False True))) 1 x) \<or>
  (\<exists>x. op = Write (fairmerge False False) 1 x) \<Longrightarrow> p = 1 \<or> p = 2"
  apply (induct p op rule: op.set_induct(1))
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  apply (subst (asm) fairmerge.code; auto split: observation.splits elim!: chd.elims)
  done


lemma inputs_fairmerge_False_False[simp]: "inputs (fairmerge False False) = {1, 2}"
  apply (auto dest: inputs_fairmerge_False_FalseD)
  apply (subst fairmerge.code; auto split: observation.splits elim!: chd.elims)+
  done


lemma cleaned_fairmerge: "cleaned (fairmerge e1 e2)"
  apply (coinduction arbitrary: e1 e2 rule: cleaned_coinduct_upto)
  subgoal for e1 e2
    apply (subst (1 3 5) fairmerge.code)
    apply (auto 3 4 split: bool.splits split: observation.splits
      intro: cc_base intro!: cc_write cc_read cc_cleaned[of End])
    done
  done

lemma mergedL1_fueled_fairmerge: "mergedL1_fueled lns (lxs i) (lxs j) (lzs 1) \<Longrightarrow> i = 1 \<and> j = 2 \<or> i = 2 \<and> j = 1 \<Longrightarrow>
  produced (\<lambda>p. if p = j \<and> lns \<noteq> LNil then lhd lns else 0) (fairmerge False False) lxs lzs"
  apply (coinduction arbitrary: i j lns lxs lzs rule: produced_coinduct_upto)
  subgoal for i j lns lxs lzs
    apply (erule mergedL1_fueled.cases)
    subgoal for lxs'
      apply (elim disjE conjE)
       apply (rule disjI1)
       apply (subst fairmerge.code; simp add: muted_def)
       apply (rule exI[of _ 0])
       apply (rule produced_cong.produced; auto simp add: produced_fairmerge_True_False fun_eq_iff)
      apply (rule disjI1)
      apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
       apply (rule exI[of _ 0])
       apply (rule produced_cong.produced)
       apply (rule produced_Write[rotated])
         apply (rule produced.Read[rotated])
          apply (simp add: produced_fairmerge_False_True)
         apply (auto simp: fun_eq_iff muted_def) [3]
      apply (rule exI[of _ 0])
      apply (rule produced_cong.produced)
      apply (simp add: produced_fairmerge_True_False)
      apply (auto simp: fun_eq_iff) []
      done
    subgoal for lxs'
      apply (elim disjE conjE)
       apply (rule disjI1)
       apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
        apply (rule exI[of _ 0])
        apply (rule produced_cong.produced)
        apply (rule produced_Write[rotated])
          apply (rule produced.Read[rotated])
           apply (simp add: produced_fairmerge_False_True)
          apply (auto simp: fun_eq_iff muted_def) [3]
       apply (subst fairmerge.code; simp)
       apply (rule exI[of _ 0])
       apply (rule produced_cong.produced)
       apply (simp add: produced_fairmerge_True_False)
       apply (auto simp: fun_eq_iff) []
      apply (rule disjI1)
      apply (subst fairmerge.code; simp add: muted_def)
      apply (rule exI[of _ 0])
      apply (rule produced_cong.produced)
      apply (simp add: produced_fairmerge_True_False)
      apply (auto simp: fun_eq_iff) []
      done
    subgoal for n lns' lys lxs' lzs' x
      apply (elim disjE conjE)
       apply (simp_all split: if_splits)
         apply hypsubst_thin
         apply (cases "lns' = LNil")
      subgoal
        apply (rule disjI1)
        apply (erule mergedL1_fueled.cases; simp)
         apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
         apply (rule exI[of _ 0])
         apply (rule produced_cong.produced)
         apply (rule produced_Write[rotated])
           apply (rule produced.Read[rotated])
            apply (simp add: produced_fairmerge_False_True)
           apply (auto simp: fun_eq_iff muted_def) [3]
        apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
        apply (rule exI[of _ 0])
        apply (rule produced_cong.produced)
        apply (rule produced_Write[rotated])
          apply (rule produced.Read[rotated])
           apply (auto 0 0 simp add: muted_def produced_fairmerge_False_True fun_eq_iff
            split: observation.split elim!: chd.elims)
        apply (rule produced_Write[rotated])
          apply (auto simp: fun_eq_iff) [3]
        apply (subst fairmerge.code; auto split: observation.split elim!: chd.elims)
        apply (rule produced.Read[rotated])
         apply (auto 0 0 simp add: muted_def produced_fairmerge_True_False fun_eq_iff
            split: observation.split elim!: chd.elims)
        done
      subgoal
        apply (rule disjI1)
        apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
        apply (rule exI[of _ "lhd lns'"])
        apply (rule produced_cong.write[where lys' = "CTL 1 lzs"]; auto simp: fun_eq_iff)
        apply (rule produced_cong.read; auto simp: fun_eq_iff)
        apply (rule produced_cong.base)
        apply (auto intro: exI[of _ 2])
        done
        apply hypsubst_thin
      subgoal
        apply (rule disjI1)
        apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
        apply (rule exI[of _ 0])
        apply (rule produced_cong.write[where lys' = "CTL 1 lzs"]; auto simp: fun_eq_iff)
        apply (rule produced_cong.read; auto simp: fun_eq_iff)
        apply (rule produced_cong.base)
        apply (rule exI[of _ 1])
        apply (rule exI[of _ 2])
        apply (rule exI[of _ "LCons n lns'"])
        apply (rule conjI[rotated])
         apply (rule conjI[OF refl])
         apply (rule conjI)
          apply (auto intro: exI[of _ 1]) 
        done
       apply hypsubst_thin
       apply (cases "lns' = LNil")
      subgoal
        apply (rule disjI2)
        apply (rule disjI1)
        apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
        apply (rule produced_cong.produced)
          apply (rule produced.Read[rotated]; auto 0 0 split: observation.split elim!: chd.elims)
        apply (rule produced_Write[where lys = "CTL 1 lzs", rotated])
        apply (auto simp: fun_eq_iff elim: mergedL1_fueled.cases) [3]
        apply (subst fairmerge.code; auto split: observation.split elim!: chd.elims)
        apply (rule produced.Read[rotated]; auto 0 0 split: observation.split elim!: chd.elims)
        apply (rule produced_Write[where lys = "CTL 1 (CTL 1 lzs)", rotated])
        apply (rule produced.Read[rotated]; auto 0 0 split: observation.split elim!: chd.elims)
        apply (rule produced_Write[where lys = "CTL 1 (CTL 1 lzs)", rotated])
        apply (auto simp: muted_def fun_eq_iff produced_fairmerge_False_True produced_fairmerge_True_False elim: mergedL1_fueled.cases)
        done
      subgoal
        apply (rule disjI2)
        apply (rule disjI1)
        apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
        apply (rule produced_cong.read; auto simp: fun_eq_iff)
        apply (rule produced_cong.write[where lys' = "CTL 1 lzs"]; auto simp: fun_eq_iff)
        apply (rule produced_cong.base)
        apply (rule exI[of _ 1])
        apply (rule exI[of _ 2])
        apply (rule exI[of _ "lns'"])
        apply (rule conjI[rotated])
         apply (rule conjI[OF refl])
         apply (rule conjI)
          apply (auto intro: exI[of _ 2]) 
        done
      apply hypsubst_thin
      apply (rule disjI2)
      apply (rule disjI1)
      apply (subst fairmerge.code; auto simp: muted_def split: observation.split elim!: chd.elims)
      apply (rule produced_cong.read; auto simp: fun_eq_iff)
      apply (rule produced_cong.write[where lys' = "CTL 1 lzs"]; auto simp: fun_eq_iff)
      apply (rule produced_cong.base)
      apply (rule exI[of _ 2])
      apply (rule exI[of _ 1])
      apply (rule exI[of _ "LCons n lns'"])
      apply (rule conjI[rotated])
       apply (rule conjI[OF refl])
       apply (rule conjI)
        apply (auto intro: exI[of _ 2]) 
      done
    done
  done

lemma merged_fairmerge_False_False:
  "merged (lxs 1) (lxs 2) (lzs 1) \<Longrightarrow> \<lbrakk>fairmerge False False\<rbrakk> lxs lzs"
  unfolding merged_alt mergedL_alt mergedL_fueled_alt semantics_def
  using mergedL1_fueled_fairmerge[of _ lxs 1 2 lzs] mergedL1_fueled_fairmerge[of _ lxs 2 1 lzs]
  by blast
(*
lemma traced_merged:
  "traced m (fairmerge False False) ios \<Longrightarrow> lxs = lproject Inl ios \<Longrightarrow> lzs = lproject Inr ios \<Longrightarrow> merged (lxs 1) (lxs 2) (lzs 1)"
  apply (coinduction arbitrary: m ios lxs lzs)
  apply (subst (asm) fairmerge.code; simp)
  apply (erule traced_ReadE; auto 0 0 split: observation.splits simp: lproject_def elim!: chd.elims)
  subgoal
    by (smt (verit, del_insts) llist.simps(3) lshift_simps(1) lshift_simps(2))
                      apply (simp_all add: image_iff split_beta split: observation.splits)
  
  sorry

lemma produced_traced:
  "produced m op lxs lys \<Longrightarrow> \<exists>ios. traced m op ios \<and> (\<forall>p. lprefix (lproject Inl ios p) (lxs p)) \<and> lys = lproject Inr ios"
  sorry

lemma fairmerge_semantics: "\<lbrakk>fairmerge False False\<rbrakk> lxs lzs \<Longrightarrow> merged (lxs 1) (lxs 2) (lzs 1)"
  unfolding semantics_def
  apply (erule exE)
  apply (drule produced_traced)
  apply (erule exE conjE)+
  apply (drule traced_merged)
    apply (rule refl)
   apply assumption
  apply assumption
  done
*)

inductive producing for p where
  "producing p End lxs 0"
| "producing p (Write _ p _) lxs 0"
| "producing p (f (CHD p' lxs)) (CTL p' lxs) i \<Longrightarrow> producing p (Read p' f) lxs (Suc i)"
| "p \<noteq> p' \<Longrightarrow> producing p op lxs i \<Longrightarrow> producing p (Write op p' x) lxs (Suc i)"

inductive_cases producing_EndE[elim!]: "producing p End lxs n"
inductive_cases producing_WriteE[elim!]: "producing p (Write op p' x) lxs n"
inductive_cases producing_ReadE[elim!]: "producing p (Read p' f) lxs n"

lemma producing_inject: "producing p op lxs i \<Longrightarrow> producing p op lxs j \<Longrightarrow> i = j"
  by (induct op lxs i arbitrary: j rule: producing.induct) fastforce+

lemma The_producing: "producing p op lxs i \<Longrightarrow> The (producing p op lxs) = i"
  using producing_inject by fast

corecursive produce where
  "produce op lxs p = (let produce' = (\<lambda>op' lxs'. if \<exists>i. producing p op lxs i then produce op' lxs' p else LNil) in case op of
    Read p' f \<Rightarrow> (produce' (f (CHD p' lxs)) (CTL p' lxs))
  | Write op' p' x \<Rightarrow> (if p = p' then LCons x (produce op' lxs p) else produce' op' lxs)
  | End \<Rightarrow> LNil)"
  by (relation "measure (\<lambda>(op, lxs, p). THE i. producing p op lxs i)")
    (auto 0 3 simp: The_producing del: producing_ReadE producing_WriteE elim: producing.cases)

lemma produce_code[code]:
  "produce op lxs p = (case op of
    Read p' f \<Rightarrow> produce (f (CHD p' lxs)) (CTL p' lxs) p
  | Write op' p' x \<Rightarrow> (if p = p' then LCons x (produce op' lxs p) else produce op' lxs p)
  | End \<Rightarrow> LNil)"
  apply (subst produce.code)
  apply (simp split: op.splits if_splits)
  apply safe
  subgoal for p' f
    by (subst produce.code) (auto 0 5 split: op.splits intro: producing.intros)
  subgoal for op p x
    by (subst produce.code) (auto 0 4 split: op.splits intro: producing.intros)
  done

simps_of_case produce_simps[simp]: produce_code

lemma producing_mute_LNil: "producing p op lxs n \<Longrightarrow> mute p op lxs \<Longrightarrow> produce op lxs p = LNil"
  by (induct op lxs n rule: producing.induct) (auto elim: mute.cases)

lemma mute_produce_LNil: "mute p op lxs \<Longrightarrow> produce op lxs p = LNil"
  by (subst produce.code)
    (auto split: op.splits dest: producing_mute_LNil simp flip: produce_def)

lemma not_producing_LNil: "(\<forall>n. \<not> producing p op lxs n) \<Longrightarrow> produce op lxs p = LNil"
  by (subst produce.code) (auto split: op.splits intro: producing.intros)

lemma muted_produce: "muted op lxs (produce op lxs)"
  using mute_produce_LNil[of _ op lxs] unfolding muted_def
  by blast

lemma produced_produce: "produced m op lxs (produce op lxs)"
  apply (coinduction arbitrary: m op lxs)
  subgoal for m op lxs
    by (cases op) (force simp: muted_def muted_produce[unfolded muted_def])+
  done

lemma semantics_produce: "\<lbrakk>op\<rbrakk> lxs (produce op lxs)"
  unfolding semantics_def
  by (simp add: produced_produce)

datatype 'd buf = BEmpty | BEnded | BCons 'd "'d buf"

fun bhd where
  "bhd BEmpty = EOB"
| "bhd BEnded = EOS"
| "bhd (BCons x xs) = Observed x"

fun btl where
  "btl BEmpty = BEmpty"
| "btl BEnded = BEnded"
| "btl (BCons x xs) = xs"

fun bend where
  "bend BEmpty = BEnded"
| "bend BEnded = BEnded"
| "bend (BCons xs xss) = BCons xs (bend xss)"

fun benq where
  "benq x BEmpty = BCons x BEmpty"
| "benq x BEnded = BCons x BEnded"
| "benq x (BCons y ys) = BCons y (benq x ys)"

abbreviation BHD :: "'a \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> 'd observation" where "BHD p buf \<equiv> bhd (buf p)"
abbreviation (input) BUPD where "BUPD f p buf \<equiv> buf(p := f (buf p))"
abbreviation BTL :: "'a \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BTL \<equiv> BUPD btl"
abbreviation BENQ :: "'a \<Rightarrow> 'd \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BENQ p x buf \<equiv> BUPD (benq x) p buf"
abbreviation BENQ_TL :: "'a \<Rightarrow> 'd \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BENQ_TL p x buf \<equiv> BUPD (btl o benq x) p buf"

inductive loop_producing :: "('op \<rightharpoonup> 'ip) \<Rightarrow> ('ip \<Rightarrow> 'd buf) \<Rightarrow> ('ip, 'op, 'd) op \<Rightarrow> nat \<Rightarrow> bool" where
  "loop_producing wire buf End 0"
| "p \<notin> ran wire \<Longrightarrow> loop_producing wire buf (Read p f) 0"
| "wire p' = None \<Longrightarrow> loop_producing wire buf (Write op p' x) 0"
| "p \<in> ran wire \<Longrightarrow> loop_producing wire (buf(p := btl (buf p))) (f (bhd (buf p))) n \<Longrightarrow> loop_producing wire buf (Read p f) (Suc n)"
| "wire p' = Some p \<Longrightarrow> loop_producing wire (buf(p := benq x (buf p))) op n \<Longrightarrow> loop_producing wire buf (Write op p' x) (Suc n)"

lemma loop_producing_inject: "loop_producing wire buf op i \<Longrightarrow> loop_producing wire buf op j \<Longrightarrow> i = j"
proof (induct wire buf op i arbitrary: j rule: loop_producing.induct)
  case (4 p wire buf f n)
  from 4(4,1,2) 4(3)[of "j - 1"] show ?case
    by (elim loop_producing.cases[of _ _ "Read p f"]) (auto simp del: fun_upd_apply)
next
  case (5 wire p' p buf x op n)
  from 5(4,1,2) 5(3)[of "j - 1"] show ?case
    by (elim loop_producing.cases[of _ _ "Write op p' x"]) (auto simp del: fun_upd_apply)
qed (auto elim: loop_producing.cases)

lemma The_loop_producing: "loop_producing wire buf op i \<Longrightarrow> The (loop_producing wire buf op) = i"
  using loop_producing_inject by fast

corecursive loop_op :: "('op \<rightharpoonup> 'ip) \<Rightarrow> ('ip \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip, 'op, 'd) op \<Rightarrow> ('ip, 'op, 'd) op" where
  "loop_op wire buf op = (
     let loop_op' = (\<lambda>buf' op'. if \<exists>n. loop_producing wire buf op n then loop_op wire buf' op' else End)
     in case op of
     End \<Rightarrow> End
   | Read p f \<Rightarrow> if p \<in> ran wire
       then loop_op' (BTL p buf) (f (BHD p buf))
       else Read p (\<lambda>x. loop_op wire buf (f x))
   | Write op' p' x \<Rightarrow> (case wire p' of
         None \<Rightarrow> Write (loop_op wire buf op') p' x
       | Some p \<Rightarrow> loop_op' (BENQ p x buf) op'))"
  by (relation "measure (\<lambda>(wire, buf, op). THE i. loop_producing wire buf op i)")
    (auto 0 3 simp: The_loop_producing elim: loop_producing.cases)

lemma loop_op_code[code]:
  "loop_op wire buf op = (case op of
     End \<Rightarrow> End
   | Read p f \<Rightarrow> if p \<in> ran wire
       then loop_op wire (BTL p buf) (f (BHD p buf))
       else Read p (\<lambda>x. loop_op wire buf (f x))
   | Write op' p' x \<Rightarrow> (case wire p' of
         None \<Rightarrow> Write (loop_op wire buf op') p' x
       | Some p \<Rightarrow> loop_op wire (BENQ p x buf) op'))"
  apply (subst loop_op.code)
  apply (simp split: op.splits option.splits)
  apply safe
  subgoal for p f
    by (subst loop_op.code) (auto 0 4 split: op.splits option.splits intro: loop_producing.intros)
  subgoal for op' p' x
    by (subst loop_op.code) (auto 0 4 split: op.splits option.splits intro: loop_producing.intros)
  done
simps_of_case loop_op_simps[simp]: loop_op_code

inductive comp_producing :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow> ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> nat \<Rightarrow> bool" for wire where
  "comp_producing wire buf End End 0"
| "comp_producing wire buf (Read p1 f1) End 0"
| "wire p1 = None \<Longrightarrow> comp_producing wire buf (Write op1' p1 x1) End 0"
| "wire p1 = Some p \<Longrightarrow> comp_producing wire buf op1' End n \<Longrightarrow> comp_producing wire buf (Write op1' p1 x1) End (Suc n)"
| "comp_producing wire buf End (Write op2' p2 x2) 0"
| "comp_producing wire buf (Read p1 f1) (Write op2' p2 x2) 0"
| "comp_producing wire buf (Write op1' p1 x1) (Write op2' p2 x2) 0"
| "p2 \<notin> ran wire \<Longrightarrow> comp_producing wire buf End (Read p2 f2) 0"
| "p2 \<in> ran wire \<Longrightarrow> comp_producing wire (BTL p2 (bend o buf)) End (f2 (BHD p2 (bend o buf))) n \<Longrightarrow> comp_producing wire buf End (Read p2 f2) (Suc n)"
| "comp_producing wire buf (Read p1 f1) (Read p2 f2) 0"
| "p2 \<notin> ran wire \<or> wire p1 = None \<Longrightarrow> comp_producing wire buf (Write op1' p1 x1) (Read p2 f2) 0"
| "p2 \<in> ran wire \<Longrightarrow> wire p1 = Some p \<Longrightarrow>
    comp_producing wire (BTL p2 (BENQ p x1 buf)) op1' (f2 (BHD p2 (BENQ p x1 buf))) n \<Longrightarrow>
    comp_producing wire buf (Write op1' p1 x1) (Read p2 f2) (Suc n)"

lemma comp_producing_inject: "comp_producing wire buf op1 op2 i \<Longrightarrow> comp_producing wire buf op1 op2 j \<Longrightarrow> i = j"
proof (induct buf op1 op2 i arbitrary: j rule: comp_producing.induct)
  case (4 p1 p buf op1' n x1)
  from 4(4,1-2) 4(3)[of "j - 1"] show ?case
    by (elim comp_producing.cases[of _ _ "Write op1' p1 x1"]) (auto simp del: fun_upd_apply)
next
  case (9 p2 buf f2 n)
  from 9(4,1-2) 9(3)[of "j - 1"] show ?case
    by (elim comp_producing.cases[of _ _ _ "Read p2 f2"]) (auto simp del: fun_upd_apply)
next
  case (12 p2 p1 p buf x1 op1' f2 n)
  from 12(5,1-3) 12(4)[of "j - 1"] show ?case
    by (elim comp_producing.cases[of _ _ _ "Read p2 f2"]) (auto simp del: fun_upd_apply)
qed (auto elim: comp_producing.cases)

lemma The_comp_producing: "comp_producing wire buf op1 op2 i \<Longrightarrow> The (comp_producing wire buf op1 op2) = i"
  using comp_producing_inject by fast

(*workaround about termination issue in corecursive*)
lemma case_prod_cong4[fundef_cong]:
  fixes prod prod' f g
  shows "prod = prod' \<Longrightarrow>
    (\<And>x1 x2 y1 y2. prod' = ((x1, x2), (y1, y2)) \<Longrightarrow> f x1 x2 y1 y2 = g x1 x2 y1 y2) \<Longrightarrow>
    ((\<lambda>((x1, x2), (y1, y2)). f x1 x2 y1 y2) prod) = ((\<lambda>((x1, x2), (y1, y2)). g x1 x2 y1 y2) prod')"
  by (auto split: prod.splits)

corecursive comp_op :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> ('ip1 + 'ip2, 'op1 + 'op2, 'd) op" where
  "comp_op wire buf op1 op2 =
     (let comp_op' = (\<lambda>buf' op1' op2'. if \<exists>n. comp_producing wire buf op1 op2 n then comp_op wire buf' op1' op2' else End) in
     case (op1, op2) of
     (End, End) \<Rightarrow> End
   | (End, Write op2' p2 x2) \<Rightarrow> Write (comp_op wire (bend o buf) End op2') (Inr p2) x2
   | (End, Read p2 f2) \<Rightarrow> let buf' = bend o buf in if p2 \<in> ran wire
     then comp_op' (BTL p2 buf') End (f2 (BHD p2 buf'))
     else Read (Inr p2) (\<lambda>y2. comp_op wire buf' End (f2 y2))
   | (Read p1 f1, End) \<Rightarrow> Read (Inl p1) (\<lambda>y1. comp_op wire buf (f1 y1) End)
   | (Read p1 f1, Write op2' p2 x2) \<Rightarrow> Read (Inl p1) (\<lambda>y1. Write (comp_op wire buf (f1 y1) op2') (Inr p2) x2)
   | (Read p1 f1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then Read (Inl p1) (\<lambda>y1. comp_op wire (BTL p2 buf) (f1 y1) (f2 (BHD p2 buf)))
     else Read (Inl p1) (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2)))
   | (Write op1' p1 x1, End) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> Write (comp_op wire buf op1' End) (Inl p1) x1
     | Some p \<Rightarrow> comp_op' buf op1' End)
   | (Write op1' p1 x1, Write op2' p2 x2) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> Write (Write (comp_op wire buf op1' op2') (Inr p2) x2) (Inl p1) x1
     | Some p \<Rightarrow> Write (comp_op wire (BENQ p x1 buf) op1' op2') (Inr p2) x2)
   | (Write op1' p1 x1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then (case wire p1 of
       None \<Rightarrow> Write (comp_op wire (BTL p2 buf) op1' (f2 (BHD p2 buf))) (Inl p1) x1
     | Some p \<Rightarrow> comp_op' (BTL p2 (BENQ p x1 buf)) op1' (f2 (BHD p2 (BENQ p x1 buf))))
     else (case wire p1 of
       None \<Rightarrow> Write (Read (Inr p2) (\<lambda>y2. comp_op wire buf op1' (f2 y2))) (Inl p1) x1
     | Some p \<Rightarrow> Read (Inr p2) (\<lambda>y2. comp_op wire (BENQ p x1 buf) op1' (f2 y2))))"
  by (relation "measure (\<lambda>((wire, buf), op1, op2). THE i. comp_producing wire buf op1 op2 i)")
    (auto 0 3 simp: The_comp_producing elim: comp_producing.cases)

lemma not_comp_producing_eq_End: "\<forall>n. \<not> comp_producing wire buf op1 op2 n \<Longrightarrow> comp_op wire buf op1 op2 = End"
  apply (coinduction arbitrary: buf op1 op2)
  apply auto
  subgoal for buf op1 op2
    apply (subst (asm) comp_op.code)
    apply (auto split: op.splits if_splits option.splits simp: Let_def intro: comp_producing.intros)
    done
  subgoal for buf op1 op2
    apply (subst (asm) comp_op.code)
    apply (auto split: op.splits if_splits option.splits simp: Let_def intro: comp_producing.intros)
    done
  done

lemma comp_op_code[code]:
  "comp_op wire buf op1 op2 = (case (op1, op2) of
     (End, End) \<Rightarrow> End
   | (End, Write op2' p2 x2) \<Rightarrow> Write (comp_op wire (bend o buf) End op2') (Inr p2) x2
   | (End, Read p2 f2) \<Rightarrow> let buf = bend o buf in if p2 \<in> ran wire
     then comp_op wire (BTL p2 buf) End (f2 (BHD p2 buf))
     else Read (Inr p2) (\<lambda>y2. comp_op wire buf End (f2 y2))
   | (Read p1 f1, End) \<Rightarrow> Read (Inl p1) (\<lambda>y1. comp_op wire buf (f1 y1) End)
   | (Read p1 f1, Write op2' p2 x2) \<Rightarrow> Read (Inl p1) (\<lambda>y1. Write (comp_op wire buf (f1 y1) op2') (Inr p2) x2)
   | (Read p1 f1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then Read (Inl p1) (\<lambda>y1. comp_op wire (BTL p2 buf) (f1 y1) (f2 (BHD p2 buf)))
     else Read (Inl p1) (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2)))
   | (Write op1' p1 x1, End) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> Write (comp_op wire buf op1' End) (Inl p1) x1
     | Some p \<Rightarrow> comp_op wire buf op1' End)
   | (Write op1' p1 x1, Write op2' p2 x2) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> Write (Write (comp_op wire buf op1' op2') (Inr p2) x2) (Inl p1) x1
     | Some p \<Rightarrow> Write (comp_op wire (BENQ p x1 buf) op1' op2') (Inr p2) x2)
   | (Write op1' p1 x1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then (case wire p1 of
       None \<Rightarrow> Write (comp_op wire (BTL p2 buf) op1' (f2 (BHD p2 buf))) (Inl p1) x1
     | Some p \<Rightarrow> comp_op wire (BTL p2 (BENQ p x1 buf)) op1' (f2 (BHD p2 (BENQ p x1 buf))))
     else (case wire p1 of
       None \<Rightarrow> Write (Read (Inr p2) (\<lambda>y2. comp_op wire buf op1' (f2 y2))) (Inl p1) x1
     | Some p \<Rightarrow> Read (Inr p2) (\<lambda>y2. comp_op wire (BENQ p x1 buf) op1' (f2 y2))))"
  apply (subst comp_op.code)
  apply (simp split: op.splits option.splits add: Let_def)
  apply safe
  subgoal for p1 f1 op2' p2 x2
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros)
  subgoal for p2 f2 op1' p1 x1
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal for p2 f2 op1' p1 x1
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal for p2 f2 op1' p1 x1
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal for p2 f2 op1' p1 x1
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal for p2 f2 op1' p1 x1 p
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal for p2 f2
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  done
simps_of_case comp_op_simps': comp_op_code[unfolded prod.case]

simps_of_case comp_op_simps[simp]: comp_op.code[unfolded prod.case Let_def]

lemma loud_in_outputs: "loud p op lxs \<Longrightarrow> p \<in> outputs op"
  by (induct op lxs pred: loud) auto

lemma loud_cong[cong]: "p = q \<Longrightarrow> op = op' \<Longrightarrow> (\<And>q. q \<in> inputs op' \<Longrightarrow> lxs q = lxs' q) \<Longrightarrow> loud p op lxs = loud q op' lxs'"
  apply hypsubst_thin
  apply (rule iffI)
  subgoal premises prems
    using prems(2,1)
  proof (induct op' lxs arbitrary: lxs' pred: loud)
    case (Read f p' lxs)
    then have *: "lxs p' = lxs' p'"
      by simp
    show ?case
      by (force intro!: loud.intros(3) Read(2)[unfolded *] Read(3))
  qed (auto intro: loud.intros)
  subgoal premises prems
    using prems(2,1)
  proof (induct op' lxs' arbitrary: lxs pred: loud)
    case (Read f p' lxs')
    then have *: "lxs p' = lxs' p'"
      by simp
    show ?case
      by (force intro!: loud.intros(3) Read(2)[folded *] Read(3))
  qed (auto intro: loud.intros)
  done

definition "lproject R ios = (\<lambda>p. lmap (obs o snd) (lfilter (\<lambda>qx. case qx of (q, Observed x) \<Rightarrow> R p q | _ \<Rightarrow> False) ios))"

lemma lproject_LNil[simp]: "lproject R LNil = (\<lambda>p. LNil)"
  by (simp add: lproject_def)

lemma lproject_LCons[simp]: "lproject R (LCons (q, Observed x) lxs) =
  (\<lambda>p. if R p q then LCons x (lproject R lxs p) else lproject R lxs p)"
  "lproject R (LCons (q, EOS) lxs) = lproject R lxs"
  "lproject R (LCons (q, EOB) lxs) = lproject R lxs"
  by (auto simp add: lproject_def)

lemma lproject_empty_conv:
  "lproject R lxs p = LNil \<longleftrightarrow> (\<forall>q x. (q, Observed x) \<in> lset lxs \<longrightarrow> \<not> R p q)"
  "LNil = lproject R lxs p \<longleftrightarrow> (\<forall>q x. (q, Observed x) \<in> lset lxs \<longrightarrow> \<not> R p q)"
  by (force simp: lproject_def lmap_eq_LNil LNil_eq_lmap lfilter_empty_conv
    split: observation.splits)+

lemma lproject_False: 
  "(\<And>q x. (q, Observed x) \<in> lset lxs \<Longrightarrow> \<not> R p q) \<Longrightarrow> lproject R lxs p = LNil"
  by (simp add: lproject_empty_conv)

lemma lproject_False_weak: 
  "(\<And>qx. qx \<in> lset lxs \<Longrightarrow> \<not> R p (fst qx)) \<Longrightarrow> lproject R lxs p = LNil"
  by (force simp add: lproject_empty_conv)

lemma Inr_in_traced_loud:
  "r \<in> lset ios \<Longrightarrow>
   r = (Inr p, x) \<Longrightarrow>
   traced fuel op ios \<Longrightarrow>
   cleaned op \<Longrightarrow>
   loud p op (lproject (\<lambda>p q. Inl p = q) ios)"
  apply (induct ios arbitrary: op fuel rule: lset_induct'[where x=r])
  subgoal for xs op
    apply (auto intro: loud.intros elim: traced.cases)
    done
  subgoal for x xs op fuel
    apply (cases op)
      apply hypsubst
      apply (auto intro: loud.intros)
    subgoal for p' f' x n
      apply (cases x)
      subgoal
        apply (force intro: loud.intros elim: loud_cong[OF refl refl, THEN iffD1, rotated 1])
        done
      subgoal for y
        apply hypsubst_thin
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply simp
        apply (rule loud.Read)
        apply (auto elim: loud_cong[OF refl refl, THEN iffD1, rotated 1])
        done
      done
    subgoal for p' f'
        apply hypsubst_thin
        apply (drule meta_spec)+
        apply (drule meta_mp)
       apply simp
        apply (drule meta_mp)
       apply simp
      apply (rule loud.Read)
      apply (erule loud_cong[OF refl, THEN iffD1, rotated 2])
      using lproject_False_weak[of xs "(\<lambda>p q. Inl p = q)" p']
       apply (auto simp: image_iff)
      apply (metis chd.simps(1) mem_Collect_eq non_input_traces traces_def)
      apply (metis chd.simps(1) mem_Collect_eq non_input_traces traces_def)
      done
    subgoal
      apply (auto intro: loud.intros)
      done
    done
  done

lemma If_eq_triv[simp]: "(if x = y then f y else f x) = f x"
  by auto

lemma traced_produced:
  "traced m op ios \<Longrightarrow> cleaned op \<Longrightarrow>
   produced m op (lproject (\<lambda>p q. Inl p = q) ios) (lproject (\<lambda>p q. Inr p = q) ios)"
  apply (coinduction arbitrary: m op ios)
  subgoal for m op ios
    apply (erule traced.cases)
    subgoal for fuel p n f x lxs'
      apply (rule disjI1)
      apply (auto simp add: muted_def lproject_empty_conv dest: Inr_in_traced_loud loud_not_mute cong: if_cong)
      subgoal
        apply (auto simp add: fun_eq_iff)
        done
      done
    subgoal for fuel p n f lxs
      apply (rule disjI1)
      apply (auto simp add: muted_def lproject_empty_conv)
      subgoal for p' y
        apply (frule Inr_in_traced_loud[rotated 2])
        apply simp
          apply assumption
         apply (rule refl)
        apply (drule loud_not_mute)
        using lproject_False_weak[of lxs "(\<lambda>p q. Inl p = q)" p]
        apply (auto simp: image_iff elim!: notE[of "mute _ _ _"]
          elim: mute_cong[OF refl refl, THEN iffD1, rotated 1])
        apply (smt (verit, ccfv_SIG) chd.simps(1) mem_Collect_eq mute_cong non_input_traces traces_def)
        done
      subgoal
        apply (rule exI[of _ "n"])
        apply (rule disjI1)
        apply (rule exI[of _ lxs])
        using lproject_False[of lxs "(\<lambda>p q. Inl p = q)" p]
        apply (auto simp add: image_iff)
        using non_input_traces traces_def apply fastforce
        using non_input_traces traces_def apply fastforce
        done
      done
    subgoal for fuel p n f lxs
      apply (rule disjI2)
      apply (rule disjI1)
      apply (auto simp add: muted_def lproject_empty_conv dest: Inr_in_traced_loud loud_not_mute)
      done
    subgoal for fuel op lxs p x
      apply (rule disjI2)
      apply (rule disjI2)
      apply (auto simp add: lproject_empty_conv)
      apply (rule exI[of _ "lproject (\<lambda>p q. Inr p = q) lxs"])
        apply (auto simp add: muted_def lproject_empty_conv dest: loud_not_mute Inr_in_traced_loud)
      done
    subgoal
      by auto
    done
  done

corec trace_op where
  "trace_op fuel op lxs lys = (case op of
     End \<Rightarrow> LNil
   | Write op' p x \<Rightarrow> LCons (Inr p, Observed x) (trace_op fuel op' lxs (CTL p lys))
   | Read p f \<Rightarrow> (if fuel p > 0 \<and> produced (fuel(p := (fuel p - 1))) (f EOB) lxs lys
           then
             LCons (Inl p, EOB) (trace_op (fuel(p := (fuel p - 1))) (f EOB) lxs lys)
           else
            let n = SOME n. produced (fuel(p := n)) (f (CHD p lxs)) (CTL p lxs) lys in
            LCons (Inl p, CHD p lxs) (trace_op (fuel(p := n)) (f (CHD p lxs)) (CTL p lxs) lys)))"


lemma Inl_in_trace_op_not_Observed:
  "r \<in> lset (trace_op fuel op lxs lys) \<Longrightarrow>
   r = (Inl p, c) \<Longrightarrow>
   lxs p = LNil \<Longrightarrow>
   \<not> is_Observed c"
  apply (induct "trace_op fuel op lxs lys" arbitrary: fuel op lxs lys rule: lset_induct)
  subgoal for lxs
    apply (subst (asm) trace_op.code)
    apply (auto split: op.splits if_splits elim: produced.cases; hypsubst_thin?)
    done
  subgoal for x xs fuel op lxs lys
    apply (subst (asm) (2) trace_op.code)
    apply (auto split: op.splits if_splits elim: produced.cases; hypsubst_thin?)
       apply fastforce
      apply (metis fun_upd_apply ltl_simps(1))
    subgoal
      by (metis fun_upd_other)
    subgoal
      by (metis fun_upd_other fun_upd_same ltl_simps(1))
    done
  done

lemma *:
  "r \<in> lset (trace_op fuel op lxs lys) \<Longrightarrow>
   produced fuel op lxs lys \<Longrightarrow>
   \<exists>x. r = (Inl p', Observed x) \<Longrightarrow>
   lxs p' \<noteq> LNil \<Longrightarrow> obs (snd (lhd (ldropWhile (\<lambda>x. \<not> (case x of (q, Observed x) \<Rightarrow> Inl p' = q | _ \<Rightarrow> False)) (trace_op fuel op lxs lys)))) = lhd (lxs p')"
  apply (induct "trace_op fuel op lxs lys" arbitrary: fuel op lxs lys rule: lset_induct)
  subgoal for xs fuel op lxs lys
    apply (subst (asm) trace_op.code)
    apply (subst trace_op.code)
    apply (auto dest: sym split: op.splits if_splits observation.splits elim: produced.cases chd.elims; hypsubst_thin?)
    done
  subgoal premises prems
    using prems(1,2,4-)
    apply (subst (asm) trace_op.code)
    apply (subst trace_op.code)
    apply (auto 4 0 split: op.splits if_splits observation.splits dest: prems(3))
    apply (drule prems(3); simp)
    apply (drule prems(3); simp)
    apply (drule prems(3); simp)
    apply (drule prems(3); simp)
    apply (drule prems(3); simp)
    apply (drule prems(3); simp)
    apply (drule prems(3); simp)
    apply (drule prems(3); simp)
                        apply (drule prems(3); auto elim: someI)
                        apply (drule prems(3); auto elim: someI)
                        apply (drule prems(3); auto elim: someI)
                        apply (drule prems(3); auto elim: someI)
                        apply (drule prems(3); auto elim: someI)
                        apply (drule prems(3); auto elim: someI)
                        apply (drule prems(3); auto elim: someI)
                        apply (drule prems(3); auto elim: someI)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
    using Inl_in_trace_op_not_Observed apply fastforce
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
    using Inl_in_trace_op_not_Observed apply fastforce
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
    using Inl_in_trace_op_not_Observed apply fastforce
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
    using Inl_in_trace_op_not_Observed apply fastforce
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
                        apply (drule prems(3); auto simp: Inl_in_trace_op_not_Observed elim: someI elim!: chd.elims)
    apply (drule prems(3); simp?)
    done
  done

term loud

lemma traced_produced:
  "produced m op lxs lys \<Longrightarrow>
   \<exists> ios. traced m op ios \<and> (\<forall>p. lprefix (lmap (obs o snd) (lfilter (\<lambda>x. case x of (q, Observed x) \<Rightarrow> Inl p = q | _ \<Rightarrow> False) ios)) (lxs p)) \<and> lys = (\<lambda>p. lmap (obs o snd) (lfilter (\<lambda>x. case x of (q, Observed x) \<Rightarrow> Inl p = q | _ \<Rightarrow> False) ios))"
  apply (rule exI[of _ "trace_op m op lxs lys"])
  apply (intro conjI)
  prefer 2
  subgoal
    apply (rule allI)
    apply (coinduction arbitrary: m op lxs lys)
    subgoal for m op lxs lys p'
        apply (intro conjI impI)
      subgoal
      apply (erule produced.cases)
      subgoal for f p lxs' lys' fuel n
        apply hypsubst_thin
        apply (cases "lxs' p'")
        subgoal
          apply clarsimp
          using Inl_in_trace_op_not_Observed apply (fastforce split: observation.splits simp: is_Observed_def)
          done
        subgoal for x lxs''
          apply clarsimp
          done
        done
      subgoal
        using Inl_in_trace_op_not_Observed by (fastforce split: observation.splits simp: is_Observed_def)
      subgoal
        using Inl_in_trace_op_not_Observed by (fastforce split: observation.splits simp: is_Observed_def)
      subgoal
        using Inl_in_trace_op_not_Observed by (fastforce split: observation.splits simp: is_Observed_def)
      done
    subgoal
      apply (auto split: observation.splits dest: *)
      done
    subgoal
      apply (rule disjI1)
      apply (auto split: observation.splits)
      oops

fun bapp where
  "bapp BEmpty lxs = lxs"
| "bapp BEnded lxs = LNil"
| "bapp (BCons x xs) lxs = LCons x (bapp xs lxs)"

definition "extend A buf R lxs lys =
   (\<exists>lzs. R lxs (case_sum (lys o Inl) lzs) \<and> (\<forall>p. lys (Inr p) = (if p \<in> A then bapp (buf p) (lzs p) else lzs p)))"

lemma extend_empty: "extend {} buf R = R"
  using arg_cong2[of x x "case_sum (f o Inl) (f o Inr)" f R for x f, unfolded o_def, OF refl surjective_sum]
  by (auto simp: extend_def o_def fun_eq_iff[of "extend _ _ _"] fun_eq_iff[of "extend _ _ _ _"]
    simp flip: fun_eq_iff split: sum.splits)

definition "compose A R S lxs lys = (\<exists>lzs. R (lxs o Inl) (case_sum (lys o Inl) lzs) \<and> S (\<lambda>p. if p \<in> A then lzs p else lxs (Inr p)) (lys o Inr))"

lemma semantics_cong: "\<lbrakk>op\<rbrakk> lxs lys \<Longrightarrow>
   (\<forall>p \<in> inputs op. lxs p = lxs' p) \<Longrightarrow>
   (\<forall>p. mute p op lxs \<or> lys p = lys' p) \<Longrightarrow>
   (\<And>p. lys p = LNil \<Longrightarrow> lys' p = LNil) \<Longrightarrow> \<lbrakk>op\<rbrakk> lxs' lys'"
  unfolding semantics_def
  by (metis (no_types) produced_cong)

lemma mute_map_op': "inj_on g (inputs op) \<Longrightarrow>
  mute (h p) (map_op g h op) lxs \<Longrightarrow> (\<forall>p \<in> inputs op. lxs (g p) = lxs' p) \<Longrightarrow> mute p op lxs'"
  apply (coinduction arbitrary: op lxs lxs')
  subgoal for op lxs lxs'
    apply (cases op)
      apply (auto 0 0 simp: inj_on_def)
      apply blast
    apply (smt (verit))
    apply blast
    done
  done

lemma mute_map_op: "inj_on g (inputs op) \<Longrightarrow> mute (h p) (map_op g h op) lxs \<Longrightarrow> mute p op (lxs o g)"
  by (rule mute_map_op') auto

lemma mute_map_opI: "mute (h' p) op lxs' \<Longrightarrow>
  inj_on g (inputs op) \<Longrightarrow>
  (\<And>x. x \<in> outputs op \<Longrightarrow> h' (h x) = x) \<Longrightarrow>
  (\<forall>p \<in> inputs op. lxs' p = lxs (g p)) \<Longrightarrow> mute p (map_op g h op) lxs"
  apply (coinduction arbitrary: op lxs lxs')
  subgoal for op lxs lxs'
    apply (cases op)
      apply (auto 6 0 simp: inj_on_def fun_upd_def)
      apply (smt (verit))
      apply (smt (verit))
    done
  done

lemma mute_map_op_inj: "inj_on g (inputs op) \<Longrightarrow> inj h \<Longrightarrow> muted (map_op g h op) lxs lys \<Longrightarrow> muted op (lxs o g) (lys o h)"
  unfolding muted_def
  apply safe
  subgoal for p
    using mute_map_opI[of "inv h" "h p" op "lxs o g" g h lxs]
    by (auto dest!: spec[of _ "h p"])
  done

lemma produced_map_op: "inj_on g (inputs op) \<Longrightarrow> inj_on h (outputs op) \<Longrightarrow>
  produced m (map_op g h op) lxs lys \<Longrightarrow>
  produced (m o g) op (lxs o g) (\<lambda>q. if mute q op (lxs o g) then LNil else lys (h q))"
  apply (subgoal_tac "\<And>lxs' m'. (\<forall>p \<in> inputs op. lxs (g p) = lxs' p \<and> m (g p) = m' p) \<Longrightarrow>
       produced m' op lxs' (\<lambda>q. if mute q op lxs' then LNil else lys (h q))")
   apply (simp add: o_def)
  subgoal for lxs' m'
    apply (coinduction arbitrary: m op lxs lys lxs' m' rule: produced.coinduct)
    subgoal for m op lxs lys lxs' m'
      apply (cases op)
      subgoal for p f
        apply simp_all
        apply (erule produced_ReadE)
        subgoal for n
          apply (rule disjI1)
          apply (simp add: inj_on_def muted_def)
          apply (rule conjI allI impI)+
          subgoal for q
            apply (cases "q \<in> outputs op")
             apply (drule spec[of _ "h q"])
             apply (erule mp)
             apply (rule mute_map_opI[of "the_inv_into (outputs op) h"])
                apply (subst the_inv_into_f_f)
                  apply (simp add: inj_on_def)
                 apply assumption
                apply assumption
               apply (simp add: inj_on_def)
              apply (rule the_inv_into_f_f)
               apply (simp add: inj_on_def)
              apply auto []
             apply (metis (no_types, lifting) DiffI UNIV_I UnionI empty_iff imageI insert_iff)
            apply (meson not_loud_mute loud_in_outputs)
            done
          apply (rule exI[of _ n])
          apply (rule disjI1)
          apply (rule exI[of _ "m(g p := n)"])
          apply (rule exI disjI1)+
          apply (rule conjI[rotated])
           apply (rule conjI[rotated])
            apply (auto 0 0 simp: fun_eq_iff inj_on_def) [3]
              apply (metis UNIV_I UN_iff imageI insert_Diff_single insert_iff)
             apply (metis UNIV_I UN_iff imageI insert_Diff_single insert_iff)
            apply (metis)
           apply (metis)
          subgoal for q
            apply (cases "q \<in> outputs op")
             apply (drule spec[of _ "h q"])
             apply (erule mp)
             apply (rule mute_map_opI[of "the_inv_into (outputs op) h"])
                apply (subst the_inv_into_f_f)
                  apply (simp add: inj_on_def)
                 apply assumption
                apply assumption
               apply (simp add: inj_on_def)
              apply (rule the_inv_into_f_f)
               apply (simp add: inj_on_def)
              apply auto []
             apply (metis (no_types, lifting) DiffI UNIV_I UnionI empty_iff imageI insert_iff)
            apply (meson not_loud_mute loud_in_outputs)
            done
          done
        subgoal for n
          apply (simp add: muted_def)
          unfolding o_apply
          apply (rule disjI2)
          apply (rule conjI allI impI)+
          subgoal for q
            apply (cases "q \<in> outputs op")
             apply (drule spec[of _ "h q"])
             apply (erule mp)
             apply (rule mute_map_opI[of "the_inv_into (outputs op) h"])
                apply (subst the_inv_into_f_f)
                  apply (simp add: inj_on_def)
                 apply assumption
                apply assumption
               apply (simp add: inj_on_def)
              apply (rule the_inv_into_f_f)
               apply (simp add: inj_on_def)
              apply auto []
             apply (metis)
            apply (meson not_loud_mute loud_in_outputs)
            done
          apply (rule exI[of _ n])
          apply (simp add: inj_on_def)
          apply (rule disjI1)
          apply (rule exI)+
          apply (rule conjI[rotated])
           apply (rule conjI[rotated])
            apply (auto 0 0 simp: fun_eq_iff inj_on_def) [3]
              apply (metis)
             apply (metis UNIV_I UN_iff imageI insert_Diff_single insert_iff)
            apply (metis)
           apply (metis)
          subgoal for q
            apply (cases "q \<in> outputs op")
             apply (drule spec[of _ "h q"])
             apply (erule mp)
             apply (rule mute_map_opI[of "the_inv_into (outputs op) h"])
                apply (subst the_inv_into_f_f)
                  apply (simp add: inj_on_def)
                 apply assumption
                apply assumption
               apply (simp add: inj_on_def)
              apply (rule the_inv_into_f_f)
               apply (simp add: inj_on_def)
              apply auto []
             apply (metis)
            apply (meson not_loud_mute loud_in_outputs)
            done
          done
        done
      subgoal for op' p x
        apply (auto 0 0 simp: muted_def)
        subgoal premises prems for lzs
          using prems
          apply -
          apply (rule exI[where x="\<lambda>q. if mute q op lxs' then LNil else lzs (h q)"] conjI[rotated] exI disjI1)+
              prefer 2
              apply assumption
             apply (auto 2 0 simp: fun_eq_iff inj_on_def)
          subgoal for q
            apply (cases "q \<in> outputs op")
             apply (drule spec[of _ "h q"])
             apply (erule mp)
             apply (rule mute_map_opI[of "the_inv_into (outputs op) h"])
                apply (subst the_inv_into_f_f)
                  apply (simp add: inj_on_def)
                  apply (metis Diff_empty Diff_insert0 image_iff)
                 apply assumption
                apply assumption
               apply (simp add: inj_on_def)
              apply (rule the_inv_into_f_f)
               apply (simp add: inj_on_def)
               apply (metis Diff_empty Diff_insert0 image_iff)
              apply auto []
             apply (metis)
            apply (meson not_loud_mute loud_in_outputs)
            done
          subgoal for q
            apply (cases "q \<in> outputs op")
             apply (drule spec[of _ "h q"])
             apply (erule mp)
             apply (rule mute_map_opI[of "the_inv_into (outputs op) h"])
                apply (subst the_inv_into_f_f)
                  apply (simp add: inj_on_def)
                  apply (metis Diff_empty Diff_insert0 image_iff)
                 apply assumption
                apply assumption
               apply (simp add: inj_on_def)
              apply (rule the_inv_into_f_f)
               apply (simp add: inj_on_def)
               apply (metis Diff_empty Diff_insert0 image_iff)
              apply auto []
             apply (metis)
            apply (meson not_loud_mute loud_in_outputs)
            done
          apply (metis Diff_empty Diff_insert0 image_iff not_loud_mute mute.Write loud_in_outputs)
          done
        done
      subgoal
        apply auto
        done
      done
    done
  done

lemma semantics_map_op:
  "inj_on g (inputs op) \<Longrightarrow>
   inj_on h (outputs op) \<Longrightarrow>
   semantics (map_op g h op) lxs lys \<Longrightarrow> semantics op (lxs o g) (\<lambda>q. if mute q op (lxs o g) then LNil else lys (h q))"
  unfolding semantics_def
  apply (erule exE)
  apply (rule exI)
  apply (erule (2) produced_map_op[rotated 2])
  done

lemma semantics_map_op_inj:
  "inj_on g (inputs op) \<Longrightarrow>
   inj h \<Longrightarrow>
   semantics (map_op g h op) \<le> BNF_Def.vimage2p (\<lambda> lxs. lxs o g) (\<lambda>lys. lys o h) (semantics op)"
  unfolding vimage2p_def semantics_def
  apply (rule predicate2I)
  apply (erule exE)
  subgoal for lxs lys m
    apply (rule exI[of _ "m o g"])
    apply (subgoal_tac "\<And>lxs' m'. (\<forall>p \<in> inputs op. lxs (g p) = lxs' p \<and> m (g p) = m' p) \<Longrightarrow> produced m' op lxs' (lys o h)")
     apply (simp add: o_def)
    subgoal for lxs' m'
      apply (coinduction arbitrary: m op lxs lys lxs' m' rule: produced.coinduct)
      subgoal for m op lxs lys lxs' m'
        apply (cases op)
        subgoal for p f
          apply simp_all
          apply (erule produced_ReadE)
          subgoal for n
            unfolding o_apply
            apply (rule disjI1)
            apply (rule conjI)
             apply (drule mute_map_op_inj[rotated 2])
               apply (simp add: inj_on_def)
              apply assumption
             apply simp
             apply (erule muted_cong)
              apply (metis UNIV_I UN_iff comp_apply fun_upd_other fun_upd_same image_iff member_remove remove_def)
            apply simp
            apply (rule exI[of _ n])
            apply (rule disjI1)
            apply (rule exI[of _ "m(g p := n)"])
            apply (rule exI disjI1)+
            apply (rule conjI[rotated])
             apply (rule conjI[rotated])
              apply (auto 0 0 simp: fun_eq_iff inj_on_def) [3]
               apply (metis UNIV_I UN_iff imageI insert_Diff_single insert_iff)
              apply (metis UNIV_I UN_iff imageI insert_Diff_single insert_iff)
             apply (metis)
            apply (metis)
            done
          subgoal for n
            unfolding o_apply
            apply (rule disjI2)
            apply (rule conjI)
             apply (drule mute_map_op_inj[rotated 2])
               apply (simp add: inj_on_def)
              apply assumption
             apply simp
             apply (erule muted_cong)
              apply (metis comp_apply)
             apply simp
            apply (rule exI[of _ n])
            apply (simp add: inj_on_def)
            apply (rule disjI1)
            apply (rule exI)+
            apply (rule conjI[rotated])
             apply (rule conjI[rotated])
              apply (auto 0 0 simp: fun_eq_iff inj_on_def) [3]
               apply (metis)
              apply (metis UNIV_I UN_iff imageI insert_Diff_single insert_iff)
             apply (metis)
            apply (metis)
            done
          done
        subgoal for op' p x
          apply simp
          apply (erule produced_WriteE)
          apply simp
          subgoal premises prems for lzs
            using prems
            apply -
            apply (rule exI[where x="lzs o h"] conjI[rotated] exI disjI1)+
                prefer 2
                apply assumption
               apply (auto simp: fun_eq_iff inj_on_def dest!: mute_map_op_inj[rotated 2]
                elim: muted_cong)
            done
          done
        subgoal
          apply auto
          done
        done
      done
    done
  done

definition "lift A lxs lys p = (if p \<in> A then lxs p else lys p)"
lemma semantics_loop_op:
 "semantics (loop_op wire buf op) lxs lys \<Longrightarrow>
  \<exists>lzs. extend (ran wire) buf (semantics (map_op id (\<lambda>p. case wire p of Some q \<Rightarrow> Inr q | _ \<Rightarrow> Inl p) op))
     (lift (ran wire) lzs lxs) (case_sum lys lzs)"
  sorry

lemma semantics_loop_op_BEmpty:
 "semantics (loop_op wire (\<lambda>p. BEmpty) op) lxs lys \<Longrightarrow>
  \<exists>lzs. semantics (map_op id (\<lambda>p. case wire p of Some q \<Rightarrow> Inr q | _ \<Rightarrow> Inl p) op)
     (lift (ran wire) lzs lxs) (case_sum lys lzs)"
  apply (drule semantics_loop_op)
  apply (auto simp: extend_def o_def simp flip: fun_eq_iff cong: if_cong)
  done

lemma loop_producing_Some: "loop_producing wire buf op n \<Longrightarrow> wire = Some \<Longrightarrow> loop_op wire buf op = End"
  apply (induct buf op n rule: loop_producing.induct)
      apply (auto simp: ran_def)
  done

lemma loop_op_Some: "loop_op Some buf op = End"
  apply (coinduction arbitrary: buf op)
  apply auto
  subgoal for buf op
    apply (subst (asm) loop_op.code)
    apply (auto simp: ran_def dest: loop_producing_Some split: op.splits if_splits)
    done
  subgoal for buf op
    apply (subst (asm) loop_op.code)
    apply (auto simp: ran_def dest: loop_producing_Some split: op.splits if_splits)
    done
  done

lemma semantics_comp_op:
 "semantics (comp_op wire buf op1 op2) \<le>
  compose (ran wire) (extend (ran wire) buf (semantics (map_op id (\<lambda>p. case wire p of Some q \<Rightarrow> Inr q | _ \<Rightarrow> Inl p) op1)))
          (semantics op2)"
  unfolding compose_def extend_def
  apply (rule predicate2I)
   apply auto
  sorry

inductive input_at where
  "input_at p (Read p f) n"
| "p \<noteq> p' \<Longrightarrow> input_at p (f x) n \<Longrightarrow> input_at p (Read p' f) (Suc n)"
| "input_at p op' n \<Longrightarrow> input_at p (Write op' p' x) (Suc n)"

lemma inputs_input_at: "p \<in> inputs op \<Longrightarrow> \<exists>n. input_at p op n"
  by (induct p op rule: op.set_induct(1)) (auto intro: input_at.intros)

lemma input_at_inputs: "input_at p op n \<Longrightarrow> p \<in> inputs op"
  by (induct p op n rule: input_at.induct) auto

lemma inputs_alt: "p \<in> inputs op \<longleftrightarrow> (\<exists>n. input_at p op n)"
  by (metis input_at_inputs inputs_input_at)

definition "input_depth p op = (LEAST n. input_at p op n)"

lemma input_depth_Read: "p \<in> inputs op \<Longrightarrow> input_depth p op = 0 \<longleftrightarrow> (\<exists>f. op = Read p f)"
  unfolding input_depth_def
  apply (cases op)
  apply (auto intro: input_at.intros Least_eq_0)
  apply (metis LeastI_ex Zero_not_Suc input_at.simps inputs_input_at op.inject(1))
  apply (metis input_at.simps inputs_input_at op.simps(4) wellorder_Least_lemma(1) zero_less_Suc)
  done

lemma input_depth_Write[simp]:
  "p \<in> inputs op' \<Longrightarrow> input_depth p (Write op' p' x) = Suc (input_depth p op')"
  unfolding input_depth_def
  apply (drule inputs_input_at)
  apply (erule exE)
  apply (rule Least_Suc2)
     apply (auto elim: input_at.cases intro: input_at.intros)
  done

lemma input_at_mono: "input_at p op n \<Longrightarrow> n \<le> m \<Longrightarrow> input_at p op m"
  by (induct p op n arbitrary: m rule: input_at.induct)
    (auto intro: input_at.intros simp: less_eq_nat.simps split: nat.splits)

lemma input_depth_Read_diff: 
  "p \<noteq> p' \<Longrightarrow> \<exists>x. p \<in> inputs (f x) \<Longrightarrow>
   input_depth p (Read p' f) = Suc (input_depth p (f (arg_min (input_depth p o f) (\<lambda>x. p \<in> inputs (f x)))))"
  unfolding input_depth_def inputs_alt
  apply (erule exE)
  apply (frule arg_min_natI[of "\<lambda>x. \<exists>n. input_at p (f x) n" _ "input_depth p o f"])
  unfolding input_depth_def
  apply (erule exE)+
  apply (rule Least_Suc2)
     apply (erule input_at.intros)
     apply assumption
    apply assumption
   apply (auto elim: input_at.cases intro: input_at.intros)
  apply (erule input_at.cases[of _ "Read p' f"])
    apply auto
  apply (smt (verit, del_insts) LeastI Least_le arg_min_nat_le comp_eq_dest_lhs input_at_mono)
  done

lemma input_depth_arg_min_le[simp]:
  "p \<in> inputs (f x) \<Longrightarrow>
   input_depth p (f (ARG_MIN (input_depth p o f) x. p \<in> inputs (f x))) \<le> input_depth p (f x)"
  by (metis arg_min_nat_le comp_apply)

lemma inputs_comp_op_arg_min_1[simp]:
  "p \<in> inputs (comp_op wire buf (f1 x) op) \<Longrightarrow>
   p \<in> inputs (comp_op wire buf (f1 (ARG_MIN (m :: _ \<Rightarrow> nat) x. p \<in> inputs (comp_op wire buf (f1 x) op))) op)"
  by (rule arg_min_natI)

lemma inputs_comp_op_arg_min_2[simp]:
  "p \<in> inputs (comp_op wire buf op (f2 y)) \<Longrightarrow>
   p \<in> inputs (comp_op wire buf op (f2 (ARG_MIN (m :: _ \<Rightarrow> nat) y. p \<in> inputs (comp_op wire buf op (f2 y)))))"
  by (rule arg_min_natI)

lemma inputs_comp_op_arg_min_3[simp]:
  "p \<in> inputs (comp_op wire buf (f1 x) (f2 y)) \<Longrightarrow>
   p \<in> inputs
         (comp_op wire buf
            (f1 (ARG_MIN (m1 :: _ \<Rightarrow> nat) x. (\<exists>xa. p \<in> inputs (comp_op wire buf (f1 x) (f2 xa)))))
            (f2 (ARG_MIN (m2 :: _ \<Rightarrow> nat) x. p \<in> inputs (comp_op wire buf
                            (f1 (ARG_MIN (m1 :: _ \<Rightarrow> nat) x. (\<exists>xa. p \<in> inputs (comp_op wire buf (f1 x) (f2 xa))))) (f2 x)))))"
  by (smt (verit, best) arg_min_natI)

lemma input_depth_Read_diff'[simp]: 
  "p \<noteq> p' \<Longrightarrow> p \<in> inputs (f x) \<Longrightarrow>
   input_depth p (Read p' f) = Suc (input_depth p (f (arg_min (input_depth p o f) (\<lambda>x. p \<in> inputs (f x)))))"
  by (metis input_depth_Read_diff)

lemma inputs_comp_producing:
  "p \<in> inputs (comp_op wire buf op1 op2) \<Longrightarrow> 
   \<exists> n. comp_producing wire buf op1 op2 n"
  using not_comp_producing_eq_End by fastforce

lemma not_comp_producing_no_inputs:
  "\<forall>x. \<not> comp_producing wire buf op1 op2 x \<Longrightarrow>
   inputs (comp_op wire buf op1 op2) = {}"
  by (simp add: not_comp_producing_eq_End)

lemma inputs_comp_op_1:
  "p \<in> inputs op1 \<Longrightarrow>
   Inl p \<in> inputs (comp_op wire buf op1 op2)"
  apply (induct p op1 arbitrary: buf op2 rule: op.set_induct(1))
  subgoal for z1 z2 buf op2
    apply (cases op2)
      apply auto
    done
  subgoal for z1 z2 xa xb buf op2
    apply (cases op2)
      apply auto
    done
  subgoal for z1a z2a z3 xd buf op2
    apply (cases op2)
      apply (auto split: option.splits)
     defer
    subgoal
      by (metis all_not_in_conv comp_producing.intros(4) not_comp_producing_eq_End op.simps(37))
    subgoal for x11 x12 x2
      by (meson comp_producing.intros(12) inputs_comp_producing)
    done
  done

lemma
  "p \<in> inputs op2 - ran wire \<Longrightarrow>
   Inr p \<in> inputs (comp_op wire buf op1 op2)"
  oops

lemma input_depth_Read_diff_le[simp]: 
  "p \<noteq> p' \<Longrightarrow> \<exists>x. p \<in> inputs (f x) \<Longrightarrow>
   (input_depth p (f (arg_min (input_depth p o f) (\<lambda>x. p \<in> inputs (f x))))) \<le> input_depth p (Read p' f)"
  by force

lemma comp_op_Read_simps_case:
  "comp_op wire buf (Read p f) op2 =
   Read (Inl p) (\<lambda> x. case op2 of
     End \<Rightarrow> comp_op wire buf (f x) End
   | Write op' p' y \<Rightarrow> Write (comp_op wire buf (f x) op') (Inr p') y
   | Read p' f' \<Rightarrow> (if p' \<in> ran wire then comp_op wire (buf(p' := btl (buf p'))) (f x) (f' (BHD p' buf)) else (Read (Inr p') (\<lambda>y2. comp_op wire buf (f x) (f' y2)))))"
  apply (cases op2)
    apply auto
  done

lemma input_depth_Read_0[simp]:
  "input_depth p (Read p f) = 0"
  by (simp add: input_depth_Read)

lemma input_depth_Suc_diff[simp]:
  "input_depth p (comp_op wire buf op1 op2) = Suc n \<Longrightarrow>
   op1 = Read p' f \<Longrightarrow>
   Inl p' \<noteq> p"
  by (metis (no_types, lifting) Zero_neq_Suc comp_op_Read_simps_case input_depth_Read_0)

lemma input_depth_Read_Write[simp]:
  "p \<in> inputs (comp_op wire buf (Read p1 f1) (Write op' p' x)) \<Longrightarrow>
   p \<noteq> Inl p1 \<Longrightarrow>
   input_depth p (comp_op wire buf (Read p1 f1) (Write op' p' x)) = 
   Suc (Suc (input_depth p (comp_op wire buf (f1 (ARG_MIN (input_depth p \<circ> (\<lambda>y1. Write (comp_op wire buf (f1 y1) op') (Inr p') x)) x. p \<in> inputs (comp_op wire buf (f1 x) op'))) op')))"
  apply simp
  apply (subst input_depth_Read_diff)
    apply fast
   apply force
  apply (subst input_depth_Write)
   apply force
  apply auto
  done

lemma comp_producing_inputs_comp_op:
  fixes op1 :: "('ip1, 'op1, 'd) op" and op2 :: "('ip2, 'op2, 'd) op"
  shows "comp_producing wire buf op1 op2 i \<Longrightarrow>
    p \<in> inputs (comp_op wire buf op1 op2) \<Longrightarrow>
    input_depth p (comp_op wire buf op1 op2) = Suc n \<Longrightarrow>
    (\<And>buf (op1 :: ('ip1, 'op1, 'd) op) (op2 :: ('ip2, 'op2, 'd) op).
        input_depth p (comp_op wire buf op1 op2) \<le> n \<Longrightarrow>
        p \<in> inputs (comp_op wire buf op1 op2) \<Longrightarrow>
        p \<in> Inl ` inputs op1 \<union> Inr ` (inputs op2 - ran wire)) \<Longrightarrow>
    p \<in> Inl ` inputs op1 \<union> Inr ` (inputs op2 - ran wire)"
  apply (induct buf op1 op2 i rule: comp_producing.induct)
             apply (auto 7 7 intro: le_SucI split: if_splits option.splits)
          apply (fastforce intro!: le_SucI)+
  subgoal
    apply (rule ccontr)
    apply (subst (asm) input_depth_Read_diff)
      apply fastforce+
    done
  subgoal
    apply fastforce+
    done
  subgoal for buf p1 f1 p2 f2 x y
    apply (subst (asm) input_depth_Read_diff)
      apply auto
    apply (subst (asm) (1 2) input_depth_Read_diff)
        apply auto
      apply (smt (verit, del_insts) DiffI arg_min_natI image_iff insert_iff)
     apply (smt (verit, del_insts) DiffI arg_min_natI image_iff insert_iff)
    apply hypsubst_thin
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule le_SucI)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply (smt (verit, del_insts) Diff_iff arg_min_natI image_iff insertI1)
    apply auto
    done
  subgoal
    by (force intro!: le_SucI)
  subgoal
    by (force intro!: le_SucI)
  done

lemma inputs_comp_op: "p \<in> inputs (comp_op wire buf op1 op2) \<Longrightarrow> p \<in> Inl ` inputs op1 \<union> Inr ` (inputs op2 - ran wire)"
  apply (induct "input_depth p (comp_op wire buf op1 op2)" arbitrary: buf op1 op2 rule: less_induct)
  subgoal for buf op1 op2
    apply (cases "input_depth p (comp_op wire buf op1 op2)")
    subgoal
      apply simp
      apply (simp add: input_depth_Read)
      apply auto
      apply (cases "\<exists>n. comp_producing wire buf op1 op2 n"; (simp add: not_comp_producing_eq_End)?)
      apply (erule exE)+
      subgoal premises prems for f n
        using prems(3,1-2)
        apply (induct buf op1 op2 n arbitrary: p f rule: comp_producing.induct)
                   apply (auto split: if_splits option.splits)
        done
      done
    subgoal premises prems for n
      unfolding less_Suc_eq_le apply -
      using prems(2-) apply -
      apply (cases op1)
        apply (auto split: if_splits option.splits simp: input_depth_Read_diff)
      subgoal for p1 f1 
        apply (cases op2)
        subgoal for p1' f1'
          apply (auto split: if_splits option.splits simp: input_depth_Read_diff)
          subgoal 
            apply (rule ccontr)
            apply (insert prems(1))
            apply force
            done
          subgoal for y z
            using prems(1) apply -
            apply hypsubst_thin
            apply (rule ccontr)
            apply simp
            apply (subst (asm) input_depth_Read_diff)
              apply fast
             apply auto
            apply (subst (asm) input_depth_Read_diff)
              apply blast
             apply (smt (verit, ccfv_threshold) Diff_iff arg_min_natI image_iff insertI1)
            apply auto
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule le_SucI)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply force+
            done
          done
        subgoal for op' p' x
          using prems(1)
          apply(force intro: le_SucI simp add: less_Suc_eq_le)
          done
        subgoal
          apply (drule sym)
          apply (insert prems(1))
          apply hypsubst
          apply simp
          apply (subst (asm) (2) input_depth_Read_diff)
            apply fast
           apply force
          apply simp
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (subst less_Suc_eq_le)
           apply (rule order_refl)
          apply (drule meta_mp)
           apply (auto simp add: image_iff)
          done
        done
      subgoal prem for op' p' x
        apply (insert prems(1))
        apply hypsubst_thin
        apply (cases op2)
        subgoal
          apply (drule sym)
          apply hypsubst
          apply (auto split: if_splits option.splits)
          subgoal
            by fastforce
          subgoal
            apply (subst (asm) if_P)
             apply fast
            apply simp
            apply (drule comp_producing_inject, assumption)
            apply hypsubst_thin
            apply (rotate_tac 5)
            apply (drule sym)
            apply (erule comp_producing.cases)
                       apply simp_all
            apply (drule comp_producing_inputs_comp_op)
               apply assumption+
             apply (meson UnCI le_imp_less_Suc)
            apply blast
            done
          subgoal
            apply (subst (asm) if_P)
             apply fast
            apply simp
            apply (drule comp_producing_inject, assumption)
            apply hypsubst_thin
            apply (rotate_tac 5)
            apply (drule sym)
            apply (erule comp_producing.cases)
                       apply simp_all
            apply (drule comp_producing_inputs_comp_op)
               apply assumption+
             apply (meson UnCI le_imp_less_Suc)
            apply blast
            done
          subgoal
            apply (subst (asm) (1) input_depth_Read_diff)
              apply blast+
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule le_SucI)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply simp
            apply blast
            done
          subgoal
            by force
          done
        subgoal
          by (smt (verit) UnE comp_producing_inputs_comp_op inputs_comp_producing le_imp_less_Suc op.simps(36))
        subgoal
          apply (auto split: option.splits)
           apply fastforce
          apply (smt (z3) UnE UnI1 UnI2 all_not_in_conv comp_producing_inputs_comp_op empty_Diff image_empty inputs_comp_producing le_imp_less_Suc op.simps(37))
          done
        done
      subgoal
        using prems(1) by (metis UnE comp_producing_inputs_comp_op equals0D image_empty inputs_comp_producing less_Suc_eq_le op.simps(37))
      done
    done
  done

lemma comp_producing_cleanedD: "comp_producing wire buf op1 op2 n \<Longrightarrow>
  cleaned op1 \<Longrightarrow>
  cleaned op2 \<Longrightarrow>
  comp_op wire buf op1 op2 = End \<or>
  (\<exists>op' q x. comp_op wire buf op1 op2 = Write op' q x \<and> 
    cleaned_cong (\<lambda>op. \<exists>buf op1 op2. op = comp_op wire buf op1 op2 \<and> cleaned op1 \<and> cleaned op2) op') \<or>
  (\<exists>f p. comp_op wire buf op1 op2 = Read p f \<and> p \<notin> inputs (f EOS) \<and>
   (\<forall>x. cleaned_cong (\<lambda>op. \<exists>buf op1 op2. op = comp_op wire buf op1 op2 \<and> cleaned op1 \<and> cleaned op2) (f x)))"
  by (induct buf op1 op2 n pred: comp_producing)
    (auto 6 0 split: option.splits intro: cc_base intro!: cc_write cc_read dest!: inputs_comp_op)+
    

lemma cleaned_comp_op: "cleaned op1 \<Longrightarrow> cleaned op2 \<Longrightarrow> cleaned (comp_op wire buf op1 op2)"
  apply (coinduction arbitrary: buf op1 op2 rule: cleaned_coinduct_upto)
  subgoal for buf op1 op2
    apply (cases op1; cases op2)
            apply (auto dest!: inputs_comp_op split: option.splits)
                        apply (rule cc_base, (rule exI conjI refl)+; simp)
                       apply (rule cc_read, blast dest!: inputs_comp_op, rule cc_base, (rule exI conjI refl)+; simp)
                      apply (rule cc_write, rule cc_base, (rule exI conjI refl)+; simp)
                     apply (rule cc_base, (rule exI conjI refl)+; simp)
                    apply (rule cc_base, (rule exI conjI refl)+; simp)
                   apply (rule cc_read, blast dest!: inputs_comp_op, rule cc_base, (rule exI conjI refl)+; simp)
    subgoal for op' q x f p n
      by (frule comp_producing_cleanedD) (auto intro: cleaned.intros(1,2) split: if_splits)
                 apply (rule cc_base, (rule exI conjI refl)+; simp)
                apply (rule cc_base, (rule exI conjI refl)+; simp)
    subgoal for op' q x p f p' n 
      by (frule comp_producing_cleanedD) (auto intro: cleaned.intros(1,2) split: if_splits)
              apply (rule cc_base, (rule exI conjI refl)+; simp)
             apply (rule cc_base, (rule exI conjI refl)+; simp)
            apply (rule cc_write, rule cc_base, (rule exI conjI refl)+; simp)
           apply (rule cc_base, (rule exI conjI refl)+; simp)
          apply (rule cc_base, (rule exI conjI refl)+; simp)
         apply (rule cc_base, (rule exI conjI refl)+; simp)
    subgoal for op' q x p' n 
      by (frule comp_producing_cleanedD) (auto intro: cleaned.intros(1,2) split: if_splits)
    subgoal for p f n 
      by (frule comp_producing_cleanedD) (auto intro: cleaned.intros(1,2) split: if_splits)
      apply (rule cc_base, (rule exI conjI refl)+; simp)
     apply (rule cc_base, (rule exI conjI refl)+; simp)
    apply (rule cc_base, (rule exI conjI refl)+; simp)
    done
  done

lemma inputs_comp_op_le:
  "inputs (comp_op wire buf op1 op2) \<subseteq> Inl ` inputs op1 \<union> Inr ` (inputs op2 - ran wire)"
  using inputs_comp_op by blast

inductive output_at where
  "output_at p (Write op' p x) n"
| "p \<noteq> p' \<Longrightarrow> output_at p op' n \<Longrightarrow> output_at p (Write op' p' x) (Suc n)"
| "output_at p op' n \<Longrightarrow> op' \<in> range f \<Longrightarrow> output_at p (Read p' f) (Suc n)"

lemma outputs_output_at: "p \<in> outputs op \<Longrightarrow> \<exists>n. output_at p op n"
  by (induct p op rule: op.set_induct(2)) (auto intro: output_at.intros)

lemma output_at_outputs: "output_at p op n \<Longrightarrow> p \<in> outputs op"
  by (induct p op n rule: output_at.induct) auto

lemma outputs_alt: "p \<in> outputs op \<longleftrightarrow> (\<exists>n. output_at p op n)"
  by (metis output_at_outputs outputs_output_at)

definition "output_depth p op = (LEAST n. output_at p op n)"

lemma output_depth_Write_simp_eq[simp]:
  "output_depth p (Write op p x) = 0"
  by (simp add: output_depth_def output_at.intros(1))

lemma input_depth_Write_0: 
  "p \<in> outputs op \<Longrightarrow>
   output_depth p op = 0 \<longleftrightarrow> (\<exists>x op'. op = Write op' p x)"
  unfolding output_depth_def
  apply (auto elim: output_at.cases intro: output_at.intros)
   apply (metis LeastI_ex Zero_neq_Suc output_at.cases outputs_alt)
  apply (simp add: output_at.intros(1))
  done

lemma output_at_mono: "output_at p op n \<Longrightarrow> n \<le> m \<Longrightarrow> output_at p op m"
  by (induct p op n arbitrary: m rule: output_at.induct)
    (auto intro: output_at.intros simp: less_eq_nat.simps split: nat.splits)

lemma output_depth_Read[simp]:
  "\<exists>x. p \<in> outputs (f x) \<Longrightarrow>
   output_depth p (Read p' f) = Suc (output_depth p (f (arg_min (output_depth p o f) (\<lambda>x. p \<in> outputs (f x)))))"
  unfolding output_depth_def outputs_alt
  apply (erule exE)
  subgoal for  d
    apply (frule arg_min_natI[of "\<lambda>x. \<exists>n. output_at p (f x) n" _ "output_depth p o f"])
    unfolding output_depth_def
    apply (erule exE)+
    apply (rule Least_Suc2)
       apply (erule output_at.intros)
       apply simp_all
     apply (meson Zero_neq_Suc op.distinct(1) output_at.cases)
    apply (auto elim: output_at.cases intro: output_at.intros)
    apply (erule output_at.cases[of _ "Read p' f"])
      apply auto
    using output_at_mono 
    apply (smt (verit, ccfv_SIG) LeastI Least_le arg_min_nat_le comp_eq_dest_lhs)
    done
  done

lemma output_depth_Write_simp_diff[simp]:
  "\<exists>x. p \<in> outputs op \<Longrightarrow>
   p \<noteq> p' \<Longrightarrow>
   output_depth p (Write op p' x) = Suc (output_depth p op)"
 unfolding output_depth_def outputs_alt
  apply (elim exE)
  subgoal for x n
    apply (rule Least_Suc2[where n="Suc n"])
    defer
       apply assumption
    using output_at.cases apply force
    apply (smt (verit, ccfv_threshold) diff_Suc_1 op.distinct(1) op.inject(2) output_at.cases output_at.intros(2))
    apply (auto intro: output_at.intros)
    done
  done

lemma outputs_comp_op_arg_min_1[simp]:
  "p \<in> outputs (comp_op wire buf (f1 x) op) \<Longrightarrow>
   p \<in> outputs (comp_op wire buf (f1 (ARG_MIN (m :: _ \<Rightarrow> nat) x. p \<in> outputs (comp_op wire buf (f1 x) op))) op)"
  by (rule arg_min_natI)

lemma outputs_comp_op_arg_min_2[simp]:
  "p \<in> outputs (comp_op wire buf op (f2 y)) \<Longrightarrow>
   p \<in> outputs (comp_op wire buf op (f2 (ARG_MIN (m :: _ \<Rightarrow> nat) y. p \<in> outputs (comp_op wire buf op (f2 y)))))"
  by (rule arg_min_natI)

lemma outputs_comp_op_arg_min_3[simp]:
  "p \<in> outputs (comp_op wire buf (f1 x) (f2 y)) \<Longrightarrow>
   p \<in> outputs
         (comp_op wire buf
            (f1 (ARG_MIN (m1 :: _ \<Rightarrow> nat) x. (\<exists>xa. p \<in> outputs (comp_op wire buf (f1 x) (f2 xa)))))
            (f2 (ARG_MIN (m2 :: _ \<Rightarrow> nat) x. p \<in> outputs (comp_op wire buf
                            (f1 (ARG_MIN (m1 :: _ \<Rightarrow> nat) x. (\<exists>xa. p \<in> outputs (comp_op wire buf (f1 x) (f2 xa))))) (f2 x)))))"
  by (smt (verit, best) arg_min_natI)

lemma comp_producing_outputs_comp_op:
  fixes op1 :: "('ip1, 'op1, 'd) op" and op2 :: "('ip2, 'op2, 'd) op"
  shows "comp_producing wire buf op1 op2 i \<Longrightarrow>
    p \<in> outputs (comp_op wire buf op1 op2) \<Longrightarrow>
    output_depth p (comp_op wire buf op1 op2) = Suc n \<Longrightarrow>
    (\<And>buf (op1 :: ('ip1, 'op1, 'd) op) (op2 :: ('ip2, 'op2, 'd) op).
        output_depth p (comp_op wire buf op1 op2) \<le> n \<Longrightarrow>
        p \<in> outputs (comp_op wire buf op1 op2) \<Longrightarrow>
         p \<in> Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2) \<Longrightarrow>
     p \<in> Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2"
  apply (induct buf op1 op2 i rule: comp_producing.induct)
             apply (auto 7 7 intro: le_SucI split: if_splits option.splits)
  subgoal
    apply (rule ccontr)
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
    done
  subgoal
    apply (rule ccontr)      
    apply (subst (asm) output_depth_Write_simp_diff)
      apply simp
     apply blast
    apply simp
    apply hypsubst
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
    done
  subgoal
    apply (rule ccontr)      
    apply (subst (asm) output_depth_Write_simp_diff)
      apply simp
     apply blast
    apply simp
    apply hypsubst
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
    done
  subgoal
    apply (rule ccontr) 
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule le_SucI)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
    apply blast
    done
  subgoal
    apply (rule ccontr)      
    apply (subst (asm) output_depth_Write_simp_diff)
      apply simp
     apply blast
    apply simp
    apply hypsubst
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule le_SucI)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
    done
  subgoal
    by blast
  subgoal
    by fastforce
  subgoal
    apply (rule ccontr) 
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
    apply blast
    done
  subgoal
    apply (subst (asm) (1 2) output_depth_Read)
      apply (smt (verit) arg_min_natI)
     apply (smt (verit) arg_min_natI)
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule le_SucI)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
     apply blast+
    done
  subgoal
    apply (rule ccontr)      
    apply (subst (asm) output_depth_Write_simp_diff)
      apply simp
     apply blast
    apply simp
    apply hypsubst
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule order_refl)
    apply (drule meta_mp)
     apply force
    apply auto
    done
  subgoal
    apply (rule ccontr)      
    apply (subst (asm) output_depth_Write_simp_diff)
      apply simp
      apply blast
     apply blast
    apply simp
    apply (subst (asm)  output_depth_Read)
     apply (smt (verit) arg_min_natI)
    apply (drule sym[of _ n])
    apply simp
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply (rule le_SucI)
     apply (rule order_refl)
    apply auto
    done
  subgoal
    by (smt (z3) UN_I arg_min_natI domI dom_const dual_order.refl imageE image_eqI insert_Diff1)
  done

lemma outputs_comp_op: 
  "p \<in> outputs (comp_op wire buf op1 op2) \<Longrightarrow>
   p \<in> Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2"
  apply (induct "output_depth p (comp_op wire buf op1 op2)" arbitrary: buf op1 op2 rule: less_induct)
  subgoal for buf op1 op2
    apply (cases "output_depth p (comp_op wire buf op1 op2)")
    subgoal
      apply (simp add: input_depth_Write_0)
      apply auto
      apply (cases "\<exists>n. comp_producing wire buf op1 op2 n"; (simp add: not_comp_producing_eq_End)?)
      apply (erule exE)+
      subgoal premises prems for x op' n
        using prems(3,1-2)
        apply (induct buf op1 op2 n arbitrary: p x op' rule: comp_producing.induct)
                   apply (auto split: if_splits option.splits)
        done
      done
    subgoal premises prems for n
      using prems(2-) apply -
      apply (cases op1)
        apply (auto split: if_splits option.splits simp: input_depth_Read_diff)
      subgoal for p1 f1 
        apply (cases op2)
        subgoal for p1' f1'
          apply (auto split: if_splits option.splits)
          subgoal 
            apply (rule ccontr)
            apply (insert prems(1))
            apply simp
            apply (subst (asm) output_depth_Read)
             apply fast
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply (meson arg_min_natI)
            apply blast
            done
          subgoal 
            apply (rule ccontr)
            apply (insert prems(1))
            apply simp
            apply (subst (asm) (2) output_depth_Read)
             apply simp
             apply blast
            apply (subst (asm) (2) output_depth_Read)
             apply simp
             apply (smt (verit, ccfv_SIG) arg_min_natI)
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule le_SucI)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply simp
            apply blast
            done
          done
        subgoal for op' p' x
          apply (auto split: if_splits option.splits)
          apply (insert prems(1))
          apply simp
          apply (rule ccontr)
          apply (subst (asm) output_depth_Read)
           apply simp
           apply blast
          apply (subst (asm) output_depth_Write_simp_diff)
            apply simp
           apply (smt (verit, ccfv_SIG) arg_min_natI)
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (subst less_Suc_eq_le)
           apply (rule le_SucI)
           apply (rule order_refl)
          apply (drule meta_mp)
           apply simp
          apply blast
          done
        subgoal
          apply (auto split: if_splits option.splits)
          apply (insert prems(1))
          apply simp
          apply (rule ccontr)
          apply (subst (asm) output_depth_Read)
           apply blast
          apply simp
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (subst less_Suc_eq_le)
           apply (rule order_refl)
          apply (drule meta_mp)
           apply (smt (verit) arg_min_natI)
          apply auto
          done
        done
      subgoal for op' p' x
        apply (drule sym)
        apply (cases op2)
        subgoal for p1' f1'
          apply (auto split: if_splits option.splits)
          subgoal
            apply (insert prems(1))
            apply simp
            apply (subst (asm) (2) output_depth_Write_simp_diff)
              apply simp
             apply force
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply (smt (verit) arg_min_natI)
            apply auto
            done
          subgoal
            apply (insert prems(1))
            apply (drule comp_producing_outputs_comp_op[where p=p and n=n])
               apply simp
               apply (subst (asm) if_P)
                apply fast    
               apply fast
              apply force
             apply (metis le_imp_less_Suc prems(3))
            apply auto
            done
          subgoal
            apply (insert prems(1))
            apply (drule comp_producing_outputs_comp_op[where p=p and n=n])
               apply simp
               apply (subst (asm) if_P)
                apply fast    
               apply fast
              apply force
             apply (metis le_imp_less_Suc prems(3))
            apply auto
            done
          subgoal
            apply (cases "p = Inl p'")
             apply simp
            apply (insert prems(1))
            apply simp
            apply (subst (asm) (1 2) output_depth_Write_simp_diff)
                apply force
               apply force
              apply force
             apply fast
            apply (subst (asm) (1 2) output_depth_Read)
              apply blast+
            apply simp
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule le_SucI)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply auto
            done
          subgoal
            by (smt (z3) UNIV_I Un_iff Union_iff arg_min_natI domI dual_order.refl imageE image_eqI insert_Diff1 le_imp_less_Suc prems(1) prems(3))
          done
        subgoal
          apply (cases op2)
            apply (auto split: if_splits option.splits)
          subgoal 
            apply (cases "p = Inl p'")
             apply simp
            apply (insert prems(1))
            apply (subst (asm) output_depth_Write_simp_diff)
              apply force
             apply blast
            apply (subst (asm) output_depth_Write_simp_diff)
              apply force
             apply blast
            apply simp
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule le_SucI)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply auto
            done
          subgoal for p''
            apply (insert prems(1))
            apply simp
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply auto
            done
          done
        subgoal
          apply (insert prems(1))
          apply (auto split: option.splits if_splits)
          subgoal
            apply (cases "p = Inl p'")
             apply simp
            apply (subst (asm) (1 2) output_depth_Write_simp_diff)
                apply force
               apply force
              apply fast+            
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (subst less_Suc_eq_le)
             apply (rule order_refl)
            apply (drule meta_mp)
             apply auto
            done   
          subgoal for op'' n'' n'
            apply (subst (asm) if_P)
             apply fast    
            apply simp
            apply (drule comp_producing_outputs_comp_op[where p=p and n=n])
               apply force
              apply force
             apply (metis less_Suc_eq_le prems(1) prems(3))
            apply auto
            done
          done
        done
      subgoal
        by (smt (z3) UnE comp_producing_outputs_comp_op empty_Diff empty_iff image_empty le_imp_less_Suc not_comp_producing_eq_End op.set(6) prems(1))
      done
    done
  done

lemma outputs_comp_op_le:
  "outputs (comp_op wire buf op1 op2) \<subseteq> Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2"
  using outputs_comp_op by blast

lemma comp_producing_muteD: "comp_producing wire buf op1 op2 n \<Longrightarrow>
  wire p = None \<Longrightarrow>
  mute p op1 (lxs \<circ> Inl) \<Longrightarrow>
  comp_op wire buf op1 op2 = End \<or>
  (\<exists>op'. comp_op wire buf op1 op2 = Write op' (Inl p) EOS) \<or>
  (\<exists>f p'. comp_op wire buf op1 op2 = Read p' f \<and>
    mute_cong (Inl p) (\<lambda>op lxs. \<exists>buf op1. (\<exists>op2. op = comp_op wire buf op1 op2) \<and> mute p op1 (lxs \<circ> Inl)) (f (CHD p' lxs)) (CTL p' lxs) \<and>
    mute_cong (Inl p) (\<lambda>op lxs. \<exists>buf op1. (\<exists>op2. op = comp_op wire buf op1 op2) \<and> mute p op1 (lxs \<circ> Inl)) (f EOB) lxs) \<or>
  (\<exists>p' op'. (\<exists>x. comp_op wire buf op1 op2 = Write op' p' x) \<and> Inl p \<noteq> p' \<and>
    mute_cong (Inl p) (\<lambda>op lxs. \<exists>buf op1. (\<exists>op2. op = comp_op wire buf op1 op2) \<and> mute p op1 (lxs \<circ> Inl)) op' lxs)"
  apply (induct buf op1 op2 n arbitrary: lxs pred: comp_producing)
             apply (auto 4 0 simp: Let_def elim!: contrapos_np[of "mute_cong _ _ _ _"]
      elim!: mute_cong[THEN iffD1, rotated -1] split: option.splits
      intro!: mute_cong.write mute_cong.read intro: mute_cong.base)
            apply (rule mute_cong.base)
            apply (rule exI conjI refl)+
            apply (auto elim: mute_cong[THEN iffD1, rotated -1]) []
           apply (rule mute_cong.base)
           apply (rule exI conjI refl)+
           apply (auto elim: mute_cong[THEN iffD1, rotated -1]) []
          apply (rule mute_cong.base)
          apply (rule exI conjI refl)+
          apply (auto elim: mute_cong[THEN iffD1, rotated -1]) []
         apply (rule mute_cong.base)
         apply (rule exI conjI refl)+
         apply (auto elim: mute_cong[THEN iffD1, rotated -1]) []
        apply (rule mute_cong.base)
        apply (rule exI conjI refl)+
        apply (auto elim: mute_cong[THEN iffD1, rotated -1]) []
       apply (rule mute_cong.base)
       apply (rule exI conjI refl)+
       apply (auto elim: mute_cong[THEN iffD1, rotated -1]) []
      apply (rule mute_cong.base)
      apply (rule exI conjI refl)+
      apply (auto elim: mute_cong[THEN iffD1, rotated -1]) []
     apply (rule mute_cong.base)
     apply (rule exI conjI refl)+
     apply (auto elim: mute_cong[THEN iffD1, rotated -1]) []
    apply (rule mute_cong.base)
    apply (rule exI conjI refl)+
     apply (auto elim: mute_cong[THEN iffD1, rotated -1]) []
  subgoal for p2 p1 buf op1' f2 lxs
    by (smt (verit, del_insts) Inl_Inr_False base comp_apply fun_upd_other mute_cong)
  subgoal for p2 p1 buf op1' x1 f2 lxs
    by (smt (verit, del_insts) Inl_Inr_False base comp_apply fun_upd_other mute_cong)
   apply (drule meta_spec, drule meta_mp, assumption)
   apply auto []
  apply (drule meta_spec, drule meta_mp, assumption)
  apply auto []
  done

lemma mute_on_non_output: "p \<notin> outputs op \<Longrightarrow> mute p op lxs"
  apply (coinduction arbitrary: op lxs)
  subgoal for op lxs
    by (cases op) auto
  done

definition "pcomp_op = comp_op (\<lambda>_. None) (\<lambda>_. BEnded)"

lemma inputs_pcomp_op[simp]:
  "inputs (pcomp_op op1 op2) \<subseteq> Inl ` inputs op1 \<union> Inr ` inputs op2"
  unfolding pcomp_op_def by (auto dest: inputs_comp_op)

lemma outputs_pcomp_op[simp]:
  "outputs (pcomp_op op1 op2) \<subseteq> Inl ` outputs op1 \<union> Inr ` outputs op2"
  unfolding pcomp_op_def by (auto dest: outputs_comp_op)

definition conv where
  "conv f = (f o Inl, f o Inr)"

lemma produced_pcomp_op:
  "semantics (pcomp_op op1 op2) \<le> BNF_Def.vimage2p conv conv (rel_prod (semantics op1) (semantics op2))"
  unfolding pcomp_op_def
  apply (intro order_trans[OF semantics_comp_op])
  apply (auto simp: vimage2p_def conv_def compose_def extend_def o_def
    dest!: predicate2D[OF semantics_map_op_inj, rotated 2])
  done

definition "scomp_op op1 op2 = map_op projl projr (comp_op Some (\<lambda>_. BEmpty) op1 op2)"

lemma inputs_scomp_op[simp]:
  "inputs (scomp_op op1 op2) \<subseteq> inputs op1"
  unfolding scomp_op_def by (auto simp: op.set_map ran_def dest: inputs_comp_op)

lemma outputs_scomp_op[simp]:
  "outputs (scomp_op op1 op2) \<subseteq> outputs op2"
  unfolding scomp_op_def by (auto simp: op.set_map ran_def dest: outputs_comp_op)

lemma semantics_muted: "semantics op lxs lys \<Longrightarrow> muted op lxs lys"
  by (auto simp add: semantics_def produced_muted)

lemma "traced m (scomp_op op1 op2) ios \<longleftrightarrow> (\<exists>ios1 ios2. 
       traced m1 op1 ios1 \<and> agree (rel_sum (=) \<bottom>) ios ios1 \<and>
       agree (\<lambda>l r. case (l, r) of (Inr x, Inl y) \<Rightarrow> x = y | _ \<Rightarrow> False) ios1 ios2 \<and>
       traced m2 op2 ios2 \<and> agree (rel_sum \<bottom> (=)) ios ios2)"
  oops

lemma semantics_scomp_op:
  "\<lbrakk>scomp_op op1 op2\<rbrakk> \<le> \<lbrakk>op1\<rbrakk> OO \<lbrakk>op2\<rbrakk>"
  unfolding scomp_op_def fun_eq_iff
  apply (rule predicate2I)
  subgoal for lxs lys
    apply (frule semantics_muted)
  apply (drule semantics_map_op[rotated 2])
       apply (auto simp: inj_on_def ran_def vimage2p_def op.set_map dest!: inputs_comp_op outputs_comp_op)
  apply (frule predicate2D[OF semantics_comp_op])
  apply (auto simp: compose_def extend_def ran_def o_def cong: if_cong)
  apply (drule predicate2D[OF semantics_map_op_inj, rotated 2])
      apply (auto simp: vimage2p_def o_def image_iff cong: if_cong)
    apply (rule relcomppI)
     apply assumption
    apply (erule semantics_cong)
      apply (simp_all add: muted_def)
    apply safe
    subgoal for lzs lzs' p
      apply (drule spec[of _ p], drule mp)
       apply (erule mute_map_opI)
          apply (auto simp: inj_on_def ran_def dest!: outputs_comp_op inputs_comp_op)
      done
      apply (simp split: if_splits)
    subgoal for lzs lzs' p
      apply (drule spec[of _ p], drule mp)
       apply (erule mute_map_opI)
          apply (auto simp: inj_on_def ran_def dest!: outputs_comp_op inputs_comp_op)
      done
    done
  done

type_synonym 'd op22 = "(2, 2, 'd) op"
type_synonym 'd op11 = "(1, 1, 'd) op"

coinductive welltyped where
  "welltyped A B (f EOB) \<Longrightarrow> welltyped A B (f EOS) \<Longrightarrow> \<forall>x \<in> A p. welltyped A B (f (Observed x)) \<Longrightarrow> welltyped A B (Read p f)"
| "x \<in> B p \<Longrightarrow> welltyped A B op \<Longrightarrow> welltyped A B (Write op p x)"
| "welltyped A B End"

(*characteristic property of welltyped*)
lemma "welltyped A B op \<Longrightarrow> \<lbrakk>op\<rbrakk> lxs lys \<Longrightarrow> (\<forall>p. lset (lxs p) \<subseteq> A p) \<Longrightarrow> (\<forall>p. lset (lys p) \<subseteq> B p)"
  sorry

abbreviation "write op p x \<equiv> Write op p (Observed x)"
abbreviation "eob op p \<equiv> Write op p EOB"
abbreviation "eos op p \<equiv> Write op p EOS"

section \<open>BNA operators\<close>

definition bna_feedback :: "('m + 'l, 'n + 'l, 'd) op \<Rightarrow> ('m, 'n, 'd) op" where
  "bna_feedback op = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some o Inr)) (\<lambda>_. BEmpty) op)"

corec (friend) cp_list where "cp_list \<pi> ps op = (case ps of p # ps \<Rightarrow> Read p (\<lambda>x. Write (cp_list \<pi> ps op) (\<pi> p) x) | [] \<Rightarrow> 
  (case op of End \<Rightarrow> End | Write op p x \<Rightarrow> Write op p x | Read p f \<Rightarrow> Read p f))"
lemma cp_list_code: "cp_list \<pi> ps op = (case ps of p # ps \<Rightarrow> Read p (\<lambda>x. Write (cp_list \<pi> ps op) (\<pi> p) x) | [] \<Rightarrow> op)"
  by (subst cp_list.code) (auto split: list.splits op.splits)

corec bna_identity :: "('m :: enum, 'm, 'd) op" where
  "bna_identity = (case Enum.enum :: 'm list of (p # ps) \<Rightarrow> Read p (\<lambda>x. Write (cp_list id ps bna_identity) p x))"

corec bna_transpose :: "('m :: enum + 'n :: enum, 'n + 'm, 'd) op" where
  "bna_transpose = (case Enum.enum :: 'm list of (p # ps) \<Rightarrow> Read (Inl p) (\<lambda>x. Write (cp_list (case_sum Inr Inl) (map Inl ps @ map Inr Enum.enum) bna_transpose) (Inr p) x))"

abbreviation "bna_parcomp \<equiv> pcomp_op"
abbreviation "bna_seqcomp \<equiv> scomp_op"


corec cp22_op :: "'d op22" where
  "cp22_op = 
     (let read1 = (\<lambda>op. Read 1 (case_observation (write op 1) (eob op 1) End));
          read2 = (\<lambda>op. Read 2 (case_observation (write op 2) (eob op 2) End))
      in read1 (read2 cp22_op))"
lemmas cp22_op_code[code] = cp22_op.code[unfolded Let_def]

corec cp22_1_op :: "'d op22" where
  "cp22_1_op = Read 1 (case_observation (write cp22_1_op 1) cp22_1_op End)"

corec cp_op :: "'d op11" where
  "cp_op = Read 1 (case_observation (write cp_op 1) (eob cp_op 1) End)"

corec inc_op :: "nat op11" where
  "inc_op = Read 1 (case_observation (\<lambda>x. write inc_op 1 (x + 1)) inc_op End)"

definition print_port where
  "print_port a = (if a = 1 then ''port 1'' else ''port 2'')"

definition debug_port where
  "debug_port m a = Debug.tracing (String.implode (m @ print_port a)) a"

fun print_nat where
  "print_nat 0 = ''0''"
| "print_nat (Suc 0) = ''1''"
| "print_nat (Suc (Suc 0)) = ''2''"
| "print_nat (Suc (Suc (Suc 0))) = ''3''"
| "print_nat (Suc (Suc (Suc (Suc 0)))) = ''4''"
| "print_nat (Suc (Suc (Suc (Suc (Suc 0))))) = ''5''"
| "print_nat (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) = ''6''"
| "print_nat (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) = ''7''"
| "print_nat (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) = ''8''"
| "print_nat (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))) = ''9''"
| "print_nat n = print_nat (n div 10) @ print_nat (n mod 10)"

definition debug_nat where
  "debug_nat m x = Debug.tracing (String.implode (m @ print_nat x))"

corec (friend) debug_write_nat where
  "debug_write_nat op p x = write op p (Debug.tracing (String.implode (''Writing '' @ print_nat x @ '' at '' @ print_port p)) x)"

corec cinc_op :: "nat op22" where
  "cinc_op = Read 1 (case_observation (\<lambda>x. debug_write_nat (debug_write_nat cinc_op 2 x) 1 (x+1)) cinc_op End)"

lemma "welltyped A A cp_op"
(*needs coinduction up-to for welltyped (or a custom bisimulation)*)
  sorry

definition loop22_op :: "'d op22 \<Rightarrow> 'd op11" where
  "loop22_op op = map_op (\<lambda>_. 1) (\<lambda>_. 1) (loop_op
    (\<lambda>x. if x = 1 then Some 1 else None) (\<lambda>_. BEmpty) op)"

fun Cons_fst where
  "Cons_fst x [] = [[x]]"
| "Cons_fst x ([] # xss) = [x] # xss"
| "Cons_fst x (xs # xss) = (x # xs) # xss"

fun ltaken where
  "ltaken 0 _ = []"
| "ltaken _ LNil = []"
| "ltaken (Suc n) (LCons x xs) = x # ltaken n xs"

(*
lemma loop_op_lSup:
  "produce (loop_op wire buf op) lxs p =
   lSup {xs | xs n. xs = produce (Nat.funpow n (\<lambda> op'. map_op (case_sum id id) projr (comp_op wire buf op' op')) op) lxs p}"
  oops
*)

corec (friend) bulk_write where
  "bulk_write ys i op =
    (case ys of [] \<Rightarrow> End | [x] \<Rightarrow> write op i x | x#xs \<Rightarrow> write (bulk_write xs i op) i x)"

definition "my_pow n f = Nat.funpow n (\<lambda> x. f x x)"

definition loop22_with_comp_op :: "(2, 2, 'a) op \<Rightarrow> nat \<Rightarrow> (2, 2, 'a) op" where
  "loop22_with_comp_op op n = my_pow n 
    (\<lambda> op1 op2. map_op (case_sum id (\<lambda> _. undefined)) (case_sum (\<lambda> e.  1) (debug_port ''output 2 ''))
      (comp_op (\<lambda>x. if x = 1 then Some 1 else None) (\<lambda>_. BEmpty) op1 op2)) op"

corec foo_op :: "nat list \<Rightarrow> (2, 2, nat) op" where
  "foo_op buf = Read 1 (case_observation (\<lambda>x. foo_op (buf@[x])) (bulk_write (map ((+)1) buf) 1 (bulk_write buf 2 (foo_op []))) End)"

value "scomp_op (bulk_write [1,2,3] 1 cp22_1_op) (foo_op [])"
value "ltaken 30 (produce 1 (loop22_op (scomp_op (bulk_write [1,2,3] 1 cp22_1_op) (foo_op [1,2,3]))) (\<lambda> _. undefined))"
value "ltaken 30 (produce 2 (loop22_with_comp_op (scomp_op (bulk_write [1,2,3] 1 cp22_1_op) (foo_op [])) 3) (\<lambda> _. LNil))"

corec foo2_op :: "nat list \<Rightarrow> (2, 2, nat) op" where
  "foo2_op buf = Read 1 (case_observation (\<lambda>x. bulk_write (map ((+)1) buf) 1 (foo2_op (buf@[x]))) ((bulk_write buf 2 (foo2_op []))) End)"

value "ltaken 5 (produce 1 (loop22_op (scomp_op (bulk_write [1,2,3] 1 cp22_1_op) (foo2_op []))) (\<lambda> _. LNil))"
value "ltaken 5 (produce 2 (loop22_with_comp_op (scomp_op (bulk_write [1,2,3] 1 cp22_1_op) (foo2_op [])) 3) (\<lambda> _. LNil))"


value "ltaken 30 (produce 1 (loop22_op (scomp_op (write cp22_1_op 1 1) cinc_op)) (\<lambda> _. LNil))"
value "ltaken 30 (produce 2 (loop22_with_comp_op (scomp_op (write cp22_1_op 1 1) cinc_op) 3) (\<lambda> _. LNil))"


code_thms produce

(* TODO does not terminate: has to do with produce code equation using lmap_lhd which seems to break productivity
value "ctaken 1 30 (produce (loop22_op (scomp_op (write cp22_1_op 1 1) cinc_op)) (\<lambda> _. TNil LNil) 1)"
value "ctaken 5 30 (produce (loop22_with_comp_op (scomp_op (write cp22_1_op 1 1) cinc_op) 3) (\<lambda> _. TNil LNil) 2)"
*)
(*produce works fine*)
value "ltaken 30 (produce 1 (loop22_op (scomp_op (write cp22_1_op 1 1) cinc_op)) (\<lambda> _. LNil))"

(*
lemma
  "lprefix
   (produce (loop22_with_comp_op (bulk_write [1,2,3] 1 (foo_op [])) n) (\<lambda> _. LNil) 1)
   (produce (loop22_op (bulk_write [1,2,3] 1 (foo_op []))) (\<lambda> _. undefined) 1)"
  oops
*)
  thm ltake_enat_eq_imp_eq

  find_theorems ltake "_ \<Longrightarrow> _ = _"

locale collatz =
  fixes encode_nat3 :: "nat \<times> nat \<times> nat \<Rightarrow> 'd"
    and decode_nat3 :: "'d \<Rightarrow> nat \<times> nat \<times> nat"
    and encode_nat2 :: "nat \<times> nat \<Rightarrow> 'd"
    and decode_nat2 :: "'d \<Rightarrow> nat \<times> nat"
    and encode_nat1 :: "nat \<Rightarrow> 'd"
    and decode_nat1 :: "'d \<Rightarrow> nat"
  assumes type_definition_nat3: "type_definition encode_nat3 decode_nat3 (range encode_nat3)"
      and type_definition_nat2: "type_definition encode_nat2 decode_nat2 (range encode_nat2)"
      and type_definition_nat1: "type_definition encode_nat1 decode_nat1 (range encode_nat1)"
begin

(*boolean signals if there is more input*)
abbreviation collatz_input :: "(bool \<Rightarrow> 'd op22) \<Rightarrow> bool \<Rightarrow> 'd op22" where
  "collatz_input op b \<equiv> (if b then Read 2 (\<lambda>x. case x of
     Observed x \<Rightarrow> let n = decode_nat1 x in write (op True) 1 (encode_nat3 (n, n, 0))
   | EOB \<Rightarrow> op True
   | EOS \<Rightarrow> op False)
   else op False)"
abbreviation collatz_loop_input :: "(bool \<Rightarrow> 'd op22) \<Rightarrow> bool \<Rightarrow> 'd op22" where
  "collatz_loop_input op b \<equiv> Read 1 (\<lambda>x. case x of
     Observed x \<Rightarrow> let (n, ni, i) = decode_nat3 x in
       if ni = 1 then write (op b) 2 (encode_nat2 (n, i)) else
         write (op b) 1 (encode_nat3 (n, if ni mod 2 = 0 then ni div 2 else 3 * ni + 1, i + 1))
   | _ \<Rightarrow> if b then op True else End)"
corec collatz_step :: "bool \<Rightarrow> 'd op22" where
  "collatz_step b = collatz_input (collatz_loop_input collatz_step) b"
definition collatz_op :: "'d op11" where
  "collatz_op = loop22_op (collatz_step True)"

definition collatz :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "collatz n \<equiv> map (decode_nat2 o val)
     (list_of (produce 1 collatz_op (\<lambda>_. llist_of (map (Value o encode_nat1) [1 ..< Suc n]))))"

lemma collatz_op_welltyped: "welltyped (\<lambda>_. range encode_nat1) (\<lambda>_. range encode_nat2) collatz_op"
  sorry

end

term "collatz (Inr o Inr) (projr o projr) (Inr o Inl)"

global_interpretation c: collatz
  "Inr o Inr" "projr o projr" "Inr o Inl" "projl o projr" Inl projl
  defines ccollatz_step = "collatz.collatz_step (Inr o Inr) (projr o projr) (Inr o Inl) projl"
  and ccollatz_op = "collatz.collatz_op (Inr o Inr) (projr o projr) (Inr o Inl) projl"
  and ccollatz = "collatz.collatz (Inr o Inr) (projr o projr) (Inr o Inl) (projl o projr) Inl projl"
  by standard auto

term ccollatz_op

value "ccollatz 100"

datatype ('t, 'd) event = Data (tmp: 't) (data: 'd) | Watermark (tmp: "'t::order")



simps_of_case bulk_write_simps[simp]: bulk_write.code[unfolded]

fun batches where
  "batches ((t::_::order)#tss) xs = (let (bs, xs') = batches tss [(t', d) \<leftarrow> xs. \<not> t' \<le> t] in
   (Data t [(t', d) \<leftarrow> xs. t' \<le> t] # bs, xs'))"
| "batches [] xs = ([], xs)"

fun maximal_antichain_list where
  "maximal_antichain_list [] = []"
| "maximal_antichain_list ((wm::_::order)#xs) = (let ma = maximal_antichain_list (filter (\<lambda> t. \<not> t \<le> wm) xs) in if \<exists> wm' \<in> set ma. wm \<le> wm' then ma else wm#ma)"

locale op11 =
  fixes input_type :: "'a itself"
    and output_type :: "'b itself"
    and domain_type :: "'d itself"
    and encode_input :: "'a \<Rightarrow> 'd"
    and decode_input :: "'d \<Rightarrow> 'a"
    and encode_output :: "'b \<Rightarrow> 'd"
    and decode_output :: "'d \<Rightarrow> 'b"
  assumes type_definition_event: "type_definition encode_input decode_input (range encode_input)"
  assumes type_definition_batch_event: "type_definition encode_output decode_output (range encode_output)"
begin

abbreviation read :: "('a observation \<Rightarrow> 'd op11) \<Rightarrow> 'd op11" where
 "read f \<equiv> Read 1 (f o map_observation decode_input)"

abbreviation "write" :: "'d op11 \<Rightarrow> 'b \<Rightarrow> 'd op11" where
  "write op \<equiv> Cycles_X.write op 1 o encode_output"

abbreviation bulk_write where "bulk_write ys op \<equiv> Cycles_X.bulk_write (map encode_output ys) 1 op"

end

locale top11 = t?: op11
  where input_type = "input_type :: 'a itself"
    and output_type = "output_type :: 'b itself"
    and domain_type = "domain_type :: 'd itself"
  for input_type output_type domain_type +
  fixes time_type :: "'t :: order itself"
begin

abbreviation read :: "(('t, 'a) event observation \<Rightarrow> ('t, 'd) event op11) \<Rightarrow> ('t, 'd) event op11" where
 "read f \<equiv> Read 1 (f o map_observation (map_event id decode_input))"

abbreviation "write" :: "('t, 'd) event op11 \<Rightarrow> ('t, 'b) event \<Rightarrow> ('t, 'd) event op11" where
  "write op \<equiv> Cycles_X.write op 1 o map_event id encode_output"

abbreviation bulk_write where "bulk_write ys op \<equiv> Cycles_X.bulk_write (map (map_event id encode_output) ys) 1 op"

end

locale batch = top11
  where input_type = "TYPE('dd)"
    and output_type = "TYPE(('t :: order \<times> 'dd) list)"
    and domain_type = "TYPE('d)"
    and time_type = "TYPE('t)" +
  fixes
    dummy :: "'dd itself"
begin

corec batch_op where
  "batch_op buf = read (\<lambda> x. case x of
    Observed ev \<Rightarrow> (case ev of
        Data t d \<Rightarrow> batch_op (buf @ [(t, d)])
      | Watermark wm \<Rightarrow> let (out, buf') = batches [wm] buf in bulk_write ([x \<leftarrow> out. data x \<noteq> []] @ [Watermark wm]) (batch_op buf'))
    | EOS \<Rightarrow> let wms = maximal_antichain_list (map fst buf) ;
             (bts, _) = batches wms buf in
             bulk_write bts End
    | EOB \<Rightarrow> batch_op buf)"

abbreviation "batch_input_test_1 xs \<equiv> llist_of (map (Value o map_event id encode_input) xs)"

definition "batch_op_test_1 xs = map (map_event id decode_output o val) (list_of (produce 1 (batch_op []) (\<lambda> _. batch_input_test_1 xs)))"

end

global_interpretation b: batch Inl projl Inr projr
  defines bbatch_op = "batch.batch_op projl Inr"
  and bbatch_op_test_1 = "batch.batch_op_test_1 Inl projl Inr projr"
  by standard auto

abbreviation "bbatch_op_test_1_r \<equiv> bbatch_op_test_1  [Data (0::nat) ''dog'', Data 2 ''cat'', Watermark 1, Watermark 2]"
value bbatch_op_test_1_r

locale incr =
top11
  where input_type = "TYPE(('t :: order \<times> 'dd) list)"
    and output_type = "TYPE(('t :: order \<times> 'dd) list)"
    and domain_type = "TYPE('d)"
    and time_type = "TYPE('t)" +
  fixes
    dummy :: "'dd itself"
begin


corec incr_op where
  "incr_op buf = read (\<lambda> x. case x of
    Observed ev \<Rightarrow> (case ev of
        Data wm b \<Rightarrow> let ts = rev (remdups (map fst (rev b))) ;
                         out = map (\<lambda> t . Data t (buf@ b)) ts in
                         bulk_write out (incr_op (buf @ b))
      | Watermark wm \<Rightarrow> write (incr_op buf) (Watermark wm)) 
    | EOS \<Rightarrow> End
    | EOB \<Rightarrow> incr_op buf)"

abbreviation "incr_input_test_1 xs \<equiv> llist_of (map (Value o map_event id encode_input) xs)"
definition "incr_op_test_1 xs = map (map_event id decode_output o val) (list_of (produce 1 (incr_op []) (\<lambda> _. incr_input_test_1 xs)))"

end

global_interpretation i: incr id id id id
  defines iincr_op = "incr.incr_op id id"
    and iincr_op_test_1 = "incr.incr_op_test_1 id id id id"
  by standard auto

value "iincr_op_test_1 bbatch_op_test_1_r"

locale incr_batch =
  b?:batch where dummy = "TYPE('dd)" and encode_input=encode_input and decode_input=decode_input and encode_output=encode_output and decode_output=decode_output
  +
  i?:incr where dummy = "TYPE('dd)" and encode_input=encode_output and decode_input=decode_output and encode_output=encode_output and decode_output=decode_output
  for encode_input decode_input encode_output decode_output
begin

definition "incr_batch_op buf1 buf2 = scomp_op (batch_op buf1) (incr_op buf2)"

abbreviation "incr_batch_input_test_1 xs \<equiv> llist_of (map (Value o map_event id encode_input) xs)"
(* write abbreviation for produce with finite_1 *)
definition "incr_batch_op_test_1 xs = map (map_event id decode_output o val) (list_of (produce 1 (incr_batch_op [] []) (\<lambda> _. incr_batch_input_test_1 xs)))"

end

term incr_batch

global_interpretation ib: incr_batch Inl projl "(Inr:: ('t::order \<times> 'a) list \<Rightarrow> 'a + ('t \<times> 'a) list)" projr 
  defines ibincr_op = "incr.incr_op projr (Inr :: ('t::order \<times> 'a) list \<Rightarrow> 'a + ('t \<times> 'a) list)"
   and  ibatch_op = "batch.batch_op projl (Inr :: ('t::order \<times> 'a) list \<Rightarrow> 'a + ('t \<times> 'a) list)"
   and ibbatch_incr_op = "incr_batch.incr_batch_op projl (Inr :: ('t::order \<times> 'a) list \<Rightarrow> 'a + ('t \<times> 'a) list) projr" 
  and ibincr_batch_op_test_1 = "incr_batch.incr_batch_op_test_1 Inl projl Inr projr"  
  by standard auto

value "ibincr_batch_op_test_1 [Data (0::nat) ''dog'', Data 2 ''cat'', Watermark 1, Watermark 2]"


