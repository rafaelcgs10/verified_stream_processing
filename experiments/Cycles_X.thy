theory Cycles_X
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
datatype (discs_sels) (the_value: 'd) "channel_value" = Value (val: 'd) | No_Value
codatatype (inputs: 'ip, outputs: 'op, dead 'd) op =
    Read 'ip "'d observation \<Rightarrow> ('ip, 'op, 'd) op"
  | Write "('ip, 'op, 'd) op" 'op "'d observation"
  | End

type_synonym 'd channel = "'d channel_value llist"

code_lazy_type op
 
fun chd where
  "chd LNil = EOS"
| "chd (LCons No_Value lxs) = EOB"
| "chd (LCons (Value x) lxs) = Observed x"

abbreviation ctl :: "'d channel \<Rightarrow> 'd channel" where "ctl \<equiv> ltl"

abbreviation CHD :: "'a \<Rightarrow> ('a \<Rightarrow> 'd channel) \<Rightarrow> 'd observation" where "CHD p lxs \<equiv> chd (lxs p)"
abbreviation CTL :: "'a \<Rightarrow> ('a \<Rightarrow> 'd channel) \<Rightarrow> ('a \<Rightarrow> 'd channel)" where "CTL p lxs \<equiv> lxs(p := ctl (lxs p))"

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

fun value_of where
  "value_of (Observed x) = Value x"
| "value_of EOB = No_Value"
| "value_of EOS = undefined"

abbreviation "VCons x \<equiv> LCons (value_of x)"

corecursive produce where
  "produce p op lxs = (let produce' = (\<lambda>op' lxs'. if \<exists>i. producing p op lxs i then produce p op' lxs' else LNil) in case op of
    Read p' f \<Rightarrow> (produce' (f (CHD p' lxs)) (CTL p' lxs))
  | Write op' p' x \<Rightarrow> (if p = p' then (if x = EOS then LNil else VCons x (produce p op' lxs)) else produce' op' lxs)
  | End \<Rightarrow> LNil)"
  by (relation "measure (\<lambda>(p, op, lxs). THE i. producing p op lxs i)")
    (auto 0 3 simp: The_producing del: producing_ReadE producing_WriteE elim: producing.cases)

lemma produce_code[code]:
  "produce p op lxs = (case op of
    Read p' f \<Rightarrow> produce p (f (CHD p' lxs)) (CTL p' lxs)
  | Write op' p' x \<Rightarrow> (if p = p' then (if x = EOS then LNil else VCons x (produce p op' lxs)) else produce p op' lxs)
  | End \<Rightarrow> LNil)"
  apply (subst produce.code)
  apply (simp split: op.splits if_splits channel_value.splits)
  apply safe
  subgoal for p' f
    by (subst produce.code) (auto 0 5 split: op.splits intro: producing.intros)
  subgoal for op p x
    by (subst produce.code) (auto 0 4 split: op.splits intro: producing.intros)
  done

simps_of_case produce_simps[simp]: produce_code

inductive vocal for p where
  Write_same: "x \<noteq> EOS \<Longrightarrow> vocal p (Write op p x) lxs"
| Write_other: "p \<noteq> p' \<Longrightarrow> vocal p op' lxs \<Longrightarrow> vocal p (Write op' p' x) lxs"
| Read: "vocal p (f (CHD p' lxs)) (CTL p' lxs) \<Longrightarrow> vocal p (Read p' f) lxs"

inductive_cases vocal_EndE[elim!]: "vocal p End lxs"
inductive_cases vocal_WriteE[elim!]: "vocal p (Write op p' x) lxs"
inductive_cases vocal_ReadE[elim!]: "vocal p (Read p' f) lxs"

coinductive silent for p where
  End[simp, intro!]: "silent p End lxs"
| WriteEOS[simp, intro!]: "silent p (Write op p EOS) lxs"
| Write: "p \<noteq> p' \<Longrightarrow> silent p op' lxs \<Longrightarrow> silent p (Write op' p' x) lxs"
| Read: "silent p (f (CHD p' lxs)) (CTL p' lxs) \<Longrightarrow> silent p (Read p' f) lxs"

inductive_cases silent_EndE[elim!]: "silent p End lxs"
inductive_cases silent_WriteE[elim!]: "silent p (Write op p' x) lxs"
inductive_cases silent_ReadE[elim!]: "silent p (Read p' f) lxs"

lemma vocal_not_silent: "vocal p op lxs \<Longrightarrow> \<not> silent p op lxs"
  by (induct op lxs pred: vocal) (auto simp: fun_upd_def)

lemma not_vocal_silent: "\<not> vocal p op lxs \<Longrightarrow> silent p op lxs"
  apply (coinduction arbitrary: op lxs)
  subgoal for op lxs
    by (cases op) (auto simp: fun_upd_def intro: vocal.intros)
  done

lemma not_silent_iff_vocal: "\<not> silent p op lxs \<longleftrightarrow> vocal p op lxs"
  by (metis not_vocal_silent vocal_not_silent)

lemma lnull_produce_silent: "produce p op lxs = LNil \<Longrightarrow> silent p op lxs"
  apply (coinduction arbitrary: op lxs)
  apply (subst produce_code)
  subgoal for op lxs
    apply (cases op)
      apply (auto simp: split: if_splits op.splits channel_value.splits llist.splits)
    done
  done

lemma producing_silent_LNil: "producing p op lxs n \<Longrightarrow> silent p op lxs \<Longrightarrow> produce p op lxs = LNil"
  by (induct op lxs n rule: producing.induct) (auto elim: silent.cases split: channel_value.splits)

lemma silent_produce_LNil: "silent p op lxs \<Longrightarrow> produce p op lxs = LNil"
  by (subst produce.code)
    (auto split: op.splits channel_value.splits dest: producing_silent_LNil simp flip: produce_def)

lemma lnull_produce_iff_silent: "produce p op lxs = LNil \<longleftrightarrow> silent p op lxs"
  using lnull_produce_silent silent_produce_LNil by fastforce

lemma not_producing_LNil: "(\<forall>n. \<not> producing p op lxs n) \<Longrightarrow> produce p op lxs = LNil"
  by (subst produce.code) (auto split: op.splits intro: producing.intros)

datatype 'd buf = BEmpty | BEnded | BCons "'d list" "'d buf"

fun bhd where
  "bhd BEmpty = EOB"
| "bhd BEnded = EOS"
| "bhd (BCons [] xss) = EOB"
| "bhd (BCons (x # xs) xss) = Observed x"

fun btl where
  "btl BEmpty = BEmpty"
| "btl BEnded = BEnded"
| "btl (BCons [] xss) = xss"
| "btl (BCons (x # xs) xss) = BCons xs xss"

fun bend where
  "bend BEmpty = BEnded"
| "bend BEnded = BEnded"
| "bend (BCons xs xss) = BCons xs (bend xss)"

fun benq where
  "benq (Observed x) BEmpty = BCons [x] BEmpty"
| "benq (Observed x) BEnded = BCons [x] BEnded"
| "benq EOB BEmpty = BCons [] BEmpty"
| "benq EOB BEnded = BCons [] BEnded"
| "benq EOS x = bend x"
| "benq (Observed x) (BCons xs BEmpty) = BCons (xs @ [x]) BEmpty"
| "benq (Observed x) (BCons xs BEnded) = BCons (xs @ [x]) BEnded"
| "benq x (BCons ys yss) = BCons ys (benq x yss)"


abbreviation BHD :: "'a \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> 'd observation" where "BHD p buf \<equiv> bhd (buf p)"
abbreviation (input) BUPD where "BUPD f p buf \<equiv> buf(p := f (buf p))"
abbreviation BTL :: "'a \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BTL \<equiv> BUPD btl"
abbreviation BENQ :: "'a \<Rightarrow> 'd observation \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BENQ p x buf \<equiv> BUPD (benq x) p buf"
abbreviation BENQ_TL :: "'a \<Rightarrow> 'd observation \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BENQ_TL p x buf \<equiv> BUPD (btl o benq x) p buf"

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

lemma vocal_in_outputs: "vocal p op lxs \<Longrightarrow> p \<in> outputs op"
  by (induct op lxs pred: vocal) auto

lemma silent_cong: "p = q \<Longrightarrow> (\<And>q. q \<in> inputs op \<Longrightarrow> lxs q = lxs' q) \<Longrightarrow> silent p op lxs = silent q op lxs'"
  apply hypsubst_thin
  apply (rule iffI)
  subgoal premises prems
    using prems(2,1)
    apply (coinduction arbitrary: op lxs lxs')
    subgoal for op lxs lxs'
      apply (erule silent.cases)
         apply (auto 0 0)
       apply blast
      apply (metis fun_upd_apply)
      done
    done
  subgoal premises prems
    using prems(2,1)
    apply (coinduction arbitrary: op lxs lxs')
    subgoal for op lxs lxs'
      apply (erule silent.cases)
         apply (auto 0 0)
       apply blast
      apply (metis fun_upd_apply)
      done
    done
  done

lemma vocal_cong: "p = q \<Longrightarrow> (\<And>q. q \<in> inputs op \<Longrightarrow> lxs q = lxs' q) \<Longrightarrow> vocal p op lxs = vocal q op lxs'"
  apply hypsubst_thin
  apply (rule iffI)
  subgoal premises prems
    using prems(2,1)
  proof (induct op lxs arbitrary: lxs' pred: vocal)
    case (Read f p' lxs)
    then have *: "lxs p' = lxs' p'"
      by simp
    show ?case
      by (force intro!: vocal.intros Read(2)[unfolded *] Read(3))
  qed (auto intro: vocal.intros)
  subgoal premises prems
    using prems(2,1)
  proof (induct op lxs' arbitrary: lxs pred: vocal)
    case (Read f p' lxs')
    then have *: "lxs p' = lxs' p'"
      by simp
    show ?case
      by (force intro!: vocal.intros Read(2)[folded *] Read(3))
  qed (auto intro: vocal.intros)
  done

lemma produce_cong: "p = q \<Longrightarrow> (\<And>q. q \<in> inputs op \<Longrightarrow> lxs q = lxs' q) \<Longrightarrow> produce p op lxs = produce q op lxs'"
  apply hypsubst_thin
  apply (coinduction arbitrary: op lxs lxs')
    unfolding lnull_def lnull_produce_iff_silent not_silent_iff_vocal
  apply (safe del: iffI)
  subgoal for op lxs lxs'
    apply (rule iffI)
     apply (coinduction arbitrary: op lxs lxs')
    subgoal for op lxs lxs'
      apply (erule silent.cases)
         apply clarsimp+
       apply blast
      apply clarsimp
      apply (rule exI conjI[rotated] | assumption)+
      apply auto
      done
    apply (coinduction arbitrary: op lxs lxs')
    subgoal for op lxs lxs'
      apply (erule silent.cases)
         apply clarsimp+
       apply blast
      apply clarsimp
      apply (rule exI conjI[rotated] | assumption)+
      apply auto
      done
    done
  subgoal premises prems for op lxs lxs'
    using prems(2,1,3)
    apply (induct op lxs arbitrary: lxs' pred: vocal)
      apply (clarsimp simp del: fun_upd_apply)+
     apply blast
    apply (clarsimp simp del: fun_upd_apply)
    apply (metis fun_upd_other fun_upd_same)
    done
  subgoal premises prems for op lxs lxs'
    using prems(2,1,3)
    apply (induct op lxs arbitrary: lxs' pred: vocal)
      apply (clarsimp simp del: fun_upd_apply)+
      apply metis
     apply auto[1]
    subgoal for f p' lxs lxs'
      apply (drule meta_spec[of _ "lxs'(p' := ctl (lxs' p'))"])
      apply (clarsimp simp del: fun_upd_apply)
      apply (metis fun_upd_other fun_upd_same)
      done
    done
  done

lemma produce_not_in_outputs: "p \<notin> outputs op \<Longrightarrow> produce p op lxs = LNil"
  unfolding lnull_produce_iff_silent
  apply (coinduction arbitrary: op lxs)
  subgoal for op lxs
    by (cases op) auto
  done

lemma produce_map_op:
  "inj_on g (inputs op) \<Longrightarrow>
   (\<And>x. x \<in> outputs op \<Longrightarrow> h' (h x) = x) \<Longrightarrow>
   (\<And>x. h (h' x) = x) \<Longrightarrow>
   produce p (map_op g h op) lxs = produce (h' p) op (lxs o g)"
  apply (coinduction arbitrary: op lxs)
  unfolding lnull_def lnull_produce_iff_silent not_silent_iff_vocal
  apply safe
  subgoal premises prems for op lxs
  proof -
    have "silent (h' p) op lxs'" if "\<forall>x \<in> inputs op. lxs' x = lxs (g x)" for lxs'
      using that prems
      apply (coinduction arbitrary: op lxs lxs')
      subgoal for op lxs lxs'
        apply (cases op)
          apply (auto 0 1)
        subgoal for q ff
          apply (rule exI conjI[rotated] | assumption)+
            apply blast
           apply (simp add: inj_on_def)
          apply (metis (no_types, lifting) Diff_empty Diff_insert0 UNIV_I UN_iff fun_upd_def image_iff the_inv_into_f_eq)
          done
        done
      done
    then show ?thesis
      by auto
  qed
  subgoal for op lxs
    apply (coinduction arbitrary: op lxs)
    subgoal for op lxs
      apply (cases op)
        apply (auto 0 1)
      subgoal for q ff
        apply (rule exI conjI refl allI impI | assumption)+          
         apply (auto simp: inj_on_def)
        apply (erule silent_cong[OF refl, THEN iffD2, rotated -1])
        apply auto
        apply (metis UNIV_I UN_iff image_iff insertCI insertE insert_Diff_single)
        done
      subgoal for op' q x
        apply (drule spec[of _ op'])
        apply auto
        done
      subgoal for op' q x
        apply (drule spec[of _ op'])
        apply auto
        done
      done
    done
  subgoal premises prems for op lxs
    using prems(4,1,2,3,5)
  proof (induct "map_op g h op" lxs arbitrary: op pred: vocal)
    case (Write_same x op' lxs)
    then show ?case
      by (cases op) auto
  next
    case (Write_other p' op' lxs x)
    then show ?case
      apply (cases op)
        apply (auto 0 0)
      done
  next
    case (Read f p' lxs)
    then show ?case
      apply (cases op)
        apply auto
      subgoal for q ff
        apply (cases "p \<notin> outputs (map_op g h (ff (chd (lxs (g q)))))")
         apply (meson lnull_produce_iff_silent produce_not_in_outputs vocal_not_silent)
        apply (drule meta_spec, drule meta_mp, rule refl)
        apply (drule meta_mp; (auto elim!: inj_on_subset)?)
        apply (drule meta_mp, blast)
        apply (drule meta_mp)
        subgoal
          apply (erule iffD1[OF vocal_cong, rotated -1])
           apply (metis UNIV_I UN_iff imageE inj_onI op.set_map(2) the_inv_into_f_f)
          apply (metis Diff_iff UNIV_I UN_iff comp_def fun_upd_other fun_upd_same image_iff singletonD)
          done
        apply (erule trans)
        apply (rule arg_cong[where f= lhd])
        apply (rule produce_cong[OF refl])
        apply (metis DiffI UNIV_I UN_iff comp_apply fun_upd_other fun_upd_same imageI singletonD)
        done
      done
  qed
  subgoal premises prems for op lxs
    using prems(4,1,2,3,5)
  proof (induct "map_op g h op" lxs arbitrary: op pred: vocal)
    case (Write_same x op' lxs)
    then show ?case
      by (cases op) auto
  next
    case (Write_other p' op' lxs x)
    then show ?case
      apply (cases op)
        apply (auto 0 0)
      done
  next
    case (Read f p' lxs)
    then show ?case
      apply (cases op)
      apply auto
      subgoal for q ff
        apply (cases "p \<notin> outputs (map_op g h (ff (chd (lxs (g q)))))")
        apply (meson lnull_produce_iff_silent produce_not_in_outputs vocal_not_silent)
        apply (drule meta_spec, drule meta_mp, rule refl)
        apply (drule meta_mp; (auto elim!: inj_on_subset)?)
        apply (drule meta_mp, blast)
        apply (drule meta_mp)
        subgoal
          apply (erule iffD1[OF vocal_cong, rotated -1])
          apply (metis UNIV_I UN_iff imageE inj_onI op.set_map(2) the_inv_into_f_f)
          apply (metis Diff_iff UNIV_I UN_iff comp_def fun_upd_other fun_upd_same image_iff singletonD)
          done
        apply (erule exE conjE)+
        apply simp
        apply (rule exI conjI refl)+
        apply (erule trans[rotated])
        apply (rule arg_cong[where f= ctl])
        apply (rule produce_cong[OF refl])
        apply (metis DiffI UNIV_I UN_iff comp_apply fun_upd_other fun_upd_same imageI singletonD)
        apply simp
        done
      done
  qed
  done

inductive silent_cong for p R where
  silent: "silent p op lxs \<Longrightarrow> silent_cong p R op lxs"
| base: "R op lxs \<Longrightarrow> silent_cong p R op lxs"
| "write": "p \<noteq> p' \<Longrightarrow> silent_cong p R op' lxs \<Longrightarrow> silent_cong p R (Write op' p' x) lxs"
| read: "silent_cong p R (f (CHD p' lxs)) (CTL p' lxs) \<Longrightarrow> silent_cong p R (Read p' f) lxs"

lemma silent_coinduct_upto:
  assumes "R op lxs"
  and "(\<And>op lxs.
    R op lxs \<Longrightarrow>
    (op = End) \<or> (\<exists>op'. op = Write op' p EOS) \<or>
    (\<exists>p' op' x. op = Write op' p' x \<and> p \<noteq> p' \<and> silent_cong p R op' lxs) \<or>
    (\<exists>f p'. op = Read p' f \<and> silent_cong p R (f (CHD p' lxs)) (CTL p' lxs)))"
  shows "silent p op lxs"
  apply (rule silent.coinduct[where X = "silent_cong p R"])
   apply (rule silent_cong.intros, rule assms(1))
  subgoal for op lxs
    apply (induct op lxs pred: silent_cong)
    subgoal
      by (erule silent.cases) (auto simp del: fun_upd_apply)
    subgoal for op lxs
      by (drule assms) (auto simp del: fun_upd_apply)
    subgoal for p' op' lxs x
      by blast
    subgoal for f lxs p'
      by blast
    done
  done

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

lemma aux:
  "input_depth p (Read (Inl p1) (\<lambda>y1. comp_op wire buf (f y1) op2)) = Suc n \<Longrightarrow>
   p \<noteq> Inl p1 \<Longrightarrow>
   p \<in> inputs (comp_op wire buf op1 op2) \<Longrightarrow>
   op1 \<in> range f \<Longrightarrow>
   \<exists> op1 \<in> range f. input_depth p (comp_op wire buf op1 op2) \<le> n \<and> p \<in> inputs (comp_op wire buf op1 op2)"
  apply (subst (asm) input_depth_Read_diff)
    apply auto
  by (meson arg_min_natI order_refl)

find_theorems input_depth

lemma input_depth_Read_simp:
  "input_depth p (Read p' f) =
  (if p = p' then 0 else (if \<exists>x. p \<in> inputs (f x) then Suc (input_depth p (f (ARG_MIN (input_depth p \<circ> f) x. p \<in> inputs (f x)))) else undefined))"
  apply (auto simp add: input_depth_Read input_depth_Read_diff split: if_splits)
  oops


lemma input_depth_arg_min_le[simp]:
  "p \<in> inputs (f x) \<Longrightarrow>
   input_depth p (f (ARG_MIN (input_depth p o f) x. p \<in> inputs (f x))) \<le> input_depth p (f x)"
  by (metis arg_min_nat_le comp_apply)

lemma input_depth_com_op_arg_min_le_1[]:
  "p \<in> inputs (comp_op wire buf (f1 x) op2) \<Longrightarrow>
  input_depth p (comp_op wire buf (f1 (ARG_MIN (input_depth p \<circ> (\<lambda>x. comp_op wire buf (f1 x) op2)) x. p \<in> inputs (comp_op wire buf (f1 x) op2))) op2)
  \<le> input_depth p (comp_op wire buf (f1 x) op2)"
  by (metis (mono_tags, lifting) arg_min_nat_le comp_apply)

lemma input_depth_com_op_arg_min_le_2[]:
  "p \<in> inputs (comp_op wire buf op1 (f2 x)) \<Longrightarrow>
   input_depth p (comp_op wire buf op1 
   (f2 (ARG_MIN (input_depth p \<circ> (\<lambda>y. comp_op wire buf op1 (f2 y))) xa. p \<in> inputs (comp_op wire buf op1 (f2 xa)))))
   \<le> input_depth p (comp_op wire buf op1 (f2 x))"
  by (metis (mono_tags, lifting) arg_min_nat_le comp_apply)

lemma aux2[simp]:
  "p \<in> inputs (comp_op wire buf (f1 x) op) \<Longrightarrow>
   p \<in> inputs (comp_op wire buf (f1 (ARG_MIN (m :: _ \<Rightarrow> nat) x. p \<in> inputs (comp_op wire buf (f1 x) op))) op)"
  by (rule arg_min_natI)

lemma aux3[simp]:
  "p \<in> inputs (comp_op wire buf op (f2 y)) \<Longrightarrow>
   p \<in> inputs (comp_op wire buf op (f2 (ARG_MIN (m :: _ \<Rightarrow> nat) y. p \<in> inputs (comp_op wire buf op (f2 y)))))"
  by (rule arg_min_natI)

lemma aux4[simp]:
  fixes m1 m2 :: "_ \<Rightarrow> nat"
  shows "p \<in> inputs (comp_op wire buf (f1 x) (f2 y)) \<Longrightarrow>
         p \<noteq> Inr p2 \<Longrightarrow>
   p \<in> inputs
          (comp_op wire buf (f1 (ARG_MIN (input_depth p \<circ> (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2)))) x. p = Inr p2 \<or> (\<exists>xa. p \<in> inputs (comp_op wire buf (f1 x) (f2 xa)))))
            (f2 (ARG_MIN (input_depth p \<circ>
                          (\<lambda>y2. comp_op wire buf (f1 (ARG_MIN (input_depth p \<circ> (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2)))) x. p = Inr p2 \<or> (\<exists>xa. p \<in> inputs (comp_op wire buf (f1 x) (f2 xa))))) (f2 y2))) x.
                    p \<in> inputs (comp_op wire buf (f1 (ARG_MIN (input_depth p \<circ> (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2)))) x. p = Inr p2 \<or> (\<exists>xa. p \<in> inputs (comp_op wire buf (f1 x) (f2 xa))))) (f2 x)))))"
  apply (drule aux2[where op="f2 y"])
  oops

lemma input_depth_com_op_arg_min_le_3[simp]:
  "p \<in> inputs (comp_op wire buf (f1 x) (f2 y)) \<Longrightarrow>
  input_depth p (comp_op wire buf 
  (f1 (ARG_MIN (input_depth p \<circ> (\<lambda>x. comp_op wire buf (f1 x) (f2 y))) x. p \<in> inputs (comp_op wire buf (f1 x) (f2 y))))
  (f2 (ARG_MIN (input_depth p \<circ> (\<lambda>y. comp_op wire buf (f1 x) (f2 y))) xa. p \<in> inputs (comp_op wire buf (f1 x) (f2 xa)))))
  \<le> input_depth p (comp_op wire buf (f1 x) (f2 y))"
  oops

lemma input_depth_Read_diff'[simp]: 
  "p \<noteq> p' \<Longrightarrow> p \<in> inputs (f x) \<Longrightarrow>
   input_depth p (Read p' f) = Suc (input_depth p (f (arg_min (input_depth p o f) (\<lambda>x. p \<in> inputs (f x)))))"
  by (metis input_depth_Read_diff)

lemma input_depth_comp_op_le_3[simp]:
  "p \<in> inputs (comp_op wire buf (f1 x) (f2 y)) \<Longrightarrow>
   p \<noteq> Inl p1 \<Longrightarrow>
   p \<noteq> Inr p2 \<Longrightarrow>
   p2 \<notin> ran wire \<Longrightarrow>
   input_depth p
                 (comp_op wire buf
                   (f1 (ARG_MIN (input_depth p \<circ> (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2)))) x.
                           p \<in> inputs (Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 x) (f2 y2)))))
                   (f2 (ARG_MIN (input_depth p \<circ>
                                 (\<lambda>y2. comp_op wire buf
                                        (f1 (ARG_MIN (input_depth p \<circ> (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2)))) x.
                                                p \<in> inputs (Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 x) (f2 y2)))))
                                        (f2 y2))) x.
                           p \<in> inputs
                                 (comp_op wire buf
                                   (f1 (ARG_MIN (input_depth p \<circ> (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2)))) x.
                                           p \<in> inputs (Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 x) (f2 y2)))))
                                   (f2 x))))) < input_depth p (comp_op wire buf (Read p1 f1) (Read p2 f2))"
  apply auto
         apply (subst input_depth_Read_diff)
    apply blast
   apply auto
           apply (subst input_depth_Read_diff)
    apply blast
   apply auto
  apply (smt (verit, best) arg_min_natI)
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
    apply (subst (asm) input_depth_Read_diff')
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
      apply (force intro!: le_SucI)+
    done
  subgoal
      apply (force intro!: le_SucI)+
    done
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
      apply (cases op1; cases op2)
              apply (auto split: if_splits option.splits simp: input_depth_Write input_depth_Read_diff)
      subgoal for p1 f1 p2 f2 x
        apply (rule ccontr)
        apply (insert prems(1))
        apply fastforce
        done
      subgoal for p1 f1 p2 f2 x y
        apply (rule ccontr)
        apply (drule sym)
        apply (insert prems(1))
        apply hypsubst_thin
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply (rule input_depth_comp_op_le_3)
            apply assumption+
          apply auto
        apply (drule meta_mp)
         apply auto[2]


        oops

end


         apply simp
                 apply (subst input_depth_Read_diff)
          apply blast
         apply force
         apply (subst input_depth_Read_diff)
           apply fast
        apply simp
          apply (smt (verit, del_insts) Diff_iff arg_min_natI image_iff insertI1)
         apply simp
        apply (simp flip: Suc_le_eq)
         apply (rule le_SucI)
         apply (rule order_refl)
        apply auto
        apply hypsubst_thin
        apply (drule meta_mp)
        apply (smt (verit, del_insts) DiffI arg_min_natI image_iff insertI1)
        apply auto
        done
      subgoal for p1 f1 op2' p2 x2 x
        apply (rule ccontr)
        apply (insert prems(1))


        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply hypsubst
        using le_Suc_eq apply auto[1]
         apply auto
        

end
        done
      subgoal for p1 f1 x
        apply (rule ccontr)
        apply (subst (asm) input_depth_Read_diff; auto simp: less_Suc_eq_le simp flip: inputs_alt)
        apply (insert prems(1))
        apply (drule meta_spec)+
        apply (drule meta_mp)
        apply blast
        apply (drule meta_mp)
         apply (smt (verit, del_insts) DiffI arg_min_nat_lemma image_iff inputs_alt insertI1)
        apply auto
        done
      subgoal using prems(1) by fastforce
      subgoal for op1' p1 x1 f2 p2 i j
        apply (drule comp_producing_inject, assumption)
        apply hypsubst_thin
        apply (insert prems(1))
        apply (rotate_tac 4)
        apply (erule comp_producing.cases)
                   apply simp_all
        apply (drule comp_producing_inputs_comp_op)
           apply assumption+
         apply blast
        apply blast
        done
      subgoal for op1' p1 x1 f2 p2 i j
        apply (drule comp_producing_inject, assumption)
        apply hypsubst_thin
        apply (insert prems(1))
        apply (rotate_tac 4)
        apply (erule comp_producing.cases)
                   apply simp_all
        apply (drule comp_producing_inputs_comp_op)
           apply assumption+
         apply blast
        apply blast
        done
      subgoal
        apply (insert prems(1))
        apply simp
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply (subst input_depth_Read_diff)
           apply blast
          apply (smt (verit, del_insts) arg_min_natI image_insert insertI1 insert_Diff_if)
         apply (rule le_SucI)
         apply (rule order_refl)
        apply (drule meta_mp)
         apply (smt (verit, del_insts) DiffI arg_min_nat_lemma image_iff inputs_alt insertI1)
        apply blast
        done
      subgoal
        apply (rule ccontr)
        apply (subst (asm) input_depth_Read_diff; auto simp: simp flip: inputs_alt)
        apply (insert prems(1))
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply hypsubst
        apply (rule order_refl)
        apply (drule meta_mp)
         apply (smt (verit, del_insts) arg_min_natI image_insert insertI1 insert_Diff_if)
        apply auto
        done
      subgoal
        apply (insert prems(1))
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply hypsubst
        apply (rule le_SucI)
         apply (rule order_refl)
        apply auto
        done
      subgoal using prems(1) by fastforce
      subgoal using prems(1) by fastforce
      subgoal
        apply (drule comp_producing_inject, assumption)
        apply hypsubst_thin
        apply (insert prems(1))
        apply (rotate_tac 4)
        apply (erule comp_producing.cases)
                   apply simp_all
        apply (drule comp_producing_inputs_comp_op)
           apply assumption+
         apply blast
        apply auto
        done
      subgoal using prems(1) by fastforce
      subgoal
        apply (drule comp_producing_inject, assumption)
        apply hypsubst_thin
        apply (insert prems(1))
        apply (rotate_tac 4)
        apply (erule comp_producing.cases)
                   apply simp_all
        apply (drule comp_producing_inputs_comp_op)
           apply assumption+
         apply blast
        apply force
        done
      subgoal
        apply (subst (asm) input_depth_Read_diff; auto simp: less_Suc_eq_le simp flip: inputs_alt)
        apply (insert prems(1))
        apply (drule meta_spec)+
        apply (drule meta_mp)
        apply blast
        apply (drule meta_mp)
         apply (smt (verit, del_insts) DiffI arg_min_nat_lemma image_iff inputs_alt insertI1)
        apply auto
        done
      subgoal using prems(1) by fastforce
      done
    done
  done

lemma inputs_comp_op_le:
  "inputs (comp_op wire buf op1 op2) \<subseteq> Inl ` inputs op1 \<union> Inr ` (inputs op2 - ran wire)"
  using inputs_comp_op by blast

lemma outputs_comp_op:
  "outputs (comp_op wire buf op1 op2) \<subseteq> Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2"
  sorry (* Rafael *)

lemma comp_producing_silentD: "comp_producing wire buf op1 op2 n \<Longrightarrow>
  wire p = None \<Longrightarrow>
  silent p op1 (lxs \<circ> Inl) \<Longrightarrow>
  comp_op wire buf op1 op2 = End \<or>
  (\<exists>op'. comp_op wire buf op1 op2 = Write op' (Inl p) EOS) \<or>
  (\<exists>f p'. comp_op wire buf op1 op2 = Read p' f \<and>
    silent_cong (Inl p) (\<lambda>op lxs. \<exists>buf op1. (\<exists>op2. op = comp_op wire buf op1 op2) \<and> silent p op1 (lxs \<circ> Inl)) (f (CHD p' lxs)) (CTL p' lxs)) \<or>
  (\<exists>p' op'. (\<exists>x. comp_op wire buf op1 op2 = Write op' p' x) \<and> Inl p \<noteq> p' \<and>
    silent_cong (Inl p) (\<lambda>op lxs. \<exists>buf op1. (\<exists>op2. op = comp_op wire buf op1 op2) \<and> silent p op1 (lxs \<circ> Inl)) op' lxs)"
  apply (induct buf op1 op2 n arbitrary: lxs pred: comp_producing)
             apply (auto 4 0 simp: Let_def elim!: contrapos_np[of "silent_cong _ _ _ _"]
      elim!: silent_cong[THEN iffD1, rotated -1] split: option.splits
      intro!: silent_cong.write silent_cong.read intro: silent_cong.base)
            apply (rule silent_cong.base)
            apply (rule exI conjI refl)+
            apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
           apply (rule silent_cong.base)
           apply (rule exI conjI refl)+
           apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
          apply (rule silent_cong.base)
          apply (rule exI conjI refl)+
          apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
         apply (rule silent_cong.base)
         apply (rule exI conjI refl)+
         apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
        apply (rule silent_cong.base)
        apply (rule exI conjI refl)+
        apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
       apply (rule silent_cong.base)
       apply (rule exI conjI refl)+
       apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
      apply (rule silent_cong.base)
      apply (rule exI conjI refl)+
      apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
     apply (rule silent_cong.base)
     apply (rule exI conjI refl)+
     apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
    apply (rule silent_cong.base)
    apply (rule exI conjI refl)+
    apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
   apply (drule meta_spec, drule meta_mp, assumption)
   apply auto []
  apply (drule meta_spec, drule meta_mp, assumption)
  apply auto []
  done
(*
comp_producing wire (buf(q' := btl (benq x (buf q')))) op' (f (bhd (benq x (buf q')))) m \<Longrightarrow>
    wire p = Some q \<Longrightarrow>
    comp_op wire (buf(q' := btl (benq x (buf q')))) op' (f (bhd (benq x (buf q')))) \<noteq> End \<Longrightarrow>
    \<forall>op'a.
       comp_op wire (buf(q' := btl (benq x (buf q')))) op' (f (bhd (benq x (buf q')))) \<noteq>
       Write op'a (Inl p) EOS \<Longrightarrow>
    \<forall>fa p'.
       comp_op wire (buf(q' := btl (benq x (buf q')))) op' (f (bhd (benq x (buf q')))) = Read p' fa \<longrightarrow>
       \<not> silent_cong (Inl p) (\<lambda>op__ _. \<exists>buf op1 op2. op__ = comp_op wire buf op1 op2) (fa (chd (lxs p')))
           (lxs(p' := ctl (lxs p'))) \<Longrightarrow>
    q' \<in> ran wire \<Longrightarrow>
    wire p' = Some q' \<Longrightarrow>
    \<exists>p' op'a.
       (\<exists>xa. comp_op wire (buf(q' := btl (benq x (buf q')))) op' (f (bhd (benq x (buf q')))) =
             Write op'a p' xa) \<and>
       Inl p \<noteq> p' \<and> silent_cong (Inl p) (\<lambda>op__ _. \<exists>buf op1 op2. op__ = comp_op wire buf op1 op2) op'a lxs
*)

lemma silent_on_non_output: "p \<notin> outputs op \<Longrightarrow> silent p op lxs"
  apply (coinduction arbitrary: op lxs)
  subgoal for op lxs
    by (cases op) auto
  done

corec (friend) lshift :: "'a list \<Rightarrow> 'a llist \<Rightarrow> 'a llist" (infixr \<open>@@-\<close> 65) where
  "lshift xs ys = (case xs of [] \<Rightarrow> (case ys of LNil \<Rightarrow> LNil | LCons y' ys' \<Rightarrow> LCons y' ys') | x#xs \<Rightarrow> LCons x (lshift xs ys))"

lemma lshift_simps[simp]:
  "lshift [] lxs = lxs"
  "lshift (x#xs) lxs = LCons x (lshift xs lxs)"
  by (subst lshift.code; auto split: llist.splits)+

lemma snoc_shift[simp]: "(xs @ [x]) @@- ws = xs @@- LCons x ws"
  by (induct xs) auto

coinductive cembed where
  "cembed LNil (llist_of (replicate n No_Value))"
| "cembed xs ys \<Longrightarrow> cembed (LCons x xs) (replicate n No_Value @@- LCons x ys)"

fun ch_of_buf where
  "ch_of_buf BEmpty = []"
| "ch_of_buf BEnded = []"
| "ch_of_buf (BCons xs buf) = map Value xs @ No_Value # ch_of_buf buf"

consts produce_compL_producing :: "'ip2 \<Rightarrow> ('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> ('ip1 + 'ip2 \<Rightarrow> 'd channel) \<Rightarrow> nat \<Rightarrow> bool"

corecursive produce_compL :: "'ip2 \<Rightarrow> ('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> ('ip1 + 'ip2 \<Rightarrow> 'd channel) \<Rightarrow> 'd channel" where
  "produce_compL p wire buf op1 op2 lxs = (let
     produce_compL' = (\<lambda>buf' op1' op2' lxs'.
     if \<exists>n. produce_compL_producing p wire buf op1 op2 lxs n then produce_compL p wire buf' op1' op2' lxs' else LNil);
     produce_compL'' = (\<lambda>p2 x buf' op1' op2' lxs'. if p = p2 then VCons x (produce_compL p wire buf' op1' op2' lxs')
       else produce_compL' buf' op1' op2' lxs')
   in case (op1, op2) of
     (End, End) \<Rightarrow> LNil
   | (End, Write op2' p2 x2) \<Rightarrow> produce_compL' (bend o buf) End op2' lxs
   | (End, Read p2 f2) \<Rightarrow> let buf' = bend o buf in if p2 \<in> ran wire
     then produce_compL'' p2 (BHD p2 buf') (BTL p2 buf') End (f2 (BHD p2 buf')) lxs
     else produce_compL' buf' End (f2 (CHD (Inr p2) lxs)) (CTL (Inr p2) lxs)
   | (Read p1 f1, End) \<Rightarrow> produce_compL' buf (f1 (CHD (Inl p1) lxs)) End (CTL (Inl p1) lxs)
   | (Read p1 f1, Write op2' p2 x2) \<Rightarrow> produce_compL' buf (f1 (CHD (Inl p1) lxs)) op2' (CTL (Inl p1) lxs)
   | (Read p1 f1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then produce_compL'' p2 (BHD p2 buf) (BTL p2 buf) (f1 (CHD (Inl p1) lxs)) (f2 (BHD p2 buf)) (CTL (Inl p1) lxs)
     else produce_compL' buf (f1 (CHD (Inl p1) lxs)) (f2 (CHD (Inr p2) lxs)) (CTL (Inr p2) (CTL (Inl p1) lxs))
   | (Write op1' p1 x1, End) \<Rightarrow> produce_compL' buf op1' End lxs
   | (Write op1' p1 x1, Write op2' p2 x2) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> produce_compL' buf op1' op2' lxs
     | Some p \<Rightarrow> produce_compL' (BENQ p x1 buf) op1' op2' lxs)
   | (Write op1' p1 x1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then (case wire p1 of
       None \<Rightarrow> produce_compL'' p (BHD p2 buf) (BTL p2 buf) op1' (f2 (BHD p2 buf)) lxs
     | Some p \<Rightarrow> produce_compL'' p (BHD p2 (BENQ p2 x1 buf)) (BTL p2 (BENQ p x1 buf)) op1' (f2 (BHD p2 (BENQ p x1 buf))) lxs)
     else (case wire p1 of
       None \<Rightarrow> produce_compL' buf op1' (f2 (CHD (Inr p2) lxs)) (CTL (Inr p2) lxs)
     | Some p \<Rightarrow> produce_compL' (BENQ p x1 buf) op1' (f2 (CHD (Inr p2) lxs)) (CTL (Inr p2) lxs))
)"
  sorry

lemma produce_comp_op:
   "produce p (comp_op wire buf op1 op2) lxs = (case p of
    Inl p1 \<Rightarrow> (if p1 \<in> dom wire then LNil else
      produce p1 op1 (lxs o Inl))
  | Inr p2 \<Rightarrow> produce p2 op2
      (\<lambda> p'. if p' \<in> ran wire then produce_compL p' wire buf op1 op2 lxs else lxs (Inr p')))"
  apply (coinduction arbitrary: buf op1 op2 lxs rule: llist.coinduct_upto)
  apply (split sum.splits if_splits)+
  unfolding lnull_def lnull_produce_iff_silent not_silent_iff_vocal
  apply safe
  subgoal for buf op1 op2 lxs p q
    apply (rule silent_on_non_output)
    apply (auto dest: set_mp[OF outputs_comp_op])
    done
  subgoal for buf op1 op2 lxs p
    apply (coinduction arbitrary: buf op1 op2 lxs rule: silent_coinduct_upto)
    subgoal for buf op1 op2 lxs
      apply (cases op1; cases op2)
              apply (auto split: option.splits if_splits simp: Let_def
          elim!: contrapos_np[of "silent_cong _ _ _ _"] intro!: silent_cong.write silent_cong.read intro: silent_cong.base)
                 apply (rule silent_cong.base)
                 apply (rule exI conjI[rotated] | assumption)+
                 apply auto []
                apply (rule silent_cong.base)
                apply (rule exI conjI[rotated] | assumption)+
                apply auto []
               apply (rule silent_cong.base)
               apply (rule exI conjI[rotated] | assumption)+
               apply auto []
              apply (rule silent_cong.base)
              apply (rule exI conjI[rotated] | assumption)+
              apply auto []
             apply (rule silent_cong.base)
             apply (rule exI conjI[rotated] | assumption)+
             apply auto []
            apply (rule silent_cong.base)
            apply (rule exI conjI[rotated] | assumption)+
            apply auto []
           apply (auto dest!: not_comp_producing_eq_End simp del: comp_op_simps simp add: comp_op_simps' split: if_splits) [2]
             apply (rule silent_cong.base)
             apply (rule exI conjI refl | erule ssubst)+
             apply (rule silent.intros)
            apply (rule silent_cong.base)
            apply (rule exI conjI refl | erule ssubst)+
            apply (rule silent.intros)
           apply (rule silent_cong.base)
           apply (rule exI conjI refl | erule ssubst)+
           apply (rule silent.intros)
          apply (rule silent_cong.base)
          apply (rule exI conjI refl | erule ssubst)+
          apply (rule silent.intros)
         apply (rule silent_cong.base)
         apply (rule exI conjI[rotated] | assumption)+
         apply auto []
        apply (rule silent_cong.base)
        apply (rule exI conjI[rotated] | assumption)+
        apply auto []
       apply (auto dest!: not_comp_producing_eq_End simp del: comp_op_simps simp add: comp_op_simps' split: if_splits) [2]
       apply (rule silent_cong.base)
       apply (rule exI conjI refl | erule ssubst)+
       apply (rule silent.intros)
      apply (rule silent_cong.base)
      apply (rule exI conjI refl | erule ssubst)+
      apply (rule silent.intros)
      done
    done
  subgoal for buf op1 op2 lxs p
    apply (coinduction arbitrary: buf op1 op2 lxs rule: silent_coinduct_upto)
    subgoal for buf op1 op2 lxs
      apply (cases op1; cases op2)
              apply (auto split: option.splits if_splits simp: Let_def
          elim!: contrapos_np[of "silent_cong _ _ _ _"] intro!: silent_cong.write silent_cong.read intro: silent_cong.base)
                   apply (rule silent_cong.base)
                   apply (rule exI conjI refl)+
                   apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
                  apply (rule silent_cong.base)
                  apply (rule exI conjI refl)+
                  apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
                 apply (rule silent_cong.base)
                 apply (rule exI conjI refl)+
                 apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
                apply (rule silent_cong.base)
                apply (rule exI conjI refl)+
                apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
               apply (rule silent_cong.base)
               apply (rule exI conjI refl)+
               apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
              apply (rule silent_cong.base)
              apply (rule exI conjI refl)+
              apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
             apply (erule comp_producing.cases; simp)
             apply (blast dest: comp_producing_silentD)
            apply (rule silent_cong.base)
            apply (rule exI conjI refl)+
            apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
           apply (rule silent_cong.base)
           apply (rule exI conjI refl)+
           apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
          apply (erule comp_producing.cases; simp)
          apply (blast dest: comp_producing_silentD)
         apply (rule silent_cong.base)
         apply (rule exI conjI refl)+
         apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
        apply (rule silent_cong.base)
        apply (rule exI conjI refl)+
        apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
       apply (erule comp_producing.cases; simp)
       apply (blast dest: comp_producing_silentD)
      apply (erule comp_producing.cases; simp)
      apply (blast dest: comp_producing_silentD)
      done
    done
  subgoal for buf op1 op2 lxs p
    sorry
  subgoal for buf op1 op2 lxs p
    sorry
  subgoal for buf op1 op2 lxs p
    sorry
  subgoal for buf op1 op2 lxs p
    sorry
  subgoal for buf op1 op2 lxs p
    sorry
  subgoal for buf op1 op2 lxs p
    sorry
  done

lemma produce_comp_op:
   "\<exists>lzs. (\<forall>p'. cembed (produce p' (map_op id (case_option undefined id o wire) op1) (lxs o Inl)) (lzs p')) \<and>
    produce p (comp_op wire buf op1 op2) lxs = (case p of
    Inl p1 \<Rightarrow> (if p1 \<in> dom wire then LNil else
      produce p1 op1 (lxs o Inl))
  | Inr p2 \<Rightarrow> produce p2 op2
      (\<lambda> p'. if p' \<in> ran wire then ch_of_buf (buf p') @@- lzs p' else lxs (Inr p')))"
(*TODO*)
  oops
  apply (coinduction arbitrary: buf op1 op2 lxs rule: llist.coinduct_upto)
  apply (split sum.splits if_splits)+
  unfolding lnull_def lnull_produce_iff_silent not_silent_iff_vocal
  apply safe
  subgoal for buf op1 op2 lxs p q
    apply (rule silent_on_non_output)
    apply auto
    done
  subgoal for buf op1 op2 lxs p
    apply (coinduction arbitrary: buf op1 op2 lxs rule: silent_coinduct_upto)
    subgoal for buf op1 op2 lxs
      apply (cases op1; cases op2)
              apply (auto split: option.splits if_splits simp: Let_def
          elim!: contrapos_np[of "silent_cong _ _ _ _"] intro!: silent_cong.write silent_cong.read intro: silent_cong.base)
                 apply (rule silent_cong.base)
                 apply (rule exI conjI[rotated] | assumption)+
                 apply auto []
                apply (rule silent_cong.base)
                apply (rule exI conjI[rotated] | assumption)+
                apply auto []
               apply (rule silent_cong.base)
               apply (rule exI conjI[rotated] | assumption)+
               apply auto []
              apply (rule silent_cong.base)
              apply (rule exI conjI[rotated] | assumption)+
              apply auto []
             apply (rule silent_cong.base)
             apply (rule exI conjI[rotated] | assumption)+
             apply auto []
            apply (rule silent_cong.base)
            apply (rule exI conjI[rotated] | assumption)+
            apply auto []
           apply (auto dest!: not_comp_producing_eq_End simp del: comp_op_simps simp add: comp_op_simps' split: if_splits) [2]
             apply (rule silent_cong.base)
             apply (rule exI conjI refl | erule ssubst)+
             apply (rule silent.intros)
            apply (rule silent_cong.base)
            apply (rule exI conjI refl | erule ssubst)+
            apply (rule silent.intros)
           apply (rule silent_cong.base)
           apply (rule exI conjI refl | erule ssubst)+
           apply (rule silent.intros)
          apply (rule silent_cong.base)
          apply (rule exI conjI refl | erule ssubst)+
          apply (rule silent.intros)
         apply (rule silent_cong.base)
         apply (rule exI conjI[rotated] | assumption)+
         apply auto []
        apply (rule silent_cong.base)
        apply (rule exI conjI[rotated] | assumption)+
        apply auto []
       apply (auto dest!: not_comp_producing_eq_End simp del: comp_op_simps simp add: comp_op_simps' split: if_splits) [2]
       apply (rule silent_cong.base)
       apply (rule exI conjI refl | erule ssubst)+
       apply (rule silent.intros)
      apply (rule silent_cong.base)
      apply (rule exI conjI refl | erule ssubst)+
      apply (rule silent.intros)
      done
    done
  subgoal for buf op1 op2 lxs p
    apply (coinduction arbitrary: buf op1 op2 lxs rule: silent_coinduct_upto)
    subgoal for buf op1 op2 lxs
      apply (cases op1; cases op2)
              apply (auto split: option.splits if_splits simp: Let_def
          elim!: contrapos_np[of "silent_cong _ _ _ _"] intro!: silent_cong.write silent_cong.read intro: silent_cong.base)
                   apply (rule silent_cong.base)
                   apply (rule exI conjI refl)+
                   apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
                  apply (rule silent_cong.base)
                  apply (rule exI conjI refl)+
                  apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
                 apply (rule silent_cong.base)
                 apply (rule exI conjI refl)+
                 apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
                apply (rule silent_cong.base)
                apply (rule exI conjI refl)+
                apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
               apply (rule silent_cong.base)
               apply (rule exI conjI refl)+
               apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
              apply (rule silent_cong.base)
              apply (rule exI conjI refl)+
              apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
             apply (erule comp_producing.cases; simp)
             apply (blast dest: comp_producing_silentD)
            apply (rule silent_cong.base)
            apply (rule exI conjI refl)+
            apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
           apply (rule silent_cong.base)
           apply (rule exI conjI refl)+
           apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
          apply (erule comp_producing.cases; simp)
          apply (blast dest: comp_producing_silentD)
         apply (rule silent_cong.base)
         apply (rule exI conjI refl)+
         apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
        apply (rule silent_cong.base)
        apply (rule exI conjI refl)+
        apply (auto elim: silent_cong[THEN iffD1, rotated -1]) []
       apply (erule comp_producing.cases; simp)
       apply (blast dest: comp_producing_silentD)
      apply (erule comp_producing.cases; simp)
      apply (blast dest: comp_producing_silentD)
      done
    done
  subgoal for buf op1 op2 lxs p
    sorry
  subgoal for buf op1 op2 lxs p
    sorry
  subgoal for buf op1 op2 lxs p
    sorry
  subgoal for buf op1 op2 lxs p
    sorry
  subgoal for buf op1 op2 lxs p
    sorry
  subgoal for buf op1 op2 lxs p
    sorry
  done

lemma "produce p (loop_op wire buf op) lxs =
  (THE lzs. \<forall>p. lzs p = produce p (map_op id (todo) op)
     (\<lambda>p. if p \<in> ran wire then lapp (buf p1) (lzs p2) else lxs p3)) p"
  oops

lemma loop_op_unfold:
  "loop_op wire buf op = map_op (case_sum id id) projr (comp_op wire (\<lambda> x. BEmpty) (read_op (ran wire) buf op) (loop_op wire buf op))"
  oops

  term "loop_op wire buf"

  term "Nat.funpow n (\<lambda> op. map_op (case_sum id id) projr (comp_op wire buf op op))"

  typ enat


  term "(comp_op wire2 buf2 ^^ n) op op"
  term "(map_op (case_sum id id) projr (comp_op wire2 buf2 op op) ^^ n)"
  term enat_unfold



(*   apply (coinduction arbitrary: buf op rule: op.coinduct_strong)
  subgoal for buf op
    apply (cases op)
    subgoal for ip f
      apply auto *)

(*
lemma "producing p op lxs i \<Longrightarrow> \<forall>p. lprefix (lxs p) (lxs' p) \<Longrightarrow> producing p op lxs' i"
proof (induct p op lxs i arbitrary: lxs' rule: producing.induct)
  case (3 p f lxs p' i)
  then show ?case
    apply (intro producing.intros)
    
    sorry
qed (auto intro: producing.intros)


lemma "\<forall>p. lprefix (lxs p) (lxs' p) \<Longrightarrow> lprefix (produce p op lxs) (produce op lxs' p)"
  apply (coinduction arbitrary: op lxs lxs' p)
  subgoal for op lxs lxs' p
    apply safe
    subgoal sorry
    subgoal
      apply (subst (1 2) produce.code)
      apply (auto split: op.splits if_splits)
      sorry
    subgoal sorry
    done
    apply (subst (asm) (1) produce.code)
      apply (auto split: op.splits if_splits)
*)

(*
fun produce_loop where
  "produce_loop (0 :: nat) wire op lxs p = produce op (\<lambda>p'. if p' \<in> ran wire then LNil else lxs p') p"
| "produce_loop (Suc n) wire op lxs p = produce op (\<lambda>p'. if p' \<in> ran wire then produce_loop n wire op lxs p else lxs p') p"

lemma "produce (comp_op wire buf op1 op2) lxs p = (case p of
    Inl p1 \<Rightarrow> (if p1 \<in> dom wire then LNil else
      produce op1 (\<lambda>p1'. if Inl p1' \<in> ran wire then undefined else lxs (Inl p1')) p1)
  | Inr p2 \<Rightarrow> produce op2 (\<lambda>p2'. if Inr p2' \<in> ran wire then undefined else lxs (Inr p2')) p2)"
  oops
*)

definition "pcomp_op = comp_op (\<lambda>_. None) (\<lambda>_. BEnded)"

lemma inputs_pcomp_op[simp]:
  "inputs (pcomp_op op1 op2) = Inl ` inputs op1 \<union> Inr ` inputs op2"
  unfolding pcomp_op_def by auto

lemma outputs_pcomp_op[simp]:
  "outputs (pcomp_op op1 op2) = Inl ` outputs op1 \<union> Inr ` outputs op2"
  unfolding pcomp_op_def by auto

lemma produce_pcomp_op:
  "produce p (pcomp_op op1 op2) lxs =
    (case p of Inl p1 \<Rightarrow> produce p1 op1 (lxs o Inl) | Inr p2 \<Rightarrow> produce p2 op2 (lxs o Inr))"
  unfolding produce_comp_op pcomp_op_def
  by (auto split: sum.splits simp add: o_def)

definition "scomp_op op1 op2 = map_op projl projr (comp_op Some (\<lambda>_. BEmpty) op1 op2)"

lemma inputs_scomp_op[simp]:
  "inputs (scomp_op op1 op2) = inputs op1"
  unfolding scomp_op_def by (force simp: op.set_map ran_def)

lemma outputs_scomp_op[simp]:
  "outputs (scomp_op op1 op2) = outputs op2"
  unfolding scomp_op_def by (force simp: op.set_map ran_def)

lemma produce_scomp_op:
  "produce p (scomp_op op1 op2) lxs = produce p op2 (\<lambda>p. produce p op1 lxs)"
  unfolding scomp_op_def fun_eq_iff
  by (subst produce_map_op[where g=projl and h'=Inr and h=projr, simplified])
    (auto split: sum.splits simp add: ranI o_def id_def op.map_ident inj_on_def produce_comp_op)

type_synonym 'd op22 = "(2, 2, 'd) op"
type_synonym 'd op11 = "(1, 1, 'd) op"

coinductive welltyped where
  "welltyped A B (f EOB) \<Longrightarrow> welltyped A B (f EOS) \<Longrightarrow> \<forall>x \<in> A p. welltyped A B (f (Observed x)) \<Longrightarrow> welltyped A B (Read p f)"
| "x \<in> B p \<Longrightarrow> welltyped A B op \<Longrightarrow> welltyped A B (Write op p (Observed x))"
| "welltyped A B op \<Longrightarrow> welltyped A B (Write op p EOS)"
| "welltyped A B op \<Longrightarrow> welltyped A B (Write op p EOB)"
| "welltyped A B End"

(*characteristic property of welltyped*)
lemma "welltyped A B op \<Longrightarrow> (\<forall>p. (\<Union> (the_value ` lset (lxs p))) \<subseteq> A p) \<Longrightarrow> (\<Union> (the_value ` lset (produce p op lxs))) \<subseteq> B p"
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


