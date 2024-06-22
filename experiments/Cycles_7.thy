theory Cycles_7
  imports Coinductive.Coinductive_List
    "HOL-Library.BNF_Corec"
    "HOL-Library.Code_Lazy"
    "HOL-Library.Simps_Case_Conv"
    Coinductive.Coinductive_Nat
    "HOL-Library.Debug"
begin

code_lazy_type llist

datatype (discs_sels) 'd input = Input 'd | NoInput | EOS
codatatype (inputs: 'ip, outputs: 'op, dead 'd) op =
    Read 'ip "'d input \<Rightarrow> ('ip, 'op, 'd) op"
  | Write "('ip, 'op, 'd) op" 'op 'd
  | End

code_lazy_type op

fun lhd' where
  "lhd' LNil = EOS"
| "lhd' (LCons x lxs) = Input x"

inductive producing where
  "producing End lxs p 0"
| "producing (Write _ p _) lxs p 0"
| "producing (f (lhd' (lxs p'))) (lxs(p' := ltl (lxs p'))) p i \<Longrightarrow> producing (Read p' f) lxs p (Suc i)"
| "p \<noteq> p' \<Longrightarrow> producing op lxs p i \<Longrightarrow> producing (Write op p' x) lxs p (Suc i)"

lemma producing_inject: "producing op lxs p i \<Longrightarrow> producing op lxs p j \<Longrightarrow> i = j"
proof (induct op lxs p i arbitrary: j rule: producing.induct)
  case (3 f lxs p' p i)
  from 3(3,1) 3(2)[of "j - 1"] show ?case
    by (elim producing.cases[of "Read p' f"]) (auto simp del: fun_upd_apply)
next
  case (4 p p' op lxs i x)
  from 4(4,1,2) 4(3)[of "j - 1"] show ?case
    by (elim producing.cases[of "Write op p' x"]) auto
qed (auto elim: producing.cases)

lemma The_producing: "producing p op lxs i \<Longrightarrow> The (producing p op lxs) = i"
  using producing_inject by fast

corecursive produce where
  "produce op lxs p = (case op of
    Read p' f \<Rightarrow> (if \<exists>i. producing op lxs p i then produce (f (lhd' (lxs p'))) (lxs(p' := ltl (lxs p'))) p else LNil)
  | Write op' p' x \<Rightarrow> (if p = p' then LCons x (produce op' lxs p) else
     if \<exists>i. producing op lxs p i then produce op' lxs p else LNil)
  | End \<Rightarrow> LNil)"
  by (relation "measure (\<lambda>(op, lxs, p). THE i. producing op lxs p i)")
    (auto 0 3 simp: The_producing elim: producing.cases)

lemma produce_code[code]:
  "produce op lxs p = (case op of                    
    Read p' f \<Rightarrow> produce (f (lhd' (lxs p'))) (lxs(p' := ltl (lxs p'))) p
  | Write op' p' x \<Rightarrow> (if p = p' then LCons x (produce op' lxs p) else produce op' lxs p)
  | End \<Rightarrow> LNil)"
  apply (subst produce.code)
  apply (simp split: op.splits)
  apply safe
  subgoal for p' f
    by (subst produce.code) (auto 0 4 split: op.splits intro: producing.intros)
  subgoal for op p x
    by (subst produce.code) (auto 0 4 split: op.splits intro: producing.intros)
  done

simps_of_case produce_simps[simp]: produce_code

coinductive silent where
  "silent End lxs p"
| "p \<noteq> p' \<Longrightarrow> silent op' lxs p \<Longrightarrow> silent (Write op' p' x) lxs p"
| "silent (f (lhd' (lxs p'))) (lxs(p' := ltl (lxs p'))) p \<Longrightarrow> silent (Read p' f) lxs p"

lemma lnull_produce_silent: "lnull (produce op lxs p) \<Longrightarrow> silent op lxs p"
  apply (coinduction arbitrary: op lxs)
  apply (subst produce_code)
  subgoal for op lxs
    apply (cases op)
      apply (auto split: if_splits op.splits)
    done
  done

lemma producing_silent_LNil: "producing op lxs p n \<Longrightarrow> silent op lxs p \<Longrightarrow> produce op lxs p = LNil"
  by (induct op lxs p n rule: producing.induct) (auto elim: silent.cases)

lemma silent_produce_LNil: "silent op lxs p \<Longrightarrow> produce op lxs p = LNil"
  by (subst produce.code)
    (auto split: op.splits elim: silent.cases dest: producing_silent_LNil)

lemma lnull_produce_iff_silent: "lnull (produce op lxs p) \<longleftrightarrow> silent op lxs p"
  using lnull_produce_silent silent_produce_LNil by fastforce

datatype 'd buf = BEmpty | BEnded | BCons 'd (btl: "'d buf")
  where "btl BEmpty = BEmpty" | "btl BEnded = BEnded"

fun bhd' where
  "bhd' BEmpty = NoInput"
| "bhd' BEnded = EOS"
| "bhd' (BCons x xs) = Input x"

fun bend where
  "bend BEmpty = BEnded"
| "bend BEnded = BEnded"
| "bend (BCons x xs) = BCons x (bend xs)"

fun benq where
  "benq x BEmpty = BCons x BEmpty"
| "benq x BEnded = BCons x BEnded"
| "benq x (BCons y ys) = BCons y (benq x ys)"

inductive loop_producing :: "('op \<rightharpoonup> 'ip) \<Rightarrow> ('ip \<Rightarrow> 'd buf) \<Rightarrow> ('ip, 'op, 'd) op \<Rightarrow> nat \<Rightarrow> bool" where
  "loop_producing wire buf End 0"
| "p \<notin> ran wire \<Longrightarrow> loop_producing wire buf (Read p f) 0"
| "wire p' = None \<Longrightarrow> loop_producing wire buf (Write op p' x) 0"
| "p \<in> ran wire \<Longrightarrow> loop_producing wire (buf(p := btl (buf p))) (f (bhd' (buf p))) n \<Longrightarrow> loop_producing wire buf (Read p f) (Suc n)"
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
  "loop_op wire buf op = (case op of
     End \<Rightarrow> End
   | Read p f \<Rightarrow> if p \<in> ran wire
       then (if \<exists>n. loop_producing wire buf op n then loop_op wire (buf(p := btl (buf p))) (f (bhd' (buf p))) else End)
       else Read p (\<lambda>x. loop_op wire buf (f x))
   | Write op' p' x \<Rightarrow> (case wire p' of
         None \<Rightarrow> Write (loop_op wire buf op') p' x
       | Some p \<Rightarrow> (if \<exists>n. loop_producing wire buf op n then loop_op wire (buf(p := benq x (buf p))) op' else End)))"
  by (relation "measure (\<lambda>(wire, buf, op). THE i. loop_producing wire buf op i)")
    (auto 0 3 simp: The_loop_producing elim: loop_producing.cases)

lemma loop_op_code[code]:
  "loop_op wire buf op = (case op of
     End \<Rightarrow> End
   | Read p f \<Rightarrow> if p \<in> ran wire
       then loop_op wire (buf(p := btl (buf p))) (f (bhd' (buf p)))
       else Read p (\<lambda>x. loop_op wire buf (f x))
   | Write op' p' x \<Rightarrow> (case wire p' of
         None \<Rightarrow> Write (loop_op wire buf op') p' x
       | Some p \<Rightarrow> loop_op wire (buf(p := benq x (buf p))) op'))"
  apply (subst loop_op.code)
  apply (simp split: op.splits option.splits)
  apply safe
  subgoal for p f
    by (subst loop_op.code) (auto 0 4 split: op.splits option.splits intro: loop_producing.intros)
  subgoal for op' p' x
    by (subst loop_op.code) (auto 0 4 split: op.splits option.splits intro: loop_producing.intros)
  done
simps_of_case loop_op_simps[simp]: loop_op_code

inductive comp_producing :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow> ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> nat \<Rightarrow> bool" where
  "comp_producing wire buf End End 0"
| "comp_producing wire buf (Read p1 f1) End 0"
| "comp_producing wire buf (Write op1' p1 x1) End 0"
| "comp_producing wire buf End (Write op2' p2 x2) 0"
| "comp_producing wire buf (Read p1 f1) (Write op2' p2 x2) 0"
| "comp_producing wire buf (Write op1' p1 x1) (Write op2' p2 x2) 0"
| "p2 \<notin> ran wire \<Longrightarrow> comp_producing wire buf End (Read p2 f2) 0"
| "p2 \<in> ran wire \<Longrightarrow> comp_producing wire ((bend o buf)(p2 := btl ((bend o buf) p2))) End (f2 (bhd' ((bend o buf) p2))) n \<Longrightarrow> comp_producing wire buf End (Read p2 f2) (Suc n)"
| "comp_producing wire buf (Read p1 f1) (Read p2 f2) 0"
| "p2 \<notin> ran wire \<or> wire p1 = None \<Longrightarrow> comp_producing wire buf (Write op1' p1 x1) (Read p2 f2) 0"
| "p2 \<in> ran wire \<Longrightarrow> wire p1 = Some p2 \<Longrightarrow>
    comp_producing wire (buf(p2 := btl (benq x1 (buf p2)))) op1' (f2 (bhd' (benq x1 (buf p2)))) n \<Longrightarrow>
    comp_producing wire buf (Write op1' p1 x1) (Read p2 f2) (Suc n)"
| "p2 \<in> ran wire \<Longrightarrow> wire p1 = Some p \<Longrightarrow> p \<noteq> p2 \<Longrightarrow>
    comp_producing wire (buf(p := benq x1 (buf p), p2 := btl (buf p2))) op1' (f2 (bhd' (buf p2))) n \<Longrightarrow>
    comp_producing wire buf (Write op1' p1 x1) (Read p2 f2) (Suc n)"

lemma comp_producing_inject: "comp_producing wire buf op1 op2 i \<Longrightarrow> comp_producing wire buf op1 op2 j \<Longrightarrow> i = j"
proof (induct wire buf op1 op2 i arbitrary: j rule: comp_producing.induct)
  case (8 p2 wire buf f2 n)
  from 8(4,1-2) 8(3)[of "j - 1"] show ?case
    by (elim comp_producing.cases[of _ _ _ "Read p2 f2"]) (auto simp del: fun_upd_apply)
next
  case (11 p2 wire p1 buf x1 op1' f2 n)
  from 11(5,1-3) 11(4)[of "j - 1"] show ?case
    by (elim comp_producing.cases[of _ _ _ "Read p2 f2"]) (auto simp del: fun_upd_apply)
next
  case (12 p2 wire p1 p buf x1 op1' f2 n)
  from 12(6,1-4) 12(5)[of "j - 1"] show ?case
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
  "comp_op wire buf op1 op2 = (case (op1, op2) of
     (End, End) \<Rightarrow> End
   | (End, Write op2' p2 x2) \<Rightarrow> Write (comp_op wire (bend o buf) End op2') (Inr p2) (Debug.tracing (String.implode ''hi4'') x2)
   | (End, Read p2 f2) \<Rightarrow> let buf' = bend o buf in if p2 \<in> ran wire
     then if \<exists>n. comp_producing wire buf op1 op2 n then comp_op wire (buf'(p2 := btl (buf' p2))) End (f2 (bhd' (buf' p2))) else End
     else Read (Inr p2) (\<lambda>y2. comp_op wire buf' End (f2 y2))
   | (Read p1 f1, End) \<Rightarrow> Read (Inl p1) (\<lambda>y1. comp_op wire buf (f1 y1) End)
   | (Read p1 f1, Write op2' p2 x2) \<Rightarrow> Read (Inl p1) (\<lambda>y1. Write (comp_op wire buf (f1 y1) op2') (Inr p2) (Debug.tracing (String.implode ''hi3'') x2))
   | (Read p1 f1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then Read (Inl p1) (\<lambda>y1. comp_op wire (buf(p2 := btl (buf p2))) (f1 y1) (f2 (bhd' (buf p2))))
     else Read (Inl p1) (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2)))
   | (Write op1' p1 x1, End) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> Write (comp_op wire buf op1' End) (Inl p1) x1
     | Some p \<Rightarrow> End)
   | (Write op1' p1 x1, Write op2' p2 x2) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> Write (Write (comp_op wire buf op1' op2') (Inr p2) x2) (Inl p1) x1
     | Some p \<Rightarrow> Write (comp_op wire (buf(p := benq x1 (buf p))) op1' op2') (Inr p2) x2)
   | (Write op1' p1 x1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then (case wire p1 of
       None \<Rightarrow> Write (comp_op wire (buf(p2 := btl (buf p2))) op1' (f2 (bhd' (buf p2)))) (Inl p1) x1
     | Some p \<Rightarrow> if \<exists>n. comp_producing wire buf op1 op2 n then if p = p2 then comp_op wire (buf(p2 := btl (benq x1 (buf p2)))) op1' (f2 (bhd' (benq x1 (buf p2))))
         else comp_op wire (buf(p := benq x1 (buf p), p2 := btl (buf p2))) op1' (f2 (bhd' (buf p2))) else End)
     else (case wire p1 of
       None \<Rightarrow> Write (Read (Inr p2) (\<lambda>y2. comp_op wire buf op1' (f2 y2))) (Inl p1) x1
     | Some p \<Rightarrow> Read (Inr p2) (\<lambda>y2. comp_op wire (buf(p := benq x1 (buf p))) op1' (f2 y2))))"
  by (relation "measure (\<lambda>((wire, buf), op1, op2). THE i. comp_producing wire buf op1 op2 i)")
    (auto 0 3 simp: The_comp_producing elim: comp_producing.cases)

lemma comp_op_code[code]:
  "comp_op wire buf op1 op2 = (case (op1, op2) of
     (End, End) \<Rightarrow> End
   | (End, Write op2' p2 x2) \<Rightarrow> Write (comp_op wire (bend o buf) End op2') (Inr p2) x2
   | (End, Read p2 f2) \<Rightarrow> let buf = bend o buf in if p2 \<in> ran wire
     then comp_op wire (buf(p2 := btl (buf p2))) End (f2 (bhd' (buf p2)))
     else Read (Inr p2) (\<lambda>y2. comp_op wire buf End (f2 y2))
   | (Read p1 f1, End) \<Rightarrow> Read (Inl p1) (\<lambda>y1. comp_op wire buf (f1 y1) End)
   | (Read p1 f1, Write op2' p2 x2) \<Rightarrow> Read (Inl p1) (\<lambda>y1. Write (comp_op wire buf (f1 y1) op2') (Inr p2) x2)
   | (Read p1 f1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then Read (Inl p1) (\<lambda>y1. comp_op wire (buf(p2 := btl (buf p2))) (f1 y1) (f2 (bhd' (buf p2))))
     else Read (Inl p1) (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2)))
   | (Write op1' p1 x1, End) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> Write (comp_op wire buf op1' End) (Inl p1) x1
     | Some p \<Rightarrow> End)
   | (Write op1' p1 x1, Write op2' p2 x2) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> Write (Write (comp_op wire buf op1' op2') (Inr p2) x2) (Inl p1) x1
     | Some p \<Rightarrow> Write (comp_op wire (buf(p := benq x1 (buf p))) op1' op2') (Inr p2) x2)
   | (Write op1' p1 x1, Read p2 f2) \<Rightarrow> if p2 \<in> ran wire
     then (case wire p1 of
       None \<Rightarrow> Write (comp_op wire (buf(p2 := btl (buf p2))) op1' (f2 (bhd' (buf p2)))) (Inl p1) x1
     | Some p \<Rightarrow> if p = p2 then comp_op wire (buf(p2 := btl (benq x1 (buf p2)))) op1' (f2 (bhd' (benq x1 (buf p2))))
         else comp_op wire (buf(p := benq x1 (buf p), p2 := btl (buf p2))) op1' (f2 (bhd' (buf p2))))
     else (case wire p1 of
       None \<Rightarrow> Write (Read (Inr p2) (\<lambda>y2. comp_op wire buf op1' (f2 y2))) (Inl p1) x1
     | Some p \<Rightarrow> Read (Inr p2) (\<lambda>y2. comp_op wire (buf(p := benq x1 (buf p))) op1' (f2 y2))))"
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
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros)
  subgoal for p2 f2 op1' p1 x1
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal for p2 f2 op1' p1 x1 p
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  subgoal for p2 f2
    by (subst comp_op.code) (auto 0 4 split: op.splits option.splits intro: comp_producing.intros simp: Let_def)
  done
simps_of_case comp_op_simps[simp]: comp_op_code[unfolded prod.case]

consts read_op :: "'ip set \<Rightarrow> ('ip \<Rightarrow> 'd buf) \<Rightarrow> ('ip, 'op, 'd) op \<Rightarrow> ('ip, 'op, 'd) op"
lemma read_op_code[code]:
  "read_op A buf op = (case op of
     End \<Rightarrow> End
   | Read p f \<Rightarrow> if p \<in> A
       then read_op A (buf(p := btl (buf p))) (f (bhd' (buf p)))
       else Read p (\<lambda>x. read_op A buf (f x))
   | Write op p x \<Rightarrow> Write (read_op A buf op) p x)"
  sorry
simps_of_case read_op_simps[simp]: read_op_code

fun iter_op where
  "iter_op 0 wire buf op = read_op (ran wire) buf op"
| "iter_op (Suc n) wire buf op = map_op (case_sum id id) projr (comp_op wire buf (iter_op n wire buf op) op)"

lemma produce_map_op:
  "\<forall> x. h (g x) = x \<Longrightarrow> produce (map_op f h op) lxs p = produce op (lxs o f) (g p)"
  apply (coinduction arbitrary: op)
  subgoal for op
    apply(induction arg\<equiv>"(map_op f h op, lxs, p)" arbitrary: op lxs rule: produce.inner_induct)
    sorry
  done

lemma produce_comp_op:
   "produce (comp_op wire buf op1 op2) lxs p = (case p of
    Inl p1 \<Rightarrow> (if p1 \<in> dom wire then LNil else
      produce op1 (lxs o Inl) p1)
  | Inr p2 \<Rightarrow> produce op2 (\<lambda> p'. if p' \<in> ran wire then produce (map_op id (case_option undefined id o wire) op1) (lxs o Inl) p' else lxs (Inr p')) p2)"
  sorry

lemma "lprefix (produce (iter_op n wire buf op) lxs p) (produce (iter_op (Suc n) wire buf op) lxs p)"
  apply (coinduction arbitrary: op buf lxs p)
  apply (auto simp: produce_map_op[where g = Inr] produce_comp_op)
  sorry

lemma "produce (loop_op wire buf op) lxs =
  (THE lzs. \<forall>p. lzs p = produce (map_op id (todo) op)
     (\<lambda>p. if p \<in> ran wire then lapp (buf p1) (lzs p2) else lxs p3) p)"
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


lemma "\<forall>p. lprefix (lxs p) (lxs' p) \<Longrightarrow> lprefix (produce op lxs p) (produce op lxs' p)"
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

lemma inputs_comp_op[simp]:
  "inputs (comp_op wire buf op1 op2) = Inl ` inputs op1 \<union> Inr ` (inputs op2 - ran wire)"
  sorry (* Rafael *)

lemma outputs_comp_op[simp]:
  "outputs (comp_op wire buf op1 op2) = Inl ` (outputs op1 - dom wire) \<union> Inr ` outputs op2"
  sorry (* Rafael *)

definition "pcomp_op = comp_op (\<lambda>_. None) (\<lambda>_. BEnded)"

lemma inputs_pcomp_op[simp]:
  "inputs (pcomp_op op1 op2) = Inl ` inputs op1 \<union> Inr ` inputs op2"
  unfolding pcomp_op_def by auto

lemma outputs_pcomp_op[simp]:
  "outputs (pcomp_op op1 op2) = Inl ` outputs op1 \<union> Inr ` outputs op2"
  unfolding pcomp_op_def by auto

lemma produce_pcomp_op:
  "produce (pcomp_op op1 op2) lxs p =
    (case p of Inl p \<Rightarrow> produce op1 (lxs o Inl) p | Inr p \<Rightarrow> produce op2 (lxs o Inr) p)"
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
  "produce (scomp_op op1 op2) lxs = (produce op2 (produce op1 lxs))"
    unfolding produce_comp_op scomp_op_def produce_map_op[where g=Inr and h=projr, simplified]
    by (auto split: sum.splits simp add: ranI o_def id_def op.map_ident)

type_synonym 'd op22 = "(Enum.finite_2, Enum.finite_2, 'd) op"
type_synonym 'd op11 = "(Enum.finite_1, Enum.finite_1, 'd) op"

coinductive welltyped where
  "\<forall>x \<in> A p. welltyped A B (f (Input x)) \<Longrightarrow> welltyped A B (Read p f)"
| "x \<in> B p \<Longrightarrow> welltyped A B op \<Longrightarrow> welltyped A B (Write op p x)"
| "welltyped A B End"

(*characteristic property of welltyped*)
lemma "welltyped A B op \<Longrightarrow> (\<forall>p. lset (lxs p) \<subseteq> A p) \<Longrightarrow> lset (produce op lxs p) \<subseteq> B p"
  sorry

corec cp_op :: "'d op11" where
  "cp_op = Read finite_1.a\<^sub>1 (case_input (Write cp_op finite_1.a\<^sub>1) cp_op End)"

corec inc_op :: "nat op11" where
  "inc_op = Read finite_1.a\<^sub>1 (case_input (\<lambda>x. Write inc_op finite_1.a\<^sub>1 (x + 1)) inc_op End)"

definition print_port where
  "print_port a = (if a = Enum.finite_2.a\<^sub>1 then ''port 1'' else ''port 2'')"

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
| "print_nat (Suc n) = ''Suc ('' @ print_nat n @ '')''"

definition debug_nat where
  "debug_nat m x = Debug.tracing (String.implode (m @ print_nat x))"

definition debug_write_nat_at_port where
  "debug_write_nat_at_port x p = Debug.tracing (String.implode (''Writing '' @ print_nat x @ '' at '' @ print_port p))"


corec cinc_op :: "nat op22" where
  "cinc_op = Read finite_2.a\<^sub>1 (case_input (\<lambda>x. Write (Write cinc_op finite_2.a\<^sub>2 x) finite_2.a\<^sub>1 (x+1)) cinc_op End)"

lemma "welltyped A A cp_op"
(*needs coinduction up-to for welltyped (or a custom bisimulation)*)
  sorry

term rel_op

definition loop22_op where
  "loop22_op op = (loop_op
    (\<lambda>x. if x = finite_2.a\<^sub>1 then Some finite_2.a\<^sub>1 else None) (\<lambda>_. BEmpty) op)"

fun ltaken where
  "ltaken _ 0 = []"
| "ltaken LNil _ = []"
| "ltaken (LCons x xs) (Suc n) = x # ltaken xs n"


lemma loop_op_lSup:
  "produce (loop_op wire buf op) lxs p =
   lSup {xs | xs n. xs = produce (Nat.funpow n (\<lambda> op'. map_op (case_sum id id) projr (comp_op wire buf op' op')) op) lxs p}"
  oops

corec (friend) bulk_write where
  "bulk_write ys i op =
    (case ys of [] \<Rightarrow> End | [x] \<Rightarrow> Write op i x | x#xs \<Rightarrow> Write (bulk_write xs i op) i x)"

definition "my_pow n f = Nat.funpow n (\<lambda> x. f x x)"

definition loop22_with_comp_op :: "(Enum.finite_2, Enum.finite_2, 'a) op \<Rightarrow> nat \<Rightarrow> (Enum.finite_2, Enum.finite_2, 'a) op" where
  "loop22_with_comp_op op n = my_pow n 
    (\<lambda> op1 op2. map_op (case_sum id id) (case_sum id id)
      (comp_op (\<lambda>x. if x = finite_2.a\<^sub>1 then Some finite_2.a\<^sub>1 else None) (\<lambda>_. BEmpty) op1 op2)) op"

corec foo_op :: "nat list \<Rightarrow> (Enum.finite_2, Enum.finite_2, nat) op" where
  "foo_op buf = Read finite_2.a\<^sub>1 (case_input (\<lambda>x. foo_op (buf@[x])) (bulk_write (map ((+)1) buf) finite_2.a\<^sub>1 (bulk_write buf finite_2.a\<^sub>2 (foo_op []))) End)"

value "ltaken (produce (loop22_op (bulk_write [1,2,3] finite_2.a\<^sub>1 (foo_op []))) (\<lambda> _. undefined) finite_2.a\<^sub>2) 30"

value "ltaken (produce (loop22_with_comp_op (bulk_write [1,2] finite_2.a\<^sub>1 (foo_op [])) 3) (\<lambda> _. LNil) finite_2.a\<^sub>2) 25"

corec foo2_op :: "nat list \<Rightarrow> (Enum.finite_2, Enum.finite_2, nat) op" where
  "foo2_op buf = Read finite_2.a\<^sub>1 (case_input (\<lambda>x. bulk_write (map ((+)1) buf) finite_2.a\<^sub>1 (foo2_op (buf@[x]))) ((bulk_write buf finite_2.a\<^sub>2 (foo2_op []))) End)"

value "ltaken (produce (loop22_op (bulk_write [1,2,3] finite_2.a\<^sub>1 (foo_op []))) (\<lambda> _. undefined) finite_2.a\<^sub>2) 30"
value "ltaken (produce (loop22_with_comp_op (foo_op []) 3) (\<lambda> _. LCons 1 (LCons 2 (LCons 3 LNil))) finite_2.a\<^sub>2) 25"

value "ltaken (produce (loop22_op (Write cinc_op finite_2.a\<^sub>1 1)) (\<lambda> _. LNil) finite_2.a\<^sub>2) 4"
value "ltaken (produce (loop22_with_comp_op cinc_op 4) (\<lambda> _. LCons 1 LNil) finite_2.a\<^sub>2) 50"

value "ltaken (produce (comp_op (\<lambda>x. if x = finite_2.a\<^sub>1 then Some finite_2.a\<^sub>1 else None) (\<lambda>_. BEmpty) cinc_op cinc_op)  (\<lambda> _. LCons 1 LNil) (Inl finite_2.a\<^sub>1)) 100"
value "ltaken (produce (comp_op (\<lambda>x. if x = finite_2.a\<^sub>1 then Some finite_2.a\<^sub>1 else None) (\<lambda>_. BEmpty) cinc_op cinc_op)  (\<lambda> _. LCons 1 LNil) (Inr finite_2.a\<^sub>1)) 100"
value "ltaken (produce (map_op (case_sum id id) (case_sum id id) (comp_op (\<lambda>x. if x = finite_2.a\<^sub>1 then Some finite_2.a\<^sub>1 else None) (\<lambda>_. BEmpty) cinc_op cinc_op))  (\<lambda> _. LCons 1 LNil) (finite_2.a\<^sub>2)) 100"
value "ltaken (produce (comp_op (\<lambda>x. if x = finite_2.a\<^sub>1 then Some finite_2.a\<^sub>1 else None) (\<lambda>_. BEmpty) cinc_op cinc_op)  (\<lambda> _. LCons 1 LNil) (Inr finite_2.a\<^sub>2)) 100"


abbreviation "comp_2 op \<equiv> map_op (case_sum id id) (case_sum id id) (comp_op (\<lambda>x. if x = finite_2.a\<^sub>1 then Some finite_2.a\<^sub>1 else None) (\<lambda>_. BEmpty) op op)"
abbreviation "comp_4 op \<equiv> comp_2 (comp_2 op)"
abbreviation "comp_16 op \<equiv> comp_4 (comp_4 op)"

(*
Read finite_2.a\<^sub>1 (
    case_input 
     (\<lambda>x. if even x then Write (foo3_op n) finite_2.a\<^sub>1 x else Write (foo3_op (n+1)) finite_2.a\<^sub>1 (x-1)) 
     (Write (foo3_op n) finite_2.a\<^sub>1 666)
     End
    )
*)

corec foo3_op :: "nat \<Rightarrow> (Enum.finite_2, Enum.finite_2, nat) op" where
  "foo3_op n = Read finite_2.a\<^sub>2 (case_input 
     (\<lambda>x. if even x
          then Write ((Read finite_2.a\<^sub>1 (case_input 
               (\<lambda>x. if even x then Write (foo3_op n) finite_2.a\<^sub>2 x else Write (foo3_op (n+1)) finite_2.a\<^sub>1 (x div 2)) 
               (Write (foo3_op n) finite_2.a\<^sub>2 666)
               End
               ))) finite_2.a\<^sub>2 x
          else Write (foo3_op (n+1)) finite_2.a\<^sub>1 (x div 2)) 
     (Write (Read finite_2.a\<^sub>1 (case_input 
               (\<lambda>x. if even x then Write (foo3_op n) finite_2.a\<^sub>2 x else Write (foo3_op (n+1)) finite_2.a\<^sub>1 (x div 2)) 
               (Write (foo3_op n) finite_2.a\<^sub>2 444)
               End
               )) finite_2.a\<^sub>2 333)
     (Read finite_2.a\<^sub>1 (case_input 
               (\<lambda>x. if even x then Write (foo3_op n) finite_2.a\<^sub>2 x else Write (foo3_op (n+1)) finite_2.a\<^sub>1 (x div 2)) 
               (Write (foo3_op n) finite_2.a\<^sub>2 777)
               (Write End finite_2.a\<^sub>2 (10000 + n))
               ))
    )"

find_consts  name: fun_upd

value "ltaken (produce (loop22_op (foo3_op 0)) (\<lambda> e. if e = finite_2.a\<^sub>2 then LCons 2 (LCons 1 LNil) else LNil) finite_2.a\<^sub>2) 99"

end
value "ltaken (produce (san_op (foo3_op 0)) (\<lambda> e. if e = finite_2.a\<^sub>2 then LCons 2 (LCons 1 LNil) else LNil) (finite_2.a\<^sub>2)) 99"



lemma
  "lprefix
   (produce (loop22_with_comp_op (bulk_write [1,2,3] finite_2.a\<^sub>1 (foo_op [])) n) (\<lambda> _. LNil) finite_2.a\<^sub>1)
   (produce (loop22_op (bulk_write [1,2,3] finite_2.a\<^sub>1 (foo_op []))) (\<lambda> _. undefined) finite_1.a\<^sub>1)"
  oops

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
  "collatz_input op b \<equiv> (if b then Read finite_2.a\<^sub>2 (\<lambda>x. case x of
     Input x \<Rightarrow> let n = decode_nat1 x in Write (op True) finite_2.a\<^sub>1 (encode_nat3 (n, n, 0))
   | NoInput \<Rightarrow> op True
   | EOS \<Rightarrow> op False)
   else op False)"
abbreviation collatz_loop_input :: "(bool \<Rightarrow> 'd op22) \<Rightarrow> bool \<Rightarrow> 'd op22" where
  "collatz_loop_input op b \<equiv> Read finite_2.a\<^sub>1 (\<lambda>x. case x of
     Input x \<Rightarrow> let (n, ni, i) = decode_nat3 x in
       if ni = 1 then Write (op b) finite_2.a\<^sub>2 (encode_nat2 (n, i)) else
         Write (op b) finite_2.a\<^sub>1 (encode_nat3 (n, if ni mod 2 = 0 then ni div 2 else 3 * ni + 1, i + 1))
   | _ \<Rightarrow> if b then op True else End)"
corec collatz_step :: "bool \<Rightarrow> 'd op22" where
  "collatz_step b = collatz_input (collatz_loop_input collatz_step) b"
definition collatz_op :: "'d op11" where
  "collatz_op = loop22_op (collatz_step True)"

definition collatz :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "collatz n \<equiv> map decode_nat2
     (list_of (produce collatz_op (\<lambda>_. llist_of (map encode_nat1 [1 ..< Suc n])) finite_1.a\<^sub>1))"

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

abbreviation read :: "('a input \<Rightarrow> 'd op11) \<Rightarrow> 'd op11" where
 "read f \<equiv> Read finite_1.a\<^sub>1 (f o map_input decode_input)"

abbreviation "write" :: "'d op11 \<Rightarrow> 'b \<Rightarrow> 'd op11" where
  "write op \<equiv> Write op finite_1.a\<^sub>1 o encode_output"

abbreviation bulk_write where "bulk_write ys op \<equiv> Cycles_7.bulk_write (map encode_output ys) finite_1.a\<^sub>1 op"

end

locale top11 = t?: op11
  where input_type = "input_type :: 'a itself"
    and output_type = "output_type :: 'b itself"
    and domain_type = "domain_type :: 'd itself"
  for input_type output_type domain_type +
  fixes time_type :: "'t :: order itself"
begin

abbreviation read :: "(('t, 'a) event input \<Rightarrow> ('t, 'd) event op11) \<Rightarrow> ('t, 'd) event op11" where
 "read f \<equiv> Read finite_1.a\<^sub>1 (f o map_input (map_event id decode_input))"

abbreviation "write" :: "('t, 'd) event op11 \<Rightarrow> ('t, 'b) event \<Rightarrow> ('t, 'd) event op11" where
  "write op \<equiv> Write op finite_1.a\<^sub>1 o map_event id encode_output"

abbreviation bulk_write where "bulk_write ys op \<equiv> Cycles_7.bulk_write (map (map_event id encode_output) ys) finite_1.a\<^sub>1 op"

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
    Input ev \<Rightarrow> (case ev of
        Data t d \<Rightarrow> batch_op (buf @ [(t, d)])
      | Watermark wm \<Rightarrow> let (out, buf') = batches [wm] buf in bulk_write ([x \<leftarrow> out. data x \<noteq> []] @ [Watermark wm]) (batch_op buf'))
    | EOS \<Rightarrow> let wms = maximal_antichain_list (map fst buf) ;
             (bts, _) = batches wms buf in
             bulk_write bts End
    | NoInput \<Rightarrow> batch_op buf)"

abbreviation "batch_input_test_1 xs \<equiv> llist_of (map (map_event id encode_input) xs)"

definition "batch_op_test_1 xs = map (map_event id decode_output) (list_of (produce (batch_op []) (\<lambda> _. batch_input_test_1 xs) finite_1.a\<^sub>1))"

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
    Input ev \<Rightarrow> (case ev of
        Data wm b \<Rightarrow> let ts = rev (remdups (map fst (rev b))) ;
                         out = map (\<lambda> t . Data t (buf@ b)) ts in
                         bulk_write out (incr_op (buf @ b))
      | Watermark wm \<Rightarrow> write (incr_op buf) (Watermark wm)) 
    | EOS \<Rightarrow> End
    | NoInput \<Rightarrow> incr_op buf)"

abbreviation "incr_input_test_1 xs \<equiv> llist_of (map (map_event id encode_input) xs)"
definition "incr_op_test_1 xs = map (map_event id decode_output) (list_of (produce (incr_op []) (\<lambda> _. incr_input_test_1 xs) finite_1.a\<^sub>1))"

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

abbreviation "incr_batch_input_test_1 xs \<equiv> llist_of (map (map_event id encode_input) xs)"
(* write abbreviation for produce with finite_1 *)
definition "incr_batch_op_test_1 xs = map (map_event id decode_output) (list_of (produce (incr_batch_op [] []) (\<lambda> _. incr_batch_input_test_1 xs) finite_1.a\<^sub>1))"

end

term incr_batch

global_interpretation ib: incr_batch Inl projl "(Inr:: ('t::order \<times> 'a) list \<Rightarrow> 'a + ('t \<times> 'a) list)" projr 
  defines ibincr_op = "incr.incr_op projr (Inr :: ('t::order \<times> 'a) list \<Rightarrow> 'a + ('t \<times> 'a) list)"
   and  ibatch_op = "batch.batch_op projl (Inr :: ('t::order \<times> 'a) list \<Rightarrow> 'a + ('t \<times> 'a) list)"
   and ibbatch_incr_op = "incr_batch.incr_batch_op projl (Inr :: ('t::order \<times> 'a) list \<Rightarrow> 'a + ('t \<times> 'a) list) projr" 
  and ibincr_batch_op_test_1 = "incr_batch.incr_batch_op_test_1 Inl projl Inr projr"  
  by standard auto

value "ibincr_batch_op_test_1 [Data (0::nat) ''dog'', Data 2 ''cat'', Watermark 1, Watermark 2]"


