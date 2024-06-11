theory Cycles_7
  imports Coinductive.Coinductive_List
    "HOL-Library.BNF_Corec"
    "HOL-Library.Code_Lazy"
    "HOL-Library.Simps_Case_Conv"
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
  "producing p End lxs 0"
| "producing p (Write _ p _) lxs 0"
| "producing p (f (lhd' (lxs p'))) (lxs(p' := ltl (lxs p'))) i \<Longrightarrow> producing p (Read p' f) lxs (Suc i)"
| "p \<noteq> p' \<Longrightarrow> producing p op lxs i \<Longrightarrow> producing p (Write op p' x) lxs (Suc i)"

lemma producing_inject: "producing p op lxs i \<Longrightarrow> producing p op lxs j \<Longrightarrow> i = j"
proof (induct p op lxs i arbitrary: j rule: producing.induct)
  case (3 p f lxs p' i)
  from 3(3,1) 3(2)[of "j - 1"] show ?case
    by (elim producing.cases[of _ "Read p' f"]) (auto simp del: fun_upd_apply)
next
  case (4 p p' op lxs i x)
  from 4(4,1,2) 4(3)[of "j - 1"] show ?case
    by (elim producing.cases[of _ "Write op p' x"]) auto
qed (auto elim: producing.cases)

lemma The_producing: "producing p op lxs i \<Longrightarrow> The (producing p op lxs) = i"
  using producing_inject by fast

corecursive produce where
  "produce op lxs p = (case op of
    Read p' f \<Rightarrow> (if \<exists>i. producing p op lxs i then produce (f (lhd' (lxs p'))) (lxs(p' := ltl (lxs p'))) p else LNil)
  | Write op' p' x \<Rightarrow> (if p = p' then LCons x (produce op' lxs p) else
     if \<exists>i. producing p op lxs i then produce op' lxs p else LNil)
  | End \<Rightarrow> LNil)"
  by (relation "measure (\<lambda>(op, lxs, p). THE i. producing p op lxs i)")
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
    apply (subst produce.code)
    apply (cases "lxs p'")
     apply (auto 0 4 split: op.splits intro: producing.intros)
    done
  subgoal for op p x
    apply (subst produce.code)
    apply (auto 0 4 split: op.splits intro: producing.intros)
    done
  done

simps_of_case produce_simps[simp]: produce_code

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

consts comp_op :: "('op1 \<rightharpoonup> 'ip1 + 'ip2) \<Rightarrow> ('ip1 + 'ip2 \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> ('ip1 + 'ip2, 'op1 + 'op2, 'd) op"

lemma comp_op_code[code]:
  "comp_op wire buf op1 op2 = (case (op1, op2) of
     (End, End) \<Rightarrow> End
   | (Read p1 f1, End) \<Rightarrow> if Inl p1 \<in> ran wire
       then comp_op wire (buf(Inl p1 := btl (buf (Inl p1)))) (f1 (bhd' (buf (Inl p1)))) End
       else Read (Inl p1) (\<lambda>y1. comp_op wire buf (f1 y1) End)
   | (Write op1' p1 x1, End) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> Write (comp_op wire buf op1' End) (Inl p1) x1
     | Some (Inl p) \<Rightarrow> comp_op wire (buf(Inl p := benq x1 (buf (Inl p)))) op1' End
     | Some (Inr p) \<Rightarrow> End)
   | (End, Write op2' p2 x2) \<Rightarrow> Write (comp_op wire (bend o buf) End op2') (Inr p2) x2
   | (Read p1 f1, Write op2' p2 x2) \<Rightarrow>  if Inl p1 \<in> ran wire
       then Write (comp_op wire (buf(Inl p1 := btl (buf (Inl p1)))) (f1 (bhd' (buf (Inl p1)))) op2') (Inr p2) x2
       else Read (Inl p1) (\<lambda>y1. Write (comp_op wire buf (f1 y1) op2') (Inr p2) x2)
   | (Write op1' p1 x1, Write op2' p2 x2) \<Rightarrow> (case wire p1 of
       None \<Rightarrow> Write (Write (comp_op wire buf op1' op2') (Inr p2) x2) (Inl p1) x1
     | Some p \<Rightarrow> Write (comp_op wire (buf(p := benq x1 (buf p))) op1' op2') (Inr p2) x2)
   | (End, Read p2 f2) \<Rightarrow> let buf = bend o buf in if Inr p2 \<in> ran wire
     then comp_op wire (buf(Inr p2 := btl (buf (Inr p2)))) End (f2 (bhd' (buf (Inr p2))))
     else Read (Inr p2) (\<lambda>y2. comp_op wire buf End (f2 y2))
   | (Read p1 f1, Read p2 f2) \<Rightarrow> if Inl p1 \<in> ran wire \<and> Inr p2 \<in> ran wire
     then comp_op wire (buf(Inl p1 := btl (buf (Inl p1)), Inr p2 := btl (buf (Inr p2)))) (f1 (bhd' (buf (Inl p1)))) (f2 (bhd' (buf (Inr p2))))
     else if Inl p1 \<in> ran wire then Read (Inr p2) (\<lambda>y2. comp_op wire (buf(Inl p1 := btl (buf (Inl p1)))) (f1 (bhd' (buf (Inl p1)))) (f2 y2))
     else if Inr p2 \<in> ran wire then Read (Inl p1) (\<lambda>y1. comp_op wire (buf(Inr p2 := btl (buf (Inr p2)))) (f1 y1) (f2 (bhd' (buf (Inr p2)))))
     else Read (Inl p1) (\<lambda>y1. Read (Inr p2) (\<lambda>y2. comp_op wire buf (f1 y1) (f2 y2)))
   | (Write op1' p1 x1, Read p2 f2) \<Rightarrow> if Inr p2 \<in> ran wire
     then (case wire p1 of
       None \<Rightarrow> Write (comp_op wire (buf(Inr p2 := btl (buf (Inr p2)))) op1' (f2 (bhd' (buf (Inr p2))))) (Inl p1) x1
     | Some p \<Rightarrow> if p = Inr p2 then comp_op wire (buf(Inr p2 := btl (benq x1 (buf (Inr p2))))) op1' (f2 (bhd' (benq x1 (buf (Inr p2)))))
         else comp_op wire (buf(p := benq x1 (buf p), Inr p2 := btl (buf (Inr p2)))) op1' (f2 (bhd' (buf (Inr p2)))))
     else (case wire p1 of
       None \<Rightarrow> Write (Read (Inr p2) (\<lambda>y2. comp_op wire buf op1' (f2 y2))) (Inl p1) x1
     | Some p \<Rightarrow> Read (Inr p2) (\<lambda>y2. comp_op wire (buf(p := benq x1 (buf p))) op1' (f2 y2))))"
  sorry (* Dmitriy *)

simps_of_case comp_op_simps[simp]: comp_op_code[unfolded prod.case]

lemma inputs_comp_op[simp]:
  "inputs (comp_op wire buf op1 op2) = (Inl ` inputs op1 \<union> Inr ` inputs op2) - ran wire"
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
  sorry

definition "scomp_op op1 op2 = map_op projl projr (comp_op (Some o Inr) (\<lambda>_. BEmpty) op1 op2)"

lemma inputs_scomp_op[simp]:
  "inputs (scomp_op op1 op2) = inputs op1"
  unfolding scomp_op_def by (force simp: op.set_map ran_def)

lemma outputs_scomp_op[simp]:
  "outputs (scomp_op op1 op2) = outputs op2"
  unfolding scomp_op_def by (force simp: op.set_map ran_def)

lemma produce_scomp_op:
  "produce (scomp_op op1 op2) lxs = (produce op2 (produce op1 lxs))"
  sorry


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

lemma "welltyped A A cp_op"
(*needs coinduction up-to for welltyped (or a custom bisimulation)*)
  sorry

definition loop_op :: "'d op22 \<Rightarrow> 'd op11" where
  "loop_op op = map_op (\<lambda>x. finite_1.a\<^sub>1) projr (comp_op
    (\<lambda>x. Some (if x = finite_2.a\<^sub>1 then Inl finite_2.a\<^sub>1 else Inr finite_1.a\<^sub>1)) (\<lambda>_. BEmpty)
      op cp_op)"

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
  "collatz_op = loop_op (collatz_step True)"

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

corec (friend) bulk_write where
  "bulk_write ys i op =
    (case ys of [] \<Rightarrow> End | [x] \<Rightarrow> Write op i x | x#xs \<Rightarrow> Write (bulk_write xs i op) i x)"

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

locale batch = op11 "TYPE(('t::order, 'dd) event)" "TYPE(('t, ('t \<times> 'dd) list) event)"
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

abbreviation "batch_input_test_1 xs \<equiv> llist_of (map encode_input xs)"

definition "batch_op_test_1 xs = map decode_output (list_of (produce (batch_op []) (\<lambda> _. batch_input_test_1 xs) finite_1.a\<^sub>1))"

end

global_interpretation b: batch Inl projl Inr projr
  defines bbatch_op = "batch.batch_op projl Inr"
  and bbatch_op_test_1 = "batch.batch_op_test_1 Inl projl Inr projr"
  by standard auto

abbreviation "bbatch_op_test_1_r \<equiv> bbatch_op_test_1  [Data (0::nat) ''dog'', Data 2 ''cat'', Watermark 1, Watermark 2]"
value bbatch_op_test_1_r

locale incr = op11 "TYPE(('t::order, ('t \<times> 'dd) list) event)" "TYPE(('t, ('t \<times> 'dd) list) event)" encode decode encode decode for encode decode
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

abbreviation "incr_input_test_1 xs \<equiv> llist_of (map encode xs)"
definition "incr_op_test_1 xs = map decode (list_of (produce (incr_op []) (\<lambda> _. incr_input_test_1 xs) finite_1.a\<^sub>1))"

end

global_interpretation i: incr id id
  defines iincr_op = "incr.incr_op id id"
    and iincr_op_test_1 = "incr.incr_op_test_1 id id"
  by standard auto

value "iincr_op_test_1 bbatch_op_test_1_r"

locale incr_batch = b?:batch + i?:incr encode_output decode_output
begin

definition "batch_incr_op buf1 buf2 = scomp_op (batch_op buf1) (incr_op buf2)"

abbreviation "incr_batch_input_test_1 xs \<equiv> llist_of (map encode_input xs)"
(* write abbreviation for produce with finite_1 *)
definition "incr_batch_op_test_1 xs = map decode_output (list_of (produce (batch_incr_op [] []) (\<lambda> _. incr_batch_input_test_1 xs) finite_1.a\<^sub>1))"

end

global_interpretation ib: incr_batch Inl projl Inr projr
  defines ibincr_op = "incr.incr_op (Inr:: ('a, ('a \<times> 'b) list) event
   \<Rightarrow> ('a, 'b) event + ('a, ('a \<times> 'b) list) event) projr"
  and ibbatch_incr_op = "incr_batch.batch_incr_op projl Inr projr"
  and ibincr_batch_op_test_1 = "incr_batch.incr_batch_op_test_1 Inl projl Inr projr"
  by standard auto

term ibbatch_incr_op

find_theorems bbatch_op
find_theorems ibincr_op
find_theorems ibbatch_incr_op

value "ibincr_batch_op_test_1 [Data (0::nat) ''dog'', Data 2 ''cat'', Watermark 1, Watermark 2]"


