section \<open>The loop operator\<close>

theory Loop

imports
  Operator
begin


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
simps_of_case loop_op_simps': loop_op_code
simps_of_case loop_op_simps[simp]: loop_op.code[unfolded prod.case Let_def]


section\<open>Correctness\<close>

definition "lift A lxs lys p = (if p \<in> A then lxs p else lys p)"

(* lemma semantics_loop_op:
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
 *)

lemma loop_producing_Some: "loop_producing wire buf op n \<Longrightarrow> wire = Some \<Longrightarrow> loop_op wire buf op = End"
  apply (induct buf op n rule: loop_producing.induct)
      apply (auto simp: ran_def)
  done

lemma not_loop_producing_eq_End: "\<forall>n. \<not> loop_producing wire buf op n \<Longrightarrow> loop_op wire buf op = End"
  apply (coinduction arbitrary: buf op)
  apply auto
  subgoal for buf op
    apply (subst (asm) loop_op.code)
    apply (auto split: op.splits if_splits option.splits simp: Let_def intro: loop_producing.intros)
    done
  subgoal for buf op
    apply (subst (asm) loop_op.code)
    apply (auto split: op.splits if_splits option.splits simp: Let_def intro: loop_producing.intros)
    done
  done

lemma loop_op_Some: "loop_op Some buf op = End"
  apply (coinduction arbitrary: buf op)
  apply auto
  subgoal for buf op
    apply (cases op)
      apply (simp_all add: ranI split: if_splits)
    using loop_producing_Some not_loop_producing_eq_End apply blast+
    done
  subgoal for buf op
    apply (cases op)
      apply (simp_all add: ranI split: if_splits)
    using loop_producing_Some not_loop_producing_eq_End apply blast+
    done
  done

coinductive causal for wire where
  "causal wire (BTL p buf) ios \<Longrightarrow> y = BHD p buf \<Longrightarrow> p \<in> ran wire \<Longrightarrow> causal wire buf (LCons (Inp p y) ios)"
| "causal wire buf ios \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> causal wire buf (LCons (Inp p y) ios)"
| "causal wire (BENQ p' y buf) ios \<Longrightarrow> wire p = Some p' \<Longrightarrow> causal wire buf (LCons (Out p y) ios)"
| "causal wire buf ios \<Longrightarrow> wire p = None \<Longrightarrow> causal wire buf (LCons (Out p y) ios)"
| "causal wire buf LNil"

inductive_cases causal_Inp[elim!]: "causal wire buf (LCons (Inp p y) ios)"
inductive_cases causal_Out[elim!]: "causal wire buf (LCons (Out p y) ios)"
inductive_cases causal_LNil[elim!]: "causal wire buf LNil"

abbreviation visible_IO where "visible_IO wire io \<equiv> case_IO (\<lambda>p _. p \<notin> ran wire) (\<lambda> p _. p \<notin> dom wire) io" 

lemma loop_producing_traced_causal_cong:
  "loop_producing wire buf op n \<Longrightarrow>
   traced op ios' \<Longrightarrow>
   causal wire buf ios' \<Longrightarrow>
   (\<exists>p f. loop_op wire buf op = Read p f \<and>
          (\<exists>x lxs'.
              lfilter (visible_IO wire) ios' = LCons (Inp p x) lxs' \<and>
              traced_cong (\<lambda>opa lxs. \<exists>ios ios' op buf. opa = loop_op wire buf op \<and> lxs = ios \<and> traced op ios' \<and> ios = lfilter (visible_IO wire) ios' \<and> causal wire buf ios') (f x) lxs')) \<or>
   (\<exists>op' q x.
       loop_op wire buf op = Write op' q x \<and>
       (\<exists>lxs'.
           lfilter (visible_IO wire) ios' = LCons (Out q x) lxs' \<and>
           traced_cong (\<lambda>opa lxs. \<exists>ios ios' op buf. opa = loop_op wire buf op \<and> lxs = ios \<and> traced op ios' \<and> ios = lfilter (visible_IO wire) ios' \<and> causal wire buf ios') op' lxs')) \<or>
    loop_op wire buf op = End \<and> lfilter (visible_IO wire) ios' = LNil"
  apply (induct  buf op n arbitrary: ios' rule: loop_producing.induct)
  subgoal
    by auto
  subgoal
    by (auto 10 10 intro: traced_cong.intros)
  subgoal
    apply (erule causal.cases)
        apply (auto intro: traced_cong.intros)
    done
  subgoal
    apply (erule causal.cases)
        apply (auto intro: traced_cong.intros)
    apply (meson loop_producing.intros(4))
    done
  subgoal
    apply (erule causal.cases)
        apply (auto intro: traced_cong.intros)
      apply blast+
    apply (meson loop_producing.intros(5))
    done
  done

lemma in_traced_End_not_visible:
  "x \<in> lset ios \<Longrightarrow> 
   traced op ios \<Longrightarrow>
   causal wire buf ios \<Longrightarrow>
   loop_op wire buf op = End \<Longrightarrow>
   \<not> visible_IO wire x"
  apply (induct ios arbitrary: op buf rule: lset_induct)
  subgoal for xs op buf
    apply (cases op)
      apply auto
    done
  subgoal for x' xs op buf
    apply (cases op)
      apply (auto split: if_splits)
      apply (metis loop_op_simps'(1) loop_op_simps(1))
     apply blast
    apply (meson loop_producing.intros(5) not_loop_producing_eq_End)
    done
  done

primcorec retrace_loop_op where
  "retrace_loop_op wire buf op inps = (case op of
     End \<Rightarrow> LNil
   | Read p f \<Rightarrow> if p \<in> ran wire
       then LCons (Inp p (BHD p buf)) (retrace_loop_op wire (BTL p buf) (f (BHD p buf)) inps)
       else LCons (Inp p (lhd inps)) (retrace_loop_op wire buf (f (lhd inps)) (ltl inps))
   | Write op' p' x \<Rightarrow> (case wire p' of
         None \<Rightarrow> LCons (Out p' x) (retrace_loop_op wire buf op' inps)
       | Some p \<Rightarrow> LCons (Out p' x) (retrace_loop_op wire (BENQ p x buf) op' inps)))"

simps_of_case retrace_loop_op_simps[simp]: retrace_loop_op.code


abbreviation "Inp_llist ios \<equiv> lmap (case_IO (\<lambda> p ob. ob) undefined) (lfilter (case_IO \<top> \<bottom>) ios)"

lemma traced_retrace_loop_op:
  "traced (loop_op wire buf op) ios \<Longrightarrow>
   traced op (retrace_loop_op wire buf op (Inp_llist ios))"
  apply (coinduction arbitrary: buf op ios)
  subgoal for buf op ios
    apply (cases op)
    subgoal
      apply (clarsimp simp add: lmap_eq_LNil split: if_splits; blast?)
      apply (metis End lfilter_LNil lmap_eq_LNil loop_op_simps'(1) loop_op_simps(1))
      done
    subgoal
      apply (clarsimp simp add: lmap_eq_LNil split: if_splits option.splits; blast?)
      apply (metis (no_types, lifting) lfilter_LNil lmap_eq_LNil loop_op_simps'(2) not_loop_producing_eq_End option.simps(5) traced.simps)
      done
    subgoal
      apply (clarsimp simp add: lmap_eq_LNil split: if_splits option.splits; blast?)
      done
    done
  done


lemma traced_retrace_loop_op_any[simp]:
  "traced op (retrace_loop_op wire buf op inps)"
  apply (coinduction arbitrary: op buf inps)
  subgoal for op buf inps
    apply (cases op)
      apply (auto split: option.splits)
    done
  done

lemma causal_retrace_loop_op[simp]:
  "causal wire buf (retrace_loop_op wire buf op inps)"
  apply (coinduction arbitrary: op buf inps)
  subgoal for op buf inps
    apply (cases op)
      apply (auto split: option.splits)
    done
  done

lemma retrace_loop_op_End_not_visible:
  "x \<in> lset (retrace_loop_op wire buf op inps) \<Longrightarrow>
   loop_op wire buf op = End \<Longrightarrow>
   \<not> visible_IO wire x"
  apply (induct "retrace_loop_op wire buf op inps" arbitrary: buf op inps rule: lset_induct)
  subgoal for xs buf op inps
    apply (cases op)
      apply (auto split: if_splits option.splits)
    done
  subgoal for x' xs buf op inp
    apply (cases op)
      apply (simp_all split: if_splits option.splits)
    subgoal
      by (metis loop_op_simps'(1) loop_op_simps(1))
    subgoal
      by (metis loop_producing.intros(5) not_loop_producing_eq_End)
    done
  done

lemma in_traced_loop_cases:
  "loop_producing wire buf op n \<Longrightarrow>
   traced (loop_op wire buf op) ios \<Longrightarrow>
   loop_op wire buf op = End \<and> ios = LNil \<or>
   (\<exists> op' x p buf'. loop_op wire buf op = Write (loop_op wire buf' op') p x \<and> lhd ios = Out p x \<and> wire p = None) \<or>
   (\<exists> f x p buf'. loop_op wire buf op = Read p (\<lambda> x. loop_op wire buf' (f x)) \<and> lhd ios = Inp p x \<and> p \<notin> ran wire)"
  apply (induct buf op n arbitrary: ios rule: loop_producing.induct)
      apply (auto intro: End split: if_splits)
  done

lemma in_traced_loop_visible:
  "x \<in> lset ios \<Longrightarrow>
   traced (loop_op wire buf op) ios \<Longrightarrow>
   visible_IO wire x"
  apply (induct ios arbitrary: buf op rule: lset_induct)
  subgoal for xs buf op
    apply (cases "\<exists> n. loop_producing wire buf op n")
    subgoal
      apply (elim exE)
      apply (frule in_traced_loop_cases)
       apply auto
      done
    subgoal
      by (metis llist.distinct(1) not_loop_producing_eq_End traced_EndE)
    done
  subgoal for x' xs buf op
    apply (cases "\<exists> n. loop_producing wire buf op n")
    subgoal
      apply (elim exE)
      apply (frule in_traced_loop_cases)
       apply assumption
      apply auto
      done
    subgoal
      by (metis llist.distinct(1) not_loop_producing_eq_End traced_EndE)
    done
  done

lemma loop_producing_traced_in_retrace_loop_op:
  "loop_producing wire buf op n \<Longrightarrow>
   x \<in> lset ios \<Longrightarrow>
   traced (loop_op wire buf op) ios \<Longrightarrow>
   \<exists> x. x \<in> lset (retrace_loop_op wire buf op (Inp_llist ios)) \<and> visible_IO wire x"
  apply (induct buf op n arbitrary: ios rule: loop_producing.induct)
      apply (fastforce split: if_splits option.splits)+
  done 

lemma traced_in_retrace_loop_op:
  "x \<in> lset ios \<Longrightarrow>
   traced (loop_op wire buf op) ios \<Longrightarrow>
   \<exists> x. x \<in> lset (retrace_loop_op wire buf op (Inp_llist ios)) \<and> visible_IO wire x"
  apply (cases "\<exists> n. loop_producing wire buf op n")
  subgoal
    by (auto dest: loop_producing_traced_in_retrace_loop_op)
  subgoal
    by (metis empty_iff lset_LNil not_loop_producing_eq_End traced_EndE)
  done

lemma loop_producing_traced_lhd_loop_producing:
  "loop_producing wire buf op n \<Longrightarrow>
   traced (loop_op wire buf op) (LCons io ios) \<Longrightarrow>
   io = lhd (lfilter (visible_IO wire) (retrace_loop_op wire buf op (Inp_llist (LCons io ios))))"
  apply (induct buf op n arbitrary: ios rule: loop_producing.induct)
      apply (fastforce split: if_splits option.splits)+
  done

lemma traced_lhd_loop_producing:
  "traced (loop_op wire buf op) (LCons io ios) \<Longrightarrow>
   io = lhd (lfilter (visible_IO wire) (retrace_loop_op wire buf op (Inp_llist (LCons io ios))))"
  apply (cases "\<exists> n. loop_producing wire buf op n")
  subgoal
    by (auto dest: loop_producing_traced_lhd_loop_producing)
  subgoal
    by (metis llist.simps(3) not_loop_producing_eq_End traced_EndE)
  done

lemma loop_producing_traced_cong:
  "loop_producing wire buf op n \<Longrightarrow>
   traced (loop_op wire buf op) ios \<Longrightarrow>
   ios \<noteq> LNil \<Longrightarrow>
   llist.v1.congclp
    (\<lambda>llist llist'.
        \<exists>buf op ios.
           llist = ios \<and> llist' = lfilter (visible_IO wire) (retrace_loop_op wire buf op (Inp_llist ios)) \<and> traced (loop_op wire buf op) ios)
    (ctl ios) (ctl (lfilter (visible_IO wire) (retrace_loop_op wire buf op (Inp_llist ios))))"
  apply (induct buf op n arbitrary: ios rule: loop_producing.induct)
      apply (force simp add:  observation.map_id split: if_splits option.splits intro!: llist.cong_LCons intro: llist.cong_base)+
  done

lemma traced_ios_lfilter_visible:
  "traced (loop_op wire buf op) ios \<Longrightarrow>
   ios = lfilter (visible_IO wire) (retrace_loop_op wire buf op (Inp_llist ios))"
  apply (coinduction arbitrary: buf op ios rule: llist.coinduct_upto)
  subgoal for buf op ios
    apply (intro conjI impI iffI)
    subgoal
      by (auto simp add: lnull_def lmap_eq_LNil lfilter_eq_LNil dest: retrace_loop_op_End_not_visible)
    subgoal
      apply (simp add: lnull_def lmap_eq_LNil lfilter_eq_LNil)
      apply (rule ccontr)
      apply (clarsimp simp add: neq_LNil_conv)
      apply (frule traced_in_retrace_loop_op[rotated 1]) 
       apply auto
      done
    subgoal
      unfolding lnull_def
      apply (simp only: neq_LNil_conv)
      apply (elim exE)
      apply hypsubst_thin
      apply (drule traced_lhd_loop_producing)
      apply (metis lhd_LCons)
      done
    subgoal
      apply (cases "\<exists> n. loop_producing wire buf op n")
      subgoal
        by (auto dest: loop_producing_traced_cong)
      subgoal
        by (metis lnull_def not_loop_producing_eq_End traced_EndE)
      done
    done
  done

lemma traced_loop_op:
  "traced (loop_op wire buf op) ios =
   (\<exists>ios'. traced op ios' \<and> ios = lfilter (visible_IO wire) ios' \<and> causal wire buf ios')"
  apply (rule iffI)
  subgoal 
    apply (rule exI[of _ "retrace_loop_op wire buf op (Inp_llist ios)"])
    apply (intro conjI)
      apply (auto dest: traced_ios_lfilter_visible)
    done
  subgoal
    apply (elim exE conjE)
    subgoal for ios'
      apply (coinduction arbitrary: ios ios' op buf rule: traced_coinduct_upto)
      subgoal for ios ios' op buf
        apply hypsubst_thin
        apply (cases "\<exists> n. loop_producing wire buf op n")
         apply (elim exE)
        subgoal for n
          apply (drule loop_producing_traced_causal_cong)
            apply auto
          done
        subgoal
          apply simp
          apply (drule not_loop_producing_eq_End)
          apply (auto simp add: lfilter_eq_LNil)
          using in_traced_End_not_visible apply fast
          done
        done
      done
    done
  done

definition loop22_op :: "_ \<Rightarrow> 'd op22 \<Rightarrow> 'd op11" where
  "loop22_op buf op  = map_op (\<lambda>_. 1) (\<lambda>_. 1) (loop_op
    (\<lambda>x. if x = 1 then Some 1 else None) buf op)"

lemma iterates_Out_not_Inp:
  "x \<in> lset lxs \<Longrightarrow>
   lxs = iterates (case_IO undefined (\<lambda>p n. Out p (f n))) (Out p' n) \<Longrightarrow>
   \<not> is_Inp x"
  apply (induct lxs arbitrary: f p' n rule: lset_induct)
  subgoal
    apply (subst (asm) iterates.code)
    apply auto
    done
  subgoal
    apply (subst (asm) (2) iterates.code)
    apply auto
    done
  done

corec while_body_op where
  "while_body_op P f b = (
   let read_1 = Read (1::2) (case_observation (\<lambda> x. if P x then Write (while_body_op P f b) (2::2) x else Write (while_body_op P f b) (1::2) (f x)) (while_body_op P f b) End) in
   if b
   then
     read_1
   else
     Read 2 (case_observation (\<lambda> x. if P x then Write read_1 2 x else Write read_1 1 (f x)) read_1 (while_body_op P f True))
   )"


abbreviation "while_op buf P f \<equiv> loop_op
  (\<lambda>x. if x = 1 then Some 1 else None) buf (while_body_op P f False)"
  (* 
value "lhd (produce (while_op is_even Suc) (\<lambda> x. if x = 2 then LCons 0 LNil else LNil) 1)" 
*)

coinductive trace_while_body_True for P f where
  "trace_while_body_True P f (LCons (Inp 1 EOS) LNil)"
| "trace_while_body_True P f ios \<Longrightarrow> P x \<Longrightarrow> trace_while_body_True P f (LCons (Inp 1 (Observed x)) (LCons (Out 2 x) ios))"
| "trace_while_body_True P f ios \<Longrightarrow> \<not> P x \<Longrightarrow> trace_while_body_True P f (LCons (Inp 1 (Observed x)) (LCons (Out 1 (f x)) ios))"
| "trace_while_body_True P f ios \<Longrightarrow> trace_while_body_True P f (LCons (Inp 1 EOB) ios)"

coinductive trace_while_body_False for P f where
  "trace_while_body_False P f ios \<Longrightarrow> P x \<Longrightarrow> P y \<Longrightarrow> trace_while_body_False P f (LCons (Inp 2 (Observed x)) (LCons (Out 2 x) (LCons (Inp 1 (Observed y)) (LCons (Out 2 y) ios))))"
| "trace_while_body_False P f ios \<Longrightarrow> \<not> P x \<Longrightarrow> P y \<Longrightarrow> trace_while_body_False P f (LCons (Inp 2 (Observed x)) (LCons (Out 1 (f x)) (LCons (Inp 1 (Observed y)) (LCons (Out 2 y) ios))))"
| "trace_while_body_False P f ios \<Longrightarrow> P x \<Longrightarrow> \<not> P y \<Longrightarrow> trace_while_body_False P f (LCons (Inp 2 (Observed x)) (LCons (Out 2 x) (LCons (Inp 1 (Observed y)) (LCons (Out 1 (f y)) ios))))"
| "trace_while_body_False P f ios \<Longrightarrow> \<not> P x \<Longrightarrow> \<not> P y \<Longrightarrow> trace_while_body_False P f (LCons (Inp 2 (Observed x)) (LCons (Out 1 (f x)) (LCons (Inp 1 (Observed y)) (LCons (Out 1 (f y)) ios))))"
| "trace_while_body_False P f ios \<Longrightarrow> P x \<Longrightarrow> trace_while_body_False P f  (LCons (Inp 2 (Observed x)) (LCons (Out 2 x) (LCons (Inp 1 EOB) ios)))"
| "P x \<Longrightarrow> trace_while_body_False P f  (LCons (Inp 2 (Observed x)) (LCons (Out 2 x) (LCons (Inp 1 EOS) LNil)))"
| "trace_while_body_False P f ios \<Longrightarrow> \<not> P x \<Longrightarrow> trace_while_body_False P f (LCons (Inp 2 (Observed x)) (LCons (Out 1 (f x)) (LCons (Inp 1 EOB) ios)))"
| "\<not> P x \<Longrightarrow> trace_while_body_False P f (LCons (Inp 2 (Observed x)) (LCons (Out 1 (f x)) (LCons (Inp 1 EOS) LNil)))"
| "P x \<Longrightarrow> trace_while_body_False P f (LCons (Inp 2 (Observed x)) (LCons (Out 2 x) (LCons (Inp 1 EOS) LNil)))"
| "trace_while_body_False P f ios \<Longrightarrow> P x \<Longrightarrow> trace_while_body_False P f (LCons (Inp 2 EOB) (LCons (Inp 1 (Observed x)) (LCons (Out 2 x) ios)))"
| "trace_while_body_False P f ios \<Longrightarrow> \<not> P x \<Longrightarrow> trace_while_body_False P f (LCons (Inp 2 EOB) (LCons (Inp 1 (Observed x)) (LCons (Out 1 (f x)) ios)))"
| "trace_while_body_False P f ios \<Longrightarrow> trace_while_body_False P f  (LCons (Inp 2 EOB) (LCons (Inp 1 EOB) ios))"
| "trace_while_body_False P f (LCons (Inp 2 EOB) (LCons (Inp 1 EOS) LNil))"
| "trace_while_body_True P f ios \<Longrightarrow> trace_while_body_False P f  (LCons (Inp 2 EOS) ios)"

lemma traced_trace_while_body_True:
  "traced (while_body_op P f True) ios \<Longrightarrow>
   trace_while_body_True P f ios"
  apply (coinduction arbitrary: ios)
  subgoal for ios
    apply (subst (asm) while_body_op.code)
    apply simp
    apply (elim traced_ReadE)
    apply (simp split: observation.splits if_splits)
    subgoal
      apply (elim traced_WriteE traced_ReadE)
      apply (auto split: observation.splits)
      done
    subgoal
      by fastforce
    subgoal
      by fastforce
    done
  done


lemma traced_trace_while_body_False:
  "traced (while_body_op P f False) ios \<Longrightarrow>
   trace_while_body_False P f ios"
  apply (coinduction arbitrary: ios)
  subgoal for ios
    apply (subst (asm) while_body_op.code)
    unfolding Let_def
    apply (simp split: observation.splits if_splits)
    apply (elim traced_ReadE)
    apply (simp split: observation.splits if_splits)
       apply (auto split: observation.splits if_splits dest: traced_trace_while_body_True)
    done
  done

lemma trace_while_body_True_traced:
  "trace_while_body_True P f ios \<Longrightarrow>
   traced (while_body_op P f True) ios"
  apply (coinduction arbitrary: ios rule: traced_coinduct_upto)
  subgoal for ios
    apply (erule trace_while_body_True.cases)
       apply simp_all
    subgoal
      apply (subst while_body_op.code)
      apply (auto intro: End traced_cong.intros)
      done
    subgoal
      apply (subst (1 2) while_body_op.code)
      apply simp
      apply (intro tc_write)
      apply (subst (4) while_body_op.code)
      apply simp
      apply (rule tc_base)
      apply auto
      done
    subgoal
      apply (subst (1) while_body_op.code)
      apply (auto intro: traced_cong.intros)
      done
    subgoal
      apply (subst (1) while_body_op.code)
      apply (auto intro: traced_cong.intros)
      done
    done
  done

lemma trace_while_body_False_traced:
  "trace_while_body_False P f ios \<Longrightarrow>
   traced (while_body_op P f False) ios"
  apply (coinduction arbitrary: ios rule: traced_coinduct_upto)
  subgoal for ios
    apply (subst while_body_op.code)
    unfolding Let_def
    apply (erule trace_while_body_False.cases)
                 apply (auto simp add: tc_base tc_read tc_write End Read Write tc_traced dest: trace_while_body_True_traced)
    done
  done

lemma while_body_op_traced_correctness:
  "traced (while_body_op P f False) ios = trace_while_body_False P f ios"
  using trace_while_body_False_traced traced_trace_while_body_False by blast

lemma traced_map_op_lmap_case_IO:
  "traced op ios \<Longrightarrow>
   traced (map_op f g op) (lmap (case_IO (\<lambda> p ob. Inp (f p) ob) (\<lambda> p x. Out (g p) x)) ios)"
  apply (coinduction arbitrary: op ios)
  subgoal for op ios
    apply (cases op)
      apply force+
    done
  done

coinductive trace_while_True_op for P f where
  "BHD 1 buf = EOS \<Longrightarrow> trace_while_True_op P f buf LNil"
| "trace_while_True_op P f (BENQ 1 (f x) (BTL 1 buf)) ios \<Longrightarrow> BHD 1 buf = Observed x \<Longrightarrow> \<not> P x \<Longrightarrow> trace_while_True_op P f buf ios"
| "trace_while_True_op P f (BTL 1 buf) ios \<Longrightarrow> BHD 1 buf = Observed x \<Longrightarrow> P x \<Longrightarrow> trace_while_True_op P f buf (LCons (Out 2 x) ios)"
| "trace_while_True_op P f buf ios \<Longrightarrow> BHD 1 buf = EOB \<Longrightarrow> trace_while_True_op P f buf ios"

coinductive trace_while_op for P f where
  "BHD 1 buf = EOS \<Longrightarrow> trace_while_op P f buf LNil"
| "BHD 1 buf = EOS \<Longrightarrow> P x \<Longrightarrow> trace_while_op P f buf (LCons (Inp 2 (Observed x)) (LCons (Out 2 x) LNil))"
| "BHD 1 buf = EOS \<Longrightarrow> \<not> P x \<Longrightarrow> trace_while_op P f buf (LCons (Inp 2 (Observed x)) LNil)"
| "BHD 1 buf = EOS \<Longrightarrow> trace_while_op P f buf (LCons (Inp 2 EOB) LNil)"

| "trace_while_op P f buf ios \<Longrightarrow> P x \<Longrightarrow> BHD 1 buf = EOB \<Longrightarrow> trace_while_op P f buf (LCons (Inp 2 (Observed x)) (LCons (Out 2 x) ios))"
| "trace_while_op P f (BTL 1 buf) ios \<Longrightarrow> P x \<Longrightarrow> P y \<Longrightarrow> BHD 1 buf = Observed y \<Longrightarrow> trace_while_op P f buf (LCons (Inp 2 (Observed x)) (LCons (Out 2 x) (LCons (Out 2 y) ios)))"
| "trace_while_op P f (BENQ 1 (f y) (BTL 1 buf)) ios \<Longrightarrow> P x \<Longrightarrow> \<not> P y \<Longrightarrow> BHD 1 buf = Observed y \<Longrightarrow> trace_while_op P f buf (LCons (Inp 2 (Observed x)) (LCons (Out 2 x) ios))"
| "trace_while_op P f buf ios \<Longrightarrow> P x \<Longrightarrow> BHD 1 buf = EOB \<Longrightarrow> trace_while_op P f buf (LCons (Inp 2 (Observed x)) (LCons (Out 2 x) ios))"
| "trace_while_op P f (BENQ 1 (f y) (BTL 1 (BENQ 1 (f x) buf))) ios \<Longrightarrow> \<not> P x \<Longrightarrow> \<not> P y \<Longrightarrow> BHD 1 (BENQ 1 (f x) buf) = Observed y \<Longrightarrow> trace_while_op P f buf (LCons (Inp 2 (Observed x)) ios)"
| "trace_while_op P f (BTL 1 (BENQ 1 (f x) buf)) ios \<Longrightarrow> \<not> P x \<Longrightarrow> P y \<Longrightarrow> BHD 1 (BENQ 1 (f x) buf) = Observed y \<Longrightarrow> trace_while_op P f buf (LCons (Inp 2 (Observed x)) (LCons (Out 2 y) ios))"

| "trace_while_op P f (BTL 1 buf) ios \<Longrightarrow> BHD (1::2) buf = Observed x \<Longrightarrow> P x \<Longrightarrow> trace_while_op P f buf (LCons (Inp 2 EOB) (LCons (Out 2 x) ios))"
| "trace_while_op P f (BENQ 1 (f x) (BTL 1 buf)) ios \<Longrightarrow> BHD 1 buf = Observed x \<Longrightarrow> \<not> P x \<Longrightarrow> trace_while_op P f buf (LCons (Inp 2 EOB) ios)"
| "trace_while_op P f buf ios \<Longrightarrow> BHD 1 buf = EOB \<Longrightarrow> trace_while_op P f buf (LCons (Inp 2 EOB) ios)"
| "trace_while_True_op P f buf ios \<Longrightarrow>  trace_while_op P f buf (LCons (Inp 2 EOS) ios)"

(* FIXME: move me *)
lemma ran_dom_Some1[simp]:
  "(2::2) \<notin> ran (\<lambda>x. if x = 1 then Some 1 else None)"
  "(2::2) \<notin> dom (\<lambda>x. if x = 1 then Some 1 else None)"
  "1 \<in> ran (\<lambda>x. if x = 1 then Some 1 else None)"
  "1 \<in> dom (\<lambda>x. if x = 1 then Some 1 else None)"
  unfolding ran_def dom_def
     apply auto
  done

(* FIXME: move me *)
lemma BHD_benqD:
  "ob = BHD (buf 1) (benq x) \<Longrightarrow>
   ob \<noteq> EOS \<and> ob \<noteq> EOB"
  apply (induct "buf 1" arbitrary: buf)
    apply auto[1]
  subgoal
    by force
  subgoal
    by (metis benq.simps(3) bhd.simps(3) observation.disc(1) observation.disc(2) observation.disc(3))
  done

lemma trace_while_body_True_trace_while_True_op_lfilter:
  "trace_while_body_True P f ios \<Longrightarrow>
   causal (\<lambda>x. if x = (1::2) then Some (1::2) else None) buf ios \<Longrightarrow>
   trace_while_True_op P f buf (lfilter (visible_IO (\<lambda>x. if x = 1 then Some 1 else None)) ios)"
  apply (coinduction arbitrary: buf ios)
  subgoal for buf ios
    apply (erule trace_while_body_True.cases)
       apply simp_all
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      apply (rule disjI2)
      apply (rule disjI1)
      apply force
      done
    subgoal
      by (smt (verit, ccfv_SIG) bhd.elims btl.simps(1) causal_Inp fun_upd_triv observation.distinct(5) observation.simps(3) ran_dom_Some1(3)) 
    done
  done

lemma traced_while_op:
  "traced (while_op buf P f) ios \<Longrightarrow>
   trace_while_op P f buf ios"
  unfolding traced_loop_op while_body_op_traced_correctness
  apply (elim exE conjE)
  subgoal for ios
    apply hypsubst_thin
    apply (coinduction arbitrary: buf ios)
    subgoal for buf ios
      apply (erule trace_while_body_False.cases)
                   apply (simp_all add: )
      subgoal
        by auto
      subgoal
        by auto
      subgoal
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule disjI2)
        apply force
        done
      subgoal
        apply (rule disjI2)
        apply fastforce
        done
      subgoal
        apply (rule disjI2)
        apply auto
        by (metis (no_types, lifting) bhd.elims btl.simps(1) fun_upd_triv observation.distinct(5) observation.simps(3))
      subgoal
        by auto
      subgoal
        by (auto dest!: BHD_benqD)
      subgoal
        by (auto dest!: BHD_benqD)
      subgoal
        by auto
      subgoal
        by auto
      subgoal
        apply clarsimp
        apply fastforce
        done
      subgoal
        apply clarsimp
        apply (smt (verit, best) bhd.elims btl.simps(1) causal_Inp fun_upd_triv observation.distinct(5) observation.simps(3) ran_dom_Some1(3))
        done
      subgoal
        by (auto simp add: trace_while_op.intros(1))
      subgoal for ios
        by (auto dest: trace_while_body_True_trace_while_True_op_lfilter)
      done
    done
  done

coinductive history_while_op for P f where
  "history_while_op P f buf lxs LNil"
| "history_while_op P f buf lxs lys \<Longrightarrow> P x \<Longrightarrow> history_while_op P f buf (LCons x lxs) (LCons x lys)"
| "history_while_op P f (BTL 1 buf) lxs lys \<Longrightarrow> P x \<Longrightarrow> history_while_op P f buf lxs (LCons x lys)"
| "history_while_op P f buf lxs lys \<Longrightarrow> BHD 1 buf = EOB \<Longrightarrow> history_while_op P f buf lxs lys"
| "history_while_op P f (BENQ 1 (f x) (BTL 1 buf)) lxs lys \<Longrightarrow> \<not> P x \<Longrightarrow> BHD (1::2) buf = Observed x \<Longrightarrow> history_while_op P f buf lxs (LCons x lys)"

inductive history_while_op_cong for R P f where
  "R P f buf lxs lys \<Longrightarrow> history_while_op_cong R P f buf lxs lys"
| "history_while_op P f buf lxs lys \<Longrightarrow> history_while_op_cong R P f buf lxs lys"
| "history_while_op_cong R P f buf lxs lys \<Longrightarrow> P x \<Longrightarrow> history_while_op_cong R P f buf (LCons x lxs) (LCons x lys)"
| "history_while_op_cong R P f (BTL 1 buf) lxs lys \<Longrightarrow> P x \<Longrightarrow> history_while_op_cong R P f buf lxs (LCons x lys)"
| "history_while_op_cong R P f buf lxs lys \<Longrightarrow> BHD 1 buf = EOB \<Longrightarrow> history_while_op_cong R P f buf lxs lys"
| "history_while_op_cong R P f (BENQ 1 (f x) (BTL 1 buf)) lxs lys \<Longrightarrow> \<not> P x \<Longrightarrow> BHD (1::2) buf = Observed x \<Longrightarrow> history_while_op_cong R P f buf lxs (LCons x lys)"

lemma history_while_op_cong_disj[simp]:
  "(history_while_op_cong R P f buf lxs lys \<or> history_while_op P f buf lxs lys) = history_while_op_cong R P f buf lxs lys"
  apply (auto intro: history_while_op_cong.intros)
  done

thm history_while_op.coinduct[where X="history_while_op_cong R P f" and f=f and P=P, of buf lxs lys, simplified]

(* FIXME: move me *)
lemma is_1_or_2[simp]:
  "(p::2) = 1 \<or> p = 2"
  apply (cases p)
  apply auto
  subgoal for z
    apply (cases z)
     apply auto
    subgoal for n
      apply (cases n)
       apply auto[1]
      apply simp
      apply (smt (verit, ccfv_SIG) of_int_of_nat_eq of_nat_0 of_nat_0_le_iff)
      done
    done
  done

(* FIXME: move me *)
lemma fun_if_then_else_2_eq[simp]:
  "(\<lambda>p. if p = (2::2) then lxs p else lys p) = (\<lambda>p. if p = 2 then lxs' p else lys' p) \<longleftrightarrow>
   lxs 2 = lxs' 2 \<and> lys 1 = lys' 1"
  apply (rule iffI)
  subgoal
    apply (rule conjI)
     apply metis
    apply (metis (full_types) ran_dom_Some1(1) ran_dom_Some1(3))
    done
  subgoal
    apply (rule ext)
    apply auto
    apply (metis is_1_or_2)
    done
  done


lemma history_while_op_coinduct_upto:
  "R P f buf lxs lys \<Longrightarrow>
(\<And>x1 x2 x3.
    R P f x1 x2 x3 \<Longrightarrow>
    x3 = LNil \<or>
    (\<exists>lxs lys x. x2 = LCons x lxs \<and> x3 = LCons x lys \<and> history_while_op_cong R P f x1 lxs lys \<and> P x) \<or>
    (\<exists>lys x. x3 = LCons x lys \<and> history_while_op_cong R P f (x1(1 := btl (x1 1))) x2 lys \<and> P x) \<or>
    history_while_op_cong R P f x1 x2 x3 \<and> BHD 1 x1 = EOB \<or>
    (\<exists>x lys. x3 = LCons x lys \<and> history_while_op_cong R P f (x1(1 := benq (f x) (btl (x1 1)))) x2 lys \<and> \<not> P x \<and> BHD 1 x1 = Observed x)) \<Longrightarrow>
history_while_op P f buf lxs lys"
  sorry

lemma
  "history (while_op buf P f) (\<lambda> x. if x = 2 then lxs else LNil) (\<lambda> x. if x = 2 then lys else LNil)  \<Longrightarrow>
   history_while_op P f buf lxs lys"
  unfolding history_def
  apply (elim exE disjE conjE)
  subgoal for ios
    apply (drule traced_while_op)
    apply (coinduction arbitrary: buf lxs lys ios rule: history_while_op_coinduct_upto)
    subgoal for buf lxs lys ios
      apply (erule trace_while_op.cases)
      subgoal for buf
        apply auto
        apply hypsubst_thin
        apply (cases lys)
         apply (meson neq_LNil_conv)+
        done
                  prefer 5
      subgoal for buf ios x y
        apply hypsubst_thin
        apply (cases lxs; cases lys)
           apply simp_all
        subgoal
          apply hypsubst_thin
          apply auto
          using not_lnull_conv apply fastforce
          done
        subgoal for x' lxs'
          apply hypsubst_thin
          apply auto
          subgoal by (smt (verit) LCons_lprefix_LCons)
          subgoal
            apply (rule history_while_op_cong.intros(4))
             apply simp_all
            apply (rule history_while_op_cong.intros(1))
            apply simp
            apply (rule exI[of _ ios])
            apply auto
            subgoal
              by (smt (verit, best) LCons_lprefix_LCons bot2E lproject_LCons(2))
            subgoal for p
              apply (drule spec[of _ p])
              apply auto
              done
            subgoal 
              apply (rule ext)
              apply auto
              apply (metis is_1_or_2)
              done
            done
          subgoal by (smt (verit) LCons_lprefix_LCons)
          done
        done


end
      apply (rule disjI2)
      apply (rule disjI1)
      apply auto
      defer
      subgoal
        by (metis (mono_tags, opaque_lifting) llist.inject)
      subgoal
        apply (cases lys')
        subgoal
          apply simp
          by (simp add: history_while_op.intros(1) history_while_op_cong.intros(2))
        subgoal
          apply simp
          apply (rule  history_while_op_cong.intros(2))

      



        apply (subgoal_tac "y = "

end
        apply (cases lxs; cases lys)
           apply auto
   


end


      subgoal for x' x22 x21a x22a
        apply (subgoal_tac "x = x'")
        apply simp
        apply (smt (verit, ccfv_SIG) LCons_lprefix_LCons)
        done

          thm cong


end