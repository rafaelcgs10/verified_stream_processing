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

inductive_cases loop_producing_ReadE: "loop_producing wire buf (Read p f) n"
inductive_cases loop_producing_WriteE: "loop_producing wire buf (Write op p x) n"
inductive_cases loop_producing_SucE: "loop_producing wire buf op (Suc n)"
inductive_cases loop_producing_0E: "loop_producing wire buf op 0"


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
  oops

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

inductive causal_cong for R wire where
  cc_causal:  "causal wire buf ios \<Longrightarrow> causal_cong R wire buf ios"
| cc_base:  "R wire buf ios \<Longrightarrow> causal_cong R wire buf ios"
| "causal_cong R wire (BTL p buf) ios \<Longrightarrow> y = BHD p buf \<Longrightarrow> p \<in> ran wire \<Longrightarrow> causal_cong R wire buf (LCons (Inp p y) ios)"
| "causal_cong R wire buf ios \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> causal_cong R wire buf (LCons (Inp p y) ios)"
| "causal_cong R wire (BENQ p' y buf) ios \<Longrightarrow> wire p = Some p' \<Longrightarrow> causal_cong R wire buf (LCons (Out p y) ios)"
| "causal_cong R wire buf ios \<Longrightarrow> wire p = None \<Longrightarrow> causal_cong R wire buf (LCons (Out p y) ios)"

lemma causal_cong_disj[simp]:
  "(causal_cong R wire buf ios \<or> causal wire buf ios) = causal_cong R wire buf ios"
  by (auto intro: causal_cong.intros)

lemma causal_coinduct_upto:
  "R wire buf ios \<Longrightarrow>
   (\<And>x1 x2.
     R wire x1 x2 \<Longrightarrow>
     (\<exists>p ios y. x2 = LCons (Inp p y) ios \<and> causal_cong R wire (x1(p := btl (x1 p))) ios \<and> y = BHD p x1 \<and> p \<in> ran wire) \<or>
     (\<exists>ios p. (\<exists>y. x2 = LCons (Inp p y) ios) \<and> causal_cong R wire x1 ios \<and> p \<notin> ran wire) \<or>
     (\<exists>p' y ios p. x2 = LCons (Out p y) ios \<and> causal_cong R wire (x1(p' := benq y (x1 p'))) ios \<and> wire p = Some p') \<or>
     (\<exists>ios p. (\<exists>y. x2 = LCons (Out p y) ios) \<and> causal_cong R wire x1 ios \<and> wire p = None) \<or> x2 = LNil) \<Longrightarrow>
   causal wire buf ios"
  apply (rule causal.coinduct[where X="causal_cong R wire", of buf ios wire, simplified])
   apply (auto intro: cc_base)[1]
  subgoal premises prems for buf ios
    using prems(3,2,1) apply -
    apply (induct buf ios rule: causal_cong.induct)
    subgoal for buf ios
      subgoal
        apply (erule causal.cases)
            apply auto
        subgoal
          using causal_cong_disj by blast
        subgoal
          using causal_cong_disj by blast
        subgoal
          using causal_cong_disj by blast
        subgoal
          using cc_causal by blast
        done
      done
    subgoal for buf ios
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      apply auto
      done
    done
  done

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
   let read_1 = Read (1::2) (case_observation
       (\<lambda> x. if P x then Write (while_body_op P f b) (2::2) x else Write (while_body_op P f b) (1::2) (f x))
        (if b then End else while_body_op P f b) End) in
   if b
   then
     read_1
   else
     Read 2 (case_observation (\<lambda> x. if P x then Write read_1 2 x else Write read_1 1 (f x)) read_1 (while_body_op P f True))
   )"

abbreviation "while_op buf P f \<equiv> loop_op
  (\<lambda>x. if x = 1 then Some 1 else None) buf (while_body_op P f False)"

value "list_of (produce (while_op (\<lambda> _. BEmpty) (((\<le>) 10) o snd) (\<lambda> (x, y). (x, Suc y))) (\<lambda> x. if x = 2 then (llist_of [(0::nat, 3), (1::nat, 3), (2::nat, 8)]) else LNil) 2)"

coinductive trace_while_body_True for P f where
  "trace_while_body_True P f (LCons (Inp 1 EOS) LNil)"
| "trace_while_body_True P f ios \<Longrightarrow> P x \<Longrightarrow> trace_while_body_True P f (LCons (Inp 1 (Observed x)) (LCons (Out 2 x) ios))"
| "trace_while_body_True P f ios \<Longrightarrow> \<not> P x \<Longrightarrow> trace_while_body_True P f (LCons (Inp 1 (Observed x)) (LCons (Out 1 (f x)) ios))"
| "trace_while_body_True P f (LCons (Inp 1 EOB) LNil)"

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
    subgoal
      by auto
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
      apply (subst (3) while_body_op.code)
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
      apply (auto simp add: End tc_traced intro: traced_cong.intros)
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

lemma while_body_op_traced_True_correctness:
  "traced (while_body_op P f True) ios = trace_while_body_True P f ios"
  using trace_while_body_True_traced traced_trace_while_body_True by blast

lemma traced_map_op_lmap_case_IO:
  "traced op ios \<Longrightarrow>
   traced (map_op f g op) (lmap (case_IO (\<lambda> p ob. Inp (f p) ob) (\<lambda> p x. Out (g p) x)) ios)"
  apply (coinduction arbitrary: op ios)
  subgoal for op ios
    apply (cases op)
      apply force+
    done
  done

(*
coinductive trace_while_True_op for P f where
  "BHD 1 buf = EOS \<Longrightarrow> trace_while_True_op P f buf LNil"
| "BHD 1 buf = EOB \<Longrightarrow> trace_while_True_op P f buf (LNil::(2, 2, 'a) IO llist)"
| "trace_while_True_op P f (BENQ 1 (f x) (BTL 1 buf)) (LCons (Out 2 y) ios) \<Longrightarrow>
   BHD 1 buf = Observed x \<Longrightarrow> \<not> P x \<Longrightarrow> (\<exists> x \<in> set_buf (buf 1). MIN n.(f ^^ n) x = y \<and> P y) \<Longrightarrow> trace_while_True_op P f buf (LCons (Out 2 y) ios)"
| "trace_while_True_op P f (BTL 1 buf) ios \<Longrightarrow> BHD 1 buf = Observed x \<Longrightarrow> P x \<Longrightarrow> trace_while_True_op P f buf (LCons (Out 2 x) ios)"

*)

(* FIXME: move me *)
fun buf_to_list where
  "buf_to_list BEmpty = []"
| "buf_to_list BEnded = []"
| "buf_to_list (BCons x xs) = x # buf_to_list xs"


fun list_to_buf where
  "list_to_buf [] = BEmpty"
| "list_to_buf (x # xs) = BCons x (list_to_buf xs)"

lemma buf_to_list_list_to_buf:
  "buf_to_list (list_to_buf xs) = xs"
  by (induct xs) auto

lemma set_buf_to_list_set_buf:
  "set (buf_to_list buf) = set_buf buf"
  by (induct buf) auto

lemma set_buf_list_to_buf_set:
  "set_buf (list_to_buf xs) = set xs"
  by (induct xs) auto

lemma buf_to_list_benq[simp]:
  "buf_to_list (benq x buf) = buf_to_list buf @ [x]"
  by (induct buf) auto

lemma buf_to_list_btl[simp]:
  "buf_to_list (btl buf) = tl (buf_to_list buf) "
  by (induct buf) auto

inductive trace_while_True_op for P f where
  "\<not> (\<exists> x \<in> set (buf_to_list (buf 1)). \<exists> n. P ((f ^^ n) x)) \<Longrightarrow> trace_while_True_op P f buf (LNil::(2, 2, 'a) IO llist)"
| "trace_while_True_op P f (BENQ 1 (f x) (BTL 1 buf)) (LCons (Out 2 y) ios) \<Longrightarrow>
   BHD 1 buf = Observed x \<Longrightarrow> \<not> P x \<Longrightarrow> x \<noteq> y \<Longrightarrow> (\<exists> x \<in> set (buf_to_list (buf 1)). \<exists> n.(f ^^ n) x = y \<and> P y) \<Longrightarrow>
   trace_while_True_op P f buf (LCons (Out 2 y) ios)"
| "trace_while_True_op P f (BTL 1 buf) ios \<Longrightarrow> BHD 1 buf = Observed x \<Longrightarrow> P x \<Longrightarrow> trace_while_True_op P f buf (LCons (Out 2 x) ios)"

coinductive trace_while_op for P f where
  "BHD 1 buf = EOS \<Longrightarrow> P x \<Longrightarrow> trace_while_op P f buf (LCons (Inp 2 (Observed x)) (LCons (Out 2 x) LNil))"
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
| "trace_while_True_op P f buf ios \<Longrightarrow> trace_while_op P f buf (LCons (Inp 2 EOS) (ios::(2, 2, 'a) IO llist))"

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


lemma pow_f_f_Suc:
  "(f ^^ n) (f x) = (f ^^ (Suc n)) x"
  by (metis comp_apply funpow_Suc_right)

lemma f_Least:
  "\<not> P x \<Longrightarrow>
   \<exists>n. P ((f ^^ n) x) \<Longrightarrow>
   (f ^^ (LEAST n. P ((f ^^ n) (f x)))) (f x) = (f ^^ (LEAST n. P ((f ^^ n) x))) x"
  apply (subst (2) pow_f_f_Suc)
  apply (elim exE)
  subgoal for n
    apply (rule cong[of "f ^^ Suc (LEAST n. P ((f ^^ n) (f x)))" "f ^^ (LEAST n. P ((f ^^ n) x))"])
     apply (simp_all add: Least_Suc funpow_swap1)
    done
  done

lemma trace_while_True_op_soundess:
  "trace_while_True_op P f buf ios \<Longrightarrow>
   x \<in> set_buf (buf 1) \<Longrightarrow>
   n = (LEAST n. P ((f ^^ n) x)) \<Longrightarrow>
   \<exists> n. P ((f ^^ n) x) \<Longrightarrow>
   Out 2 ((f ^^ n) x) \<in> lset ios"
  apply (induct buf ios arbitrary: x n rule: trace_while_True_op.induct)
    apply simp_all
  subgoal
    by (simp add: set_buf_to_list_set_buf)
  subgoal for x buf y ios x' n
    apply (cases "buf 1")
      apply simp_all
    subgoal
      apply (elim disjE)
      subgoal
        apply (cases n)
        subgoal
          apply clarsimp
          apply (metis LeastI funpow.simps(2) funpow_0 funpow_swap1 o_apply)
          done
        subgoal for n'
          apply (cases "\<exists>n. P ((f ^^ n) (f x))")
          subgoal
            apply clarsimp
            apply (drule meta_spec[of _ "f x'"])
            apply (drule meta_spec)
            apply (drule meta_mp)
            using set_buf_to_list_set_buf apply fastforce
            apply (drule meta_mp)
             apply (rule refl)
            apply hypsubst_thin
            apply (drule meta_mp)
             apply blast
            using f_Least apply (metis pow_f_f_Suc)
            done
          subgoal
            apply clarsimp
            apply (metis LeastI pow_f_f_Suc)
            done
          done
        done
      subgoal
        apply (drule meta_spec[of _ "x'"])
        apply (drule meta_spec)
        apply (drule meta_mp)
         apply (metis Un_insert_right buf_to_list_benq insert_iff list.set(1) list.set(2) set_append set_buf_to_list_set_buf sup_bot.right_neutral)
        apply (drule meta_mp)
         apply (rule refl)
        apply (drule meta_mp)
         apply blast
        apply auto
        done
      done
    done
  subgoal for buf ios x x' n
    apply hypsubst_thin
    apply (cases "buf 1")
      apply simp_all
    subgoal for x'' buf'
      apply (elim disjE)
      subgoal
        by simp
      subgoal
        apply simp
        done
      done
    done
  done

lemma not_trace_while_True_op_LNil:
  "\<not> trace_while_True_op P f buf LNil \<Longrightarrow>
   \<exists> x \<in> set (buf_to_list (buf 1)). \<exists> n. P ((f ^^ n) x)"
  using trace_while_True_op.intros(1) by blast

lemma trace_while_True_op_all_not_P:        
  "(\<forall> x \<in> set_buf (buf 1). \<not> (\<exists> n. P ((f ^^ n) x))) \<Longrightarrow>
  trace_while_True_op P f buf LNil"
  by (simp add: set_buf_to_list_set_buf trace_while_True_op.intros(1))

lemma trace_while_True_op_some_P:        
  "\<not> (\<forall> x \<in> set_buf (buf 1). \<not> (\<exists> n. P ((f ^^ n) x))) \<Longrightarrow>
  trace_while_True_op P f buf ios \<Longrightarrow>
  ios \<noteq> LNil"
  by (metis llist.simps(3) set_buf_to_list_set_buf trace_while_True_op.simps)

lemma in_buf_to_list_in_tl_buf_to_list:
  "x' \<in> set (buf_to_list buf) \<Longrightarrow>
   P ((f ^^ n') x') \<Longrightarrow>
   bhd buf = Observed x \<Longrightarrow>
   \<forall>n. \<not> P ((f ^^ n) x) \<Longrightarrow>
   x' \<in> set (tl (buf_to_list buf))"
  by (induct buf) auto

lemma trace_while_True_op_BHD_False:     
  "trace_while_True_op P f (BENQ 1 (f x) (BTL 1 buf)) ios \<Longrightarrow>
   BHD 1 buf = Observed x \<Longrightarrow>
  \<not> P x \<Longrightarrow>
  trace_while_True_op P f buf ios"
  apply (induct "BENQ 1 (f x) (BTL 1 buf)" ios arbitrary: buf x rule: trace_while_True_op.induct)
  subgoal
    apply simp
    apply auto
    apply (smt (z3) bhd.simps(3) buf.set_cases buf_to_list.simps(3) funpow_0 lessI less_Suc_eq_0_disj list.sel(3) observation.inject pow_f_f_Suc set_buf_to_list_set_buf trace_while_True_op_all_not_P)
    done
  subgoal for x' y ios buf x
    apply (cases "\<not> (\<exists> n. P ((f ^^ n) x))")
    subgoal
      apply auto
      subgoal
        by (metis funpow.simps(2) funpow_swap1 o_apply)
      subgoal for x'' n
        apply (rule trace_while_True_op.intros(2))
            defer
            apply assumption
           apply (metis funpow_0)
          apply (metis funpow_0)
         apply (metis bhd.simps(1) bhd.simps(2) btl.simps(3) buf_to_list.elims buf_to_list_btl insert_iff list.set(2) observation.distinct(1) observation.distinct(3))
        apply (cases "\<forall>n. \<not> P ((f ^^ n) x')")
        subgoal
          apply hypsubst_thin
          apply (drule meta_spec[of _ "BENQ 1 (f x) (BTL 1 buf)"])
          apply (drule meta_spec[of _ "x'"])
          apply simp
          done
        subgoal
          apply clarsimp
          done
        done
      done
    subgoal
      apply auto
      subgoal for n n'
        by (smt (verit, del_insts) bhd.elims buf_to_list.simps(3) fun_upd_same fun_upd_upd insertI1 list.set(2) observation.distinct(3) observation.inject observation.simps(3) pow_f_f_Suc trace_while_True_op.intros(2))
      subgoal
        apply (rule trace_while_True_op.intros(2))
            defer
            apply assumption
           apply (metis funpow_0)
          apply (metis funpow_0)
         apply (metis bhd.simps(1) bhd.simps(2) btl.simps(3) buf_to_list.elims buf_to_list_btl insert_iff list.set(2) observation.distinct(1) observation.distinct(3))
        apply (cases "\<forall>n. \<not> P ((f ^^ n) x')")
        subgoal
          apply hypsubst_thin
          apply (drule meta_spec[of _ "BENQ 1 (f x) (BTL 1 buf)"])
          apply (drule meta_spec[of _ "x'"])
          apply simp
          done
        apply simp
        done
      done
    done
  subgoal for ios x buf x'
    apply simp
    apply (cases "buf 1")
      apply simp_all
    subgoal for x'' buf'
      apply hypsubst_thin
      apply (cases "buf'")
        apply simp_all
      subgoal
        by (smt (verit, del_insts) benq.simps(1) bhd.simps(3) btl.simps(3) buf_to_list.simps(3) fun_upd_same fun_upd_upd funpow_0 insert_iff list.set(2) pow_f_f_Suc trace_while_True_op.intros(2) trace_while_True_op.intros(3))
      subgoal
        by (smt (verit, del_insts) benq.simps(2) bhd.simps(3) btl.simps(3) buf_to_list.simps(3) fun_upd_same fun_upd_upd funpow_0 insert_iff list.set(2) pow_f_f_Suc trace_while_True_op.intros(2) trace_while_True_op.intros(3))
      subgoal
        apply hypsubst_thin
        apply (rule trace_while_True_op.intros(2))
            defer
            apply simp_all
          apply force
         apply (meson funpow_0)   
        apply (simp add: trace_while_True_op.intros(3))
        done
      done
    done
  done

lemma trace_while_True_op_inj:
  "trace_while_True_op P f buf ios \<Longrightarrow>
   trace_while_True_op P f buf ios' \<Longrightarrow>
   ios = ios'"
  apply (induct buf ios arbitrary: ios' rule: trace_while_True_op.induct)
  subgoal
    apply (erule trace_while_True_op.cases)
      apply (auto intro: trace_while_True_op.intros)
    apply (metis bhd.elims buf_to_list.simps(3) funpow_0 insert_iff list.set(2) observation.distinct(3) observation.inject observation.simps(3))
    done
  subgoal premises prems for x buf y ios ios'
    using prems(7,1,3,4,5,6) apply -
    apply (erule trace_while_True_op.cases)
      apply auto
    subgoal
      using prems(2) by auto
    subgoal
      using prems(2) by auto
    done
  subgoal premises prems for buf ios x ios'
    using prems(3,1,4-) apply -
    apply (erule trace_while_True_op.cases)
      apply auto
    subgoal
      apply (cases "buf 1")
        apply auto
      apply (erule trace_while_True_op.cases)
        apply auto
       apply (metis funpow_0)
      using prems(2)
      apply auto
      done
    subgoal
      apply (cases "buf 1")
        apply auto
      apply (erule trace_while_True_op.cases)
        apply (auto simp add: prems(2))
      done
    subgoal
      apply (cases "buf 1")
        apply auto
      apply (erule trace_while_True_op.cases)
        apply auto
       apply (metis funpow_0)
      apply (auto simp add: prems(2))
      done
    done
  done

lemma loop_producing_while_body_op_True_gt_0:
  "loop_producing wire buf op n \<Longrightarrow>
   op = while_body_op P f True \<Longrightarrow>
   wire = (\<lambda>x. if x = 1 then Some 1 else None) \<Longrightarrow>
   0 < n"
  apply (induct buf op n arbitrary: rule: loop_producing.induct)
  subgoal
    apply (subst (asm) while_body_op.code)
    apply auto
    done
  subgoal
    apply (subst (asm) while_body_op.code)
    apply auto
    done
  subgoal
    apply (subst (asm) while_body_op.code)
    apply auto
    done
  subgoal
    apply (subst (asm) (2) while_body_op.code)
    apply auto
    done
  subgoal
    apply (subst (asm) (2) while_body_op.code)
    apply auto
    done
  done

lemma loop_producing_while_body_op_True_cases_aux:
  "loop_producing wire buf op (Suc n) \<Longrightarrow>
   op = while_body_op P f True \<Longrightarrow>
   wire = (\<lambda>x. if x = 1 then Some 1 else None) \<Longrightarrow>
   n = 0 \<and> (\<exists> x. BHD 1 buf = Observed x \<and> P x) \<or>
   (n = 0 \<and> BHD 1 buf = EOS) \<or>
  (BHD 1 buf = EOB \<and> n = 0) \<or>
  (\<exists> x. BHD 1 buf = Observed x \<and> \<not> P x \<and> loop_producing (\<lambda>x. if x = 1 then Some 1 else None) (BENQ 1 (f x) (BTL 1 buf)) (while_body_op P f True) (n - 1))"
  apply (induct buf op "Suc n" arbitrary: n rule: loop_producing.induct)
  subgoal for p wire buf fa n
    apply (cases n)
    subgoal
      apply auto
      subgoal
        by (smt (verit) bhd.elims less_numeral_extra(3) loop_producing.simps observation.simps(8) op.distinct(1) op.distinct(5) op.inject(1) op.inject(2) option.discI while_body_op.code zero_less_Suc)
      done
    subgoal for n'
      supply disjCI[rule del]
      apply (cases "BHD 1 buf")
      subgoal
        apply simp
        apply (subst while_body_op.code)
        unfolding Let_def
        apply (elim loop_producing_SucE)
         apply (auto split: if_splits)
        subgoal
          by (simp add: while_body_op.code)
        subgoal
          apply hypsubst_thin
          apply (subst (asm) (3) while_body_op.code)
          apply (auto split: if_splits)
          done
        subgoal
          by (simp add: while_body_op.code)
        subgoal
          apply hypsubst_thin
          apply (subst (asm) (3) while_body_op.code)
          apply (auto split: if_splits)
          done
        subgoal
          by (simp add: while_body_op.code)
        subgoal
          apply hypsubst_thin
          apply (subst (asm) (3) while_body_op.code)
          apply (auto split: if_splits)
          apply (simp add: while_body_op.code)
          done
        subgoal
          by (simp add: while_body_op.code)
        subgoal
          apply hypsubst_thin
          apply (subst (asm) (3) while_body_op.code)
          apply (auto split: if_splits)
          done
        done
      subgoal
        apply (subst (asm) (3) while_body_op.code)
        apply auto
        using loop_producing.intros(1) loop_producing_inject apply blast
        done
      subgoal
        apply (subst (asm) (3) while_body_op.code)
        apply auto
        subgoal
          using loop_producing.intros(1) loop_producing_inject by blast
        done
      done
    done
  subgoal
    apply (subst (asm) (3) while_body_op.code)
    apply auto
    done
  done

(* FIXME: trace_while_True_op is not necessary *)
lemma trace_while_True_op_loop_producing:
  "trace_while_True_op P f buf ios \<Longrightarrow>
   (\<exists> x \<in> set (buf_to_list (buf 1)). \<exists> n. P ((f ^^ n) x)) \<Longrightarrow>
   \<exists> n. loop_producing (\<lambda>x. if x = (1::2) then Some (1::2) else None) buf (while_body_op P f True) n"
  apply (induct buf ios arbitrary: rule: trace_while_True_op.induct)
  subgoal for buf
    apply simp
    done
  subgoal for x buf y ios
    apply auto
    subgoal for xa n x' n'
      apply hypsubst_thin
      apply (subst while_body_op.code)
      unfolding Let_def
      apply auto
      apply (cases "\<exists>n. P ((f ^^ n) (f x))")
      subgoal
        apply simp
        apply auto
        subgoal for m
          apply (rule exI[of _ "Suc (Suc m)"])
          apply (rule loop_producing.intros(4))
           apply simp_all
          apply (rule loop_producing.intros(5))
           apply auto
          done
        done
      subgoal 
        apply simp
        apply (frule in_buf_to_list_in_tl_buf_to_list[where P=P and f=f and x'=x'])
           defer
           apply assumption
        subgoal
          apply auto
          subgoal for k
            apply (cases k)
             apply auto
            apply (metis funpow_swap1)
            done
          done
        subgoal
          apply (drule meta_mp)
           apply (rule bexI[of _ x'])
            apply (rule exI[of _ n'])
            apply auto
          subgoal for m
            apply (rule exI[of _ "Suc (Suc m)"])
            apply (rule loop_producing.intros(4))
             apply simp_all
            apply (rule loop_producing.intros(5))
             apply auto
            done
          done
        apply auto
        done
      done
    done
  subgoal
    apply (subst while_body_op.code)
    unfolding Let_def
    apply auto
    apply (rule exI)
    apply (rule loop_producing.intros(4))
     apply simp_all
    apply (rule loop_producing.intros(3))
    apply auto
    done
  done

abbreviation "while_True_retrace_size1 P f x \<equiv> (if (\<exists> n. P ((f ^^ n) x)) then LEAST i. (P ((f ^^ (i::nat)) x)) else 0)"

fun fuel_calc where
  "fuel_calc P F i [] = i"
| "fuel_calc P F i (x#xs) = (if P x then F x + i + fuel_calc P F 0 xs else fuel_calc P F (Suc i) xs)"


abbreviation "while_True_retrace_size2 P f buf \<equiv> (if \<exists> x \<in> set buf. (\<exists> n. P ((f ^^ n) x)) then length (takeWhile (\<lambda> x. \<not> (\<exists> n. P ((f ^^ n) x ))) buf) else 0)"

lemma Least_Suc_alt:
  "\<not> P 0 \<Longrightarrow>
   P (Suc n) \<Longrightarrow>
   (LEAST i. P (Suc i)) = m \<Longrightarrow> (LEAST i. P i) = Suc m"
  by (simp add: Least_Suc)

lemma Least_less_pow:
  "\<not> P x \<Longrightarrow> P ((f ^^ n) x) \<Longrightarrow> (LEAST i. P ((f ^^ i) (f x))) < (LEAST i. P ((f ^^ i) x))"
  by (smt (verit, ccfv_SIG) LeastI_ex Least_Suc funpow_0 funpow_simps_right(2) lessI linorder_less_linear not_less_Least o_apply)

lemma while_True_retrace_size1_reduces:
  "\<not> P x \<Longrightarrow>
   \<exists> n. P ((f ^^ (Suc n)) x) \<Longrightarrow>
   while_True_retrace_size1 P f (f x) < while_True_retrace_size1 P f x"
  apply (auto simp add:  Least_less_pow funpow_swap1)
  apply (metis comp_eq_dest_lhs funpow_Suc_right)
  done

lemma while_True_retrace_size2_at_0[simp]:
  "Q x \<Longrightarrow>
   length (takeWhile (Not o Q) (x#xs)) = 0"
  apply auto
  done

function while_True_retrace where
  "while_True_retrace P f xs = (if \<exists> x \<in> set xs. (\<exists> n. P ((f ^^ n) x))
   then (case xs of [] \<Rightarrow> [] | x # xs \<Rightarrow> (if P x then x # (while_True_retrace P f xs) else while_True_retrace P f (xs @ [f x])))
   else [])"
   apply auto
  done
termination
  apply (relation "measures [\<lambda>(P, f, buf). length buf, (\<lambda>(P, f, buf). sum_list (map (while_True_retrace_size1 P f) buf)), \<lambda>(P, f, buf). while_True_retrace_size2 P f buf]")
    apply simp
  subgoal
    apply auto
    done
  subgoal
    apply (auto simp add: Least_less_pow takeWhile_eq_Nil_iff)
           defer
           defer
    subgoal
      by (metis (no_types, opaque_lifting) pow_f_f_Suc)
    subgoal
      by (metis (no_types, opaque_lifting) pow_f_f_Suc)
    subgoal
      by (metis (no_types, opaque_lifting) pow_f_f_Suc)
    subgoal
      by (metis (no_types, opaque_lifting) funpow_0 old.nat.exhaust pow_f_f_Suc)
    subgoal
      by (metis (mono_tags, lifting) less_Suc_eq takeWhile_append1)
    subgoal
      by (metis Least_less_pow less_zeroE zero_less_iff_neq_zero)
    subgoal
      by (metis Least_less_pow less_zeroE zero_less_iff_neq_zero)
    subgoal
      by (metis Least_less_pow bot_nat_0.extremum_strict zero_less_iff_neq_zero)
    done
  done

lemma while_True_retrace_simp[simp]:
  "while_True_retrace P f [] = []"
  "while_True_retrace P f (x # xs) = (if P x then x # (while_True_retrace P f xs) else while_True_retrace P f (xs @ [f x]))"
   apply auto
    apply (metis funpow_0)
   apply (metis pow_f_f_Suc)
  apply (metis funpow_0)
  done

declare while_True_retrace.simps[simp del]

lemma while_True_retrace_eq_Nil:
  "(while_True_retrace P f buf = []) \<longleftrightarrow> (\<not> (\<exists> x \<in> set buf. \<exists> n. P ((f ^^ n) x)))"
  apply (rule iffI)
  subgoal 
    apply (auto split: list.splits if_splits)
    subgoal for x n
      apply (induct P f buf arbitrary: x n rule: while_True_retrace.induct)
      apply (simp split: if_splits)
      subgoal for P f buf x n
        apply (cases buf)
         apply (simp_all split: if_splits)
        subgoal for x' buf'
          apply (elim disjE)
          subgoal premises prems
            using prems(1,2,4,5-) apply -
            apply hypsubst_thin
            apply (cases n)
             apply simp
            subgoal for n'
              apply (drule meta_spec[of _ "x'"])
              apply (drule meta_spec[of _ "f x'"])  
              apply (drule meta_spec[of _ n'])
              apply (drule meta_mp)
               apply blast
              apply simp
              apply (drule meta_mp)
               apply (simp add: funpow_swap1)
              apply simp
              done
            done
          subgoal premises prems
            using prems(1,2,4,5-) apply -
            apply hypsubst_thin
            apply (drule meta_spec[of _ "x'"])
            apply (drule meta_spec[of _ "f x'"])  
            apply (drule meta_spec[of _ n])
            apply (drule meta_mp)
             apply blast
            apply simp
            apply (drule meta_mp)
            using prems(4) apply blast
            apply (simp add: funpow_swap1)
            done
          done
        done
      done
    done
  subgoal
    apply (subst while_True_retrace.simps)
    apply (auto split: list.splits)
    done
  done


lemma trace_while_True_op_evidence:
  "trace_while_True_op P f buf (llist_of (map (Out 2) (while_True_retrace P f (buf_to_list (buf 1)))))"
  apply (induct P f "buf_to_list (buf 1)" arbitrary: buf rule: while_True_retrace.induct)
  subgoal for P f buf
    apply (cases "\<forall>x\<in>set (buf_to_list (buf 1)). \<forall>n. \<not> P ((f ^^ n) x)")
    subgoal
      by (auto simp add: while_True_retrace.simps intro: trace_while_True_op.intros)
    subgoal
      apply (cases "buf 1")
        apply (auto intro: trace_while_True_op.intros)[2]
      subgoal premises prems for x buf'
        using prems(3-) apply -
        apply (cases "P x")
        subgoal
          apply (simp only: buf_to_list.simps while_True_retrace_simp if_True list.simps(9) llist_of.simps(2))
          apply (rule trace_while_True_op.intros(3))
          subgoal
            using prems(1) apply -
            apply (metis btl.simps(3) buf_to_list.simps(3) fun_upd_same)
            done
          subgoal
            apply simp
            done
          apply simp
          done
        subgoal
          apply simp
          apply (rule trace_while_True_op_BHD_False[where x=x])
            apply simp_all
          using prems(2) apply -
          apply simp
          apply (drule meta_spec)
          apply (drule meta_spec[of _ "BENQ 1 (f x) (BTL 1 buf)"])
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
           apply simp
          apply simp
          done
        done
      done
    done
  done

lemma P_in_buf_while_body_op_producing:
  "(\<exists> x \<in> set (buf_to_list (buf 1)). \<exists> n. P ((f ^^ n) x)) \<Longrightarrow>
   Ex (loop_producing (\<lambda>x. if x = 1 then Some 1 else None) buf (while_body_op P f True))"
  apply (cases "\<exists> ios. trace_while_True_op P f buf ios")
  subgoal
    apply (elim exE)
    apply (drule trace_while_True_op_loop_producing)
     apply auto
    done
  subgoal
    apply auto
    subgoal for x n
      oops
        (*       using trace_while_True_op_evidence apply blast
      done
    done
  done *)

lemma loop_producing_while_body_op_buf_all_False_aux:
  "loop_producing wire buf op n \<Longrightarrow>
   op = while_body_op P f True \<Longrightarrow>
   wire = (\<lambda>x. if x = 1 then Some 1 else None) \<Longrightarrow>
   buf 1 \<noteq> BEnded \<Longrightarrow>
   buf 1 \<noteq> BEmpty \<Longrightarrow>
   \<forall>x\<in>set (buf_to_list (buf 1)). \<forall>n. \<not> P ((f ^^ n) x) \<Longrightarrow>
   False"
  apply (induct n arbitrary: buf rule: less_induct)
  subgoal for n buf
    apply (cases n)
    subgoal
      apply simp
      using loop_producing_while_body_op_True_gt_0 apply blast
      done
    subgoal for n'
      apply simp
      apply hypsubst_thin
      apply (frule loop_producing_while_body_op_True_cases_aux)
        apply (rule refl)+
      apply auto
      subgoal
        apply (cases "buf 1")
          apply auto
        apply (metis funpow_0)
        done
      subgoal
        by (metis bhd.elims observation.distinct(3))
      subgoal
        by (metis bhd.elims observation.simps(3))
      subgoal
        apply (drule meta_spec[of _ "n' - Suc 0"])
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply simp
         apply (metis BHD_benqD bhd.simps(2) fun_upd_same)
        apply (drule meta_mp)
         apply simp_all
         apply (cases "buf 1")
           apply auto
        subgoal
          by (metis benq.elims buf.distinct(3))
        subgoal
          by (metis bhd.elims btl.simps(3) buf.set_intros(1) buf.set_intros(2) buf_to_list_btl observation.inject pow_f_f_Suc set_buf_to_list_set_buf)
        done
      done
    done
  done


lemma loop_producing_while_body_op_buf_all_False:
  "\<not> (\<exists> x \<in> set (buf_to_list (buf 1)). \<exists> n. P ((f ^^ n) x)) \<Longrightarrow>
   buf 1 \<noteq> BEnded \<Longrightarrow>
   buf 1 \<noteq> BEmpty \<Longrightarrow>
   \<not> (\<exists> n. loop_producing (\<lambda>x. if x = (1::2) then Some (1::2) else None) buf (while_body_op P f True) n)"
  using loop_producing_while_body_op_buf_all_False_aux by blast

lemma trace_while_True_op_traced:
  "trace_while_True_op P f buf ios \<Longrightarrow>
   op = while_body_op P f True \<Longrightarrow>
   wire = (\<lambda>x. if x = (1::2) then Some (1::2) else None) \<Longrightarrow>
   traced (loop_op (\<lambda>x. if x = (1::2) then Some (1::2) else None) buf op) ios"
  apply (coinduction arbitrary: buf ios)
  subgoal for buf ios
    apply (induct buf ios arbitrary: rule: trace_while_True_op.induct)
    subgoal for buf
      apply simp
      apply (subst while_body_op.code)
      unfolding Let_def
      apply (auto split: observation.splits)
      subgoal
        apply (drule loop_producing_while_body_op_buf_all_False[simplified])
          apply force+
        apply (simp add: while_body_op.code)
        done
      subgoal
        apply (drule loop_producing_while_body_op_buf_all_False[simplified])
          apply force+
        apply (simp add: while_body_op.code)
        done
      subgoal
        apply (drule loop_producing_while_body_op_buf_all_False[simplified])
          apply force+
        apply (simp add: while_body_op.code)
        done
      done
    subgoal for buf
      apply simp
      apply (subst while_body_op.code)
      unfolding Let_def
      apply auto
      subgoal
        by (smt (verit, best) loop_producing.intros(4) observation.simps(8) ran_dom_Some1(3))
      subgoal
        by (smt (verit, ccfv_threshold) loop_producing_ReadE observation.simps(8) ran_dom_Some1(3))
      subgoal
        apply (rule exI)
        apply (rule loop_producing.intros(4))
         apply simp
        apply simp
        apply (smt (verit, ccfv_threshold) fun_upd_same fun_upd_upd loop_producing.intros(5) not_loop_producing_eq_End op.distinct(5))
        done
      subgoal
        apply (rule exI)
        apply (rule loop_producing.intros(4))
         apply simp
        apply simp
        done
      subgoal
        by (smt (verit) loop_producing_ReadE observation.simps(8) ran_dom_Some1(3))
      subgoal
        apply (rule exI)
        apply (rule loop_producing.intros(4))
         apply simp
        apply simp
        apply (smt (verit, ccfv_threshold) fun_upd_same fun_upd_upd loop_producing.intros(5) not_loop_producing_eq_End op.distinct(5))
        done
      done
    subgoal for buf ios x
      apply simp
      apply (subst while_body_op.code)
      unfolding Let_def
      apply auto
      subgoal
        by (smt (verit) IO.distinct(1) llist.distinct(1) llist.inject trace_while_True_op.simps)
      subgoal
        using trace_while_True_op.cases by fastforce
      subgoal
        apply (rule exI)
        apply (rule loop_producing.intros(4))
         apply simp
        apply simp
        apply (rule loop_producing.intros(3))
        apply simp
        done
      subgoal
        apply (rule exI)
        apply (rule loop_producing.intros(4))
         apply simp
        apply simp
        apply (rule loop_producing.intros(3))
        apply simp
        done
      subgoal
        apply (rule exI)
        apply (rule loop_producing.intros(4))
         apply simp
        apply simp
        apply (rule loop_producing.intros(3))
        apply simp
        done
      done
    done
  done

lemma trace_while_body_True_trace_while_True_op_lfilter:
  "trace_while_body_True P f ios \<Longrightarrow>
   causal (\<lambda>x. if x = (1::2) then Some (1::2) else None) buf ios \<Longrightarrow>
   trace_while_True_op P f buf (lfilter (visible_IO (\<lambda>x. if x = 1 then Some 1 else None)) ios)"
  apply (induct "buf 1" arbitrary: ios)
  subgoal
    apply (erule causal.cases)
        apply auto
    oops


lemma trace_while_body_True_not_loop_producing_not_visible:
  "x \<in> lset ios \<Longrightarrow> 
   trace_while_body_True P f ios \<Longrightarrow>
   causal (\<lambda>x. if x = (1::2) then Some (1::2) else None) buf ios \<Longrightarrow>
   \<forall>x. \<not> loop_producing (\<lambda>x. if x = (1::2) then Some (1::2) else None) buf (while_body_op P f True) x \<Longrightarrow>
   \<not> visible_IO (\<lambda>x. if x = (1::2) then Some (1::2) else None) x"
  apply (clarsimp simp add: in_lset_conv_lnth)
  subgoal for n
    apply (induct n arbitrary: buf ios rule: less_induct)
    subgoal for n buf ios
      apply (cases n)
      subgoal
        apply simp
        apply (erule trace_while_body_True.cases)
           apply auto
        done
      subgoal for n'
        apply (erule trace_while_body_True.cases)
        subgoal
          apply simp
          using enat_0_iff(2) apply force
          done
        subgoal premises prems for ios' x'
          using prems(2,3,4,5,7-) apply -
          apply hypsubst_thin
          unfolding not_def
          apply (drule spec[of _ "Suc 0"])
          apply (drule mp)
           apply (subst while_body_op.code)
          unfolding Let_def
           apply auto
          apply (rule loop_producing.intros(4))
           apply (auto split: observation.splits)
          apply (rule loop_producing.intros(3))
          apply auto
          done
        subgoal for ios' x'
          apply simp
          apply (erule causal.cases)
              apply auto
          apply hypsubst_thin
          apply (cases n')
          subgoal
            by simp
          subgoal for n''
            apply hypsubst_thin
            apply (drule meta_spec[of _ n''])
            apply simp
            apply (drule meta_spec)+
            apply (drule meta_mp)
             defer
             apply (drule meta_mp)
              apply assumption
             apply (drule meta_mp)
            subgoal
              apply auto
              subgoal premises prems for i
                using prems(1,6,8) apply -
                apply (drule spec[of _ "Suc (Suc i)"])
                unfolding not_def
                using prems(5) apply -
                apply (drule mp)
                 apply (subst while_body_op.code)
                unfolding Let_def
                 apply auto
                apply (intro loop_producing.intros(4))
                 apply (auto split: observation.splits)
                apply (intro loop_producing.intros(5))
                 apply auto
                done
              done
             apply (drule meta_mp)
              apply (auto simp add: Suc_ile_eq)
            done
          done
        subgoal 
          apply (erule causal.cases)
              apply auto
          apply hypsubst_thin
          using enat_0_iff(2) apply fastforce
          done
        done
      done
    done
  done

lemma trace_while_body_True_trace_while_True_op_lfilter:
  "trace_while_body_True P f ios \<Longrightarrow>
   causal (\<lambda>x. if x = (1::2) then Some (1::2) else None) buf ios \<Longrightarrow>
   trace_while_True_op P f buf (lfilter (visible_IO (\<lambda>x. if x = 1 then Some 1 else None)) ios)"
  oops

lemma in_ios_buf_EOB_not_visible:
  "x \<in> lset ios \<Longrightarrow>
   trace_while_body_True P f ios \<Longrightarrow>
   BHD 1 buf = EOB \<Longrightarrow>
   causal (\<lambda>x. if x = 1 then Some 1 else None) buf ios \<Longrightarrow>
   \<not> visible_IO (\<lambda>x. if x = 1 then Some 1 else None) x"
  apply (induct ios arbitrary: buf rule: lset_induct)
  subgoal
    apply (erule trace_while_body_True.cases)
       apply auto
    done
  subgoal for x' xs buf
    apply (erule causal.cases)
        apply auto
    subgoal
      apply (erule trace_while_body_True.cases)
         apply auto
      done
    subgoal
      apply (erule trace_while_body_True.cases)
         apply auto
      done
    subgoal
      apply (erule trace_while_body_True.cases)
         apply auto
      done
    subgoal
      apply (erule trace_while_body_True.cases)
         apply auto
      done
    done
  done

lemma while_True_retrace_eq_lfilter_visible:
  "trace_while_body_True P f ios \<Longrightarrow>
   causal (\<lambda>x. if x = (1::2) then Some (1::2) else None) buf ios \<Longrightarrow>
    lfilter (visible_IO (\<lambda>x. if x = (1::2) then Some (1::2) else None)) ios = llist_of (map (Out 2) (while_True_retrace P f (buf_to_list (buf 1))))"
  apply (induct P f "buf_to_list (buf 1)" arbitrary: buf ios rule: while_True_retrace.induct)
  subgoal for P f buf ios
    apply (cases "buf 1")
      apply (auto 0 0 simp add: lfilter_eq_LNil)
    subgoal
      by (metis bhd.simps(1) in_ios_buf_EOB_not_visible)
    subgoal
      apply (erule trace_while_body_True.cases)
         apply auto
      done
    subgoal premises prems for x buf'
      using prems(1,3-) apply -
      subgoal
        apply (erule trace_while_body_True.cases)
           apply auto
        apply (metis fun_upd_same funpow_0)
        done
      done
    subgoal for x buf'
      apply (drule meta_spec[of _ x])
      apply simp
      apply (cases "\<exists>n. P ((f ^^ n) x)")
      subgoal
        subgoal
          apply (erule trace_while_body_True.cases)
             apply auto
          apply hypsubst_thin
          apply (metis buf_to_list_benq fun_upd_same)
          done
        done
      subgoal
        apply simp
        apply (cases "\<exists>x\<in>set (buf_to_list buf'). \<exists>n. P ((f ^^ n) x)")
        subgoal
          apply simp
          apply (erule trace_while_body_True.cases)
             apply auto
          apply hypsubst_thin
          apply (metis buf_to_list_benq fun_upd_same)
          done
        subgoal
          apply simp
          apply (subgoal_tac "while_True_retrace P f (buf_to_list buf' @ [f x]) = []")
           defer
          subgoal
            apply (simp add: while_True_retrace_eq_Nil)
            apply (metis pow_f_f_Suc)
            done
          apply (simp add: lfilter_eq_LNil)
          apply (smt (verit, ccfv_SIG) \<open>\<And>x. \<lbrakk>trace_while_body_True P f ios; causal (\<lambda>x. if x = 1 then Some 1 else None) buf ios; buf 1 = BEmpty; x \<in> lset ios; visible_IO (\<lambda>x. if x = 1 then Some 1 else None) x\<rbrakk> \<Longrightarrow> False\<close> \<open>\<And>x. \<lbrakk>trace_while_body_True P f ios; causal (\<lambda>x. if x = 1 then Some 1 else None) buf ios; buf 1 = BEnded; x \<in> lset ios; visible_IO (\<lambda>x. if x = 1 then Some 1 else None) x\<rbrakk> \<Longrightarrow> False\<close> bhd.simps(3) buf_to_list.simps(3) in_buf_to_list_in_tl_buf_to_list list.sel(3) loop_producing_while_body_op_buf_all_False trace_while_body_True_not_loop_producing_not_visible)
          done
        done
      done
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
        apply fastforce
        done
      subgoal
        apply (auto 0 0)
        subgoal
          by (metis (no_types, lifting) bhd.elims btl.simps(1) fun_upd_triv observation.distinct(5) observation.simps(3))
        subgoal
          by (metis (no_types, lifting) bhd.elims btl.simps(1) fun_upd_triv observation.distinct(5) observation.simps(3))
        done
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
        apply hypsubst_thin
        using while_True_retrace_eq_lfilter_visible trace_while_True_op_evidence
        apply force
        done
      done
    done
  done

declare [[unify_search_bound = 100]]

corec while_body_True_retrace where
  "while_body_True_retrace P f buf = (case BHD 1 buf of
       Observed x \<Rightarrow> LCons (Inp 1 (Observed x)) (if P x then LCons (Out 2 x) (while_body_True_retrace P f (BTL 1 buf)) else LCons (Out 1 (f x)) (while_body_True_retrace P f (BENQ 1 (f x) (BTL 1 buf))))
     | EOS \<Rightarrow> LCons (Inp 1 EOS) LNil
     | EOB \<Rightarrow> LCons (Inp 1 EOB) LNil)
"

simps_of_case while_body_True_retrace[simp]: while_body_True_retrace.code[unfolded observation.case]

corec while_body_retrace where
  "while_body_retrace P f buf inps = (case inps of
      LNil \<Rightarrow> (case BHD 1 buf of Observed x \<Rightarrow> LCons (Inp 1 (Observed x)) (if P x then LCons (Out 2 x) (while_body_retrace P f (BTL 1 buf) inps) else LCons (Out 1 (f x)) (while_body_retrace P f (BENQ 1 (f x) (BTL 1 buf)) inps)) | EOB \<Rightarrow> LCons (Inp 1 EOB) LNil | EOS \<Rightarrow> LCons (Inp 1 EOS) LNil)
   | LCons EOS inps' \<Rightarrow> LCons (Inp 2 EOS) (while_body_True_retrace P f buf)
   | LCons EOB inps' \<Rightarrow> LCons (Inp 2 EOB) (case BHD 1 buf of Observed x \<Rightarrow> LCons (Inp 1 (Observed x)) (if P x then LCons (Out 2 x) (while_body_retrace P f (BTL 1 buf) inps') else LCons (Out 1 (f x)) (while_body_retrace P f (BENQ 1 (f x) (BTL 1 buf)) inps')) | EOB \<Rightarrow> LCons (Inp 1 EOB) (while_body_retrace P f buf inps') | EOS \<Rightarrow> LCons (Inp 1 EOS) LNil)
   | LCons (Observed x) inps' \<Rightarrow> LCons (Inp 2 (Observed x)) (if P x
     then LCons (Out 2 x) (case BHD 1 buf of
         Observed x \<Rightarrow> LCons (Inp 1 (Observed x)) (if P x then LCons (Out 2 x) (while_body_retrace P f (BTL 1 buf) inps') else LCons (Out 1 (f x)) (while_body_retrace P f (BENQ 1 (f x) (BTL 1 buf)) inps'))
       | EOS \<Rightarrow> LCons (Inp 1 EOS) LNil
       | EOB \<Rightarrow> LCons (Inp 1 EOB) (while_body_retrace P f buf inps'))
     else LCons (Out 1 (f x)) (case BHD 1 (BENQ 1 (f x) buf) of
         Observed y \<Rightarrow> LCons (Inp 1 (Observed y)) (if P y then LCons (Out 2 y) (while_body_retrace P f (BTL 1 (BENQ 1 (f x) buf)) inps') else LCons (Out 1 (f y)) (while_body_retrace P f (BENQ 1 (f y) (BTL 1 (BENQ 1 (f x) buf))) inps'))))
)
"

simps_of_case while_body_retrace_simps[simp]: while_body_retrace.code[unfolded observation.case]

lemma trace_while_True_op_trace_while_body_True_while_body_retrace:
  "trace_while_True_op P f buf ios \<Longrightarrow> trace_while_body_True P f (while_body_True_retrace P f buf)"
  apply (coinduction arbitrary: buf ios)
  subgoal for buf ios
    apply (erule trace_while_True_op.cases)
    subgoal for buf'
      apply (cases "BHD 1 buf")
      subgoal for x
        apply (subgoal_tac "\<not> P x")
         defer
        subgoal
          by (metis bhd.elims buf.set_intros(1) funpow_0 observation.distinct(3) observation.sel observation.simps(3) set_buf_to_list_set_buf)
        apply hypsubst_thin
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule disjI1)
        apply (rule exI[of _ "while_body_True_retrace P f (BENQ 1 (f x) (BTL 1 buf'))"])
        apply (rule exI[of _ x])
        apply (intro conjI)
        subgoal
          by simp
        subgoal
          apply (rule disjI1)
          apply (rule exI)
          apply (rule exI[of _ LNil])
          apply (intro conjI exI)
           apply (simp del: while_body_True_retrace)
          apply (rule trace_while_True_op.intros(1))
          apply auto
           apply (metis bhd.elims buf.set_intros(1) observation.distinct(3) observation.sel observation.simps(3) pow_f_f_Suc set_buf_to_list_set_buf)
          apply (metis list.sel(2) list.set_sel(2))
          done
        apply simp
        done
      subgoal
        apply hypsubst_thin
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule disjI2)
        apply (subst while_body_True_retrace.code)
        apply auto
        done
      subgoal
        apply (rule disjI1)
        apply (subst while_body_True_retrace.code)
        apply auto
        done
      done
    subgoal for x buf' y ios'
      apply hypsubst_thin
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule disjI1)
      apply (rule exI[of _ "while_body_True_retrace P f (BENQ 1 (f x) (BTL 1 buf'))"])
      apply (rule exI[of _ x])
      apply (intro conjI)
      subgoal
        by simp
      subgoal
        apply (rule disjI1)
        apply (rule exI)
        apply (rule exI[of _])
        apply (intro conjI)
         apply (rule refl)
        apply (simp del: while_body_True_retrace)
        done
      subgoal
        by auto
      done
    subgoal for buf' ios x
      apply hypsubst_thin
      apply (rule disjI2)
      apply (rule disjI1)
      apply (rule exI[of _ "while_body_True_retrace P f (BTL 1 buf')"])
      apply (rule exI[of _ x])
      apply (intro conjI)
      subgoal
        by simp
      subgoal
        apply (rule disjI1)
        apply (rule exI)
        apply (rule exI[of _])
        apply (intro conjI)
         apply (rule refl)
        apply assumption
        done
      apply simp
      done
    done
  done

lemma trace_while_True_op_Inp_llist_LNil:
  "trace_while_True_op P f buf ios \<Longrightarrow>
   (Inp_llist ios) = LNil"
  apply (induct buf ios rule: trace_while_True_op.induct)
    apply auto
  done

lemma while_body_True_retrace_while_body_retrace_LNil:
  "while_body_True_retrace P f buf = while_body_retrace P f buf LNil"
  apply (coinduction arbitrary: buf rule: llist.coinduct_upto)
  subgoal for buf
    apply (intro conjI impI iffI)
    unfolding lnull_def
    subgoal
      apply (subst (asm) while_body_True_retrace.code)
      apply (subst while_body_retrace.code)
      apply (cases "BHD 1 buf")
        apply (simp_all del: while_body_True_retrace while_body_retrace_simps)
      done
    subgoal
      apply (subst while_body_True_retrace.code)
      apply (subst (asm) while_body_retrace.code)
      apply (cases "BHD 1 buf")
        apply (simp_all del: while_body_True_retrace while_body_retrace_simps)
      done
    subgoal
      apply (subst while_body_True_retrace.code)
      apply (subst while_body_retrace.code)
      apply (cases "BHD 1 buf")
        apply (simp_all del: while_body_True_retrace while_body_retrace_simps)
      done
    subgoal
      apply (cases "BHD 1 buf")
      subgoal for x
        apply (subst (2) while_body_True_retrace.code)
        apply (subst (2) while_body_retrace.code)
        apply (auto simp del: while_body_True_retrace while_body_retrace_simps intro: llist.cong_base intro!:  llist.cong_LCons)
        done
      subgoal
        apply (subst (2) while_body_True_retrace.code)
        apply (subst (2) while_body_retrace.code)
        apply (auto simp del: while_body_True_retrace while_body_retrace_simps intro: llist.cong_refl  intro!: llist.cong_LCons)
        done
      subgoal
        apply (subst (2) while_body_True_retrace.code)
        apply (subst (2) while_body_retrace.code)
        apply (auto simp del: while_body_True_retrace while_body_retrace_simps intro: llist.cong_refl intro!:  llist.cong_LCons)
        done
      done
    done
  done

lemma while_body_True_retrace_visible:
  "x \<in> lset (while_body_True_retrace P f buf) \<Longrightarrow> 
   \<forall>x\<in>set (buf_to_list (buf 1)). \<forall>n. \<not> P ((f ^^ n) x) \<Longrightarrow>
   visible_IO (\<lambda>x. if x = (1::2) then Some (1::2) else None) x \<Longrightarrow>
   False"
  apply (auto simp add: in_lset_conv_lnth simp del: while_body_True_retrace)
  subgoal for n
    apply (induct n arbitrary: buf rule: less_induct)
    subgoal for n buf
      apply (cases n)
      subgoal
        apply (subst (asm) (4) while_body_True_retrace.code)
        apply (cases "BHD 1 buf")
          apply (auto simp del: while_body_True_retrace)
        done
      subgoal for n'
        apply (subst (asm) (4 5 6) while_body_True_retrace.code)
        apply (cases "BHD 1 buf")
          apply (auto simp del: while_body_True_retrace while_body_retrace_simps split: if_splits)
        subgoal by (metis bhd.elims buf_to_list.simps(3) funpow_0 insert_iff list.set(2) observation.distinct(3) observation.sel observation.simps(3))
        subgoal for x
          apply hypsubst_thin
          apply (cases n')
           apply simp
          subgoal for n''
            apply hypsubst_thin
            subgoal
              apply (drule meta_spec[of _ n''])
              apply (drule meta_spec[of _ "buf(1 := benq (f x) (btl (buf 1)))"])
              apply (auto simp del: while_body_True_retrace)
              apply (drule meta_mp)
               apply (metis (no_types, lifting) bhd.elims btl.simps(3) buf_to_list.simps(3) buf_to_list_btl insert_iff list.set(2) observation.distinct(3) observation.sel observation.simps(3) pow_f_f_Suc)
              apply (drule meta_mp)
               apply (auto simp add: Suc_ile_eq)
              done
            done
          done    
        subgoal
          using Suc_ile_eq
          by (metis Zero_neq_Suc enat_0_iff(2))
        subgoal
          by (metis eSuc_enat zero_ne_eSuc)
        done
      done
    done
  done


lemma trace_while_True_op_while_body_True_retrace_lfilter:
  "trace_while_True_op P f buf ios \<Longrightarrow>
   lfilter (visible_IO (\<lambda>x. if x = (1::2) then Some (1::2) else None)) (while_body_True_retrace P f buf) = ios"
  apply (induct buf ios rule: trace_while_True_op.induct)
  subgoal for buf
    apply (auto simp del: while_body_True_retrace while_body_retrace_simps simp add: lfilter_eq_LNil)
    subgoal for x
      using while_body_True_retrace_visible apply blast
      done
    done
  subgoal
    apply (drule sym)
    apply (subst while_body_True_retrace.code)
    apply (auto simp del: while_body_True_retrace while_body_retrace_simps)
    apply (rule lfilter_cong)
    subgoal
      apply (rule arg_cong2[where f="while_body_True_retrace P"])
       apply simp
      apply (metis fun_upd_apply)
      done
    apply simp
    done
  subgoal
    apply (drule sym)
    apply (subst while_body_True_retrace.code)
    apply (auto simp del: while_body_True_retrace while_body_retrace_simps)
    apply (rule lfilter_cong)
    subgoal
      apply (rule arg_cong2[where f="while_body_True_retrace P"])
       apply simp
      apply (metis fun_upd_apply)
      done
    apply simp
    done
  done

lemma while_body_True_retrace_causal:
  "causal (\<lambda>x. if x = (1::2) then Some (1::2) else None) buf (while_body_True_retrace P f buf)" 
  apply (coinduction arbitrary: buf rule: causal_coinduct_upto)
  subgoal for buf
    apply (simp del: while_body_True_retrace)
    apply (cases "BHD 1 buf")
    subgoal for x
      apply (cases "P x")
      subgoal
        apply (rule disjI1)
        apply (subst while_body_True_retrace.code)
        apply (simp del: while_body_True_retrace add: causal_cong.cc_base causal_cong.intros(6))
        done
      subgoal
        apply (rule disjI1)
        apply (subst while_body_True_retrace.code)
        apply (simp del: while_body_True_retrace add: causal_cong.cc_base)
        apply (smt (verit, del_insts) causal_cong.cc_base causal_cong.intros(5) fun_upd_same fun_upd_upd)
        done
      done
    subgoal
      apply (rule disjI1)
      apply (subst while_body_True_retrace.code)
      apply (simp del: while_body_True_retrace add: causal_cong.cc_base)
      apply (meson causal.intros(5) causal_cong_disj)
      done
    subgoal
      apply (rule disjI1)
      apply (subst while_body_True_retrace.code)
      apply (simp del: while_body_True_retrace add: causal_cong.cc_base causal.intros(5) cc_causal)
      done
    done
  done

lemma trace_while_op_traced:
  "trace_while_op P f buf ios \<Longrightarrow>
   traced (while_op buf P f) ios"
  unfolding traced_loop_op while_body_op_traced_correctness
  apply (rule exI[of _ "while_body_retrace P f buf (Inp_llist ios)"])
  apply (intro conjI)
  subgoal
    apply (coinduction arbitrary: buf ios)
    subgoal for buf ios
      apply (erule trace_while_op.cases)
      subgoal
        by simp
      subgoal 
        by simp
      subgoal
        by auto
      subgoal
        by auto
      subgoal 
        by auto
      subgoal
        by auto
      subgoal 
        by auto
      subgoal
        by auto
      subgoal
        by auto
      subgoal
        by auto
      subgoal
        by auto
      subgoal for buf ios
        apply hypsubst_thin
        apply simp
        using trace_while_True_op_trace_while_body_True_while_body_retrace apply auto
        done
      done
    done
  subgoal
    apply (coinduction arbitrary: buf ios rule: llist.coinduct_upto)
    subgoal for buf ios
      apply (intro conjI impI iffI)
      unfolding lnull_def
      subgoal
        apply (erule trace_while_op.cases)
                   apply auto
        done
      subgoal
        apply (simp add: lfilter_eq_LNil)
        apply (rule ccontr)
        apply (auto simp add: neq_LNil_conv simp del: while_body_retrace_simps)
        subgoal for x xs'
          apply (erule trace_while_op.cases)
                     apply auto
          done
        done
      subgoal
        apply (erule trace_while_op.cases)
                   apply simp_all
        done
      subgoal
        apply (erule trace_while_op.cases)
                   apply (simp_all del: while_body_retrace_simps)
        subgoal
          by (auto intro!:  llist.cong_refl)
        subgoal
          by (auto intro!:  llist.cong_refl)
        subgoal
          by (auto intro: llist.cong_base intro!:  llist.cong_LCons)
        subgoal
          by (auto intro: llist.cong_base intro!:  llist.cong_LCons)
        subgoal
          by (auto intro: llist.cong_base intro!:  llist.cong_LCons)
        subgoal
          by (auto intro: llist.cong_base intro!:  llist.cong_LCons)
        subgoal
          by (auto intro: llist.cong_base intro!:  llist.cong_LCons)
        subgoal
          by (auto intro: llist.cong_base intro!:  llist.cong_LCons)
        subgoal
          by (auto intro: llist.cong_base intro!:  llist.cong_LCons)
        subgoal
          by (auto intro: llist.cong_base intro!:  llist.cong_LCons)
        subgoal
          by (auto intro: llist.cong_base intro!:  llist.cong_LCons)
        subgoal for buf ios
          apply (frule trace_while_True_op_Inp_llist_LNil)
          apply (subst (2) while_body_retrace.code)
          apply (simp_all flip: while_body_True_retrace_while_body_retrace_LNil add: trace_while_True_op_while_body_True_retrace_lfilter del: while_body_True_retrace while_body_retrace_simps)
          apply (rule llist.cong_refl)
          apply simp
          done
        done
      done
    done
  subgoal
    apply (coinduction arbitrary: buf ios rule: causal_coinduct_upto)
    subgoal for buf ios
      apply (erule trace_while_op.cases)
      subgoal
        by (auto simp add: causal.intros(5) causal_cong.intros(3) cc_causal intro!: causal_cong.intros(6))
      subgoal
        by (auto simp add: causal.intros(5) causal_cong.intros(3) cc_causal intro!: causal_cong.intros(6))
      subgoal for buf ios'
        apply simp
        apply (rule causal_cong.intros(6))
         apply auto
        apply (rule causal_cong.intros(3))
          apply auto
        apply (rule causal_cong.intros(2))
        apply auto
        apply (rule exI[of _ ios'])
        apply (metis bhd.elims btl.simps(1) fun_upd_triv observation.distinct(5) observation.simps(3))
        done
      subgoal for buf ios'
        apply simp
        apply (rule causal_cong.intros(6))
         apply auto
        apply (rule causal_cong.intros(3))
          apply auto
        apply (rule causal_cong.intros(6))
         apply auto
        apply (rule causal_cong.intros(2))
        apply auto
        done
      subgoal for y buf ios x
        apply simp
        apply (rule causal_cong.intros(6))
         apply auto
        apply (rule causal_cong.intros(3))
          apply auto
        apply (rule causal_cong.intros(5))
         apply auto
        apply (rule causal_cong.intros(2))
        apply auto
        done
      subgoal 
        apply simp
        apply (rule causal_cong.intros(6))
         apply auto
        apply (rule causal_cong.intros(3))
          apply auto
        apply (rule causal_cong.intros(2))
        apply auto
        apply (metis bhd.elims btl.simps(1) fun_upd_triv observation.distinct(5) observation.simps(3))
        done
      subgoal 
        apply simp
        apply (rule causal_cong.intros(5))
         apply auto
        apply (rule causal_cong.intros(3))
          apply auto
        apply (rule causal_cong.intros(5))
         apply auto
        apply (rule causal_cong.intros(2))
        apply auto
        done
      subgoal 
        apply simp
        apply (rule causal_cong.intros(5))
         apply auto
        apply (rule causal_cong.intros(3))
          apply auto
        apply (rule causal_cong.intros(6))
         apply auto
        apply (rule causal_cong.intros(2))
        apply auto
        done
      subgoal 
        apply simp
        apply (rule causal_cong.intros(3))
          apply auto
        apply (rule causal_cong.intros(6))
         apply auto
        apply (rule causal_cong.intros(2))
        apply auto
        done
      subgoal 
        apply simp
        apply (rule causal_cong.intros(3))
          apply auto
        apply (rule causal_cong.intros(5))
         apply auto
        apply (rule causal_cong.intros(2))
        apply auto
        done
      subgoal 
        apply simp
        apply (rule causal_cong.intros(3))
          apply auto
        apply (rule causal_cong.intros(2))
        apply auto
        apply (metis bhd.elims btl.simps(1) fun_upd_triv observation.distinct(1) observation.simps(7))
        done
      subgoal
        apply (erule trace_while_True_op.cases)
          apply (auto simp del: while_body_True_retrace)
          apply (rule causal_cong.intros(1))
        using while_body_True_retrace_causal apply blast
         apply (rule causal_cong.intros(1))
        using while_body_True_retrace_causal apply blast
        apply (rule causal_cong.intros(1))
        using while_body_True_retrace_causal apply blast
        done
      done
    done
  done


lemma traced_while_op_correctness:
  "traced (while_op buf P f) ios \<longleftrightarrow> trace_while_op P f buf ios"
  using traced_while_op trace_while_op_traced by blast


(*

 [(a, 10), (b, 3), (c, 14), (d, 4), (e, 0)]
 
 [(a, 10), (b, 3), (c, 14), (d, 4), (e, 0)]

 [(b, 3), (a, 7), (c, 14), (d, 4), (e, 0)]

 [(b, 3), (a, 7), (d, 4), (c, 10), (e, 0)]

 [(b, 3), (d, 4), (a, 3), (c, 10), (e, 0)]

 [(b, 3), (a, 0), (d, 1), (c, 10), (e, 0)]

 [(a, 0), (b, 3), (d, 1), (c, 10), (e, 0)]

 [(a, 0), (d, 1), (b, 2), (c, 10), (e, 0)]

 [(a, 0), (d, 1), (b, 2), (e, 0), (c, 10)]

 [(a, 0), (d, 1), (e, 0), (b, 2), (c, 10)]

 [(a, 0), (e, 0), (d, 1), (b, 2), (c, 10)]

 [(e, 0), (a, 0), (d, 1), (b, 2), (c, 10)]


 [a, b c d]
 [b, 
 

 [(b, 1), (a, 12), (c, 15)]
 [(b, 1), (a, 12), (c, 15)]
 
*)

datatype read_state = READ_BUF | READ_INPUT 

coinductive history_while_op for P f where
  "\<not> (\<exists> x \<in> set (buf_to_list (buf 1)). \<exists> n. P ((f ^^ n) x)) \<Longrightarrow> history_while_op P f buf lxs LNil any"
| "BHD 1 buf = EOS \<Longrightarrow> history_while_op P f buf lxs LNil any"

| "history_while_op P f (BTL 1 buf) lxs lys READ_INPUT \<Longrightarrow> P x \<Longrightarrow> BHD 1 buf = Observed x \<Longrightarrow> history_while_op P f buf lxs (LCons x lys) any"
| "history_while_op P f (BENQ 1 (f x) (BTL 1 buf)) lxs lys READ_INPUT \<Longrightarrow> \<not> P x \<Longrightarrow> BHD 1 buf = Observed x \<Longrightarrow> history_while_op P f buf lxs lys any"
| "history_while_op P f buf lxs lys READ_INPUT \<Longrightarrow> BHD 1 buf = EOB \<Longrightarrow> history_while_op P f buf lxs lys any"

| "history_while_op P f buf lxs lys READ_BUF \<Longrightarrow> P x \<Longrightarrow> history_while_op P f buf (LCons x lxs) (LCons x lys) READ_INPUT"
| "history_while_op P f (BENQ 1 (f x) buf) lxs lys READ_BUF \<Longrightarrow> \<not> P x \<Longrightarrow> history_while_op P f buf (LCons x lxs) lys READ_INPUT"


inductive history_while_op_cong for R P f where
  hwc_base:  "R P f buf lxs lys any \<Longrightarrow> history_while_op_cong R P f buf lxs lys any"
| hwc: "history_while_op P f buf lxs lys any \<Longrightarrow> history_while_op_cong R P f buf lxs lys any"

| "history_while_op_cong R P f (BTL 1 buf) lxs lys READ_INPUT \<Longrightarrow> P x \<Longrightarrow> BHD 1 buf = Observed x \<Longrightarrow> history_while_op_cong R P f buf lxs (LCons x lys) any"
| "history_while_op_cong R P f (BENQ 1 (f x) (BTL 1 buf)) lxs lys READ_INPUT \<Longrightarrow> \<not> P x \<Longrightarrow> BHD 1 buf = Observed x \<Longrightarrow> history_while_op_cong R P f buf lxs lys any"
| "history_while_op_cong R P f buf lxs lys READ_INPUT \<Longrightarrow> BHD 1 buf = EOB \<Longrightarrow> history_while_op_cong R P f buf lxs lys any"

| "history_while_op_cong R P f buf lxs lys READ_BUF \<Longrightarrow> P x \<Longrightarrow> history_while_op_cong R P f buf (LCons x lxs) (LCons x lys) READ_INPUT"
| "history_while_op_cong R P f (BENQ 1 (f x) buf) lxs lys READ_BUF \<Longrightarrow> \<not> P x \<Longrightarrow> history_while_op_cong R P f buf (LCons x lxs) lys READ_INPUT"

thm history_while_op.simps[no_vars, simplified]

lemma history_while_op_cong_disj[simp]:
  "(history_while_op_cong R P f buf lxs lys any \<or> history_while_op P f buf lxs lys any) = history_while_op_cong R P f buf lxs lys any"
  by (auto intro: history_while_op_cong.intros)

thm history_while_op.coinduct[where X="history_while_op_cong R P f", simplified, of buf lxs lys r P f, simplified]


lemma history_while_op_coinduct_upto:
  "R P f buf lxs lys r \<Longrightarrow>
  (\<And>x1 x2 x3 x4.
    R P f x1 x2 x3 x4 \<Longrightarrow>
    x3 = LNil \<and> (\<forall>x\<in>set (buf_to_list (x1 1)). \<forall>n. \<not> P ((f ^^ n) x)) \<or>
    x3 = LNil \<and> BHD 1 x1 = EOS \<or>
    (\<exists>lys x. x3 = LCons x lys \<and> history_while_op_cong R P f (x1(1 := btl (x1 1))) x2 lys READ_INPUT \<and> P x \<and> BHD 1 x1 = Observed x) \<or>
    (\<exists>x. history_while_op_cong R P f (x1(1 := benq (f x) (btl (x1 1)))) x2 x3 READ_INPUT \<and> \<not> P x \<and> BHD 1 x1 = Observed x) \<or>
    history_while_op_cong R P f x1 x2 x3 READ_INPUT \<and> BHD 1 x1 = EOB \<or>
    (\<exists>lxs lys x. x2 = LCons x lxs \<and> x3 = LCons x lys \<and> x4 = READ_INPUT \<and> history_while_op_cong R P f x1 lxs lys READ_BUF \<and> P x) \<or>
    (\<exists>x lxs. x2 = LCons x lxs \<and> x4 = READ_INPUT \<and> history_while_op_cong R P f (x1(1 := benq (f x) (x1 1))) lxs x3 READ_BUF \<and> \<not> P x)) \<Longrightarrow>
  history_while_op P f buf lxs lys r"
  apply (rule history_while_op.coinduct[where X="history_while_op_cong R P f", simplified, of buf lxs lys r P f, simplified])
   apply (auto intro: history_while_op_cong.intros)[1]
  subgoal premises prems for buf lxs lys any
    using prems(3, 2, 1) apply -
    apply (induct buf lxs lys any rule: history_while_op_cong.induct)
    subgoal
      by auto
    subgoal 
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply assumption
      apply (erule history_while_op.cases)
            apply simp_all
          apply (meson history_while_op_cong_disj)+
      done
        apply auto
    done
  done

lemma
  "history (while_op (\<lambda> _. BEmpty) P f) (\<lambda> x. if x = 2 then lxs else LNil) (\<lambda> x. if x = 2 then lys else LNil) \<Longrightarrow>
   y \<in> lset lys \<Longrightarrow>
   \<exists> x \<in> lset lxs. (\<exists> n. P ((f ^^ n) x)) \<and> y = (f ^^ (LEAST n. P ((f ^^ n) x))) x"
  unfolding history_def traced_while_op_correctness fun_eq_iff
  apply (elim exE conjE)
  subgoal for ios
    apply (frule spec[of _ 1])
    apply (frule spec[of _ 1])
    apply (drule spec[of _ 2])
    apply (drule spec[of _ 2])
    apply simp
    apply hypsubst_thin
    oops

(*

Here is the Isabelle Todos:

fairmerge: 100% (Dmitriy by 12th)
comp_op correctness trace model: 100% (Rafael by 12th)
comp_op correctness history model: (SKIP?) 0% (Rafael by ?)
example of sequential comp_op (fairmerge + (filter or fairmerge or map)): 0% (Dmitriy by ?)
example of parallel comp_op (fairmerge in parallel and sequential with fairmerge) (Dmitriy by ?)
loop_op correctness trace model: 100% (Rafael by 19th)
loop_op correctness history model: 0% (Rafael by 19th)

example of loop_op (collatz conjecture): 50%
history model time anomaly: 0%
BNA operators + axioms: 0.5% (Asta and Dmitriy by ?)
define split (maybe using nondeterministic choice operator)

*)


corec while_body_rehistory where
  "while_body_rehistory P f buf lxs lys = 
   (if (lys \<noteq> LNil \<and> BHD 1 buf = Observed (lhd lys) \<and> P (lhd lys) \<and> history_while_op P f (BTL 1 buf) lxs (ltl lys) READ_INPUT) \<or>
              (BHD 1 buf = EOB \<and> history_while_op P f buf lxs lys READ_INPUT) \<or>
              (BHD 1 buf = EOS \<and> history_while_op P f buf lxs LNil READ_INPUT) \<or>
              (\<exists> x. BHD 1 buf = Observed x \<and> history_while_op P f (BENQ 1 (f x) (BTL 1 buf)) lxs lys READ_INPUT \<and> \<not> P x)
    then LCons (Inp 2 EOB) (case BHD 1 buf of
      EOB \<Rightarrow> while_body_rehistory P f buf lxs lys
    | EOS \<Rightarrow> LNil
    | Observed x \<Rightarrow> (if P x then LCons (Out 2 x) (while_body_rehistory P f (BTL 1 buf) lxs (ltl lys)) else while_body_rehistory P f (BENQ 1 (f x) (BTL 1 buf)) lxs lys))
    else (case lxs of
      LNil \<Rightarrow> LCons (Inp 2 EOB) (case BHD 1 buf of
         EOB \<Rightarrow> LNil
       | EOS \<Rightarrow> LNil
       | Observed x \<Rightarrow> (if P x then LCons (Out 2 x) (while_body_rehistory P f (BTL 1 buf) lxs (ltl lys)) else while_body_rehistory P f (BENQ 1 (f x) (BTL 1 buf)) lxs lys))
    | LCons x lxs \<Rightarrow> LCons (Inp 2 (Observed x)) (
       if P x 
       then LCons (Out 2 x) (case BHD 1 buf of
          EOB \<Rightarrow> while_body_rehistory P f buf lxs lys
        | EOS \<Rightarrow> LNil
        | Observed x \<Rightarrow> (if P x then LCons (Out 2 x) (while_body_rehistory P f (BTL 1 buf) lxs (ltl (ltl lys))) else while_body_rehistory P f (BENQ 1 (f x) (BTL 1 buf)) lxs (ltl lys))) 
       else (case BHD 1 (BENQ 1 (f x) buf) of
          EOB \<Rightarrow> while_body_rehistory P f buf lxs lys
        | EOS \<Rightarrow> LNil
        | Observed y \<Rightarrow> (if P y then LCons (Out 2 y) (while_body_rehistory P f (BTL 1 (BENQ 1 (f x) buf)) lxs (ltl lys)) else while_body_rehistory P f (BENQ 1 (f y) (BTL 1 (BENQ 1 (f x) buf))) lxs lys)))))"

lemma Observed_not_inwhile_body_rehistory_LNil:
  "Inp q (Observed x) \<in> lset (while_body_rehistory P f buf LNil lys) \<Longrightarrow>
   False"
  apply (simp add: in_lset_conv_lnth)
  apply (elim exE conjE)
  subgoal for n
    apply (induct n arbitrary: buf lys rule: less_induct)
    subgoal for n buf lys
      apply (cases n)
      subgoal
        apply (subst (asm) (3 4) while_body_rehistory.code)
        apply (auto split: if_splits)
        done
      subgoal for n'
        apply (subst (asm) (3 4) while_body_rehistory.code)
        apply (cases n')
          apply (auto split: if_splits observation.splits)
        using Suc_ile_eq enat_0_iff(1) apply fastforce+
        done
      done
    done
  done


lemma while_body_rehistoryLCons_lhd:
  "ios = while_body_rehistory P f buf (LCons x lxs) lys \<Longrightarrow>
   lzs = lproject (=) \<bottom> ios (2::2) \<Longrightarrow>
   lzs \<noteq> LNil \<Longrightarrow>
   lhd lzs = x"
  apply (cases "\<exists>n. llength (ltakeWhile (Not o (\<lambda>x. case x of Inp q (Observed xa) \<Rightarrow> (2::2) = q | Inp q _ \<Rightarrow> False | Out q x \<Rightarrow> \<bottom> (2::2) q)) ios) = enat n")
   defer
  subgoal
    apply simp
    unfolding lproject_def neq_LNil_conv lmap_eq_LCons_conv
    apply auto
    apply (rule FalseE)
    apply hypsubst_thin
    apply (drule lfilter_eq_LCons)
    apply (elim exE conjE)
    apply hypsubst_thin
    apply (simp add: ldropWhile_eq_ldrop)
    done
  subgoal
    apply (elim exE)
    apply hypsubst_thin
    subgoal for n
      apply (induct n arbitrary: buf lxs lys rule: less_induct)
      subgoal for n buf lxs lys
        apply (cases n)
        subgoal
          apply simp
          apply (subst (asm) (1 2) while_body_rehistory.code)
          apply (subst while_body_rehistory.code)
          using zero_enat_def apply (auto split: if_splits)
          done
        subgoal for n'
          apply simp
          apply (subst (asm) (4 5) while_body_rehistory.code)
          apply (subst while_body_rehistory.code)
          using zero_enat_def apply (auto split: if_splits)
          subgoal 
            apply (cases n')
             apply simp
             apply (metis (no_types, lifting) eSuc_inject numeral_1_eq_Suc_0 numeral_One one_eSuc one_enat_def zero_ne_eSuc)
            apply simp
            apply (metis (no_types, lifting) co.enat.inject eSuc_enat less_add_Suc2 plus_1_eq_Suc)
            done
          subgoal
            using eSuc_enat_iff by auto
          subgoal
            using eSuc_enat_iff by auto
          done
        done
      done
    done
  done

lemma
  "history_while_op P f buf (LCons x lxs) lys READ_INPUT \<Longrightarrow>
   ios = while_body_rehistory P f (buf::2 \<Rightarrow> 'b buf) (LCons x lxs) lys \<Longrightarrow>
   lzs = lproject (=) \<bottom> ios (2::2) \<Longrightarrow>
   lzs \<noteq> LNil \<Longrightarrow>
   \<exists>(buf::2 \<Rightarrow> 'b buf) lys'. ctl (lproject (=) \<bottom> ios (2::2)) = lproject (=) \<bottom> (while_body_rehistory P f buf lxs lys') (2::2) \<and> history_while_op P f buf lxs' lys' READ_INPUT"
  apply (cases "\<exists>n. llength (ltakeWhile (Not o (\<lambda>x. case x of Inp q (Observed xa) \<Rightarrow> (2::2) = q | Inp q _ \<Rightarrow> False | Out q x \<Rightarrow> \<bottom> (2::2) q)) ios) = enat n")
   defer
  subgoal
    apply simp
    unfolding lproject_def neq_LNil_conv lmap_eq_LCons_conv
    apply auto
    apply (rule FalseE)
    apply (drule lfilter_eq_LCons)
    apply (elim exE conjE)
    apply hypsubst_thin
    apply (simp add: ldropWhile_eq_ldrop)
    done
  subgoal
    apply (elim exE)
    subgoal for n
      apply hypsubst_thin
    apply (induct n arbitrary: buf lxs lys rule: less_induct)
      subgoal for n buf lxs lys
        apply (cases n)
        subgoal
          apply simp
          apply (subst (asm) (1 2) while_body_rehistory.code)
          apply (subst while_body_rehistory.code)
          using zero_enat_def apply (auto split: if_splits)
          subgoal
            apply (auto split: observation.splits)
             apply (rule exI[of _ "buf(1 := btl (buf 1))"])
            apply (rule exI[of _ "ctl (ctl lys)"])
             apply (intro conjI exI)
            subgoal
              oops

(* FIXME: move me *)
lemma BHD_benq:
  "BHD 1 buf = Observed x \<Longrightarrow>
   BHD (buf 1) (benq y) = Observed x"
  by (metis benq.elims bhd.simps(1) bhd.simps(2) bhd.simps(3) observation.distinct(3) observation.simps(3))



lemma
  "history (while_op buf P f) (\<lambda> x. if x = 2 then lxs else LNil) (\<lambda> x. if x = 2 then lys else LNil) \<longleftrightarrow>
   history_while_op P f buf lxs lys READ_INPUT"
  unfolding history_def traced_while_op_correctness fun_eq_iff
  apply safe
  subgoal for ios
    apply (frule spec[of _ 1])
    apply (frule spec[of _ 1])
    apply (drule spec[of _ 2])
    apply (drule spec[of _ 2])
    apply simp
    unfolding lnull_def
    apply hypsubst_thin
    apply (coinduction arbitrary: ios lxs buf rule: history_while_op_coinduct_upto)
    subgoal for ios lxs buf
      apply (erule trace_while_op.cases)
      subgoal for buf x
        apply (cases lxs)
         apply simp_all
        subgoal for x lxs'
          apply hypsubst_thin
          apply (rule hwc)
          apply (rule history_while_op.intros(1))
          apply clarsimp
          apply (metis bhd.elims buf.simps(27) empty_iff observation.distinct(3) observation.distinct(5) set_buf_to_list_set_buf)
          done
        done
      subgoal for buf
        apply hypsubst_thin
        apply simp
        done
      subgoal for buf ios' x
        apply hypsubst
        apply simp
        apply (cases lxs)
         apply simp_all
        subgoal for lxs'
          apply (rule disjI1)
          apply (rule history_while_op_cong.intros(5))
           apply (rule hwc_base)
           apply simp_all
          apply (rule exI[of _ ios])
          apply simp
          apply (auto intro: trace_while_op.intros(3))
          done
        done
      subgoal for buf ios' x y
        apply hypsubst
        apply simp
        apply (cases lxs)
         apply simp_all
        apply hypsubst_thin
        subgoal for lxs'
          apply (rule disjI2)
          apply (rule history_while_op_cong.intros(3))
            apply simp_all
          apply (rule hwc_base)
          apply simp
          apply auto
          done
        done
      subgoal for y buf ios x
        apply hypsubst_thin
        apply simp
        apply (cases lxs)
         apply simp_all
        apply hypsubst_thin
        subgoal for lxs'
          apply (rule disjI2)
          apply (rule disjI2)
          apply (rule history_while_op_cong.intros(4))
            apply simp_all
          apply (rule hwc_base)
          apply auto
          done
        done
      subgoal for buf ios x
        apply hypsubst_thin
        apply simp
        apply (cases lxs)
         apply simp_all
        apply hypsubst_thin
        subgoal for lxs'
          by (metis (mono_tags, lifting) history_while_op_cong.intros(5) hwc_base)
        done
      subgoal for y x buf ios
        apply hypsubst_thin
        apply simp
        apply (cases lxs)
         apply simp_all
        apply hypsubst_thin
        subgoal for lxs'
          apply (rule disjI2)+
          apply (rule history_while_op_cong.intros(4))
            prefer 3
            apply simp
           defer
           apply assumption
          apply simp
          apply (rule hwc_base)
          apply simp
          apply auto
          done
        done
      subgoal for x buf ios y
        apply hypsubst_thin
        apply simp
        apply (cases lxs)
         apply simp_all
        apply hypsubst_thin
        subgoal for lxs'
          apply (rule disjI2)+
          apply (rule history_while_op_cong.intros(3))
            prefer 3
            apply simp
           defer
           apply assumption
          apply simp
          apply (rule hwc_base)
          apply simp
          apply auto
          done
        done
      subgoal for buf ios x     
        apply hypsubst_thin
        apply simp
        apply (rule disjI1)
        apply (rule hwc_base)
        apply auto
        done
      subgoal for x buf ios
        apply hypsubst_thin
        apply simp
        apply (rule disjI2)
        apply (rule disjI1)
        apply (rule hwc_base)
        apply auto
        done
      subgoal for buf ios
        apply hypsubst_thin
        apply simp
        apply (metis (mono_tags, lifting) hwc_base) 
        done
      subgoal for buf ios
        apply hypsubst_thin
        apply simp
        apply (erule trace_while_True_op.cases)
          apply simp_all
        subgoal for x buf y ios
          apply hypsubst_thin
          apply (rule disjI1)
          apply (smt (verit, ccfv_threshold) bot2E hwc_base lproject_LCons(2) lproject_LCons(3) trace_while_op.intros(12))
          done
        subgoal
          apply hypsubst_thin
          apply (smt (verit, ccfv_threshold) bot2E hwc_base lproject_LCons(2) lproject_LCons(3) trace_while_op.intros(12))
          done
        done
      done
    done
  subgoal
    apply (rule exI[of _ "while_body_rehistory P f buf lxs lys"])
    apply (intro conjI)
    subgoal
      apply (coinduction arbitrary: buf lxs lys rule: trace_while_op.coinduct)
      subgoal for buf lxs lys
        apply (cases "(lys \<noteq> LNil \<and> BHD 1 buf = Observed (lhd lys) \<and> P (lhd lys) \<and> history_while_op P f (BTL 1 buf) lxs (ltl lys) READ_INPUT) \<or>
              (BHD 1 buf = EOB \<and> history_while_op P f buf lxs lys READ_INPUT) \<or>
              (BHD 1 buf = EOS \<and> history_while_op P f buf lxs LNil READ_INPUT) \<or>
              (\<exists> x. BHD 1 buf = Observed x \<and> history_while_op P f (BENQ 1 (f x) (BTL 1 buf)) lxs lys READ_INPUT \<and> \<not> P x)")
        subgoal
          apply (elim exE disjE conjE)
          subgoal
            apply simp
            apply (subst (1 3 5 7 9) while_body_rehistory.code)
            apply auto
            done
          subgoal
            apply simp
            apply (subst (1 3 5 7 9) while_body_rehistory.code)
            apply auto
            done
          subgoal
            apply simp
            apply (subst (1 2 3 5 7) while_body_rehistory.code)
            apply auto
            done
          subgoal for x
            apply simp
            apply (cases lxs)
            subgoal
              apply simp
              apply (subst (1 3 5 7 9) while_body_rehistory.code)
              apply auto
              done
            subgoal
              apply simp
              apply (subst (1 3 5 7 9) while_body_rehistory.code)
              apply auto
              done
            done
          done
        subgoal
          apply (cases lxs)
          subgoal
            apply simp
            apply (cases "BHD 1 buf")
            subgoal
              apply simp
              apply (subst (1 3 5 7 9 11 13) while_body_rehistory.code)
              apply (erule history_while_op.cases)
                    apply simp_all
              apply(intro conjI impI)
              subgoal
                by (metis bhd.elims buf.set_intros(1) funpow_0 observation.distinct(3) observation.sel observation.simps(3) set_buf_to_list_set_buf)
              subgoal
                apply (subst (1 3) while_body_rehistory.code)
                apply simp
                done
              subgoal
                apply (drule mp)
                subgoal
                  apply (rule history_while_op.intros(1))
                  apply auto
                  subgoal
                    by (metis bhd.elims buf.set_intros(1) observation.distinct(3) observation.sel observation.simps(3) pow_f_f_Suc set_buf_to_list_set_buf)
                  subgoal
                    by (metis ball_empty bhd.elims buf.set_intros(1) empty_set list.set_sel(2) observation.distinct(3) observation.sel observation.simps(3) set_buf_to_list_set_buf)
                  done
                apply simp
                done
              done
            subgoal
              by simp
            subgoal
              apply simp
              apply (subst (1 3 5 7) while_body_rehistory.code)
              apply simp
              using history_while_op.intros(2) apply blast
              done
            done
          subgoal for x' lxs'
            apply simp
            apply (cases "BHD 1 buf")
            subgoal for y
              apply simp
              apply (cases "P x'")
              subgoal
                apply (cases "P y")
                subgoal
                  apply simp
                  apply (rule disjI1)
                  apply (subst (1) while_body_rehistory.code)
                  apply simp
                  apply (rule disjI1)
                  apply (intro exI conjI)
                   apply (rule refl)
                  apply hypsubst_thin
                  apply (erule history_while_op.cases)
                        apply auto
                  subgoal
                    apply (metis btl.simps(2) buf_to_list.simps(2) buf_to_list_btl fun_upd_same history_while_op.intros(1) list.set_sel(2))
                    done
                  subgoal
                    apply (erule history_while_op.cases)
                          apply auto
                    apply (metis btl.simps(2) buf_to_list.simps(2) buf_to_list_btl fun_upd_same history_while_op.intros(1) list.set_sel(2))
                    done
                  subgoal
                    apply (erule history_while_op.cases)
                          apply auto
                    apply (metis btl.simps(2) buf_to_list.simps(2) buf_to_list_btl fun_upd_same history_while_op.intros(1) list.set_sel(2))
                    done
                  done
                subgoal
                  apply simp
                  apply (rule disjI1)
                  apply (subst (1) while_body_rehistory.code)
                  apply simp
                  apply (rule disjI1)
                  apply (intro exI conjI)
                   apply (rule refl)
                  apply hypsubst_thin
                  apply (erule history_while_op.cases)
                        apply auto
                  subgoal
                    apply (rule history_while_op.intros(1))
                    apply auto
                    subgoal
                      by (metis bhd.elims buf.set_intros(1) observation.distinct(3) observation.sel observation.simps(3) pow_f_f_Suc set_buf_to_list_set_buf)
                    subgoal
                      by (metis btl.simps(2) buf_to_list.simps(2) buf_to_list_btl list.set_sel(2))
                    done
                  subgoal
                    apply (erule history_while_op.cases)
                          apply auto
                    apply (rule history_while_op.intros(1))
                    apply auto
                    subgoal
                      by (metis bhd.elims buf.set_intros(1) observation.distinct(3) observation.sel observation.simps(3) pow_f_f_Suc set_buf_to_list_set_buf)
                    subgoal
                      by (metis btl.simps(2) buf_to_list.simps(2) buf_to_list_btl list.set_sel(2))
                    done
                  subgoal
                    apply (erule history_while_op.cases)
                          apply auto
                    apply (rule history_while_op.intros(1))
                    apply auto
                    subgoal
                      by (metis bhd.elims buf.set_intros(1) observation.distinct(3) observation.sel observation.simps(3) pow_f_f_Suc set_buf_to_list_set_buf)
                    subgoal
                      by (metis btl.simps(2) buf_to_list.simps(2) buf_to_list_btl list.set_sel(2))
                    done
                  done
                done
              subgoal
                apply (cases "P y")
                subgoal
                  apply simp
                  apply (rule disjI2)
                  apply (rule disjI2)
                  apply (rule disjI1)
                  apply (subst (1) while_body_rehistory.code)
                  apply simp
                  apply (subgoal_tac "BHD (buf 1) (benq (f x')) = Observed y")
                   defer
                  subgoal
                    by (metis benq.elims bhd.simps(1) bhd.simps(2) bhd.simps(3) observation.disc(1) observation.disc(2) observation.disc(3))
                  apply simp
                  apply (rule disjI1)
                  apply (intro conjI exI)
                   apply (rule refl)
                  apply (erule history_while_op.cases)
                        apply auto
                  subgoal
                    apply (rule history_while_op.intros(1))
                    apply auto
                    subgoal
                      by (metis bhd.elims buf.set_intros(1) funpow_0 observation.distinct(3) observation.inject observation.simps(3) set_buf_to_list_set_buf)
                    done
                  subgoal
                    apply (erule history_while_op.cases)
                          apply auto
                    apply (rule history_while_op.intros(1))
                    apply auto
                    apply (metis bhd.elims buf.set_intros(1) funpow_0 observation.distinct(3) observation.inject observation.simps(3) set_buf_to_list_set_buf)
                    done
                  subgoal
                    apply (erule history_while_op.cases)
                          apply auto
                    apply (rule history_while_op.intros(1))
                    apply auto
                    apply (metis bhd.elims buf.set_intros(1) funpow_0 observation.distinct(3) observation.inject observation.simps(3) set_buf_to_list_set_buf)
                    done
                  subgoal
                    apply (erule history_while_op.cases)
                          apply auto
                    apply (rule history_while_op.intros(1))
                    apply auto
                    apply (metis bhd.elims buf.set_intros(1) funpow_0 observation.distinct(3) observation.inject observation.simps(3) set_buf_to_list_set_buf)
                    done
                  subgoal
                    apply (erule history_while_op.cases)
                          apply auto
                    subgoal
                      apply (rule history_while_op.intros(1))
                      apply auto
                      apply (metis bhd.elims buf.set_intros(1) funpow_0 observation.distinct(3) observation.inject observation.simps(3) set_buf_to_list_set_buf)
                      done
                    done
                  done
                subgoal
                  apply simp
                  apply (rule disjI2)
                  apply (rule disjI1)
                  apply (subst (1) while_body_rehistory.code)
                  apply simp
                  apply (subgoal_tac "BHD (buf 1) (benq (f x')) = Observed y")
                   defer
                  subgoal
                    by (metis benq.elims bhd.simps(1) bhd.simps(2) bhd.simps(3) observation.disc(1) observation.disc(2) observation.disc(3))
                  apply simp
                  apply (rule disjI1)
                  apply (intro conjI exI)
                   apply (rule refl)
                  apply (erule history_while_op.cases)
                        apply auto
                  subgoal
                    apply (rule history_while_op.intros(1))
                    apply auto
                    subgoal
                      by (metis bhd.elims buf.set_intros(1) observation.distinct(3) observation.sel observation.simps(3) pow_f_f_Suc set_buf_to_list_set_buf)
                    subgoal
                      by (smt (verit, ccfv_threshold) Un_iff \<open>\<And>n. \<lbrakk>\<not> history_while_op P f (buf(1 := benq (f y) (btl (buf 1)))) (LCons x' lxs') LNil READ_INPUT; BHD 1 buf = Observed y; \<not> P x'; \<not> P y; BHD (buf 1) (benq (f x')) = Observed y; lys = LNil; \<forall>x\<in>set (buf_to_list (buf 1)). \<forall>n. \<not> P ((f ^^ n) x); lxs = LCons x' lxs'; P ((f ^^ n) (f y))\<rbrakk> \<Longrightarrow> False\<close> buf_to_list_benq buf_to_list_btl empty_iff empty_set fun_upd_same history_while_op.intros(1) list.sel(3) list.set_sel(2) set_ConsD set_append tl_append_if)
                    done
                  subgoal
                    apply (erule history_while_op.cases)
                          apply auto
                    apply (rule history_while_op.intros(1))
                    apply auto
                    subgoal
                      by (metis bhd.elims buf.set_intros(1) observation.distinct(3) observation.sel observation.simps(3) pow_f_f_Suc set_buf_to_list_set_buf)
                    subgoal
                      by (metis Nil_is_append_conv Un_iff empty_iff empty_set list.set_sel(2) not_Cons_self2 set_ConsD set_append)
                    done
                  subgoal
                    apply (erule history_while_op.cases)
                          apply auto
                    apply (rule history_while_op.intros(1))
                    apply auto
                    subgoal
                      by (metis bhd.elims buf.set_intros(1) observation.distinct(3) observation.sel observation.simps(3) pow_f_f_Suc set_buf_to_list_set_buf)
                    subgoal
                      by (metis Nil_is_append_conv Un_iff empty_iff empty_set list.set_sel(2) not_Cons_self2 set_ConsD set_append)
                    done
                  subgoal
                    apply (erule history_while_op.cases)
                          apply auto
                    apply (rule history_while_op.intros(1))
                    apply auto
                    subgoal
                      by (metis bhd.elims buf.set_intros(1) observation.distinct(3) observation.sel observation.simps(3) pow_f_f_Suc set_buf_to_list_set_buf)
                    subgoal
                      by (metis Nil_is_append_conv Un_iff empty_iff empty_set list.set_sel(2) not_Cons_self2 set_ConsD set_append)
                    done
                  subgoal
                    apply (erule history_while_op.cases)
                          apply auto
                    apply (rule history_while_op.intros(1))
                    apply auto
                    subgoal
                      by (metis bhd.elims buf.set_intros(1) observation.distinct(3) observation.sel observation.simps(3) pow_f_f_Suc set_buf_to_list_set_buf)
                    subgoal
                      by (metis Nil_is_append_conv Un_iff empty_iff empty_set list.set_sel(2) not_Cons_self2 set_ConsD set_append)
                    done
                  done
                done
              done
             apply (simp_all add: history_while_op.intros(2))
            done
          done
        done
      done
    subgoal
      apply (intro allI)
      subgoal for p
        apply (cases "p = 2")
        subgoal
          apply simp
          apply (coinduction arbitrary: buf lxs lys)
          subgoal for buf lxs lys
            unfolding lnull_def
            apply (intro conjI impI)
            subgoal
              apply (rule lproject_False)
               apply simp_all
              using Observed_not_inwhile_body_rehistory_LNil apply fast
              done
            subgoal
              apply (cases lxs)
               apply simp_all
              subgoal for x lxs'
                apply hypsubst_thin
                using while_body_rehistoryLCons_lhd apply fast
                done
              done
            subgoal
              apply (rule disjI1)
              apply (cases lxs)
               apply simp_all
              subgoal for x lxs'
                apply hypsubst_thin
                apply (cases "\<exists>n. llength (ltakeWhile (Not o (\<lambda>x. case x of Inp q (Observed xa) \<Rightarrow> (2::2) = q | Inp q _ \<Rightarrow> False | Out (q::2) x \<Rightarrow> \<bottom> (2::2) q)) (while_body_rehistory P f buf (LCons x lxs') lys)) = enat n")
   defer
  subgoal
    apply simp
    unfolding lproject_def neq_LNil_conv lmap_eq_LCons_conv
    apply auto
    apply (rule FalseE)
    apply (drule lfilter_eq_LCons)
    apply (elim exE conjE)
    apply hypsubst_thin
    apply (simp add: ldropWhile_eq_ldrop)
    done
  subgoal
    apply (elim exE)
    subgoal for n
    apply (induct n arbitrary: buf lxs' lys rule: less_induct)
      subgoal for n buf lxs lys
        apply (cases n)
        subgoal
          apply simp
          apply (subgoal_tac "\<not> (lys \<noteq> LNil \<and> BHD (1::2) buf = Observed (lhd lys) \<and> P (lhd lys) \<and> history_while_op P f (buf(1 := btl (buf (1::2)))) (LCons x lxs) (ctl lys) READ_INPUT \<or>
         BHD (1::2) buf = EOB \<and> history_while_op P f buf (LCons x lxs) lys READ_INPUT \<or>
         BHD 1 buf = EOS \<and> history_while_op P f buf (LCons x lxs) LNil READ_INPUT \<or>
         (\<exists>xa. BHD 1 buf = Observed xa \<and> history_while_op P f (buf((1::2) := btl (buf (1::2)), (1::2) := benq (f xa) ((buf((1::2) := btl (buf (1::2)))) (1::2)))) (LCons x lxs) lys READ_INPUT \<and> \<not> P xa))")
           defer
          subgoal
            apply (subst (asm) (1 2) while_body_rehistory.code)
            using zero_enat_def apply (auto split: if_splits)
            done
          apply (subst (asm) (1 2) while_body_rehistory.code)
            using zero_enat_def apply (auto split: if_splits)
            subgoal
              


end