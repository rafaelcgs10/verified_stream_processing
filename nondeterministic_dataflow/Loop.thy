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

definition loop22_op :: "'d op22 \<Rightarrow> 'd op11" where
  "loop22_op op = map_op (\<lambda>_. 1) (\<lambda>_. 1) (loop_op
    (\<lambda>x. if x = 1 then Some 1 else None) (\<lambda>_. BEmpty) op)"

corec Suc_op where
  "Suc_op = Read (2::2) 
            (case_observation 
              (Write (Read 1 (case_observation (\<lambda> x. Write (Write Suc_op 1 (Suc x)) (2::2) (Suc x)) Suc_op Suc_op)) 1) Suc_op Suc_op)"

abbreviation "loop_Suc_op buf \<equiv> loop_op
    (\<lambda>x. if x = 1 then Some 1 else None) buf Suc_op"


lemma
  "history (loop_Suc_op (\<lambda> _. BCons 0 BEmpty)) (\<lambda> x. LNil) (\<lambda> x. if x = 2 then iterates Suc 0 else LNil)"
  unfolding history_def
  apply (simp add: traced_loop_op)
  apply (rule exI[of _ "iterates (case_IO undefined (\<lambda> p n. Out p (Suc n))) (Out 2 0)"])
  apply (intro conjI)
  subgoal
    apply (rule exI[of _ "retrace_loop_op (\<lambda>x. if x = 1 then Some 1 else None) (\<lambda>_. BCons 0 BEmpty) Suc_op LNil"])
    apply (intro conjI)
      apply (auto simp add: ran_def split: if_splits)
    subgoal
    apply (coinduction )
    apply (intro conjI impI iffI)
    subgoal
      by auto
    subgoal
      apply (subst (asm) Suc_op.code)
      apply (auto simp add: ran_def split: if_splits)
      done
    subgoal
      unfolding lnull_def
      apply (subst iterates.code)
      apply simp
      apply (subst Suc_op.code)
      apply (simp add: ran_def)
     oops

end