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
simps_of_case loop_op_simps[simp]: loop_op_code

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

definition loop22_op :: "'d op22 \<Rightarrow> 'd op11" where
  "loop22_op op = map_op (\<lambda>_. 1) (\<lambda>_. 1) (loop_op
    (\<lambda>x. if x = 1 then Some 1 else None) (\<lambda>_. BEmpty) op)"

end