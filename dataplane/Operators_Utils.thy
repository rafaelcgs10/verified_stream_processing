theory Operators_Utils

imports
  Nondeterministic_Dataflow.Operator
begin 

corec writes where
  "writes op p xs =
    (case xs of [] \<Rightarrow> case_op Read Write Choice Silent op | x #xs \<Rightarrow> Write (writes op p xs) p x)"

lemma foo[friend_of_corec_simps]:
  "(if snd (snd x) = [] then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x)))) else ctor_op (Abs_op_pre_op (Inl (Inr (algrho (fst x, fst (snd x), btl (snd (snd x))), fst (snd x), bhd (snd (snd x))))))) =
         (if snd (snd x) = []
         then if isl (Rep_op_pre_op (dtor_op (fst x))) \<and> isl (projl (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
              else if isl (Rep_op_pre_op (dtor_op (fst x))) \<and> \<not> isl (projl (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
                   else if \<not> isl (Rep_op_pre_op (dtor_op (fst x))) \<and> isl (projr (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
                        else ctor_op
                              (Abs_op_pre_op
                                (Inr (Inr (if isl (Rep_op_pre_op (dtor_op (fst x))) then undefined
                                           else if isl (projr (Rep_op_pre_op (dtor_op (fst x)))) then undefined else projr (projr (Rep_op_pre_op (dtor_op (fst x))))))))
         else ctor_op (Abs_op_pre_op (Inl (Inr (algrho (fst x, fst (snd x), btl (snd (snd x))), fst (snd x), bhd (snd (snd x)))))))"
  by (auto split: if_splits)

friend_of_corec writes where
  "writes op p xs =
    (case xs of [] \<Rightarrow> case_op Read Write Choice Silent op | x #xs \<Rightarrow> Write (writes op p xs) p x)"
  apply (rule writes.code)
  apply transfer_prover
  done

lemma step_Out_writes:
  "step io (writes op p buf) op' \<Longrightarrow>
   buf \<noteq> [] \<Longrightarrow>
   op' = writes op p (tl buf) \<and> io = Out p (hd buf)"
  apply (subst (asm) writes.code)
  apply (auto split: op.splits list.splits)
  done

lemma step_writes_reads_buf_empty:
  "step io (writes op p buf) op' \<Longrightarrow> io = Inp p' x \<Longrightarrow> buf = []"
  apply (subst (asm) writes.code)
  apply (auto split: op.splits list.splits)
  done

lemma step_writes_silent_buf_empty:
  "step io (writes op p buf) op' \<Longrightarrow> io = Tau \<Longrightarrow> buf = []"
  apply (subst (asm) writes.code)
  apply (auto split: op.splits list.splits)
  done

lemma step_writes_Out_intro[intro]:
  "buf = x # buf' \<Longrightarrow>
   op' = writes op p buf'\<Longrightarrow>
   step (Out p x) (writes op p buf) op'"
  apply (subst writes.code)
  apply (auto split: op.splits list.splits)
  done

lemma writes_empty_buf_simp[simp]:
  "writes op p [] = op"
  apply (coinduction arbitrary: op rule: op.coinduct_upto)
  apply (intro conjI impI)
  apply (subst writes.code, simp split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (meson cset.rel_refl rel_cset.rep_eq op.cong_refl)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  done

lemma writes_Cons_simp:
  "writes op p (x # xs) = Write (writes op p xs) p x"
  apply (coinduction arbitrary: op rule: op.coinduct_upto)
  apply (intro conjI impI)
  apply (subst writes.code, simp split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  done

end