theory Operator_Examples

imports
  Operator
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

corec window_op where
 "window_op f n buf time =
   Choice (cimage (\<lambda> time. 
     choice2
     (Read (1::1) (\<lambda> x. if n < time then writes (window_op f n [] (time mod n)) (1 :: 1) (f (buf @ [x]) # replicate (time div n - 1) (f [])) else Silent (window_op f n (buf @ [x]) time)))
     (if n < time then writes (window_op f n [] (time mod n)) 1 (f buf # replicate (time div n - 1) (f [])) else Silent (window_op f n buf time))
     ) (cset.acset {Suc time..}))"

corec filter_op where
  "filter_op P buf = choice2 
   (Read (1 :: 1) (\<lambda> x. filter_op P (if P x then buf @ [x] else buf)))
   (if buf = [] then filter_op P buf else Write (filter_op P (tl buf)) (1 :: 1) (hd buf))"

coinductive production_spec for P where
  "production_spec P state LNil"
| "production_spec P state' lxs \<Longrightarrow> P state ins out state' \<Longrightarrow>
   (\<forall> x \<in> set ins. is_VInp x) \<Longrightarrow> (\<forall> x \<in> set out. \<not> is_VInp x) \<Longrightarrow>
   ins @ out \<noteq> [] \<Longrightarrow> production_spec P state (ins @- out @- lxs)"

lemma step_empty_writes:
  "step io (writes op p []) op' \<Longrightarrow> step io op op'"
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

lemma writes_empty_buf_simp[simp]:
  "writes op p [] = op"
  apply (coinduction arbitrary: op rule: op.coinduct_upto)
  apply (intro conjI impI)
    apply (subst writes.code, simp split: op.splits)
    apply (subst writes.code, simp split: op.splits)
         apply (subst (asm) writes.code, simp add: window_op.cong_refl writes.friend.code rel_fun_def split: op.splits)
        apply (subst writes.code, simp split: op.splits)
         apply (subst (asm) writes.code, simp add: window_op.cong_refl writes.friend.code rel_fun_def split: op.splits)
      apply (subst writes.code, simp split: op.splits)
         apply (subst (asm) writes.code, simp add: window_op.cong_refl writes.friend.code rel_fun_def split: op.splits)
    apply (subst writes.code, simp split: op.splits)
   apply (subst (asm) writes.code, simp add: window_op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (meson cset.rel_refl rel_cset.rep_eq window_op.cong_refl)
  apply (subst (asm) writes.code, simp add: window_op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  done

lemma step_Inp_True_filter_op:
  "step io op op' \<Longrightarrow>
   io = Inp p x \<Longrightarrow>
   op = filter_op P buf \<Longrightarrow>
   P x \<Longrightarrow>
   p = 1 \<and> op' = filter_op P (buf @ [x])"
  apply (induct io op op' arbitrary: buf pred: step)
     apply (subst (asm) filter_op.code, simp)    
    apply (subst (asm) filter_op.code, simp)
    apply (subst (asm) filter_op.code, simp)
  subgoal for op ops io op' buf
    apply hypsubst_thin
    apply (subst (asm) (3) filter_op.code)
  apply (auto split: op.splits list.splits if_splits dest!: step_writes_reads_buf_empty step_empty_writes; hypsubst_thin)
    done
  done

lemma step_Inp_False_filter_op:
  "step io op op' \<Longrightarrow>
   io = Inp p x \<Longrightarrow>
   op = filter_op P buf \<Longrightarrow>
   \<not> P x \<Longrightarrow>
   p = 1 \<and> op' = filter_op P buf"
  apply (induct io op op' arbitrary: buf pred: step)
     apply (subst (asm) filter_op.code, simp)    
    apply (subst (asm) filter_op.code, simp)
    apply (subst (asm) filter_op.code, simp)
  subgoal for op ops io op' buf
    apply hypsubst_thin
    apply (subst (asm) (3) filter_op.code)
  apply (auto split: op.splits list.splits if_splits dest!: step_writes_reads_buf_empty step_empty_writes; hypsubst_thin)
    done
  done

lemma step_Tau_filter_op:
  "step io op op' \<Longrightarrow>
   io = Tau \<Longrightarrow>
   op = filter_op P buf \<Longrightarrow>
   False"
  apply (induct io op op' arbitrary: buf pred: step)
     apply (subst (asm) filter_op.code, simp)    
    apply (subst (asm) filter_op.code, simp)
    apply (subst (asm) filter_op.code, simp)
  subgoal for op ops io op' buf
    apply hypsubst_thin
    apply (subst (asm) (2) filter_op.code)
  apply (fastforce split: if_splits op.splits list.splits dest!: step_writes_reads_buf_empty step_empty_writes step_writes_silent_buf_empty; hypsubst_thin)
    done
  done

lemma wstep_Inp_True_filter_op:
  "wstep io op op' \<Longrightarrow>
   io = Inp p x \<Longrightarrow>
   op = filter_op P buf \<Longrightarrow>
   P x \<Longrightarrow>
   p = 1 \<and> op' = filter_op P (buf @ [x])"
  unfolding wstep_def
  apply (metis (mono_tags, lifting) converse_rtranclpE estep.simps(2) relcompp_apply step_Inp_True_filter_op step_Tau_filter_op)
  done

lemma wstep_Inp_False_filter_op:
  "wstep io op op' \<Longrightarrow>
   io = Inp p x \<Longrightarrow>
   op = filter_op P buf \<Longrightarrow>
   \<not> P x \<Longrightarrow>
   p = 1 \<and> op' = filter_op P buf"
  unfolding wstep_def
  apply (metis converse_rtranclpE estep.simps(2) pick_middlep step_Inp_False_filter_op step_Tau_filter_op)
  done

lemma step_Out_writes:
  "step (Out p x) (writes (filter_op P []) 1 (y # buf)) op \<Longrightarrow>
   op = writes (filter_op P []) 1 buf \<and> p = 1 \<and> y = x"
    apply (subst (asm) writes.code)
  apply (auto split: op.splits list.splits)
  done


lemma step_Out_filter_op:
  "step io op op' \<Longrightarrow>
   io = Out p x \<Longrightarrow>
   op = filter_op P buf \<Longrightarrow>
   p = 1 \<and> op' = filter_op P (tl buf) \<and> buf \<noteq> [] \<and> bhd buf = x"
  apply (induct io op op' arbitrary: buf pred: step)
     apply (subst (asm) filter_op.code, simp)    
    apply (subst (asm) filter_op.code, simp)
    apply (subst (asm) filter_op.code, simp)
  subgoal for op ops io op' buf
    apply hypsubst_thin
    apply (subst (asm) (3) filter_op.code)
    apply simp
    apply hypsubst_thin
    apply (elim disjE)
     apply hypsubst_thin
     apply force
    apply hypsubst_thin
    apply (cases buf; simp)
     apply blast
    apply (auto split: if_splits)
    done
  done

lemma wstep_Out_filter_op:
  "wstep io op op' \<Longrightarrow>
   io = Out p x \<Longrightarrow>
   op = filter_op P buf \<Longrightarrow>
   p = 1 \<and> op' = filter_op P (tl buf)\<and> buf \<noteq> [] \<and> bhd buf = x"
  unfolding wstep_def by (metis (no_types, lifting) converse_rtranclpE estep.simps(3) pick_middlep step_Out_filter_op step_Tau_filter_op step_writes_silent_buf_empty writes_empty_buf_simp)

lemma wtraced_production_spec:
  "\<forall> x \<in> set buf. P x \<Longrightarrow>
   wtraced (filter_op P buf) lxs \<Longrightarrow>
   production_spec (\<lambda> buf inps outs buf'. map (VOut 1) buf @ map (case_VIO VOut VOut) (filter (case_VIO (\<lambda> _ x. P x) \<top>) inps) = outs @ map (VOut 1) buf') buf lxs"
  apply (coinduction arbitrary: buf lxs rule: production_spec.coinduct)
  subgoal for buf lxs
    apply (erule wtraced.cases)
    subgoal for op
      by (cases buf; simp)
    subgoal for vio op op' lxs'
      apply hypsubst_thin
      apply (cases vio; simp; hypsubst_thin?)
      subgoal for p x
        apply (cases "P x")
        subgoal
          apply (rule exI[of _ "buf @ [x]"])
          apply (rule exI[of _ "lxs'"])
          apply (rule exI[of _ "[VInp p x]"])
          apply (rule exI[of _ "[]"])
          apply simp
          apply (intro disjI1 conjI)
          using wstep_Inp_True_filter_op apply force
          done
        subgoal
          apply (rule exI[of _ "buf"])
          apply (rule exI[of _ "lxs'"])
          apply (rule exI[of _ "[VInp p x]"])
          apply (rule exI[of _ "[]"])
          apply simp
          apply (intro disjI1 conjI)
          using wstep_Inp_False_filter_op apply force
          done
        done
      subgoal for p x
        apply (drule wstep_Out_filter_op)
          apply (rule refl)+
        apply safe
        apply (rule exI[of _ "btl buf"])
        apply (rule exI[of _ "lxs'"])
        apply (rule exI[of _ "[]"])
        apply (rule exI[of _ "[VOut p x]"])
        apply simp
        apply (intro disjI1 conjI)
         apply (metis list.set_sel(2))
        apply (metis (full_types) list.exhaust_sel list.simps(9) num1_eq1)
        done
      done
    done
  done  


lemma wtraced_production_spec_extends:
  "\<forall> x \<in> set buf. P x \<Longrightarrow>
   wtraced (filter_op P buf) lxs \<Longrightarrow>
   \<exists> lys. wtraced (filter_op P buf) (lappend lxs lys) \<and>
   production_spec (\<lambda> buf inps outs buf'. map (VOut 1) buf @ map (case_VIO VOut VOut) (filter (case_VIO (\<lambda> _ x. P x) \<top>) inps) = outs @ map (VOut 1) buf') buf (lappend lxs lys)"
  oops


end