theory Cycles

imports "../Llists_Processors"

begin

coinductive le_op where
   "lprefix (buf1 @@- exit op1) (buf2 @@- exit op2) \<Longrightarrow>
    (\<And> ev op1' op2' out1 out2. 
      apply op1 ev = (op1', out1) \<Longrightarrow> apply op2 ev = (op2', out2) \<Longrightarrow> le_op op1' (buf1@out1) op2' (buf2@out2)) \<Longrightarrow>
     le_op op1 buf1 op2 buf2"

primcorec cp where
  "cp = Logic (\<lambda> ev . (cp, [ev])) (LNil)"


primcorec lazy_cp where
  "lazy_cp buf = Logic (\<lambda> ev . (lazy_cp (buf@[ev]), [])) (llist_of buf)"

lemma
  "le_op (lazy_cp buf) buf' cp (buf'@buf)"
  apply (coinduction arbitrary: buf buf' rule: le_op.coinduct)
  apply auto
  by (metis lappend_llist_of lappend_llist_of_llist_of llist.leq_refl)

lemma
  "le_op cp (buf'@buf) (lazy_cp buf) buf'"
  apply (coinduction arbitrary: buf buf' rule: le_op.coinduct)
  apply auto
  by (metis lappend_llist_of lappend_llist_of_llist_of llist.leq_refl)


lemma le_op_trans:
  "le_op op1 buf1 op2 buf2 \<Longrightarrow>
   le_op op2 buf2 op3 buf3 \<Longrightarrow>
   le_op op1 buf1 op3 buf3"
  apply (coinduction arbitrary: buf1 buf2 buf3 op1 op2 op3 rule: le_op.coinduct)
  apply auto
   apply (meson le_op.cases llist.leq_trans)
  apply (erule le_op.cases)
  apply (erule le_op.cases)
  apply auto
  apply (meson surj_pair)
  done

primcorec prepend_op where
  "prepend_op buf op = Logic (\<lambda> ev. let (op', out) = apply op ev in (op', buf@out)) (buf @@- (exit op))"

lemma prepend_op_Nil[simp]:
  "prepend_op [] op = op"
  apply (coinduction arbitrary: op rule: op.coinduct_strong)
  apply (auto simp add: rel_fun_def rel_prod.simps)
  subgoal for op ev
    apply (cases "apply op ev")
    apply simp
    done
  done


lemma
  "le_op op1 buf1 op2 buf2 \<Longrightarrow>
   le_op op2 buf2 op1 buf1 \<Longrightarrow>
   prepend_op buf1 op1 = prepend_op buf2 op2"
  apply (coinduction arbitrary: op1 buf1 op2 buf2 rule: op.coinduct)
  apply (erule le_op.cases)
  apply (erule le_op.cases)
  apply (auto simp add: rel_fun_def rel_prod.simps)
  subgoal for buf1a op1a buf2a op2a x
  apply (drule llist.leq_antisym)
     apply assumption
    apply auto
    apply (drule meta_spec[of _ x])+
    apply (cases "apply op1a x")
    apply (cases "apply op2a x")
    apply auto
    oops

  find_theorems lprefix name: anti

primcorec unproduce_op :: "('a llist \<Rightarrow> 'b llist) \<Rightarrow> ('a, 'b) op" where
  "unproduce_op f = 
    (Logic (\<lambda> ev. 
             let out = f (LCons ev LNil) in
             if lfinite out
             then (unproduce_op (\<lambda> lxs. ldropn (the_enat (llength out)) (f (LCons ev lxs))), list_of out)
             else (unproduce_op (\<lambda> _. ltl out), [lhd out]))
           (f LNil))"


(* FIXME: monotone lprefix lprefx f *)
lemma unproduce_op_correct_1[simp]:
  "produce (unproduce_op f) = f"
  sorry

lemma  unproduce_op_correct_2[simp]:
  "unproduce_op (produce op) = op"
  sorry

primcorec incr_Inl where
  "incr_Inl = Logic (\<lambda> ev. 
     case ev of 
       Inl (n::nat) \<Rightarrow> (if n \<ge> 1 then (incr_Inl, [Inr n]) else (incr_Inl, [Inl (n + 1)]))
     | Inr n \<Rightarrow> (incr_Inl, [Inr n])) LNil"

primcorec loop_op where
  "loop_op b op  = Logic (\<lambda> ev. let (op', out) = apply op ev in if b ev then (loop_op b op', out) else (op, [ev])) LNil"

definition "ex1 (F::(nat + nat) llist \<Rightarrow> (nat + nat) llist) lxs = produce (compose_op incr_Inl (loop_op isl (unproduce_op F))) lxs"

declare produce_inner.simps[code]
declare llist.mono_body_fixp[code]
(* declare lSup.code[code del]
 *)

thm llist.mono_body_fixp

(* 
value "lhd' (produce (unproduce_op (llist.fixp_fun ex1)) (LCons (Inl 3) LNil))"
 *)

value "lhd' (produce incr_Inl (LCons (Inl 2) LNil))"

lemma produce_incr_Inl_if:
  "produce incr_Inl (LCons (Inl n) lxs) = (if n \<ge> 1 then LCons (Inr n) (produce incr_Inl lxs) else LCons (Inl (n+1)) (produce incr_Inl lxs))"
  apply (subst produce.code)
  apply (subst produce_inner.simps)
  apply (auto split: option.splits sum.splits)
  done

lemma produce_incr_Inr[simp]:
  "produce incr_Inl (LCons (Inr n) lxs) = LCons (Inr n) (produce incr_Inl lxs)"
  apply (subst produce.code)
  apply (subst produce_inner.simps)
  apply (auto split: option.splits sum.splits)
  done

lemma [simp]:
  "produce (loop_op b op) LNil = LNil"
  apply (subst produce.code)
  apply auto
  done

(* bicomposeOp op1 op2 = Logic (\ev ->
                               let (op1', out) = apply op1 ev in
                               let (lout, rout) = partitionEithers out in
                               let (op2', out') = finiteProduce op2 (map Left lout) [] in
                               (bicomposeOp op1' op2', rout++out')) (let (lout, rout) = partitionEithers $ exit op1 in rout ++ (if null lout then [] else produce op2 (map Left lout)))
 *)

consts lpartitionEithers::"('a + 'b) llist \<Rightarrow> ('a llist \<times> 'b llist)"
consts partitionEithers::"('a + 'b) list \<Rightarrow> ('a list \<times> 'b list)"


primcorec bicompose_op where
  "bicompose_op op1 op2 = Logic (\<lambda>ev .
                               let (op1', out) = apply op1 ev in
                               let (lout, rout) = partitionEithers out in
                               let (op2', out') = finite_produce op2 (map Inl lout) in
                               (bicompose_op op1' op2', rout@out')) (let (lout, rout) = lpartitionEithers (exit op1) in lappend rout (if lnull lout then LNil else produce op2 (lmap Inl lout))) "

instantiation op :: (type, ccpo) ccpo begin
instance sorry
end
term ccpo.fixp
definition rec_op where "rec_op op = ccpo.fixp Sup (\<le>) (bicompose_op op)"

lemma "rec_op op = bicompose_op op (rec_op op)"
  unfolding rec_op_def
  apply (rule ccpo.fixp_unfold)
  sorry

lemma produce_loop_op_if:
  "produce (loop_op b op) (LCons x lxs) = (
   let (op', out) = apply op x in
   if b x 
   then out @@- produce (loop_op b op') lxs
   else LCons x (produce op lxs))"
  apply (cases "b x")
  subgoal
    apply (subst (1) produce.code)
    apply (subst (1) produce_inner.simps)
    apply (auto 1 1 split: sum.splits llist.splits list.splits option.splits prod.splits)
    subgoal
      apply (subst (1) produce.code)
      apply auto
      done
    subgoal
      apply (subst (1) produce.code)
      apply auto
      done
    done
  apply simp
  done
(*
  subgoal
      apply (subst (1) produce.code)
      apply (auto split: option.splits)
      done
    subgoal
      apply (subst (1) produce.code)
      apply auto
      done
    done*)

lemma [simp]:
  "ldropn (the_enat (eSuc 0)) = ltl"
  apply (rule ext)
  subgoal for x
    apply (cases x; auto)
    apply (metis One_nat_def ldropn_0 ldropn_Suc_LCons one_eSuc one_enat_def the_enat.simps)
    done
  done

thm llist.mono_body_fixp

find_consts name: le name: "fun"


thm le_fun_def

find_theorems llist.fixp_fun name: mono

lemma "produce (unproduce_op (llist.fixp_fun ex1)) (LCons (Inl 0) (LCons (Inl 0) LNil)) = LCons (Inr 1) (LCons (Inr 1) LNil)"
  unfolding ex1_def
  apply (simp add:  finite_produce_simps produce_loop_op_if split: list.splits)
  apply (subst llist.mono_body_fixp)
  subgoal sorry
  apply (subst produce_compose_op_correctness)
  subgoal sorry
  apply (auto simp add: produce_incr_Inl_if produce_loop_op_if split: list.splits)
  subgoal
  apply (subst llist.mono_body_fixp)
    subgoal sorry
  apply (subst produce_compose_op_correctness)
  subgoal sorry
  apply (auto simp add: produce_incr_Inl_if produce_loop_op_if split: list.splits)
  apply (subst llist.mono_body_fixp)
    subgoal sorry
  apply (auto simp add: produce_incr_Inl_if produce_loop_op_if split: list.splits)
  apply (subst llist.mono_body_fixp)
    subgoal sorry
  apply (subst produce_compose_op_correctness)
    subgoal sorry
  apply (auto simp add: produce_incr_Inl_if produce_loop_op_if split: list.splits)
  apply (subst llist.mono_body_fixp)
    subgoal sorry
  apply (auto simp add: produce_incr_Inl_if produce_loop_op_if split: list.splits)
 apply (subst llist.mono_body_fixp)
    subgoal sorry
  apply (subst produce_compose_op_correctness)
    subgoal sorry
    apply (auto simp add: produce_incr_Inl_if produce_loop_op_if split: list.splits)
 apply (subst llist.mono_body_fixp)
    subgoal sorry
 apply (subst produce_compose_op_correctness)
    oops

(* 
primcorec rec_op where
  "rec_op b op = Logic (\<lambda> ev. 
     let (op', out) = apply op ev in
     let cycle = filter (\<lambda> x. \<not> b x) out in
     let out' = filter b out in
     let (op'', out'') = finite_produce (rec_op b op') cycle [] in
     (rec_op b op'',  out' @ out'')) LNil"

 *)

end
