theory Cycles

imports "../Llists_Processors"

begin

coinductive le_op where
   "lprefix (buf1 @@- exit op1) (buf2 @@- exit op2) \<Longrightarrow> prefix buf1 buf2 \<Longrightarrow>
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
  apply simp
  oops

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
  apply (meson eq_snd_iff le_op.cases)
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

lemma lprefix_lshift:
  "lprefix (xs @@- lxs) (xs @@- lys) \<Longrightarrow>
   lprefix lxs lys"
  apply (induct xs arbitrary: lxs lys rule: rev_induct)
   apply clarsimp+
  apply (meson LCons_lprefix_LCons)
  done

lemma le_op_same_prefix:      
  "le_op op1 (xs@ys) op2 (xs@zs) \<Longrightarrow>
   le_op op1 ys op2 zs"
  apply (coinduction arbitrary: op1 xs ys zs op2 rule: le_op.coinduct)
  apply (erule le_op.cases)
  apply auto
  using lprefix_lshift apply blast+
  done

lemma le_op_clean_buffers:      
  "le_op op1 xs op2 xs \<Longrightarrow>
   le_op op1 [] op2 []"
  using le_op_same_prefix
  by (metis append_Nil2)


lemma le_op_antisym:
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
    apply (meson le_op.cases prefix_order.dual_order.eq_iff)
    done
  subgoal for buf1a op1a buf2a op2a x
 apply (drule llist.leq_antisym)
     apply assumption
    apply auto
    apply (drule meta_spec[of _ x])+
    apply (cases "apply op1a x")
    apply (cases "apply op2a x")
    apply auto
    subgoal for op1' out1' op2' out2'    
      apply (rule exI[of _ op1'])
      apply (rule exI[of _ "[]"])
    apply (intro conjI)
       apply simp
      apply (rule exI[of _ op2'])
      apply (rule exI[of _ "[]"])
      apply simp
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)      
      apply (drule meta_mp)
       apply (rule refl)      
      apply (drule meta_mp)
      apply (rule refl)
      apply (subgoal_tac "out1' = out2'")
      subgoal
        apply hypsubst_thin
        using le_op_clean_buffers
        using prefix_order.antisym apply blast
        done
      subgoal
        by (metis le_op.cases prefix_order.antisym_conv same_prefix_prefix)
      done
    done
  subgoal
    using llist.leq_antisym by blast
  done

lemma le_op_refl:
  "le_op op buf op buf"
  apply (coinduction arbitrary: op buf  rule: le_op.coinduct)
  apply auto
  done

primcorec nil_op where "nil_op = Logic (\<lambda> ev . (nil_op, [])) (LNil)"
primcorec one_op where "one_op = Logic (\<lambda> ev . (nil_op, [1])) (LNil)"
primcorec ones_op where "ones_op = Logic (\<lambda> ev . (ones_op, [1])) (LNil)"
primcorec lazy_ones_op where "lazy_ones_op = Logic (\<lambda> ev . (lazy_ones_op, [])) (repeat 1)"
primcorec mixed_lazy_ones_op where "mixed_lazy_ones_op = Logic (\<lambda> ev . (lazy_ones_op, [1])) (LNil)"


(* primcorec Sup_op :: "('i, 'o) op set \<Rightarrow> ('i, 'o) op"
where
  "Sup_op A =
  (if \<forall>x\<in>A. lnull x then LNil
   else LCons (THE x. x \<in> lhd ` (A \<inter> {xs. \<not> lnull xs})) (Sup_op (ltl ` (A \<inter> {xs. \<not> lnull xs}))))"
 *)

definition "(Sup_op:: ('i, 'o) op set \<Rightarrow> ('i, 'o) op) A = undefined"

lemma
  "Sup_op {} = nil_op"
  oops

lemma
  "Sup_op {nil_op, one_op} = one_op"
  oops

lemma
  "Sup_op {ones_op, lazy_ones_op} = ones_op"
  oops

lemma
  "Sup_op {one_op, lazy_ones_op} = lazy_ones_op"
  oops

lemma
  "Sup_op {one_op, ones_op} = ones_op"
  oops

abbreviation "le_op' buf1 buf2 op1 op2 \<equiv> le_op op1 buf1 op2 buf2"

lemma chain_le_op_Sup_l:
  "Complete_Partial_Order.chain (le_op' buf1 buf2) A \<Longrightarrow> x \<in> A \<Longrightarrow> (le_op' buf1 buf2) x (Sup_op A)"
  oops

lemma chain_le_op_Sup_r:
  "Complete_Partial_Order.chain (le_op' buf1 buf2) A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> (le_op' buf1 buf2) y x) \<Longrightarrow> (le_op' buf1 buf2) (Sup_op A) x"
  oops


lemma res_ccpo: "class.ccpo Sup_op (le_op' buf1 buf2) (mk_lt res_ord)"
  apply intro_locales
(*     apply (rule preorder_mk_ltI)
      apply unfold_locales
      apply (auto intro: res_ord_trans res_ord_antisym chain_res_ord_res_Sup_l chain_res_ord_res_Sup_r)
  done
   *)
  oops

primcorec unproduce_op :: "('a llist \<Rightarrow> 'b llist) \<Rightarrow> ('a, 'b) op" where
  "unproduce_op f = 
    (Logic (\<lambda> ev. 
             let out = f (LCons ev LNil) in
             (unproduce_op (\<lambda> lxs. ldrop (llength out) (f (LCons ev lxs))), list_of out))
           (f LNil))"


(* FIXME: monotone lprefix lprefx f *)
lemma unproduce_op_correct_1[simp]:
  "produce (unproduce_op f) = f"
  sorry


lemma  unproduce_op_correct_2[simp]:
  "monotone lprefix lprefix (produce op) \<Longrightarrow>
   unproduce_op (produce op) = op"
  find_theorems monotone name: "_induc"


  oops
  apply (coinduction arbitrary: op)
  subgoal for op
    apply (cases op)
    apply hypsubst_thin
    subgoal for lgc exit
      apply (simp add: rel_fun_def split: list.splits prod.splits if_splits)
      apply (intro impI conjI allI)
      subgoal for ev
      apply (cases "lgc ev")
        apply simp
        subgoal for op' out'
          apply auto
          subgoal sorry
          subgoal sorry
          subgoal



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
