theory Cycles

imports "../Llists_Processors"

begin

coinductive le_op where
  "lprefix (buf1 @@- exit op1) (buf2 @@- exit op2) \<Longrightarrow> prefix buf2 buf1 \<Longrightarrow>
    (\<And> ev op1' op2' out1 out2.
      apply op1 ev = (op1', out1) \<Longrightarrow> apply op2 ev = (op2', out2) \<Longrightarrow> le_op op1' (buf1@out1) op2' (buf2@out2)) \<Longrightarrow>
     le_op op1 buf1 op2 buf2"

primcorec cp_op where
  "cp_op = Logic (\<lambda> ev . (cp_op, [ev])) (LNil)"

primcorec lazy_cp_op where
  "lazy_cp_op buf = Logic (\<lambda> ev . (lazy_cp_op (buf@[ev]), [])) (llist_of buf)"

lemma
  "le_op (lazy_cp_op buf) buf' cp_op (buf'@buf)"
  apply (coinduction arbitrary: buf buf' rule: le_op.coinduct)
  apply auto
  oops

lemma
  "le_op cp_op (buf'@buf) (lazy_cp_op buf) buf'"
  apply (coinduction arbitrary: buf buf' rule: le_op.coinduct)
  apply simp
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

lemma lprefix_lshift[simp]:
  "lprefix (xs @@- lxs) (xs @@- lys) \<longleftrightarrow>
   lprefix lxs lys"
  apply (intro iffI)
  subgoal
    apply (induct xs arbitrary: lxs lys rule: rev_induct)
     apply clarsimp+
    apply (meson LCons_lprefix_LCons)
    done
  subgoal
    by (metis lappend_llist_of lprefix_lappend_sameI)
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

(* FIXME: move me *)
lemma lshift_lfinite:
  "lfinite lxs \<Longrightarrow>
   xs @@- lxs = llist_of (xs @ list_of lxs)"
  by (metis lappend_llist_of lappend_llist_of_llist_of llist_of_list_of)

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

lemma le_op_antisym':
  "le_op op1 [] op2 [] \<Longrightarrow>
   le_op op2 [] op1 [] \<Longrightarrow>
   op1 = op2"
  apply (drule le_op_antisym)
   apply assumption
  apply simp
  done

lemma le_op_op_same_prefix_simp[simp]:
  "le_op op1 (buf @ buf1) op2 (buf @ buf2) \<longleftrightarrow> le_op op1 buf1 op2 buf2"
  apply (rule iffI)
  subgoal
    using le_op_same_prefix by blast
  subgoal
    apply (coinduction arbitrary: op1 buf buf1 buf2 op2 rule: le_op.coinduct)
    apply (erule le_op.cases)
    apply auto
    by metis
  done

abbreviation "le_op' op1 op2 \<equiv> le_op op1 [] op2 []"


instantiation op :: (_, _) ord
begin
definition "less_eq_op = le_op'"

definition "less_op op1 op2 \<longleftrightarrow> le_op' op1 op2 \<and> \<not> (le_op' op2 op1)"

instance ..
end


instance op :: (_, _) preorder
proof
  fix x y z :: "('i, 'o) op"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    unfolding less_eq_op_def less_op_def
    apply auto
    done
  show "x \<le> x"
    unfolding less_eq_op_def
    apply (simp add: le_op_refl)
    done
  assume "x \<le> y" and "y \<le> z" thus "x \<le> z"
    unfolding less_eq_op_def
    using le_op_trans apply blast
    done
qed

instance op :: (_, _) order
  apply standard
  apply (metis le_op_antisym less_eq_op_def prepend_op_Nil)
  done

primcorec nil_op where "nil_op = Logic (\<lambda> ev . (nil_op, [])) LNil"
primcorec one_op where "one_op = Logic (\<lambda> ev . (nil_op, [1])) (LCons 1 LNil)"
primcorec ones_op where "ones_op = Logic (\<lambda> ev . (ones_op, [1])) (repeat 1)"
primcorec lazy_ones_op where "lazy_ones_op = Logic (\<lambda> ev . (lazy_ones_op, [])) (repeat 1)"
primcorec mixed_lazy_ones_op where "mixed_lazy_ones_op = Logic (\<lambda> ev . (lazy_ones_op, [1])) (LNil)"

lemma one_op_neq_nil_op[simp]:
  "one_op \<noteq> nil_op"
  unfolding not_def
  apply (rule impI)
  apply (drule arg_cong[where f="apply"])
  apply (drule fun_cong[where x=undefined])
  apply simp
  done


lemma skip_n_productions_op_nil_op[simp]:
  "skip_n_productions_op nil_op n = nil_op"
  apply (coinduction arbitrary: n rule: op.coinduct)
  apply (auto simp add: rel_fun_def)
  apply (rule exI[of _ 0])
  apply auto
  done


lemma skip_n_productions_op_one_op:
  "skip_n_productions_op one_op (Suc n) = skip_n_productions_op nil_op n"
  apply (coinduction arbitrary: n rule: op.coinduct)
  apply (auto simp add: rel_fun_def)
  subgoal for n
    apply (rule exI[of _ 0])
    apply (subst skip_n_productions_op.ctr)
    apply (subst nil_op.ctr)
    apply (simp add: ldrop_enat)
    done
  subgoal
    apply (rule exI[of _ 0])
    apply (subst skip_n_productions_op.ctr)
    apply (subst nil_op.ctr)
    apply (simp add: ldrop_enat)
    done
  subgoal
    by (simp add: leI zero_enat_def)
  done    

lemma skip_n_productions_op_1_one_op[simp]:
  "skip_n_productions_op one_op (Suc 0) = nil_op"
  by (simp add: skip_n_productions_op_one_op)

lemma LCons_1_lSup[simp]:
  "lSup {LNil, LCons 1 LNil} = LCons 1 LNil"
  by (simp add: lSup_insert_LNil)

lemma LCons_1_lub_fun[simp]:
  "llist.lub_fun {\<lambda>_. LNil, \<lambda>_. LCons 1 LNil} = (\<lambda>_. LCons 1 LNil)"
  by (metis (mono_tags, lifting) LCons_1_lSup fun_lub_apply image_empty image_insert)

primcorec const_op :: "'o llist \<Rightarrow> ('i, 'o) op" where
  "const_op lxs = 
   (if lxs = LNil 
    then nil_op
   else Logic (\<lambda> _. (const_op (ltl lxs), [lhd lxs])) lxs)"

primcorec opSup :: "('i, 'o) op set \<Rightarrow> ('i, 'o) op" where
  "opSup A = (if \<forall>op\<in>A. op = nil_op then nil_op  
   else Logic (\<lambda> ev.
         let ops_outs = (\<lambda> op. apply op ev) ` A in
         let out = lSup (llist_of ` snd ` ops_outs) in
         if lfinite out
         then let A' = (\<lambda> (op', out'). prepend_op out' op') ` ops_outs in (opSup A', [])
         else (const_op out, [])) (lSup (exit ` A)))"

lemma opSup_test_1[simp]:
  "opSup {} = nil_op"
  apply (coinduction rule: op.coinduct)
  apply (simp add: opSup.ctr rel_fun_def)
  apply (subst nil_op.ctr)
  apply simp
  done

lemma opSup_test_2[simp]:
  "opSup {nil_op} = nil_op"
  apply (coinduction rule: op.coinduct)
  apply (simp add: opSup.ctr rel_fun_def)
  apply (subst nil_op.ctr)
  apply simp
  done

lemma opSup_test_3:
  "opSup {nil_op, one_op} = one_op"
  apply (coinduction rule: op.coinduct_strong)
  apply (intro conjI)
   apply clarsimp
  subgoal
    apply (clarsimp simp add: rel_fun_def)
    apply auto
     apply (smt (verit, del_insts) fst_conv image_def mem_Collect_eq opSup.code)
    apply (smt (verit, del_insts) fst_conv image_def mem_Collect_eq opSup.code)
    done
  subgoal
    apply auto
    done
  done

lemma lSup_2_simp[simp]:
  "lSup {LCons x lxs, LNil} = LCons x lxs"
  by (simp add: insert_commute lSup_insert_LNil)

lemma opSup_singleton[simp]:
  "opSup {op} = op"
  apply (coinduction arbitrary: op rule: op.coinduct)
  subgoal for op
    apply (auto simp add: rel_fun_def )
    subgoal for ev
      apply (cases "apply op ev")
      apply (auto simp add: image_constant_conv image_iff)
      done
    done
  done


lemma opSup_test_4:
  "opSup {ones_op, lazy_ones_op} = ones_op"
  apply (coinduction rule: op.coinduct_strong)
  apply (intro conjI)
   apply clarsimp
  subgoal
    apply (clarsimp simp add: rel_fun_def)
    apply (intro conjI impI)
     apply (metis lazy_ones_op.simps(1) list.distinct(1) ones_op.simps(1) prod.inject)
    subgoal
      apply (rule disjI2)
      apply (subgoal_tac "fst ` {op_out. (op_out = (ones_op, [1]) \<or> op_out = (lazy_ones_op, [])) \<and> snd op_out = [1]} = {ones_op}")
       defer
      subgoal
        apply (auto simp add: image_iff)
        done
      apply (auto simp add: insert_commute image_iff)
      subgoal
        by (smt (verit, best) Collect_cong fst_conv image_empty image_insert list.distinct(1) opSup_singleton singleton_conv snd_conv)
      subgoal
        by (simp add: \<open>ones_op = nil_op \<longrightarrow> lazy_ones_op \<noteq> nil_op \<Longrightarrow> fst ` {op_out. (op_out = (ones_op, [1]) \<or> op_out = (lazy_ones_op, [])) \<and> snd op_out = [1]} = {ones_op}\<close>)
      done
    done
  subgoal
    apply auto
    apply (metis lazy_ones_op.simps(2) nil_op.simps(2))
    done
  done

lemma opSup_test_5:
  "opSup {prepend_op buf cp_op, lazy_cp_op buf} = prepend_op buf cp_op"
  apply (coinduction arbitrary: buf rule: op.coinduct_strong)
  apply (intro conjI)
   apply clarsimp
  subgoal for buf
    apply (clarsimp simp add: rel_fun_def)
    apply (intro conjI impI allI)
    subgoal 
      by (metis cp_op.sel(1) lazy_cp_op.simps(2) list.distinct(1) list_of_LNil list_of_llist_of nil_op.sel(1) nil_op.simps(2) prepend_op_Nil prod.sel(2))
    subgoal for ev
      apply (rule disjI2)
      apply (auto simp add: image_iff insert_commute lSup_insert_LNil)
      subgoal
        by (smt (verit, best) Collect_cong Collect_conv_if append.assoc append.right_neutral append.simps(2) fst_conv image_empty image_insert list.distinct(1) opSup_singleton same_append_eq snd_conv)
      subgoal
        by (smt (verit, best) Collect_cong Collect_conv_if append.assoc append.right_neutral append.simps(2) fst_conv image_empty image_insert list.distinct(1) opSup_singleton same_append_eq snd_conv)
      done
    subgoal for ev
      apply (auto simp add: image_iff insert_commute lSup_insert_LNil)
      done
    done
  subgoal
    apply auto
    by (metis lazy_cp_op.simps(2) nil_op.simps(2))
  done


lemma
  "opSup {one_op, lazy_ones_op} = lazy_ones_op"
  oops
lemma
  "opSup {one_op, ones_op} = ones_op"
  oops


lemma le_op_applyI:
  "le_op op1 buf1 op2 buf2 \<Longrightarrow>
   le_op (fst (apply op1 ev)) (buf1@snd (apply op1 ev)) (fst (apply op2 ev)) (buf2@snd (apply op2 ev))"
  apply (coinduction arbitrary: op1 op2 ev buf1 buf2)
  apply (erule le_op.cases)
  apply auto
  subgoal
    by (metis le_op.cases prod.exhaust_sel shift_shift)
  subgoal
    by (metis le_op.cases prod.collapse)
  subgoal for ev buf1' op1' buf2' op2' ev' op1'' op2'' out1 out2
    apply (rule exI[of _ "fst (apply op1' ev)"])
    apply (rule exI[of _ "fst (apply op2' ev)"])
    apply (rule exI[of _ "ev'"])
    apply auto
    done
  done

lemma chain_applyI:
  assumes chain: "Complete_Partial_Order.chain (\<lambda> op1 op2. le_op op1 buf1 op2 buf2) A"
    and "ops_outs = (\<lambda> op. apply op ev) ` A"
    and "out = list_of (lSup (llist_of ` snd ` ops_outs))"
    and "A' = fst ` {op_out \<in> ops_outs. snd op_out = out}"
    and "prefix buf1 buf2"
  shows "Complete_Partial_Order.chain (\<lambda> op1 op2. le_op op1 buf1 op2 buf2) A'"
  using assms(2-) apply (auto intro!: chainI dest: chainD[OF chain])
  apply hypsubst_thin
  sorry


lemma chain_apply_prefix:
  assumes chain: "Complete_Partial_Order.chain (\<lambda>op1 op2. le_op op1 buf1 op2 buf2) A"
    and "op \<in> A"
    and "apply op ev = (op', out)"
  shows "prefix out (list_of (lSup (llist_of ` snd ` (\<lambda>op. apply op ev) ` A)))"
  oops
    (*   using assms(2,3) apply -
  using  chainD[OF chain assms(2)]
 *)


lemma chain_exit_lprefix:
  "Complete_Partial_Order.chain (\<lambda>op1 op2. le_op op1 buf op2 buf) A \<Longrightarrow>
   op \<in> A \<Longrightarrow>
   lprefix (exit op) (lSup (exit ` A))"
  by (metis (no_types, lifting) chain_imageI image_eqI le_op.simps llist.lub_upper lprefix_lshift)

lemma
  "\<And> lxs. lprefix (buf1 @@- produce op1 lxs) (buf2 @@- produce op2 lxs) \<Longrightarrow>
   le_op op1 buf1 op2 buf2"
  oops

lemma chain_le_op_Sup_l:
  "Complete_Partial_Order.chain (\<lambda> op1 op2. le_op op1 buf1 op2 buf2) A \<Longrightarrow>
   op \<in> A \<Longrightarrow>
   prefix buf1 buf2 \<Longrightarrow>
   (\<lambda> op1 op2. le_op op1 buf1 op2 buf2) op (opSup A)"
  sorry
    (*   apply(coinduction arbitrary: op A buf1 buf2 rule: le_op.coinduct)
  subgoal  for op A buf
    apply auto
      prefer 3
  subgoal  for op'' ev op' out
    apply (rule exI)
    apply (intro conjI)
       apply (rule refl)
    prefer 3
    subgoal
      oops *)

lemma chain_le_op_Sup_r:
  "Complete_Partial_Order.chain (\<lambda> op1 op2. le_op op1 buf1 op2 buf2) A \<Longrightarrow>
   (\<And>y. y \<in> A \<Longrightarrow> (\<lambda> op1 op2. le_op op1 buf1 op2 buf2) y x) \<Longrightarrow>
   (\<lambda> op1 op2. le_op op1 buf1 op2 buf2) (opSup A) x"
  sorry


definition "mk_lt l a b \<equiv> l a b \<and> a\<noteq>b"

lemma preorder_mk_ltI:
  assumes 
    "\<And>x. le x x"
    "\<And>x y z. \<lbrakk>le x y; le y z\<rbrakk> \<Longrightarrow> le x z"
    "\<And>x y. \<lbrakk>le x y; le y x\<rbrakk> \<Longrightarrow> x = y"
  shows "class.preorder le (mk_lt le)"
  apply unfold_locales
    apply (auto intro: assms simp: mk_lt_def)
  done

lemma op_ccpo: "class.ccpo opSup le_op' (mk_lt le_op')"
  apply intro_locales
    apply (rule preorder_mk_ltI)
      apply unfold_locales
      apply (auto intro: le_op_trans le_op_antisym' chain_le_op_Sup_l chain_le_op_Sup_r le_op_refl)
  done

subsection \<open>recursion setup\<close>

abbreviation "mono_op \<equiv> monotone (fun_ord le_op') le_op'" 

lemma op_pfd: "partial_function_definitions le_op' opSup"
  unfolding partial_function_definitions_def
  apply (auto intro: le_op_trans le_op_antisym' chain_le_op_Sup_l chain_le_op_Sup_r le_op_refl)
  done

interpretation op:
  partial_function_definitions le_op' "opSup"
  using op_pfd by auto

declaration \<open>Partial_Function.init "op" \<^term>\<open>op.fixp_fun\<close>
    \<^term>\<open>op.mono_body\<close> @{thm op.fixp_rule_uc} @{thm op.fixp_induct_uc}
    (NONE)\<close>

lemma body_rec_mono[partial_function_mono]:
  "mono_op
   (\<lambda>rec_op. Logic (\<lambda>ev. let (op', out) = apply b ev; cycle = filter (\<lambda>x. \<not> a x) out; out' = filter a out; (op'', out'') = finite_produce (rec_op (a, op')) cycle in (rec_op (a, op''), out' @ out'')) LNil)"
  sorry

partial_function (op) rec_op where
  "rec_op b op = Logic (\<lambda> ev. let (op', out) = apply op ev in
     let cycle = filter (\<lambda> x. \<not> b x) out in
     let out' = filter b out in
     let (op'', out'') = finite_produce (rec_op b op') cycle in
     (rec_op b op'',  out' @ out'')) LNil"
declare rec_op.simps[code]

primcorec incr_Inl where
  "incr_Inl = Logic (\<lambda> ev. 
     case ev of 
       Inl (n::nat) \<Rightarrow> (if n \<ge> 1 then (incr_Inl, [Inr n]) else (incr_Inl, [Inl (n + 1)]))
     | Inr n \<Rightarrow> (incr_Inl, [Inr n])) LNil"

value "list_of (produce (rec_op (\<lambda> x. \<not> isl x) incr_Inl) (LCons (Inl 0) (LCons (Inl 0) LNil)))"

primcorec collatz_op where
  "collatz_op = Logic (\<lambda> ev. 
     case ev of 
       Inl (a, Suc 0, i) \<Rightarrow> (collatz_op, [Inr (a, i)])
     | Inl (a, n, i) \<Rightarrow> (if n mod 2 = 0 then (collatz_op, [Inl (a,n div 2, i+1)]) else (collatz_op, [Inl (a, 3 * n + 1, Suc i)]))
     | Inr p \<Rightarrow> (collatz_op, [Inr p])) LNil"

primcorec collatz_init_op  where
  "collatz_init_op = Logic (\<lambda>a. (collatz_init_op, [Inl (a, a, 0)])) LNil"


value "list_of (produce (compose_op collatz_init_op (rec_op (\<lambda> x. \<not> isl x) collatz_op)) (llist_of [1 ..< 20]))"

lemma body_rec'_mono[partial_function_mono]:
  "mono_op (\<lambda>rec_op'.
              Logic (\<lambda>ev. let (ev', buf') = bb ba ev; (op', out) = apply b ev'; buf'' = buf' @ filter (\<lambda>x. \<not> ab x) out in Let (filter ab out) (Pair (rec_op' (((ab, bb), buf''), op'))))
               (if ba = [] then LNil else produce (rec_op' (((ab, bb), []), b)) (llist_of ba)))"
  sorry

partial_function (op) rec_op' where
  "rec_op' b scheduler buf op = Logic (\<lambda> ev. 
     let (ev', buf') = scheduler buf ev in
     let (op', out) = apply op ev' in
     let buf'' = buf' @ filter (\<lambda> x. \<not> b x) out in
     let out' = filter b out in
     (rec_op' b scheduler buf'' op',  out')) (if buf = [] then LNil else produce (rec_op' b scheduler [] op) (llist_of buf))"
declare rec_op'.simps[code]

abbreviation "prioritize_events \<equiv> (\<lambda> buf ev. let buf' = ev # buf in (hd buf', tl buf'))"

term "rec_op' (\<lambda> x. \<not> isl x) (\<lambda> buf ev. let buf' = buf @ [ev] in (hd buf', tl buf'))"


value "list_of (produce (compose_op collatz_init_op (rec_op' (\<lambda> x. \<not> isl x) prioritize_events [] collatz_op)) (llist_of [1 ..< 15]))"


end













lemma  unproduce_op_correct_2[simp]:
  "monotone lprefix lprefix (produce op) \<Longrightarrow>
   unproduce_op (produce op) = op"
  find_theorems monotone name: "_induc"


  oops




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
