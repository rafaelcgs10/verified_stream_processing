theory Llists_Processors
  imports
    "Coinductive.Coinductive_List"
    "Linear_Temporal_Logic_on_Llists"
    "HOL-Library.BNF_Corec"
    "HOL-Library.Code_Lazy"
    "HOL-Library.Numeral_Type"
begin

code_lazy_type llist

codatatype ('i, 'o) op = Logic ("apply": "('i \<Rightarrow> ('i, 'o) op \<times> 'o list)") ("exit": "'o llist")

(* FIXME: uncurry this *)
partial_function (option) produce_inner where
  "produce_inner op_lxs = (case op_lxs of (op, lxs) \<Rightarrow>
    (case lxs of 
        LNil \<Rightarrow> Some (Inr op)
     | LCons h lxs' \<Rightarrow> (case apply op h of 
                         (lgc', []) \<Rightarrow> produce_inner (lgc', lxs')
                       | (lgc', x#xs) \<Rightarrow> Some (Inl (lgc', x, xs, lxs')))))"

declare produce_inner.simps[code]

lemma produce_inner_LNil_None[simp]:
  "produce_inner (op, LNil) = Some (Inr op)"
  apply (subst produce_inner.simps)
  apply simp
  done

lemma produce_inner_alt[consumes 1, case_names no_production produces terminates]:
  assumes "produce_inner op_lxs = Some y"
    and "\<And>op h lxs op' zs . apply op h = (op', []) \<Longrightarrow> Q (op', lxs) zs \<Longrightarrow> Q (op, LCons h lxs) zs"
    and "\<And>op h x xs lxs lxs' op' . produce_inner (op, LCons h lxs) = Some (Inl (op', x, xs, lxs')) \<Longrightarrow>
                                    apply op h = (op', x # xs) \<Longrightarrow> Q (op, LCons h lxs) (Inl (op', x, xs, lxs'))"
    and  "\<And>op. Q (op, LNil) (Inr op)"
  shows "Q op_lxs y"
  apply (rule produce_inner.raw_induct[OF _ assms(1)])
  apply (simp split: llist.splits prod.splits list.splits)[1]
  using assms(4) apply blast  
  using assms(2) apply blast
  apply (metis (mono_tags, lifting) assms(3) list.simps(5) llist.case(2) prod.simps(2) produce_inner.simps)
  done

corec produce where
  "produce op lxs = 
    (case produce_inner (op, lxs) of
       None \<Rightarrow> LNil
    | Some (Inr op') \<Rightarrow> exit op'
    | Some (Inl (op', x, xs, lxs')) \<Rightarrow> LCons x (xs @@- produce op' lxs'))"

lemma produce_LNil_exit[simp]:
  "produce op LNil = exit op"
  apply (subst produce.code)
  apply auto
  done

primcorec skip_first_production_op :: "(_, 'i) op \<Rightarrow> (_, 'i) op" where
  "skip_first_production_op op = Logic (\<lambda> ev.
                                     let (lgc', out::_ list) = apply op ev in
                                     case out of
                                      [] \<Rightarrow> (skip_first_production_op lgc', [])
                                     | _ \<Rightarrow> (lgc', tl out)) (ltl (exit op))"

primcorec skip_n_productions_op :: "(_, 'i) op \<Rightarrow> nat \<Rightarrow> (_, 'i) op" where
  "skip_n_productions_op op n = Logic (\<lambda> ev.
                                     let (lgc', out) = apply op ev in
                                       if length out < n 
                                       then (skip_n_productions_op lgc' (n - length out), [])
                                       else (lgc', drop n out)
                                     ) (ldrop n (exit op))"

lemma skip_n_productions_op_0[simp,intro]:
  "skip_n_productions_op op 0 = op"
  apply (subst skip_n_productions_op.ctr)
  using zero_enat_def apply auto
  done

lemma produce_inner_None_produce_LNil:
  "produce_inner (op, lxs) = None \<Longrightarrow>
   produce op lxs = LNil"
  apply (subst produce.code)
  apply auto
  done

lemma skip_first_production_op_eq_skip_n_productions_op_aux:
  "skip_first_production_op (skip_n_productions_op op n) = skip_n_productions_op op (Suc n)"
proof (coinduction arbitrary: op n)
  case (Eq_op op' n')
  then show ?case
  proof -
    have "\<exists>op n. skip_first_production_op (skip_n_productions_op (fst (apply op' x)) (n' - length (snd (apply op' x)))) = skip_first_production_op (skip_n_productions_op op n) \<and> skip_n_productions_op (fst (apply op' x)) (Suc (n' - length (snd (apply op' x)))) = skip_n_productions_op op (Suc n)"
      if "length (snd (apply op' x)) < n'"
      for x :: 'a
      using that by blast
    moreover have "\<exists>op n. skip_first_production_op (fst (apply op' x)) = skip_first_production_op (skip_n_productions_op op n) \<and> skip_n_productions_op (fst (apply op' x)) (Suc 0) = skip_n_productions_op op (Suc n)"
      if "n' = length (snd (apply op' x))"
      for x :: 'a
      using that by force
    moreover have "\<exists>op n. fst (apply op' x) = skip_first_production_op (skip_n_productions_op op n) \<and> fst (apply op' x) = skip_n_productions_op op (Suc n)"
      if "drop n' (snd (apply op' x)) = y # ys"
        and "n' < length (snd (apply op' x))"
      for x :: 'a
        and y :: 'b
        and ys :: "'b list"
      using that 
      apply -
      apply (rule exI[of _ "Logic (\<lambda> ev . let (lgc', out) = apply (fst (apply op' x)) ev in (lgc', replicate n' undefined @ y# out)) (replicate (Suc n') undefined @@- (exit (fst (apply op' x))))"])
      apply (rule exI[of _ "n'"])
      apply (safe intro!:op.expand)
         apply (simp_all add: tl_drop Let_def fun_eq_iff split: prod.splits)
       apply (metis ldrop_enat length_replicate ltl_ldrop ltl_simps(2) shift_eq_shift_ldropn_length)
      apply (metis ldrop_enat ldropn_Suc_LCons length_replicate shift_eq_shift_ldropn_length)
      done
    moreover have "ys = drop (Suc n') (snd (apply op' x))"
      if "drop n' (snd (apply op' x)) = y # ys"
        and "n' < length (snd (apply op' x))"
      for x :: 'a
        and y :: 'b
        and ys :: "'b list"
      using that 
      by (metis drop_Suc list.sel(3) tl_drop)
    moreover have "ltl (ldrop (enat n') (exit op')) = ldrop (enat (Suc n')) (exit op')"
      by (simp add: ldrop_eSuc_ltl ldrop_enat ltl_ldropn)
    ultimately show ?thesis
      by (simp add: Suc_diff_le fun_eq_iff rel_fun_def not_less Suc_le_eq split: list.splits ; intro conjI allI impI ; simp ?)
  qed
qed

lemma skip_first_production_op_eq_skip_n_productions_op:
  "(skip_first_production_op ^^ n) op = skip_n_productions_op op n"
  apply (induct n)
   apply (simp_all add: skip_first_production_op_eq_skip_n_productions_op_aux)
  done

lemma skip_n_productions_op_sum[simp]:
  "skip_n_productions_op (skip_n_productions_op op m) n = skip_n_productions_op op (n + m)"
  apply (simp flip: skip_first_production_op_eq_skip_n_productions_op)
  apply (simp add: funpow_add)
  done

lemma skip_first_production_op_eq_skip_n_productions_op_1:
  "skip_n_productions_op op 1 = skip_first_production_op op"
  using skip_first_production_op_eq_skip_n_productions_op[where n=1 and op=op] by simp

lemma produce_inner_skip_n_productions_op_Suc_LCons:
  assumes "produce_inner (skip_n_productions_op op n, input_stream) = Some (Inl (lgc', h, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "produce_inner (skip_n_productions_op op (Suc n), input_stream) = Some (Inl (lgc'', h', xs', lxs''))"
  shows "LCons h' (xs' @@- produce lgc'' lxs'') = xs @@- produce lgc' lxs'"
  using assms proof (induction "?P" "?R" arbitrary: input_stream n op rule: produce_inner_alt)
  case (no_production h lxs op')
  then show ?case 
    apply -
    apply (subst (asm) (2) produce_inner.simps)
    apply (simp split: option.splits prod.splits if_splits)
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (metis (mono_tags, lifting) Suc_diff_le less_or_eq_imp_le)
      apply (simp add: Suc_diff_le)
      done
    apply (metis skip_n_productions_op_0)
    done
next
  case (produces h lxs)
  then show ?case 
    apply -
    apply (subst (2) produce.corec.code)
    apply (subst (asm) (1 2) produce_inner.simps)
    apply (simp split: option.splits prod.splits if_splits list.splits)
     apply hypsubst_thin
     apply (metis drop_Suc drop_all dual_order.refl list.sel(3) lshift_simps(1) tl_drop)
    apply hypsubst_thin
    apply safe
    subgoal
      apply (subst produce.code)
      apply (simp split: option.splits prod.splits if_splits list.splits)
      apply (simp add: drop_Suc drop_tl)
      done
    subgoal
      apply (subst produce.code)
      apply (simp split: option.splits prod.splits if_splits list.splits)
      apply (simp add: drop_Suc drop_tl)
      done
    done
qed

lemma produce_inner_skip_n_productions_op_Some_None_Suc:
  assumes "produce_inner (skip_n_productions_op op n, lxs) = Some (Inr lgc')" (is "produce_inner ?P = Some ?R")
  shows "produce_inner (skip_n_productions_op op (Suc n), lxs) = Some (Inr (skip_first_production_op lgc'))"
  using assms apply (induction "?P" "?R"  arbitrary: n op lxs rule: produce_inner_alt)
  subgoal
    apply (subst produce_inner.simps)
    apply (simp split: prod.splits llist.splits if_splits list.splits)
    apply (metis (mono_tags, lifting) Suc_diff_le less_or_eq_imp_le)
    done
  apply (simp_all split: if_splits)
  apply hypsubst_thin
  apply (simp flip: skip_first_production_op_eq_skip_n_productions_op)
  done

lemma produce_inner_skip_n_productions_op_Some_Some_Some_None:
  assumes "produce_inner (skip_n_productions_op op n, lxs) = Some (Inl (lgc', h, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "produce_inner (skip_n_productions_op op (Suc n), lxs) = Some (Inr lgc'')"
  shows "produce lgc' lxs' = exit lgc'' \<and> xs = []"
  using assms proof (induction "?P" "?R"  arbitrary: n op lxs rule: produce_inner_alt)
  case (no_production h lxs op')
  then show ?case 
    by (smt (verit) Pair_inject Suc_diff_le cancel_comm_monoid_add_class.diff_cancel drop_eq_Nil2 le_imp_less_Suc less_Suc_eq less_le_not_le list.simps(4) llist.case(2) prod.simps(2) produce_inner.simps skip_n_productions_op.simps(1) skip_n_productions_op_0)
next
  case (produces h lxs)
  then show ?case 
    apply -
    apply (subst (asm) (1 2) produce_inner.simps)
    apply (simp split: prod.splits llist.splits if_splits list.splits)
    apply (subst produce.code)
    apply (simp split: option.splits prod.splits if_splits)
    apply (metis append_eq_conv_conj length_Suc_conv_rev list.inject)
    done
qed

lemma produce_inner_skip_n_productions_op_Suc_skip_n_productions_op_n:
  assumes  "produce_inner (skip_n_productions_op op (Suc n), lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "produce_inner (skip_n_productions_op op n, lxs) = None"
  shows "False"
  using assms proof (induct "?P" "?R" arbitrary: n op lxs rule: produce_inner_alt)
  case (no_production h lxs op')
  then show ?case 
    apply -
    apply (simp split: if_splits)
    subgoal
      apply (subst (asm) (2) produce_inner.simps)
      apply (simp split: if_splits)
      subgoal
        apply hypsubst_thin
        apply (subst (asm) Suc_diff_le)
         apply simp
        apply fastforce
        done
      subgoal
        apply hypsubst_thin
        apply (metis One_nat_def add_diff_cancel_right' less_SucE plus_1_eq_Suc skip_n_productions_op_0)
        done
      done
    subgoal
      apply (subst (asm) (2) produce_inner.simps)
      apply (simp split: if_splits list.splits)
      done
    done
next
  case (produces h lxs)
  then show ?case 
    apply -
    apply (subst (asm) (1 2) produce_inner.simps)
    apply (simp split: if_splits list.splits)
    done
qed

lemma produce_inner_skip_n_productions_op_Some_None_Suc_None:
  assumes "produce_inner (skip_n_productions_op op n, lxs) = Some (Inr lys)" (is "produce_inner ?P = Some ?R")
    and "produce_inner (skip_n_productions_op op (Suc n), lxs) = Some (Inl l)"
  shows " False"
  using assms apply (induction ?P ?R arbitrary: lxs n op rule: produce_inner_alt)
   apply (simp_all split: if_splits)
   apply (smt (verit) Suc_diff_le less_le_not_le list.simps(4) llist.case(2) not_less_eq prod.simps(2) produce_inner.simps skip_n_productions_op.simps(1))
  apply (metis (mono_tags, lifting) One_nat_def add_diff_cancel_right' less_le_not_le list.simps(4) llist.simps(5) not_less_eq plus_1_eq_Suc prod.simps(2) produce_inner.simps skip_n_productions_op.simps(1) skip_n_productions_op_0)
  done

lemma produce_inner_skip_n_productions_op_Suc_None_Inr_None:
  assumes  "produce_inner (skip_n_productions_op op (Suc n), lxs) = Some (Inl l)" (is "produce_inner ?P = Some ?R")
    and "produce_inner (skip_n_productions_op op n, lxs) = None"
  shows False
  using assms apply (induction ?P ?R arbitrary: lxs n op rule: produce_inner_alt)
    apply (simp_all split: if_splits; hypsubst_thin?)
     apply (smt (verit, del_insts) Suc_diff_Suc cancel_comm_monoid_add_class.diff_cancel diff_Suc_Suc drop_eq_Nil2 less_Suc_eq less_or_eq_imp_le list.simps(4) llist.case(2) prod.simps(2) produce_inner.simps skip_n_productions_op.simps(1) skip_n_productions_op_0)
  subgoal
    apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: list.splits)
    done
   apply (meson produce_inner_skip_n_productions_op_Suc_skip_n_productions_op_n)
  done

lemma produce_inner_skip_n_productions_op_None_Inr_None:
  "produce_inner (skip_n_productions_op op (Suc n), lxs) = Some r \<Longrightarrow>
   r = Inr lys \<Longrightarrow>
   produce_inner (skip_n_productions_op op n, lxs) = None \<Longrightarrow>
   False"
  apply (induction "(skip_n_productions_op op (Suc n), lxs)" r arbitrary: lxs n op rule: produce_inner_alt[consumes 1])
    apply (simp_all split: if_splits; hypsubst_thin?)
   apply (smt (verit, del_insts) Suc_diff_Suc cancel_comm_monoid_add_class.diff_cancel diff_Suc_Suc drop_eq_Nil2 less_Suc_eq less_or_eq_imp_le list.simps(4) llist.case(2) prod.simps(2) produce_inner.simps skip_n_productions_op.simps(1) skip_n_productions_op_0)
  apply (subst (asm) (2) produce_inner.simps)
  apply (auto split: list.splits)
  done

lemma produce_inner_Some_produce[simp]:
  "produce_inner (op, lxs) = Some (Inl (lgc', x, xs, lxs')) \<Longrightarrow>
   produce op lxs = LCons x (xs @@- produce lgc' lxs')"
  apply (subst produce.code)
  apply simp
  done

lemma produce_inner_Some_None_None_False:
  "produce_inner (skip_n_productions_op op n, lxs) = Some r \<Longrightarrow>
   r = Inr lys \<Longrightarrow>
   produce_inner (op, lxs) = None \<Longrightarrow>
   False"
  apply (induct "(skip_n_productions_op op n, lxs)" "r" arbitrary: n op lxs  rule: produce_inner_alt[consumes 1])
    apply (auto split: if_splits)
  subgoal
    apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: prod.splits list.splits)
    done
  subgoal
    apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: prod.splits list.splits)
    apply (metis skip_n_productions_op_0)
    done
  done

lemma produce_inner_None_Some_None_False:
  "produce_inner (op, lxs) = Some r \<Longrightarrow>
   r = Inr lys \<Longrightarrow>
   produce_inner (skip_n_productions_op op n, lxs) = None \<Longrightarrow>
   False"
  apply (induct "(op, lxs)" "r" arbitrary: n op lxs  rule: produce_inner_alt[consumes 1])
    apply (auto split: if_splits)
  subgoal
    apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: prod.splits list.splits if_splits)
    apply (metis skip_n_productions_op_0)
    done
  done

lemma produce_inner_skip_n_productions_op_Some_llength_le:
  "produce_inner (skip_n_productions_op op n, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc'', y, ys, lxs'') \<Longrightarrow>
   llength (produce op lxs) \<le> enat n \<Longrightarrow> False"
  apply (induct "(skip_n_productions_op op n, lxs)" r arbitrary: n y ys lxs'' op lxs lgc'' rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' n y ys lxs'' op lgc''
    apply (subst (asm) (2) produce.code)
    apply (auto split:option.splits if_splits)
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto split: prod.splits list.splits llist.splits if_splits)
      apply (metis i0_lb llength_LNil produce_inner_None_produce_LNil)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto split: prod.splits list.splits llist.splits if_splits)
      apply (metis llength_LNil produce_inner_None_produce_LNil skip_n_productions_op_0 zero_le)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto split: prod.splits list.splits llist.splits if_splits sum.splits)
        apply fastforce
       apply (metis enat_ord_simps(1) llength_llist_of option.case(2) produce.code sum.case(2))
      apply (smt (verit, del_insts) add_Suc_right add_Suc_shift add_diff_cancel_left' co.enat.sel(2) eSuc_le_iff enat_less_enat_plusI2 epred_enat leD leI less_imp_Suc_add llength_shift plus_1_eq_Suc)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto split: prod.splits list.splits llist.splits if_splits sum.splits)
      using zero_enat_def apply auto[1]
       apply hypsubst_thin
       apply (metis dual_order.eq_iff enat_0 llength_LNil llist_of.simps(1) old.sum.simps(6) option.simps(5) produce.code skip_n_productions_op_0)
      apply (metis add_diff_cancel_left' co.enat.sel(2) dual_order.eq_iff eSuc_le_iff epred_enat ldropn_eq_LNil length_Cons lessI llength_LNil plus_1_eq_Suc shift_eq_shift_ldropn_length skip_n_productions_op_0 zero_enat_def)
      done
    done
  subgoal
    apply (subst (asm) produce_inner.simps)
    apply (auto split: prod.splits list.splits llist.splits if_splits)
    apply (subst (asm) produce.code)
    apply (auto split: prod.splits list.splits llist.splits if_splits option.splits sum.splits)
      apply (subst (asm) produce_inner.simps)
      apply (auto split: prod.splits list.splits llist.splits if_splits)
     apply (subst (asm) produce_inner.simps)
     apply (auto split: prod.splits list.splits llist.splits if_splits)
     apply (metis drop_eq_Nil2 eSuc_enat eSuc_plus enat_less_enat_plusI leD le_eq_less_or_eq length_Cons list.simps(3) llength_shift not_less_iff_gr_or_eq)
    apply (subst (asm) produce_inner.simps)
    apply (auto split: prod.splits list.splits llist.splits if_splits)
    done
  subgoal
    apply (auto split: prod.splits list.splits llist.splits if_splits)
    done
  done

lemma produce_inner_skip_n_productions_op_Some_produce_inner_None:
  "produce_inner (skip_n_productions_op op n, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
   produce_inner (op, lxs) = None \<Longrightarrow> False"
  apply (induct "(skip_n_productions_op op n, lxs)" r arbitrary: n xs op lxs x  lxs' lgc' rule: produce_inner_alt[consumes 1])
  subgoal
    apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: if_splits prod.splits list.splits)
    apply (metis skip_n_productions_op_0)
    done
  subgoal for h x xs lxs' lgc' n op
    apply (subst (asm) produce_inner.simps)
    apply (auto split: if_splits prod.splits list.splits)
    apply (subst (asm) produce_inner.simps)
    apply (auto split: if_splits prod.splits list.splits)
    done
  apply auto
  done

lemma produce_inner_skip_n_productions_op_Some_produce_inner_Some_None:
  "produce_inner (skip_n_productions_op op n, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
   produce_inner (op, lxs) = Some (Inr lys) \<Longrightarrow> False"
  apply (induct "(skip_n_productions_op op n, lxs)" r arbitrary: n xs op lxs x  lxs' lgc' rule: produce_inner_alt[consumes 1])
  subgoal
    apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: if_splits prod.splits list.splits)
    apply (metis skip_n_productions_op_0)
    done
  subgoal for h x xs lxs' lgc' n op
    apply (subst (asm) produce_inner.simps)
    apply (auto split: if_splits prod.splits list.splits)
    apply (subst (asm) produce_inner.simps)
    apply (auto split: if_splits prod.splits list.splits)
    done
  apply auto
  done

lemma produce_inner_Some_produce_inner_skip_n_productions_op_Suc_n_None:
  "produce_inner (skip_n_productions_op op n, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
   produce_inner (skip_n_productions_op op (Suc n), lxs) = None \<Longrightarrow>
   llength (produce op lxs) = enat (Suc n)"
  apply (induct "(skip_n_productions_op op n, lxs)" r arbitrary: n op lxs lxs' x xs rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' n op lxs'' x xs
    apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: prod.splits if_splits list.splits)
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec)+ 
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (simp add: Suc_diff_le)
      apply (subst produce.code)
      apply (auto split: option.splits)  
       apply (subst (asm) (2) produce_inner.simps)
       apply (auto split: prod.splits if_splits list.splits sum.splits)
        apply (simp add: produce.code)  
       apply (subst (asm) (2) produce_inner.simps)
       apply (auto split: prod.splits if_splits list.splits sum.splits)
       apply (metis (no_types, lifting) Suc_diff_Suc Suc_lessD eSuc_enat_iff le_add_diff_inverse less_or_eq_imp_le llength_shift plus_enat_simps(1))
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto split: prod.splits if_splits list.splits sum.splits)
      using produce_inner_None_Some_None_False apply blast
      done
    subgoal
      apply hypsubst_thin
      apply (subst produce.code)
      apply (auto split: option.splits) 
       apply (subst (asm) (3) produce_inner.simps)
       apply (auto split: prod.splits if_splits list.splits sum.splits)
        apply (metis llength_LNil produce_inner_None_produce_LNil skip_n_productions_op_0)
      subgoal
        apply (subst (asm) (3) produce_inner.simps)
        apply (auto split: prod.splits if_splits list.splits sum.splits)
         apply (metis llength_LCons produce_inner_Some_produce skip_n_productions_op_0)
        apply (metis One_nat_def eSuc_enat llength_shift one_enat_def plus_1_eSuc(2) skip_n_productions_op_0)
        done
      subgoal
        apply (subst (asm) (3) produce_inner.simps)
        apply (auto split: prod.splits if_splits list.splits sum.splits)
        using produce_inner_None_Some_None_False apply blast
        done
      done
    done
   apply (auto split: if_splits)
  apply (subst produce.code)
  apply (auto split: prod.splits if_splits list.splits sum.splits llist.splits option.splits)
  subgoal
    apply (subst (asm) (1 2 3) produce_inner.simps)
    apply (auto split: prod.splits if_splits list.splits sum.splits llist.splits option.splits)
    done
  subgoal
    apply (subst (asm) (1 2 3) produce_inner.simps)
    apply (auto split: prod.splits if_splits list.splits sum.splits llist.splits option.splits)
    apply (simp add: eSuc_enat produce_inner_None_produce_LNil)
    done
  subgoal
    apply (subst (asm) (1 2 3) produce_inner.simps)
    apply (auto split: prod.splits if_splits list.splits sum.splits llist.splits option.splits)
    done
  done

lemma produce_inner_skip_n_productions_op_Some_None_aux:
  "produce_inner (skip_n_productions_op op n, lxs) = Some r \<Longrightarrow>
   produce_inner (op, lxs) = None \<Longrightarrow> False"
  by (metis obj_sumE prod_cases4 produce_inner_Some_None_None_False produce_inner_skip_n_productions_op_Some_produce_inner_None)

lemma produce_inner_skip_n_productions_op_Some_None:
  "produce_inner (op, lxs) = None \<Longrightarrow>
   produce_inner (skip_n_productions_op op n, lxs) = None"
  using produce_inner_skip_n_productions_op_Some_None_aux by fastforce

lemma produce_inner_skip_n_productions_op_Suc_Some_None_False:
  "produce_inner (skip_n_productions_op op (Suc n), lxs) = Some r \<Longrightarrow>
   produce_inner (skip_n_productions_op op n, lxs) = None \<Longrightarrow>
   False"
  apply (induct "(skip_n_productions_op op (Suc n), lxs)" r arbitrary: n op lxs rule: produce_inner_alt[consumes 1])
  subgoal
    apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: prod.splits if_splits list.splits)
     apply (metis Suc_diff_le less_or_eq_imp_le)
    apply (metis One_nat_def add_diff_cancel_right' less_SucE plus_1_eq_Suc skip_n_productions_op_0)
    done
   apply (auto split: if_splits)
  apply (subst (asm) (1 2) produce_inner.simps)
  apply (auto split: prod.splits if_splits list.splits)
  done

lemma produce_inner_skip_n_productions_op_None_Suc:
  "produce_inner (skip_n_productions_op op n, lxs) = None \<Longrightarrow>
   produce_inner (skip_n_productions_op op (Suc n), lxs) = None"
  using produce_inner_skip_n_productions_op_Suc_Some_None_False by fastforce

lemma produce_inner_skip_n_productions_op_None_gt: 
  "produce_inner (skip_n_productions_op op n, lxs) = None \<Longrightarrow>
   m > n \<Longrightarrow>
   produce_inner (skip_n_productions_op op m, lxs) = None"
  apply (induct m arbitrary: n op lxs)
   apply simp
  apply (metis less_Suc_eq produce_inner_skip_n_productions_op_None_Suc)
  done

lemma produce_inner_Some_produce_inner_skip_n_productions_op_le_False:
  "produce_inner (op, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
   produce_inner (skip_n_productions_op op n, lxs) = Some (Inl l) \<Longrightarrow>
   eSuc (llength (xs @@- produce lgc' lxs')) \<le> enat n \<Longrightarrow>
   False"
  apply (induct "(op, lxs)" r arbitrary: n op lxs lxs' x xs lgc'  rule: produce_inner_alt[consumes 1])
  subgoal
    apply (subst (asm) (2) produce.code)
    apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: prod.splits if_splits list.splits sum.splits option.splits)
        apply (metis llength_llist_of produce_inner_None_produce_LNil shift_LNil)
       apply (metis option.case(2) produce.code sum.case(2))
      apply (metis not_eSuc_ilei0 zero_enat_def)
     apply (metis not_eSuc_ilei0 zero_enat_def)
    apply (metis not_eSuc_ilei0 zero_enat_def)
    done
   apply simp_all
  apply (metis llength_LCons prod_cases4 produce_inner_Some_produce produce_inner_skip_n_productions_op_Some_llength_le)
  done

lemma produce_inner_skip_n_productions_op_None_le:
  "produce_inner (skip_n_productions_op op n, lxs) = None \<Longrightarrow> llength (produce op lxs) \<le> enat n"
  apply (induct n arbitrary: lxs op)
   apply (simp add: produce_inner_None_produce_LNil)
  subgoal for n lxs op
    apply (subst produce.code)
    apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
    subgoal for lgc' x xs lxs'
      apply (cases "produce_inner (skip_n_productions_op op n, lxs)")
      subgoal
        by (metis ldrop_eSuc_ltl ldropn_LNil ldropn_eq_LNil llength_LCons ltl_ldropn produce_inner_Some_produce)
      subgoal for r
        apply (cases r)
         apply (metis dual_order.eq_iff llength_LCons produce_inner_Some_produce produce_inner_Some_produce_inner_skip_n_productions_op_Suc_n_None surj_pair)
        subgoal for lys
          apply simp
          apply (simp add: produce_inner_skip_n_productions_op_Some_None_Suc)
          done
        done
      done
    subgoal for lys
      using produce_inner_None_Some_None_False by blast
    done
  done

lemma produce_inner_skip_n_productions_op_Some_Inr_le:
  "produce_inner (skip_n_productions_op op n, lxs) = Some r \<Longrightarrow> 
   r = Inr lys \<Longrightarrow>
   lnull (exit lys) \<Longrightarrow> llength (produce op lxs) \<le> enat n"
  apply (induct "(skip_n_productions_op op n, lxs)" r arbitrary: n op lxs  rule: produce_inner_alt[consumes 1])
  subgoal
    apply (subst produce.code)
    apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
       apply (metis llength_LCons produce_inner_Some_produce)
      apply (metis (no_types, lifting) LNil_eq_shift_iff drop_eq_Nil2 eSuc_enat eSuc_plus ldropn_eq_LNil ldropn_shift length_Cons less_or_eq_imp_le llength_shift)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      apply (metis enat_ord_simps(1) llength_llist_of option.case(2) produce.code sum.case(2))
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
       apply (metis produce_inner_skip_n_productions_op_Some_llength_le skip_n_productions_op_0)
      apply (metis eSuc_enat_iff ile0_eq llength_LNil llength_llist_of llength_shift nle_le shift_LNil skip_n_productions_op_0 zero_enat_def)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      apply (metis enat_0_iff(1) le_zero_eq length_0_conv llength_llist_of option.case(2) produce.code skip_n_productions_op_0 sum.case(2))
      done
    done
   apply blast
  apply force
  done

lemma produce_inner_skip_n_productions_op_Some_Inr_le_lnull:
  "produce_inner (skip_n_productions_op op n, lxs) = Some r \<Longrightarrow> 
   r = Inr lys \<Longrightarrow> llength (produce op lxs) \<le> enat n \<Longrightarrow>
   lnull (exit lys)"
  apply (induct "(skip_n_productions_op op n, lxs)" r arbitrary: n op lxs  rule: produce_inner_alt[consumes 1])
  subgoal
    apply (subst (asm) (2) produce.code)
    apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      subgoal
        apply (subst produce.code)
        apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
         apply (metis drop_eq_Nil2 ldropn_eq_LNil ldropn_shift length_Cons less_or_eq_imp_le llength_LCons lshift_simps(1) lshift_simps(2))
        apply (subst (asm) produce.code)
        apply simp
        apply (smt (verit, best) add_Suc_shift add_diff_cancel_left' co.enat.sel(2) diff_Suc_eq_diff_pred eSuc_le_iff enat_less_enat_plusI2 enat_ord_simps(1) epred_enat leD leI less_imp_Suc_add llength_llist_of llength_shift plus_1_eq_Suc)
        done
      subgoal
        apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
        done
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      apply (simp add: produce.code)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      apply (metis produce_inner_skip_n_productions_op_None_le skip_n_productions_op_0)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
       apply (metis not_eSuc_ilei0 zero_enat_def)
      apply (metis LNil_eq_shift_iff cancel_comm_monoid_add_class.diff_cancel co.enat.sel(2) diff_Suc_1 eSuc_le_iff epred_enat ldropn_eq_LNil ldropn_shift skip_n_productions_op_0)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      apply (metis enat_0 ile0_eq llength_eq_0 produce_inner_skip_n_productions_op_Some_Inr_le skip_n_productions_op_0)
      done
    done
   apply auto
  done

lemma produce_inner_skip_n_productions_op_Inl_lnth:
  "produce_inner (skip_n_productions_op op n, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', y, ys, lys) \<Longrightarrow>
   n < llength (produce op lxs) \<Longrightarrow>
   y = lnth (produce op lxs) n"
  apply (induct "(skip_n_productions_op op n, lxs)" r arbitrary: n op lxs  rule: produce_inner_alt[consumes 1])
  subgoal
    apply (subst (asm) (3) produce.code)
    apply (subst produce.code)
    apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      subgoal
        apply (subst produce.code)
        apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
          apply (metis Suc_lessD enat_ord_simps(1) leD llength_llist_of not_Some_eq produce_inner_None_produce_LNil shift_LNil)
         apply (metis (no_types, lifting) LNil_eq_shift_iff drop_eq_Nil2 eSuc_enat eSuc_plus iless_Suc_eq ldropn_eq_LNil ldropn_shift leI length_Cons less_le_not_le llength_LCons llength_shift)
        apply (smt (verit, ccfv_SIG) LNil_eq_shift_iff add_diff_cancel_left' diff_Suc_eq_diff_pred drop_eq_Nil2 eSuc_enat eSuc_le_iff enat_ord_simps(1) iless_Suc_eq ldropn_eq_LNil ldropn_shift leD leI less_imp_Suc_add less_or_eq_imp_le llength_llist_of option.case(2) plus_1_eq_Suc produce.code sum.case(2))
        done
      apply (metis diff_Suc_eq_diff_pred lappend_llist_of lnth_LCons' lnth_lappend_llist_of nat_diff_split not_less_zero zero_less_diff)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      apply (simp add: produce.code)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
       apply (metis co.enat.distinct(1) enat_0 llength_LCons lnth_0 not_gr_zero produce_inner_Some_produce skip_n_productions_op_0)
      apply (metis Suc_ile_eq add_diff_cancel_right' enat_llength_ldropn ldropn_Suc_conv_ldropn length_Cons lessI lnth_0 not_eSuc_ilei0 not_gr_zero one_eSuc one_enat_def plus_1_eq_Suc shift_eq_shift_ldropn_length skip_n_productions_op_0 zero_enat_def)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      apply (metis enat_ord_simps(2) length_greater_0_conv llength_llist_of lnth_llist_of option.case(2) produce.code skip_n_productions_op_0 sum.case(2))
      done
    done
   apply (auto split: if_splits)
  apply (subst (asm) produce.code)
  apply (subst produce.code)
  apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
   apply (subst (asm) produce_inner.simps)
   apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
   apply (subst (asm) produce_inner.simps)
   apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
   apply (metis drop_Cons' drop_all lappend_llist_of leI list.simps(3) lnth_LCons' lnth_lappend_llist_of nth_via_drop)
  apply (meson produce_inner_skip_n_productions_op_Some_produce_inner_Some_None)
  done

lemma produce_inner_skip_n_productions_Inr_op_ldropn:
  "produce_inner (skip_n_productions_op op n, lxs) = Some r \<Longrightarrow>
   r = Inr y \<Longrightarrow>
   exit y = ldropn n (produce op lxs)"
  apply (induct "(skip_n_productions_op op n, lxs)" r arbitrary: n op lxs  rule: produce_inner_alt[consumes 1])
  subgoal
    apply (subst produce.code)
    apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      apply (metis drop_eq_Nil2 ldropn_shift length_Cons less_or_eq_imp_le lshift_simps(1) lshift_simps(2))
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      apply (simp add: produce.code)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      apply (metis ldropn_0 produce_inner_None_produce_LNil skip_n_productions_op_0)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
       apply (metis ldropn_0 produce_inner_Some_produce skip_n_productions_op_0)
      apply (metis Ex_list_of_length ldropn_0 lessI shift_eq_shift_ldropn_length skip_n_productions_op_0)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits)
      apply (metis (no_types, lifting) ldropn_0 llist_of_inject option.case(2) produce.code skip_n_productions_op_0 sum.case(2))
      done
    done
   apply auto
  apply (simp add: ldrop_enat)
  done

lemma produce_inner_Some_None_llenght:
  "produce_inner (op, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
   n = length (x#xs) \<Longrightarrow>
   produce_inner (lgc', lxs') = None \<Longrightarrow> llength (produce op lxs) = enat n"
  apply (induct "(op, lxs)" r arbitrary: n op lxs  rule: produce_inner_alt[consumes 1])
  subgoal
    apply auto
    apply (subst produce.code)
    apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
     apply (subst (asm) (2) produce_inner.simps)
     apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
    apply (subst (asm) (2) produce_inner.simps)
    apply (auto simp add: produce.code produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
    done
   apply auto
  apply (subst produce.code)
  apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
  using eSuc_enat apply blast
  done

lemma produce_inner_skip_n_productions_op_llength_LNil:
  "produce_inner (skip_n_productions_op op n, lxs) = Some r \<Longrightarrow>
  r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
  \<not> llength (produce op lxs) \<le> enat n \<Longrightarrow>
  produce_inner (skip_n_productions_op op (Suc n), lxs) = None \<Longrightarrow> xs @@- produce lgc' lxs' = LNil" 
  apply (induct "(skip_n_productions_op op n, lxs)" r arbitrary: op lxs x xs lxs' n  rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs' lgc'a x xs lxs'a n lgc''
    apply (subst (asm) (2) produce_inner.simps)
    apply (subst (asm) (2) produce.code)
    apply (subst produce.code)
    apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
    subgoal
      apply (subst (asm) (2) produce.code)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
       apply (subst (asm) (4) produce_inner.simps)
       apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
       apply (metis (no_types, lifting) Suc_diff_Suc Suc_lessD add_diff_cancel_right' enat_llength_ldropn ileI1 ldropn_eq_LNil leI length_Cons lessI llength_LNil not_eSuc_ilei0 one_eSuc one_enat_def plus_1_eq_Suc shift_eq_shift_ldropn_length)
      apply (subst (asm) (4) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
      using produce_inner_None_Some_None_False apply blast
      done
    subgoal
      apply (subst (asm) (3) produce.code)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
       apply (subst (asm) (4) produce_inner.simps)
       apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
       apply (metis (no_types, lifting) Suc_diff_Suc Suc_lessD add_diff_cancel_right' enat_llength_ldropn ileI1 ldropn_eq_LNil leI length_Cons lessI llength_LNil not_eSuc_ilei0 one_eSuc one_enat_def plus_1_eq_Suc shift_eq_shift_ldropn_length)
      apply (subst (asm) (4) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
      using produce_inner_None_Some_None_False apply blast
      done
    subgoal
      apply (subst (asm) (2) produce.code)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
       apply (subst (asm) (4) produce_inner.simps)
       apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
       apply (metis (no_types, lifting) Suc_diff_Suc Suc_lessD add_diff_cancel_right' enat_llength_ldropn ileI1 ldropn_eq_LNil leI length_Cons lessI llength_LNil not_eSuc_ilei0 one_eSuc one_enat_def plus_1_eq_Suc shift_eq_shift_ldropn_length)
      apply (subst (asm) (4) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
      using produce_inner_None_Some_None_False apply blast
      done
    subgoal
      apply (subst (asm) (2) produce.code)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
       apply (subst (asm) (4) produce_inner.simps)
       apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
        apply (metis produce_inner_skip_n_productions_op_Some_llength_le skip_n_productions_op_0)
       apply (metis Suc_ile_eq ileI1 le_zero_eq linorder_le_less_linear llength_eq_0 llength_llist_of llist.collapse(1) order_less_irrefl shift_LNil skip_n_productions_op_0 zero_enat_def)
      apply (subst (asm) (4) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
      using produce_inner_None_Some_None_False apply blast
      done
    subgoal
      apply (subst (asm) (3) produce.code)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
      subgoal
        apply (subst (asm) (4) produce_inner.simps)
        apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
        apply (metis produce_inner_skip_n_productions_op_Some_llength_le skip_n_productions_op_0)
        apply (metis eSuc_enat enat_0 ile0_eq linorder_le_cases llength_LNil llength_llist_of llength_shift shift_LNil skip_n_productions_op_0)
        done
      subgoal
        apply (subst (asm) (4) produce_inner.simps)
        apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
        using produce_inner_None_Some_None_False apply blast
        done
      done
    subgoal
      apply (subst (asm) (2) produce.code)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
      apply (subst (asm) (4) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
      apply (metis produce_inner_skip_n_productions_op_Some_llength_le skip_n_productions_op_0)
      apply (metis Suc_ile_eq ileI1 le_zero_eq linorder_le_less_linear llength_eq_0 llength_llist_of llist.collapse(1) order_less_irrefl shift_LNil skip_n_productions_op_0 zero_enat_def)
      apply (subst (asm) (4) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
      apply (meson produce_inner_None_Some_None_False)
      done
    done
  apply (auto split: if_splits)
  apply (subst (asm) (1 2) produce_inner.simps)
  apply (subst produce.code)
  apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits if_splits list.splits sum.splits option.splits llist.splits)
  apply (metis One_nat_def add_left_cancel diff_add_inverse2 length_0_conv length_Cons length_drop llist_of_eq_LNil_conv plus_1_eq_Suc)
  done

lemma produce_skip_n_productions_op_correctness:
  "produce (skip_n_productions_op op n) lxs = ldropn n (produce op lxs)"
  apply (coinduction arbitrary: op lxs n rule: llist.coinduct_upto)
  apply (intro conjI impI)
  subgoal for op lxs n
    apply (subst (1 2) produce.code)
    apply (auto split: prod.splits list.splits option.splits sum.splits)
    apply (meson produce_inner_skip_n_productions_op_Some_produce_inner_None)
    using produce_inner_Some_None_None_False apply blast
    subgoal for lgc' x xs lxs' 
      using produce_inner_skip_n_productions_op_None_le 
      by (metis llength_LCons produce_inner_Some_produce)
    apply (metis llength_LCons produce_inner_Some_produce produce_inner_skip_n_productions_op_Some_llength_le)
    subgoal for lgc' x xs lxs' lys
      by (metis llength_LCons null_rec(2) produce_inner_Some_produce produce_inner_skip_n_productions_op_Some_Inr_le)
    subgoal
      by (simp add: eq_Nil_null produce_inner_skip_n_productions_op_Some_Inr_le_lnull)
    subgoal
      using produce_inner_None_Some_None_False by blast
    subgoal
      by (meson produce_inner_skip_n_productions_op_Some_produce_inner_Some_None)
    subgoal
      by (metis enat_ord_simps(1) ldropn_0 llength_llist_of null_rec(2) produce_inner_skip_n_productions_Inr_op_ldropn produce_inner_skip_n_productions_op_Some_Inr_le skip_n_productions_op_0)
    subgoal
      by (simp add: eq_Nil_null produce.code produce_inner_skip_n_productions_op_Some_Inr_le_lnull)
    done
  subgoal for op lxs n
    apply (subst (1 2) produce.code)
    apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits list.splits option.splits sum.splits)
    subgoal for lgc' x xs lxs' lgc'' y ys lysa
      by (metis leI lhd_ldropn llength_LCons produce_inner_Some_produce produce_inner_skip_n_productions_op_Inl_lnth)
    subgoal for lgc' x xs lxs' y
      apply (metis lhd_llist_of produce_inner_Some_produce produce_inner_skip_n_productions_Inr_op_ldropn)
      done
    apply (meson produce_inner_skip_n_productions_op_Some_produce_inner_Some_None)
    apply (metis ldropn_llist_of list_of_llist_of option.case(2) produce.code produce_inner_skip_n_productions_Inr_op_ldropn sum.case(2))
    done
  subgoal for op lxs n
    apply (rule lshift.cong_base)
    apply (rule exI[of _ op])
    apply (rule exI[of _ lxs])
    apply (rule exI[of _ "Suc n"])
    apply safe
    subgoal 
      apply (subst (1 2) produce.code)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits list.splits option.splits sum.splits)
      subgoal for lgc' x xs lxs'
        by (meson produce_inner_skip_n_productions_op_llength_LNil)
      subgoal
        by (metis produce_inner_skip_n_productions_op_Suc_LCons)
      subgoal
        by (metis produce_inner_skip_n_productions_op_Some_Some_Some_None lshift_simps(1))
      subgoal
        by (simp add: produce_inner_skip_n_productions_op_Some_None_Suc)
      subgoal
        using produce_inner_skip_n_productions_op_Some_None_Suc_None by blast
      subgoal
        using produce_inner_skip_n_productions_op_Some_None_Suc by fastforce
      done
    by (simp add: ldrop_eSuc_ltl ltl_ldropn)
  done

definition "finite_produce op xs = fold (\<lambda> ev (op, out) . let (lgc', out') = apply op ev in (lgc', out@out')) xs (op, [])"

lemma fold_apply_old[simp]:
  "fold (\<lambda> ev (op, out) . let (lgc', out') = apply op ev in (lgc', out@out')) xs (op, old) =
   (fst (fold (\<lambda> ev (op, out) . let (lgc', out') = apply op ev in (lgc', out@out')) xs (op, [])), 
    old @ snd (fold (\<lambda> ev (op, out) . let (lgc', out') = apply op ev in (lgc', out@out')) xs (op, [])))"
  apply (induct xs arbitrary: op old)
  apply simp
  subgoal for h xs op old
    apply simp
    apply (metis (no_types, lifting) append.assoc case_prod_conv prod.collapse)
    done
  done

lemma finite_produce_simps:
  "finite_produce op xs = (case xs of
                                 [] \<Rightarrow> (op, [])
                                | (x#xs) \<Rightarrow>
                                   (let (lgc', out) = apply op x in 
                                   (fst (finite_produce lgc' xs), out @ snd (finite_produce lgc' xs))))"
  unfolding finite_produce_def
  apply (induct xs arbitrary: op)
  apply simp
  subgoal for h xs op
    apply (auto split: list.splits prod.splits)
    apply hypsubst_thin
    apply (metis (mono_tags, lifting) append.assoc fold_apply_old)
    done
  done

lemma finite_produce_Nil[simp]:
  "finite_produce op [] = (op, [])"
  apply (subst finite_produce_simps)
  apply simp
  done

primcorec compose_op where
  "compose_op lgc1 lgc2 = Logic (\<lambda> ev.
       let (lgc1', out) = apply lgc1 ev in
       let (lgc2', out') = finite_produce lgc2 out in
       (compose_op lgc1' lgc2', out'))
   (produce lgc2 (exit lgc1))
  "

lemma produce_inner_compose_op_Some_produce_inner_None:
  "produce_inner (compose_op lgc1 lgc2, lxs) = Some r \<Longrightarrow>
   produce_inner (lgc1, lxs) = None \<Longrightarrow> False"
  apply (induct "(compose_op lgc1 lgc2, lxs)" r arbitrary: lgc1 lgc2 lxs rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' lgc1 lgc2
    apply simp
    apply (elim conjE)
    apply hypsubst_thin
    apply (drule meta_spec)+
    apply (drule meta_mp)
    apply (rule refl)
    apply (drule meta_mp)
    apply (subst (asm) produce_inner.simps)
    apply (simp split: prod.splits list.splits)
    apply simp
    done
  subgoal for h lgc1 lgc2
    apply simp
    apply (elim conjE)
    apply hypsubst_thin
    apply (subst (asm) produce_inner.simps)
    apply (simp add: finite_produce_def split: prod.splits list.splits)
    apply (subst (asm) produce_inner.simps)
    apply (simp add: finite_produce_def split: prod.splits list.splits)
    done
  apply auto
  done

lemma produce_inner_None_produce_inner_compose_op_None[simp]:
  "produce_inner (lgc1, lxs) = None \<Longrightarrow> produce_inner (compose_op lgc1 lgc2, lxs) = None"
  using produce_inner_compose_op_Some_produce_inner_None by fastforce


lemma produce_inner_compose_op_Some_production:
  "apply lgc1 h = (lgc1', x#xs) \<Longrightarrow>
   finite_produce lgc2 (x#xs) = (lgc2', y#ys) \<Longrightarrow>
   produce_inner (compose_op lgc1 lgc2, LCons h lxs) = Some (Inl (compose_op lgc1' lgc2', y, ys, lxs))"
  apply (subst produce_inner.simps)
  apply (auto split: option.splits list.splits)
  done

lemma produce_inner_compose_op_finite_produce_no_production[simp]:
  "produce_inner (lgc1, lxs) = Some r \<Longrightarrow> 
   r = Inl (lgc1', x, xs, lxs') \<Longrightarrow>
   finite_produce lgc2 (x#xs) = (lgc2', []) \<Longrightarrow>
   produce_inner (compose_op lgc1 lgc2, lxs) = produce_inner (compose_op lgc1' lgc2', lxs')"
  apply (induct "(lgc1, lxs)" r arbitrary: lgc1 lgc2 lxs rule: produce_inner_alt[consumes 1])
  subgoal
    apply (subst produce_inner.simps)
    apply (auto split: option.splits list.splits llist.splits prod.splits)
    done
  subgoal
    apply (subst produce_inner.simps)
    apply (auto split: option.splits list.splits llist.splits prod.splits)
    apply (subst (asm) produce_inner.simps)
    apply (auto split: option.splits list.splits llist.splits prod.splits)
    done
  apply auto
  done

lemma produce_inner_LCons_Some_cases:
  "produce_inner (lgc1, LCons h hs) = Some (Inl (op, x, xs, lxs')) \<Longrightarrow>
   (apply lgc1 h = (op, x#xs) \<and> lxs' = hs) \<or> produce_inner (fst (apply lgc1 h), hs) = Some (Inl (op, x, xs, lxs'))"
  apply (subst (asm) produce_inner.simps)
  apply (auto split: prod.splits list.splits)
  done

lemma produce_inner_Some_Inl_compose_op:
  "produce_inner (lgc1, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
   finite_produce lgc2 (x # xs) = (lgc'', y # ys) \<Longrightarrow> produce_inner (compose_op lgc1 lgc2, lxs) = Some (Inl (compose_op lgc' lgc'', y, ys, lxs'))"
  apply (induct "(lgc1, lxs)" r arbitrary: lgc1 lgc2 lxs rule: produce_inner_alt[consumes 1])
  subgoal
    apply (subst produce_inner.simps)
    apply auto
    done
  apply auto
  apply (subst produce_inner.simps)
  apply (subst (asm) produce_inner.simps)
  apply auto
  done

lemma produce_inner_Some_Inr_compose_op:
  "produce_inner (lgc1, lxs) = Some r \<Longrightarrow>
   r = Inr lgc' \<Longrightarrow> produce_inner (compose_op lgc1 lgc2, lxs) = Some (Inr (compose_op lgc' lgc2))"
  apply (induct "(lgc1, lxs)" r arbitrary: lgc1 lgc2 lxs rule: produce_inner_alt[consumes 1])
  apply (subst produce_inner.simps)
  apply auto
  done

lemma produce_inner_compose_op:
  "produce_inner (compose_op lgc1 lgc2, lxs) =
   (case (produce_inner (lgc1, lxs)) of
      None \<Rightarrow> None
    | Some (Inr lgc') \<Rightarrow> Some (Inr (compose_op lgc' lgc2))
    | Some (Inl (op, x, xs, lxs')) \<Rightarrow> (
      let (lgc', out) = finite_produce lgc2 (x#xs) in
      (case out of 
         [] \<Rightarrow> produce_inner (compose_op op lgc', lxs') 
       | y#ys \<Rightarrow> Some (Inl (compose_op op lgc', y, ys, lxs')))))"
  apply (cases "produce_inner (lgc1, lxs)")
  apply simp
  subgoal for p
    apply (cases p)
    apply simp
    apply hypsubst_thin
    apply (auto split: prod.splits list.splits)
    apply (simp add: produce_inner_Some_Inl_compose_op)
    subgoal for lgc'
      using produce_inner_Some_Inr_compose_op by blast
    done
  done

lemma finite_produce_LCons_Nil:
  "finite_produce op (x # xs) = (lgc', []) \<Longrightarrow>
   apply op x = (lgc'', []) \<Longrightarrow> finite_produce lgc'' xs = (lgc', [])"
  apply (subst (asm) finite_produce_simps)
  apply simp
  done

lemma produce_inner_prefix_no_production:
  "produce_inner (op, xs @@- lxs) = Some (Inl (lgc', y, ys, lxs')) \<Longrightarrow>
   finite_produce op xs = (lgc'', []) \<Longrightarrow>
   produce_inner (lgc'', lxs) = Some (Inl (lgc', y, ys, lxs'))"
  apply (induct xs arbitrary: op)
  apply simp
  apply simp
  apply (subst (asm) (3) produce_inner.simps)
  apply (auto split: option.splits llist.splits list.splits prod.splits)
  subgoal
    apply (drule meta_spec)+
    apply (drule meta_mp)
    apply assumption
    apply (drule meta_mp)
    using finite_produce_LCons_Nil apply fastforce
    apply simp
    done
  subgoal for a xs op
    apply hypsubst_thin
    apply (subst (asm) finite_produce_simps)
    apply simp
    done
  done

lemma apply_compose_op_Cons:
  "apply (compose_op lgc1 lgc2) h = (lgc', x # xs) \<Longrightarrow>
   \<exists> y ys lgc1' lgc2' .apply lgc1 h = (lgc1', y#ys) \<and> finite_produce lgc2 (y#ys) = (lgc2', x#xs) \<and> lgc' = compose_op lgc1' lgc2'"
  apply (cases "apply lgc1 h")
  subgoal for op out
    apply (cases out)
    apply simp
    subgoal for y ys
      apply (rule exI[of _ y])
      apply (rule exI[of _ ys])
      apply (rule exI[of _ op])
      apply (metis compose_op.sel(1) fst_eqD prod.exhaust_sel snd_eqD)
      done
    done
  done

lemma finite_produce_move_old_out:
  "finite_produce op xs = (lgc', ys) \<Longrightarrow> ys =  snd (finite_produce op xs)"
  apply (induct xs arbitrary: op ys lgc')
  apply simp
  apply (subst (asm) (3) finite_produce_simps)
  apply (subst finite_produce_simps)
  apply (simp split: prod.splits)
  done

lemma produce_inner_prefix_Some_production:
  "produce_inner (op, xs @@- lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', y, ys, lxs') \<Longrightarrow>
   finite_produce op xs = (lgc'', y'#ys') \<Longrightarrow>
   y = y' \<and> ys = take (length ys) ys'"
  apply (induct "(op, xs @@- lxs)" r arbitrary: op xs lxs lgc'  rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs lgc' zs xs lxsa lgc'a
    apply (cases xs)
    apply simp
    subgoal for x xs'
      apply simp
      apply (elim conjE)
      by (simp add: finite_produce_simps)
    done
  subgoal for op h x xs lxs lxs'a lgc' xsa lxsa lgc'a
    apply (cases xsa)
    apply simp
    subgoal for x' xs'
      apply simp
      apply (elim conjE)
      apply safe
      subgoal
        apply (subst (asm) (1) finite_produce_simps)
        apply simp
        done
      subgoal
        apply (subst (asm) (1) finite_produce_simps)
        apply auto
        done
      done
    done
  apply fastforce
  done


lemma produce_inner_compose_op_produce_inner_produce:
  "produce_inner (compose_op lgc1 lgc2, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
   produce_inner (lgc2, produce lgc1 lxs) = Some (Inl (lgc'', y, ys, lys')) \<Longrightarrow>
   x = y \<and> (ys = take (length ys) xs)"
  apply (induct "(compose_op lgc1 lgc2, lxs)" r arbitrary: lgc1 lgc2 lxs lgc' x xs lxs' lgc'' y ys lys' rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' lgc1 lgc2 lgc'a x xs lxs'' lgc'' y ys lys'
    apply (subst (asm) (2) produce.code)
    apply (subst (asm) (3) produce_inner.simps)
    apply (auto split: option.splits prod.splits list.splits sum.splits)
    apply (simp add: produce.code)
    apply (simp add: produce.code)
    apply (metis prod.collapse produce_inner_prefix_no_production lshift_simps(2))
    apply (metis produce_inner_prefix_no_production lshift_simps(2) surjective_pairing)
    done
  subgoal for h x xs lxs lxs' lgc' lgc1 lgc2 lgc'a xa xsa lxs'a lgc'' y ys lys'
    apply (frule apply_compose_op_Cons)
    apply (elim conjE exE)
    subgoal for y' ys' lgc1' lgc2'
      apply (subst (asm) (1) produce.code)
      apply (subst (asm) (1) produce_inner.simps)
      apply (simp split: option.splits prod.splits list.splits sum.splits)
      apply hypsubst_thin
      apply simp
      subgoal for x1a x1b x1c x2c
        apply (subst (asm) (1) produce_inner.simps)
        apply (simp split: option.splits prod.splits list.splits sum.splits)
        apply (elim conjE)
        apply hypsubst_thin
        apply (subst (asm) finite_produce_simps)
        apply (simp split: option.splits prod.splits list.splits sum.splits)
        apply (subst (asm) (1) produce_inner.simps)
        apply (simp split: option.splits prod.splits list.splits sum.splits)
        apply (metis prod.exhaust_sel produce_inner_prefix_Some_production)
        apply auto
        done
      subgoal for x2 x1
        apply hypsubst_thin
        apply (subst (asm) (1) produce_inner.simps)
        apply (simp split: option.splits prod.splits list.splits)
        done
      done
    done
  apply auto
  done

(* lemma finite_produce_extend_old:
  "finite_produce x xs = (lgc1', ys') \<Longrightarrow> finite_produce x xs (zs @ ys) = (lgc1', zs @ ys')"
  apply (induct xs arbitrary: x ys zs)
   apply simp
  apply (subst (asm) (3) finite_produce_simps)
  apply (subst finite_produce_simps)
  apply (auto split: prod.splits)
  done *)

lemma finite_produce_append:
  "finite_produce op (xs @ ys) = (fst (finite_produce (fst (finite_produce op xs)) ys), snd (finite_produce op xs) @ snd (finite_produce (fst (finite_produce op xs)) ys))"
  apply (induct xs arbitrary: ys op)
  apply simp
  apply (subst (1 2 4) finite_produce_simps)
  apply (auto split: prod.splits)
  apply (simp add: finite_produce_simps)
  done

lemma produce_inner_to_finite_produce:
  "produce_inner (op, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
   \<exists> zs. lxs = zs @@- lxs' \<and> finite_produce op zs = (lgc', x#xs)"
  apply (induct "(op, lxs)" r arbitrary: op lxs lgc' x xs lxs'  rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs' lgc' lgc'a x xs lxs''
    apply (auto split: option.splits prod.splits list.splits)
    subgoal for zs
      apply (rule exI[of _ "h#zs"])
      apply simp
      apply (subst finite_produce_simps)
      apply (auto split: prod.splits)
      done
    done
  subgoal for op h x xs lxs' lgc'
    apply (rule exI[of _ "[h]"])
    apply simp
    apply (subst finite_produce_simps)
    apply (auto split: prod.splits)
    apply (subst (asm) produce_inner.simps)
    apply (auto split: prod.splits)
    done
  apply auto
  done

lemma finite_produce_to_shift_produce:
  "finite_produce op xs = (lgc', zs) \<Longrightarrow>
   produce op (xs @@- lxs) = zs @@- produce lgc' lxs"
  apply (induct xs arbitrary: op lxs zs)
  apply simp
  subgoal for a xs op lxs zs
    apply simp
    apply (subst produce.code)
    apply (subst produce_inner.simps)
    apply (subst (asm) (2) finite_produce_simps)
    apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits list.splits option.splits)
    apply (metis prod.collapse produce_inner_None_produce_LNil)
    subgoal for lgc' x xs'
      apply (drule meta_spec[of _ lgc'])
      apply (drule meta_spec[of _ lxs])
      apply (drule meta_spec[of _ "drop (length (x # xs')) zs"])
      apply (drule meta_mp)
      apply simp
      apply auto
      apply (simp add: produce_inner_None_produce_LNil)
      done
    subgoal for x1 aa 
      apply (smt (verit, del_insts) option.case(2) produce.code surjective_pairing)
      done
    subgoal for lgc' x xs' lxs'
      apply (metis prod.exhaust_sel)
      done
    done
  done

lemma finite_produce_output_not_empty_cases:
  "finite_produce op xs = (lgc', zs) \<Longrightarrow>
   zs \<noteq> [] \<Longrightarrow>
   ys \<noteq> [] \<or> xs \<noteq> []"
  apply (cases ys)
  apply (subst (asm) finite_produce_simps)
  apply (auto split: prod.splits)
  done

lemma produce_inner_shift_none_finite_produce:
  "produce_inner (op, xs @@-lxs) = None \<Longrightarrow>
   snd (finite_produce op xs) = [] \<and> produce_inner (fst (finite_produce op xs), lxs) = None"
  apply (rule conjI)
  apply (metis LNil_eq_shift_iff finite_produce_to_shift_produce prod.collapse produce_inner_None_produce_LNil)
  apply (induct xs arbitrary: op lxs)
  apply simp
  apply simp
  apply (subst (asm) (3) produce_inner.simps)
  apply (subst finite_produce_simps)
  apply (simp split: prod.splits list.splits)
  done

lemma finite_produce_prefix_no_production_produce_inner:
  "finite_produce op ys = (lgc', []) \<Longrightarrow>
   produce_inner (op, ys @@- lys) = produce_inner (lgc', lys)"
  apply (induct ys arbitrary: op)
  apply simp
  apply simp
  apply (subst produce_inner.simps)
  apply (subst (asm) (2) finite_produce_simps)
  apply (auto split: prod.splits list.splits)
  apply (metis prod.collapse)
  done

lemma produce_inner_compose_op_apply_Nil:
  "produce_inner (compose_op lgc1 lgc2, lxs) = None \<Longrightarrow>
   produce lgc1 lxs = LCons y lys \<Longrightarrow>
   \<exists> lgc2' . apply lgc2 y = (lgc2', [])"
  apply (subst (asm) produce.code)
  apply (auto split: option.splits prod.splits list.splits)
  apply (subst (asm) produce_inner_compose_op)
  apply (simp split: prod.splits list.splits)
  apply (subst (asm) finite_produce_simps)
  apply (simp split: prod.splits sum.splits list.splits)
  done

lemma finite_produce_finite_produce_drop:
  "finite_produce op xs = (lgc', []) \<Longrightarrow>
   length xs < length zs \<Longrightarrow>
   xs @@- lxs = zs @@- lys \<Longrightarrow>
   finite_produce op zs = (lgc'', []) \<Longrightarrow>
   finite_produce lgc' (drop (length xs) zs) = (lgc'', [])"
  apply (induct xs arbitrary: zs op lgc' lxs lys lgc'')
  apply simp
  apply (subst (asm) (4) finite_produce_simps)
  apply (auto split: prod.splits)
  subgoal for a xs zs op lgc' lxs lys lgc'' 
    apply (cases zs)
    apply simp
    apply auto
    apply (smt (verit, ccfv_SIG) finite_produce_LCons_Nil finite_produce_move_old_out prod.collapse)
    done
  done

lemma produce_inner_compose_op_Inl_skip_n_productions_op:
  "produce_inner (compose_op (skip_n_productions_op lgc1 n) lgc2'', lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', y, ys, lys) \<Longrightarrow>
   produce_inner (compose_op lgc1 lgc2, lxs) = None \<Longrightarrow>
   n = length zs \<Longrightarrow>
   produce lgc1 lxs = zs @@- lzs \<Longrightarrow>
   finite_produce lgc2 zs = (lgc2'', []) \<Longrightarrow>
   False"
  apply (induct "(compose_op (skip_n_productions_op lgc1 n) lgc2'', lxs)" r arbitrary: n zs lgc1 lgc2 lgc2'' lxs ys y lzs lys  rule: produce_inner_alt[consumes 1])
  subgoal premises prems for h lxs lgc'a zs n lgc1 lgc2'' zsa lgc2 ys y lzs lys
    using prems apply -
    apply (subst (asm) (2) produce.code)
    apply (subst (asm) (2) produce_inner_compose_op)
    apply (subst (asm) (3 4 ) produce_inner.simps)
    apply (auto simp add: less_Suc_eq not_less_eq produce_inner_None_produce_LNil LNil_eq_shift_iff split: list.splits option.splits if_splits prod.splits sum.splits)
    subgoal
      by (metis finite_produce_Nil length_0_conv produce_inner_None_produce_inner_compose_op_None lshift_simps(1) skip_n_productions_op_0)
    subgoal
      by (metis produce_inner_Some_produce produce_inner_compose_op_finite_produce_no_production)
    subgoal for x xs lgc1' lgc2'
      apply hypsubst_thin
      apply (subst (asm) (1) length_drop[symmetric])
      apply (drule meta_spec[of _ "lgc1'"])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ lgc2''])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ lgc2'])
      apply (drule meta_spec[of _ "drop (Suc (length xs)) zsa"])
      apply (drule meta_spec[of _ lzs])
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
      apply assumption
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (metis length_Cons lshift_simps(2) shift_eq_shift_drop_length)
      apply (drule meta_mp)
      using finite_produce_finite_produce_drop apply fastforce
      apply simp
      done
    subgoal
      by (metis finite_produce_Nil list.size(3) produce_inner_compose_op_finite_produce_no_production lshift_simps(1) skip_n_productions_op_0)
    subgoal for x xs lgc1' lgc2'
      apply hypsubst_thin
      apply (cases zsa)
      apply auto[1]
      apply (metis finite_produce_Nil list.size(3) lshift_simps(1) skip_n_productions_op_0)
      subgoal for z zs'
        apply auto
        apply hypsubst_thin
        apply (drule meta_spec[of _ "lgc1'"])
        apply (drule meta_spec[of _ 0])
        apply (drule meta_spec[of _ "fst (finite_produce lgc2'' (drop (length zs') xs))"])
        apply (drule meta_spec)
        apply (drule meta_spec[of _ lgc2'])
        apply (drule meta_spec[of _ "[]"])
        apply (drule meta_spec)
        apply (drule meta_mp)
        apply simp
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        apply simp
        apply (drule meta_mp)
        apply simp
        apply (drule meta_mp)
        apply simp
        apply simp
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) (1 3) finite_produce_simps)
          apply (auto split: prod.splits)
          apply (metis Suc_lessD finite_produce_finite_produce_drop prod.collapse)
          done
        apply force
        done
      done
    subgoal
      by (smt (verit, ccfv_SIG) finite_produce_Nil finite_produce_finite_produce_drop fst_conv length_Cons lessI list.size(3) lshift_simps(1) lshift_simps(2) skip_n_productions_op_0)
    subgoal for x xs lgc1' lgc2'
      apply hypsubst_thin
      apply (cases zsa)
      apply auto[1]
      subgoal for z zs'
        apply auto
        apply hypsubst_thin
        apply (drule meta_spec[of _ "lgc1'"])
        apply (drule meta_spec[of _ 0])
        apply (drule meta_spec[of _ "fst (finite_produce lgc2'' (drop (length zs') xs))"])
        apply (drule meta_spec)
        apply (drule meta_spec[of _ lgc2'])
        apply (drule meta_spec[of _ "[]"])
        apply (drule meta_spec)
        apply (drule meta_mp)
        apply simp
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        apply simp
        apply (drule meta_mp)
        apply simp
        apply (drule meta_mp)
        apply simp
        apply simp
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) (1 2) finite_produce_simps)
          apply (auto split: prod.splits)
          apply (metis fst_conv shift_same_prefix)
          done
        subgoal
          by (smt (verit, ccfv_SIG) finite_produce_Nil finite_produce_finite_produce_drop fst_conv length_Cons lessI list.size(3) lshift_simps(1) lshift_simps(2) skip_n_productions_op_0)
        done
      done
    done
  subgoal for h x xs lxs lxs' lgc'a n lgc1 lgc2'' zs lgc2 ys y lzs lys
    apply (subst (asm) produce.code)
    apply (auto simp add: LNil_eq_shift_iff split: if_splits option.splits sum.splits)
    subgoal
      apply (subst (asm) (1 2) produce_inner.simps)
      apply (auto simp add: LNil_eq_shift_iff split: if_splits option.splits prod.splits list.splits)
      apply (subst (asm) (1) produce_inner.simps)
      apply (auto simp add: LNil_eq_shift_iff split: if_splits option.splits prod.splits list.splits)
      apply hypsubst_thin
      apply (smt (verit, ccfv_threshold) drop_eq_Nil2 finite_produce_finite_produce_drop finite_produce_output_not_empty_cases less_or_eq_imp_le linorder_neqE_nat list.discI prod.collapse lshift_simps(2))
      done
    subgoal
      apply (subst (asm) (1 2) produce_inner.simps)
      apply (auto simp add: LNil_eq_shift_iff split: if_splits option.splits prod.splits list.splits)
      apply (subst (asm) (1) produce_inner.simps)
      apply (auto simp add: LNil_eq_shift_iff split: if_splits option.splits prod.splits list.splits)
      done
    done
  apply auto
  done

lemma produce_inner_compose_op_Inr_skip_n_productions_op:
  "produce_inner (compose_op (skip_n_productions_op lgc1 n) lgc2'', lxs) = Some r \<Longrightarrow>
   r = Inr lys \<Longrightarrow>
   produce_inner (compose_op lgc1 lgc2, lxs) = None \<Longrightarrow>
   n = length zs \<Longrightarrow>
   produce lgc1 lxs = zs @@- lzs \<Longrightarrow>
   finite_produce lgc2 zs = (lgc2'', []) \<Longrightarrow>
   False"
  apply (induct "(compose_op (skip_n_productions_op lgc1 n) lgc2'', lxs)" r arbitrary: n zs lgc1 lgc2 lgc2'' lxs lzs lys  rule: produce_inner_alt[consumes 1])
  subgoal premises prems for h lxs lgc' zs n lgc1 lgc2'' zsa lgc2 lzs lys
    using prems apply -
    apply (subst (asm) (2) produce.code)
    apply (subst (asm) (2) produce_inner_compose_op)
    apply (subst (asm) (3 4) produce_inner.simps)
    apply (auto simp add: less_Suc_eq not_less_eq produce_inner_None_produce_LNil LNil_eq_shift_iff split: list.splits option.splits if_splits prod.splits sum.splits)
    subgoal
      by (metis LNil_eq_shift_iff prems(5) prems(7) produce_inner_None_produce_LNil produce_inner_None_produce_inner_compose_op_None skip_n_productions_op_0)
    subgoal
      by (metis produce_inner_Some_produce produce_inner_compose_op_finite_produce_no_production)
    subgoal for x21 x22 x1b x1c
      apply (cases zsa)
      apply auto[1]
      apply simp
      subgoal for zs'
        apply (subst (asm) (1) length_drop[symmetric])
        apply (drule meta_spec[of _ x1b])
        apply (drule meta_spec[of _ "length (drop (length x22) zs')"])
        apply (drule meta_spec[of _ lgc2''])
        apply (drule meta_spec[of _ lys])
        apply (drule meta_spec[of _ x1c])
        apply (drule meta_spec[of _ "drop (length x22) zs'"])
        apply (drule meta_spec[of _ lzs])
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        apply simp
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        using shift_eq_shift_drop_length apply blast
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) (1 2) finite_produce_simps)
          apply (auto split: list.splits prod.splits)
          apply (metis finite_produce_finite_produce_drop prod.collapse)
          done
        apply simp
        done
      done
    subgoal
      by (metis finite_produce_Nil list.size(3) produce_inner_compose_op_finite_produce_no_production lshift_simps(1) skip_n_productions_op_0)
    subgoal
      by (smt (verit) Suc_lessD Suc_less_eq finite_produce_Nil finite_produce_finite_produce_drop fst_conv length_Cons list.size(3) lshift_simps(1) lshift_simps(2) skip_n_productions_op_0)
    subgoal
      by (smt (verit, ccfv_SIG) finite_produce_Nil finite_produce_finite_produce_drop fst_conv length_Cons lessI list.size(3) lshift_simps(1) lshift_simps(2) skip_n_productions_op_0)
    subgoal
      by (smt (verit, del_insts) Suc_length_conv drop_eq_Nil2 finite_produce_Nil ldropn_shift lessI less_or_eq_imp_le list.size(3) lshift_simps(2) shift_eq_shift_ldropn_length shift_same_prefix skip_n_productions_op_0)
    done
  apply auto
  done

lemma op_eqI:
  "exit op1 = exit op2 \<Longrightarrow> (\<forall> ev. apply op1 ev = apply op2 ev) \<Longrightarrow> op1 = op2"
  by (metis (full_types) op.expand rel_funI rel_fun_eq)

lemma produce_inner_compose_op_None_produce_shift_finite_produce: 
  "produce_inner (compose_op lgc1 lgc2, lxs) = None \<Longrightarrow>
   produce lgc1 lxs = ys @@- lys \<Longrightarrow>
   snd (finite_produce lgc2 ys) = []"
  apply (induct ys arbitrary: lgc1 lgc2 lys lxs)
  apply auto[1]
  subgoal premises prems for a ys lgc1 lgc2 lys lxs
    using prems(2-) apply -
    apply simp
    apply (frule produce_inner_compose_op_apply_Nil)
    apply assumption
    apply (subst finite_produce_simps)
    apply (auto split: prod.splits list.splits)
    apply (rule prems(1)[of "skip_n_productions_op lgc1 1" _ lxs lys])
    subgoal for lgc2''
      apply (cases "produce_inner (compose_op (skip_n_productions_op lgc1 (Suc 0)) lgc2'', lxs)")
      apply simp
      subgoal for r
        apply (cases r)
        subgoal for p
          apply (cases p)
          using produce_inner_compose_op_Inl_skip_n_productions_op[where n=1 and zs="[a]", of lgc1 lgc2'' lxs _ _ _ _ _ lgc2, where lzs="ys @@- lys"] apply simp
          apply (drule meta_mp)
          apply (subst finite_produce_simps)
          apply auto
          done
        subgoal for t
          using produce_inner_compose_op_Inr_skip_n_productions_op[where n=1 and zs="[a]", of lgc1 lgc2'' lxs _ _ lgc2, where lzs="ys @@- lys"] apply simp
          apply (drule meta_mp)
          apply (subst finite_produce_simps)
          apply auto
          done
        done
      done
    subgoal
      apply (simp add: produce_skip_n_productions_op_correctness)
      done
    done 
  done

lemma produce_inner_produce_Some:
  "produce_inner (lgc2, produce lgc1 lxs) = Some (Inl (lgc2', x, xs, lxs')) \<Longrightarrow>
   produce_inner (compose_op lgc1 lgc2, lxs) = None \<Longrightarrow> False"
  by (metis neq_Nil_conv produce_inner_compose_op_None_produce_shift_finite_produce produce_inner_to_finite_produce snd_conv)

lemma apply_compose_op:
  "apply (compose_op lgc1 lgc2) h = (lgc', x#xs) \<Longrightarrow>
   \<exists> lgc1' y ys lgc2' .apply lgc1 h = (lgc1', y#ys) \<and> finite_produce lgc2 (y#ys) = (lgc2', x#xs) \<and> lgc' = compose_op lgc1' lgc2'"
  apply (cases "apply lgc1 h")
  subgoal for lgc1' out'
    apply (cases out')
    subgoal
      apply (auto split: prod.splits list.splits)
      done
    subgoal for o out''
      apply (auto split: prod.splits list.splits)
      apply hypsubst_thin
      apply (metis prod.collapse)
      done
    done
  done

lemma finite_produce_produce_inner_Some:
  "finite_produce op zs = (lgc', x#xs) \<Longrightarrow>
   zs \<noteq> [] \<Longrightarrow>
   \<exists>ac aaa aba ba. produce_inner (op, (zs @@- lxs)) = Some (Inl (ac, aaa, aba, ba))"
  apply (induct zs arbitrary: x xs op lgc' lxs )
  apply simp
  subgoal for a zs x xs op lgc' lxs'
    apply (subst (asm) (2) finite_produce_simps)
    apply (auto split: prod.splits)
    subgoal for lgc'' out
      apply (subst produce_inner.simps)
      apply (simp split: list.splits)
      apply (metis append_Nil finite_produce_Nil list.discI old.prod.exhaust snd_conv)
      done
    done
  done

lemma produce_inner_compose_op_Some_Inl:
  "produce_inner (compose_op lgc1 lgc2, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc1', x, xs, lxs') \<Longrightarrow>
   \<exists>a aa ab b. produce_inner (lgc2, produce lgc1 lxs) = Some (Inl (a, aa, ab, b))"
  apply (induct "(compose_op lgc1 lgc2, lxs)" r arbitrary: lgc1 lgc2 lxs x xs lxs' lgc1' rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' lgc1 lgc2 x xs lxs'' lgc1'
    apply (subst produce.code)
    apply (auto split: option.splits)
    subgoal
      apply (subst produce_inner.simps)
      apply (auto split: prod.splits list.splits)
      apply (metis not_Some_eq produce_inner_None_produce_inner_compose_op_None produce_inner_produce_Some)
      done
    subgoal for a 
      apply (subst produce_inner.simps)
      apply (auto split: prod.splits list.splits sum.splits llist.splits)
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto split: prod.splits list.splits)
      using produce_inner_LCons_Some_cases apply fastforce
      apply (metis finite_produce_LCons_Nil finite_produce_prefix_no_production_produce_inner prod.collapse)
      subgoal
        apply (drule meta_spec)+
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        apply (rule refl)
        apply (subst (asm)  produce_inner.simps)
        apply (auto split: prod.splits list.splits)
        apply (simp add: produce.code)
        done
      subgoal
        apply (drule meta_spec)+
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        apply (rule refl)
        apply (subst (asm)  produce_inner.simps)
        apply (auto split: prod.splits list.splits)  
        apply (subst (asm) produce.code)
        apply auto
        apply (subst (asm)  produce_inner.simps)
        apply (auto split: prod.splits list.splits)    
        done
      done
    done
  apply auto
  apply (subst (asm)  produce_inner.simps)
  apply (auto split: prod.splits list.splits)
  apply (subst produce.code)
  apply (auto split: option.splits sum.splits)
  apply (subst produce_inner.simps)
  apply (auto split: option.splits prod.splits list.splits)
  apply (subst (asm) produce_inner.simps)
  apply (subst produce_inner.simps)
  apply (auto split: option.splits prod.splits list.splits)
  apply (subst (asm) finite_produce_simps)
  apply (auto split: option.splits prod.splits list.splits)
  apply (metis eq_snd_iff finite_produce_Nil finite_produce_produce_inner_Some neq_Nil_conv)
  apply (subst (asm) produce_inner.simps)
  apply (subst produce_inner.simps)
  apply (auto split: option.splits prod.splits list.splits)
  done

lemma produce_inner_Some_Inr_lfinite:
  "produce_inner (op, lxs) = Some r \<Longrightarrow>
   r = Inr lgc' \<Longrightarrow>
   lfinite lxs"
  apply (induct "(op, lxs)" r arbitrary: op lxs rule: produce_inner_alt[consumes 1])
  apply auto
  done

lemma produce_inner_None_not_lfinite_aux:
  "lfinite lxs \<Longrightarrow>
   produce_inner (op, lxs) = None \<Longrightarrow>
   False"
  apply (induct lxs arbitrary: op rule: lfinite_induct)
  using llist.collapse(1) apply fastforce
  subgoal for lxs op
    apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: llist.splits prod.splits list.splits)
    done
  done

lemma produce_inner_None_not_lfinite:
  "produce_inner (op, lxs) = None \<Longrightarrow>
   \<not> lfinite lxs"
  using produce_inner_None_not_lfinite_aux by blast

lemma produce_inner_Some_Inr:
  "lfinite lxs \<Longrightarrow>
   produce_inner (op, lxs) = Some (Inr lgc') \<Longrightarrow>
   \<exists> lgc'' . finite_produce op (list_of lxs) = (lgc'', [])"
  apply (induct lxs arbitrary: op lgc' rule: lfinite_induct)
  apply (metis finite_produce_Nil list_of_LNil lnull_def)
  subgoal for xs op lgc'
    apply (cases xs)
    apply simp
    apply simp
    apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: option.splits sum.splits llist.splits prod.splits list.splits)
    apply (simp add: finite_produce_simps)
    done
  done

lemma produce_inner_produce_Inr_compose_op_None:
  "produce_inner (lgc2, produce lgc1 lxs) = Some r1 \<Longrightarrow>
   r1 = Inr lgc' \<Longrightarrow>
   produce_inner (lgc1, lxs) = Some (Inr lgc'') \<Longrightarrow>
   produce_inner (compose_op lgc1 lgc2, lxs) = None \<Longrightarrow>
   False"
  apply (induct "(lgc2, produce lgc1 lxs)" r1 arbitrary: lgc1 lgc2 lxs lgc' lgc'' rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs lgc' zs lgc1 lxsa lgc'a lgc''
    apply (drule meta_spec[of _ "skip_first_production_op lgc1"])
    apply (drule meta_spec[of _ lxsa])
    apply hypsubst_thin
    apply (drule meta_spec)
    apply (drule meta_spec[of _ "skip_first_production_op lgc''"])
    apply (drule meta_mp)
    apply (metis One_nat_def ldrop_eSuc_ltl ltl_ldropn ltl_simps(2) produce_skip_n_productions_op_correctness skip_first_production_op_eq_skip_n_productions_op_1 skip_n_productions_op_0)
    apply (drule meta_mp)
    apply (rule refl)
    apply (drule meta_mp)
    using produce_inner_None_not_lfinite produce_inner_Some_Inr_lfinite apply blast
    apply (drule meta_mp)
    using produce_inner_None_not_lfinite produce_inner_Some_Inr_lfinite apply blast
    apply simp
    done
  apply (auto split: option.splits llist.splits prod.splits list.splits sum.splits if_splits)
  apply (subst (asm) produce.code)
  apply (auto split: option.splits llist.splits prod.splits list.splits sum.splits if_splits)
  using produce_inner_None_not_lfinite produce_inner_Some_Inr_lfinite apply blast
  done

lemma produce_inner_produce_Inr_lfinite:
  "produce_inner (lgc2, produce lgc1 lxs) = Some r \<Longrightarrow>
   r = Inr lgc' \<Longrightarrow>
   \<forall> n . produce_inner (skip_n_productions_op lgc1 n, lxs) \<noteq> None \<Longrightarrow>
   lfinite lxs"
  apply (induct "(lgc2, produce lgc1 lxs)" r arbitrary: lgc1 lgc2 lxs lgc' rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs lgc' zs lgc1 lxsa lgc''
    apply (drule meta_spec[of _ "skip_n_productions_op lgc1 (Suc 0)"])
    apply (drule meta_spec[of _ "lxsa"])
    apply (drule meta_spec[of _ "lgc''"])
    apply (drule meta_mp)
    apply (metis One_nat_def ldrop_eSuc_ltl ldropn_0 ltl_simps(2) produce_skip_n_productions_op_correctness skip_first_production_op_eq_skip_n_productions_op_1)
    apply (drule meta_mp)
    apply simp
    apply (drule meta_mp)
    apply simp
    apply simp
    done
  apply (auto split: option.splits llist.splits prod.splits list.splits sum.splits if_splits)
  apply (subst (asm) produce.code)
  apply (auto split: option.splits llist.splits prod.splits list.splits sum.splits if_splits)
  apply (simp add: produce_inner_skip_n_productions_op_Some_None)
  using produce_inner_None_not_lfinite produce_inner_Some_Inr_lfinite apply blast
  done

lemma produce_inner_skip_n_productions_op_not_lfinite:
  "\<forall>n. \<exists>y. produce_inner (skip_n_productions_op op n, lxs) = Some (Inl y) \<Longrightarrow> \<not> lfinite (produce op lxs)"
  by (metis dual_order.refl lfinite_conv_llength_enat prod_cases4 produce_inner_skip_n_productions_op_Some_llength_le)

lemma not_lfinite_all_dropn:
  "\<not> lfinite (produce op lxs) \<Longrightarrow> \<forall>n. (produce (skip_n_productions_op op n) lxs \<noteq> LNil)"
  by (metis lfinite_code(1) lfinite_ldropn produce_skip_n_productions_op_correctness)

lemma produce_inner_Inr_finite_produce:
  "produce_inner (op, lxs) = Some r \<Longrightarrow>
   r = Inr op' \<Longrightarrow>
   lfinite lxs \<Longrightarrow>
   op' = fst (finite_produce op (list_of lxs))"
  apply (induct "(op, lxs)" r arbitrary: op lxs op' rule: produce_inner_alt[consumes 1])
  apply (auto simp add: finite_produce_simps split: option.splits sum.splits prod.splits list.splits)
  done

lemma produce_inner_compose_op_compose_op_EX:
  "produce_inner (compose_op (op1::('b, 'c) op) (op2::('c, 'a) op), lxs) = Some r \<Longrightarrow> 
   r = Inr op' \<Longrightarrow>
   \<exists> (op1'::('b, 'c) op) (op2'::('c, 'a) op) . op' = compose_op op1' op2'"
  apply (induct "(compose_op op1 op2, lxs)" r arbitrary: lxs op' op1 op2 rule: produce_inner_alt[consumes 1])
  apply auto
  done

lemma produce_inner_compose_op_Inr:
  "produce_inner (compose_op op1 op2, lxs) = Some r \<Longrightarrow> 
   r = Inr op' \<Longrightarrow>
   \<exists> ys . produce op1 lxs = ys \<and> produce op2 ys = exit op'"
  apply (induct "(compose_op op1 op2, lxs)" r arbitrary: lxs op' op1 op2 rule: produce_inner_alt[consumes 1])
  apply auto
  subgoal for h lxs op1 op2 op'
    apply (drule meta_spec)+
    apply (drule meta_mp)
    apply (rule refl)
    apply (drule meta_mp)
    apply (rule refl)
    apply (subst (2) produce.code)
    apply (auto split: option.splits sum.splits)
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto split: prod.splits list.splits)
      apply (simp add: produce_inner_None_produce_LNil)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto split: prod.splits list.splits)
      apply (metis finite_produce_to_shift_produce lshift_simps(1) lshift_simps(2) surjective_pairing)
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto split: prod.splits list.splits)
      apply (simp add: produce.code)
      done
    done
  done

lemma produce_inner_produce_Inr:
  "produce_inner (op2, produce op1 lxs) = Some r \<Longrightarrow> 
   r = Inr op' \<Longrightarrow>
   \<exists> ys . produce op1 lxs = llist_of ys \<and> fst (finite_produce op2 ys) = op'"
  by (metis llist_of_list_of produce_inner_Inr_finite_produce produce_inner_Some_Inr_lfinite)

lemma produce_inner_skip_n_productions_op_Some_Inr_more_skips:
  "produce_inner (skip_n_productions_op op1 n, lxs) = Some r \<Longrightarrow>
   r = Inr op' \<Longrightarrow>
  produce_inner (skip_n_productions_op op1 (n + m), lxs) = Some (Inr (skip_n_productions_op op' m))"
  apply (induct "(skip_n_productions_op op1 n, lxs)" r arbitrary: op1  n m op' lxs rule: produce_inner_alt[consumes 1])
  apply (auto split: option.splits sum.splits prod.splits list.splits if_splits)
  subgoal for h lxs op1 n m op'
    apply (subst produce_inner.simps)
    apply auto
    apply (metis Nat.add_diff_assoc2 less_or_eq_imp_le)
    done
  subgoal for h lxs op1 m op
    apply (subst produce_inner.simps)
    apply (auto split: prod.splits list.splits)
    subgoal
      apply (drule meta_spec[of _ "fst (apply op1 h)"])
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "m"])
      apply (drule meta_spec[of _ "op"])
      apply simp
      done
    subgoal
      apply (drule meta_spec[of _ "fst (apply op1 h)"])
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "m"])
      apply (drule meta_spec[of _ "op"])
      apply simp
      done
    done
  apply (simp add: add.commute)
  done


lemma produce_inner_produce_Inl_compose_op_Inr:
  "produce_inner (compose_op op1 op2, lxs) = Some r \<Longrightarrow>
   r = Inr op' \<Longrightarrow>
   produce_inner (op2, produce op1 lxs) = Some (Inl (op, x, xs, lxs')) \<Longrightarrow>
   exit op' \<noteq> LNil"
  apply (induct "(compose_op op1 op2, lxs)" r arbitrary: op1 op2 op x xs lxs' op' lxs rule: produce_inner_alt[consumes 1])
  apply (auto split: option.splits sum.splits prod.splits list.splits if_splits)
  subgoal for h lxs op1 op2 op x xs lxs'a op'
    apply (subst (asm) (2) produce.code)
    apply (auto split: option.splits sum.splits)
    subgoal for a aa ab b
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto split: prod.splits list.splits)
      apply (metis finite_produce_prefix_no_production_produce_inner lshift_simps(2) prod.collapse)
      done
    subgoal for a
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto simp add: produce.code split: prod.splits list.splits)
      done
    done
  done

lemma produce_inner_produce_Inr_compose_op_Inr:
  "produce_inner (compose_op op1 op2, lxs) = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   produce_inner (op2, produce op1 lxs) = Some (Inr op') \<Longrightarrow>
   exit op = exit op'"
  apply (induct "(compose_op op1 op2, lxs)" r arbitrary: op1 op2 op' op lxs rule: produce_inner_alt[consumes 1])
  apply (auto split: option.splits sum.splits prod.splits list.splits)
  subgoal for h lxsa op1 op2 op' op
    apply (subst (asm) (2) produce.code)
    apply (auto split: option.splits sum.splits)
    subgoal
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits list.splits)
      done
    subgoal for a aa ab b
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto split: option.splits sum.splits prod.splits list.splits)
      apply (metis finite_produce_prefix_no_production_produce_inner lshift_simps(2) prod.collapse)
      done
    subgoal for a
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto simp add: produce.code split: prod.splits list.splits)
      done
    done
  subgoal for op1 op2 op'
    apply (simp add: produce.code)
    done
  done

lemma fst_finite_produce_skip_n_productions_op:
  "fst (finite_produce (skip_n_productions_op op n) xs) =
   skip_n_productions_op (fst (finite_produce op xs)) (n - length (snd (finite_produce op xs)))"
  apply (induct xs arbitrary: op n)
  apply auto
  subgoal for a xs op n
    apply (subst (1 2 3) finite_produce_simps)
    apply (auto split: prod.splits)
    done
  done

lemma length_snd_finite_produce_skip_n_productions_op_le_n:
  "length (snd (finite_produce op xs)) < n \<Longrightarrow>
   snd (finite_produce (skip_n_productions_op op n) xs) = []"
  apply (induct xs arbitrary: op n)
  apply auto
  subgoal for a xs op n     
    apply (subst (asm) (3) finite_produce_simps)
    apply (subst finite_produce_simps)
    apply (auto split: prod.splits)
    done
  done

lemma snd_finite_produce_skip_n_productions_op:
  "n \<le> length (snd (finite_produce op xs)) \<Longrightarrow>
   snd (finite_produce (skip_n_productions_op op n) xs) = drop n (snd (finite_produce op xs))"
  apply (induct xs arbitrary: op n)
  apply auto
  subgoal for a xs op n
    apply (subst (asm) (4) finite_produce_simps)
    apply (subst (1 2) finite_produce_simps)
    apply (auto split: prod.splits)
    done
  done


lemma compose_op_skip_n_productions_op:
  "compose_op op1 (skip_n_productions_op op2 n) = skip_n_productions_op (compose_op op1 op2) n"
  apply (coinduction arbitrary: op1 op2 n)
  using Suc_diff_le apply (auto simp: snd_finite_produce_skip_n_productions_op fst_finite_produce_skip_n_productions_op length_snd_finite_produce_skip_n_productions_op_le_n fun_eq_iff rel_fun_def not_less Suc_le_eq split: list.splits)
  subgoal for op1 op2 n x
    apply (rule exI[of _ "fst (apply op1 x)"])
    apply (rule exI[of _ "fst (finite_produce op2 (snd (apply op1 x)))"])
    apply (rule exI[of _ 0])
    apply auto
    done
  apply (metis ldrop_enat produce_skip_n_productions_op_correctness)
  done

lemma produce_inner_finite_produce_hd:
  "produce_inner (op, llist_of xs) = Some (Inl (op', x, ys, lxs')) \<Longrightarrow>
   hd (snd (finite_produce op xs)) = x"
  apply (induct xs arbitrary: op x op' lxs' ys)
  apply auto
  subgoal for a xs op x op'
    apply (subst (asm) (2) produce_inner.simps)
    apply (subst finite_produce_simps)
    apply (auto split: prod.splits list.splits)
    done
  done

lemma produce_inner_compose_op_Inr_Inl_hd:
  "produce_inner (compose_op op1 op2, lxs) = Some r \<Longrightarrow>
   r = Inr op \<Longrightarrow>
   produce_inner (op2, produce op1 lxs) = Some (Inl (op', x, xs, lxs')) \<Longrightarrow> lhd (exit op) = x"
  apply (induct "(compose_op op1 op2, lxs)" r arbitrary: op1 op2 op' op lxs x xs lxs' rule: produce_inner_alt[consumes 1])
  apply (auto split: option.splits sum.splits prod.splits list.splits)
  subgoal for h lxs op1 op2 op' op x xs lxs''
    apply (subst (asm) (2) produce.code)
    apply (auto split: option.splits sum.splits)
    subgoal for a aa ab b
      apply (subst (asm) (2 3) produce_inner.simps)
      apply (auto split: option.splits sum.splits prod.splits list.splits)
      subgoal
        apply (drule meta_spec)+
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        apply (subst produce.code)
        apply simp
        apply (subst produce_inner.simps)
        apply simp_all
        done
      subgoal for a
        apply (drule meta_spec)+
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        apply (rule refl)
        apply (drule meta_mp)
        apply (subst produce.code)
        apply simp
        apply (subst produce_inner.simps)
        apply simp_all
        done
      subgoal for a
        apply (metis (no_types, lifting) finite_produce_LCons_Nil prod.collapse produce_inner_prefix_no_production)
        done
      subgoal
        apply (subst (asm) finite_produce_simps)
        apply simp
        done
      done
    subgoal for a 
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto split: option.splits sum.splits prod.splits list.splits)
      apply (simp add: produce.code)
      done
    done
  done

lemma produce_compose_op_correctness:
  "\<forall> n . produce_inner (skip_n_productions_op lgc1 n, lxs) \<noteq> None \<Longrightarrow>
   produce (compose_op lgc1 lgc2) lxs = produce lgc2 (produce lgc1 lxs)"
  apply (coinduction arbitrary: lgc1 lgc2 lxs rule: llist.coinduct_upto)
  apply (intro conjI impI)
  subgoal for lgc1 lgc2 lxs
    apply (subst (1 2) produce.code)
    apply (auto simp add: split: prod.splits list.splits option.splits sum.splits)
    subgoal 
      by (meson produce_inner_produce_Some)
    subgoal for lgc'
      using produce_inner_produce_Inr_lfinite 
      by (metis option.distinct(1) produce_inner_None_not_lfinite)
    subgoal
      by (meson produce_inner_compose_op_Some_Inl)
    subgoal
      using produce_inner_compose_op_Some_Inl by fastforce
    subgoal for lgc'
      apply (metis llist.disc(1) produce_inner_None_produce_LNil produce_inner_compose_op_Inr)
      done
    subgoal for op' op x xs lxs'
      using produce_inner_produce_Inl_compose_op_Inr 
      apply (metis lnull_def)
      done
    subgoal for op op'
      using produce_inner_produce_Inr_compose_op_Inr apply fastforce
      done
    subgoal for op op'
      using produce_inner_produce_Inr_compose_op_Inr apply fastforce
      done
    done
  subgoal for lgc1 lgc2 lxs
    apply (subst (1 2) produce.code)
    apply (auto simp add: produce_inner_None_produce_LNil  split: prod.splits list.splits option.splits sum.splits)
    subgoal
      by (meson produce_inner_compose_op_produce_inner_produce)
    subgoal
      using produce_inner_compose_op_Some_Inl by fastforce
    subgoal for op op' x xs lxs'
      using produce_inner_compose_op_Inr_Inl_hd apply fast
      done
    subgoal
      by (metis produce_inner_produce_Inr_compose_op_Inr)
    done
  subgoal for lgc1 lgc2 lxs
    apply (subst (4 5) produce.code)
    apply (auto simp add: produce_inner_None_produce_LNil  split: prod.splits list.splits option.splits sum.splits)
    subgoal
      apply (rule lshift.cong_base)
      apply (rule exI[of _ lgc1])
      apply (rule exI[of _ "skip_n_productions_op lgc2 1"])
      apply (rule exI[of _ lxs])
      apply auto
      subgoal
        apply (subst (2) produce.code)
        apply (auto simp add: compose_op_skip_n_productions_op split: option.splits sum.splits)
        apply (metis One_nat_def not_one_le_zero one_enat_def produce_inner_Some_produce_inner_skip_n_productions_op_Suc_n_None produce_inner_skip_n_productions_op_llength_LNil skip_n_productions_op_0 zero_enat_def)
        apply (metis produce_inner_skip_n_productions_op_Suc_LCons skip_n_productions_op_0)
        apply (metis lshift_simps(1) produce_inner_skip_n_productions_op_Some_Some_Some_None skip_n_productions_op_0)
        done
      subgoal
        apply (subst (2) produce.code)
        apply (auto simp add: compose_op_skip_n_productions_op split: option.splits sum.splits)
        apply (metis One_nat_def not_one_le_zero one_enat_def produce_inner_Some_produce_inner_skip_n_productions_op_Suc_n_None produce_inner_skip_n_productions_op_llength_LNil skip_n_productions_op_0 zero_enat_def)
        apply (metis produce_inner_skip_n_productions_op_Suc_LCons skip_n_productions_op_0)
        apply (metis lshift_simps(1) produce_inner_skip_n_productions_op_Some_Some_Some_None skip_n_productions_op_0)
        done
      done
    subgoal
      using produce_inner_compose_op_Some_Inl by fastforce
    subgoal
      apply (rule lshift.cong_base)
      apply (rule exI[of _ lgc1])
      apply (rule exI[of _ "skip_n_productions_op lgc2 1"])
      apply (rule exI[of _ lxs])
      apply auto
      subgoal
        apply (auto simp add: compose_op_skip_n_productions_op split: option.splits sum.splits)
        apply (metis produce_inner_skip_n_productions_Inr_op_ldropn produce_inner_skip_n_productions_op_Some_None_Suc produce_skip_n_productions_op_correctness skip_first_production_op.simps(2) skip_n_productions_op_0)
        done
      subgoal
        apply (subst (2) produce.code)
        apply (auto simp add: compose_op_skip_n_productions_op split: option.splits sum.splits)
        apply (metis One_nat_def not_one_le_zero one_enat_def produce_inner_Some_produce_inner_skip_n_productions_op_Suc_n_None produce_inner_skip_n_productions_op_llength_LNil skip_n_productions_op_0 zero_enat_def)
        apply (metis produce_inner_skip_n_productions_op_Suc_LCons skip_n_productions_op_0)
        apply (metis lshift_simps(1) produce_inner_skip_n_productions_op_Some_Some_Some_None skip_n_productions_op_0)
        done
      done
    subgoal
      apply (simp add: lshift.cong_refl produce_inner_produce_Inr_compose_op_Inr)
      done
    done
  done

lemma produce_skip_n_productions_op_compose_op[simp]:
  "\<forall> n . produce_inner (skip_n_productions_op lgc1 n, lxs) \<noteq> None \<Longrightarrow>
   produce (skip_n_productions_op (compose_op lgc1 lgc2) n) lxs = produce (compose_op lgc1 (skip_n_productions_op lgc2 n)) lxs"
  apply (subst produce_compose_op_correctness)
  apply assumption
  apply (simp add: produce_compose_op_correctness produce_skip_n_productions_op_correctness)
  done

lemma produce_inner_Some_lfinite_produce_lfinite:
  "produce_inner (op, lxs) = Some (Inl (lgc', x, xs, lxs')) \<Longrightarrow> lfinite (produce op lxs) \<Longrightarrow> lfinite lxs \<Longrightarrow> lfinite (produce lgc' lxs')"
  by simp

inductive prefix_production_LE where
  pf_LE_stop: "apply op h = (lgc', out) \<Longrightarrow> m \<le> length out \<Longrightarrow>
            prefix_production_LE op (LCons h lxs) m (Suc 0)"
| pf_LE_exit: "exit op = lxs \<Longrightarrow> m \<le> llength lxs \<Longrightarrow>
              prefix_production_LE op LNil m n"
| pf_LE_step: "apply op h = (lgc', out) \<Longrightarrow> prefix_production_LE lgc' lxs (m - length out) n \<Longrightarrow> m > length out \<Longrightarrow>
            prefix_production_LE op (LCons h lxs) m (Suc n)"

lemma ltake_enat_Suc[simp]:
  "ltake (enat (Suc n)) (LCons x lxs) = LCons x (ltake n lxs)"
  apply (cases n)
  apply simp
  apply (metis One_nat_def enat_0 ltake_eSuc_LCons one_eSuc one_enat_def)
  apply simp
  apply (metis eSuc_enat ltake_eSuc_LCons)
  done

lemma produce_inner_skip_n_productions_op_Some_prefix_production_EQ_ex:
  "produce_inner (skip_n_productions_op op m, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
   \<exists>n. prefix_production_LE op lxs (Suc m) (Suc n) \<and> lnth (produce op (ltake (Suc n) lxs)) m = x \<and> Suc n \<le> llength lxs"
  apply (induct "(skip_n_productions_op op m, lxs)" r arbitrary: op lxs lgc' lxs' m rule: produce_inner_alt[consumes 1])
  subgoal for h lxs lgc' zs op m lgc'a lxs'
    apply (auto split: if_splits)
    subgoal
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply simp
      apply (elim exE conjE)
      subgoal for n
        apply (rule exI[of _ "Suc n"])
        apply safe
        apply (metis (no_types, lifting) Suc_diff_le le_imp_less_Suc less_or_eq_imp_le pf_LE_step prod.collapse)
        apply (subst produce.code)
        apply (auto split: option.splits)
        apply (subst (asm) produce_inner.simps)
        apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits list.splits)
        apply (subst (asm) produce_inner.simps)
        apply (auto simp add:  Suc_ile_eq   enat_0_iff(1) ltake_eq_LNil_iff produce_inner_None_produce_LNil split: sum.splits prod.splits list.splits option.splits llist.splits)
        apply (simp add: produce.code)
        apply (metis diff_Suc_eq_diff_pred diff_is_0_eq lappend_llist_of leD less_or_eq_imp_le lnth_LCons' lnth_lappend_llist_of not_less_zero)
        done
      done
    subgoal 
      apply (drule meta_spec[of _ "fst (apply op h)"])
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
      apply (rule refl)
      apply safe
      subgoal for n'
        apply (rule exI[of _ "Suc n'"])
        apply safe
        apply (metis One_nat_def add_diff_cancel_right' lessI pf_LE_step plus_1_eq_Suc prod.collapse)
        apply (subst produce.code)
        apply (auto split: option.splits)
        apply (subst (asm) produce_inner.simps)
        apply (auto simp add: produce_inner_None_produce_LNil split: sum.splits prod.splits list.splits)
        apply (subst (asm) produce_inner.simps)
        apply (auto simp add: produce_inner_None_produce_LNil split: sum.splits prod.splits list.splits)
        apply (metis cancel_comm_monoid_add_class.diff_cancel lappend_llist_of less_not_refl lnth_lappend_llist_of)
        apply (subst (asm) produce_inner.simps)
        apply (auto simp add: produce_inner_None_produce_LNil split: sum.splits prod.splits list.splits)
        apply (simp add: produce.code)
        apply (metis eSuc_enat eSuc_ile_mono)
        done
      done
    done
  subgoal for h lxs' lgc' op m
    apply (rule exI[of _ 0])
    apply (auto split: if_splits)
    apply (drule linorder_class.leI)
    apply (auto simp add: Nat.le_eq_less_or_eq)
    apply (metis Suc_leI old.prod.exhaust pf_LE_stop snd_conv)
    apply (subst produce.code)
    apply (auto split: option.splits)
    apply (subst (asm) produce_inner.simps)
    apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits list.splits)
    apply (subst (asm) produce_inner.simps)
    apply (auto simp add: produce_inner_None_produce_LNil split: sum.splits prod.splits list.splits)
    apply (subst (asm) produce_inner.simps)
    apply (auto simp add: produce_inner_None_produce_LNil split: sum.splits prod.splits list.splits)
    apply (subst (asm) produce_inner.simps)
    apply (auto simp add: produce_inner_None_produce_LNil split: sum.splits prod.splits list.splits)
    apply (metis drop_eq_Nil2 linorder_le_less_linear list.distinct(1) lnth_shift lshift_simps(2) nth_via_drop)
    apply (subst (asm) produce_inner.simps)
    apply (auto simp add: produce_inner_None_produce_LNil split: sum.splits prod.splits list.splits)
    apply (subst (asm) produce_inner.simps)
    apply (auto simp add: produce_inner_None_produce_LNil split: sum.splits prod.splits list.splits)
    apply (subst (asm) produce_inner.simps)
    apply (auto simp add: produce_inner_None_produce_LNil split: sum.splits prod.splits list.splits)
    apply (metis eSuc_enat iless_eSuc0 linorder_not_less zero_enat_def zero_ne_eSuc)
    done
  apply simp
  done

lemma produce_inner_skip_n_productions_op_Suc_Nil_LNil:
  "produce_inner (skip_n_productions_op op n, input_stream) = Some r \<Longrightarrow>
   r = Inl (lgc', h, xs, lxs') \<Longrightarrow>
   produce_inner (skip_n_productions_op op (Suc n), input_stream) = None \<Longrightarrow>
   xs = [] \<and> produce lgc' lxs' = LNil"
  apply (induction "(skip_n_productions_op op n, input_stream)" r arbitrary: input_stream n op rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' n opc
    apply (subst (asm) (2) produce_inner.simps)
    apply (simp split: option.splits prod.splits if_splits)
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply (rule refl)
      apply (drule meta_mp)
      apply (simp add: Suc_diff_le)
      apply assumption
      done
    apply (metis skip_n_productions_op_0)
    done
  subgoal for ha n op
    apply (subst (asm) (1 2) produce_inner.simps)
    apply (simp split: option.splits prod.splits if_splits list.splits)
    apply safe
    apply (metis append_eq_conv_conj length_Suc_conv_rev list.inject)
    apply (subst produce.corec.code)
    apply (simp split: option.splits prod.splits if_splits list.splits)
    done
  apply auto
  done

lemma produce_skip_n_productions_op_LCons:
  "produce (skip_n_productions_op op n) lxs = LCons h lxs' \<Longrightarrow> produce (skip_n_productions_op op (Suc n)) lxs = lxs'"
  apply (subst (asm) produce.code)
  apply (subst produce.code)
  apply (simp split: option.splits prod.splits sum.splits)
  apply hypsubst_thin
  apply safe
  apply simp
  subgoal for lgc' xs lxs'
    apply (subst LNil_eq_shift_iff)
    apply (auto simp add: produce_inner_skip_n_productions_op_Suc_Nil_LNil)
    done
  apply simp
  subgoal for lgc' xs lxs' lgc'' h' xs' lxs''
    apply (auto simp add: produce_inner_skip_n_productions_op_Suc_LCons)
    done
  apply auto
  using produce_inner_skip_n_productions_op_Some_Some_Some_None apply fastforce
  using produce_inner_None_not_lfinite_aux produce_inner_Some_Inr_lfinite apply blast
  using produce_inner_skip_n_productions_op_Some_None_Suc_None apply blast
  apply (metis ldropn_Suc_conv_ldropn ldropn_eq_LConsD llist.inject produce_inner_skip_n_productions_Inr_op_ldropn)
  done

lemma produce_inner_skip_n_productions_op_Suc_Inr:
  "produce_inner (skip_n_productions_op op i, lxs) = Some r \<Longrightarrow>
   r = Inr op' \<Longrightarrow>
   produce_inner (skip_n_productions_op op (Suc i), lxs) = Some (Inr (skip_n_productions_op op' 1))"
  by (metis produce_inner_skip_n_productions_op_Some_None_Suc skip_first_production_op_eq_skip_n_productions_op_1)


lemma produce_skip_n_productions_op_LCons_prefix_production_EQ_Ex:
  "produce (skip_n_productions_op op m) lxs = LCons x lxs' \<Longrightarrow>
   \<exists> n. prefix_production_LE op lxs (Suc m) (Suc n) \<and> lnth (produce op (ltake (Suc n) lxs)) m = x \<and> Suc n \<le> llength lxs \<or>
   n \<ge> llength lxs"
  apply (subst (asm) produce.code)
  apply (simp split: option.splits sum.splits prod.splits)
  using produce_inner_skip_n_productions_op_Some_prefix_production_EQ_ex 
  apply fastforce
  apply (metis eSuc_enat ile_eSuc lfinite_conv_llength_enat produce_inner_Some_Inr_lfinite)
  done

lemma lnth_produce_prefix_production_EQ_Ex:
  "lnth (produce op lxs) m = x \<Longrightarrow>
   m < llength (produce op lxs) \<Longrightarrow>
   \<exists> n . prefix_production_LE op lxs (Suc m) (Suc n) \<and> lnth (produce op (ltake (Suc n) lxs)) m = x \<and> Suc n \<le> llength lxs \<or>
   n \<ge> llength lxs"
  apply (metis ldropn_Suc_conv_ldropn produce_skip_n_productions_op_LCons_prefix_production_EQ_Ex produce_skip_n_productions_op_correctness)
  done 

lemma produce_coinduction:
  assumes rel: "P op ilxs olxs"
    and nonterm: "\<And>op ilxs olxs. P op ilxs olxs \<Longrightarrow> produce_inner (op, ilxs) = None \<Longrightarrow> olxs = LNil"
    and exit: "\<And>op olxs. P op LNil olxs \<Longrightarrow> olxs = exit op"
    and step: "\<And>op h ilxs olxs op' out.
    P op (LCons h ilxs) olxs \<Longrightarrow> apply op h = (op', out) \<Longrightarrow> \<exists>olxs'. olxs = out @@- olxs' \<and> P op' ilxs olxs'"
  shows "produce op ilxs = olxs"
proof -
  have coind: "\<And>op ilxs olxs. P op ilxs olxs \<Longrightarrow>
    (case produce_inner (op, ilxs) of None \<Rightarrow> olxs = LNil
       | Some (Inl (op', x, xs, ilxs')) \<Rightarrow> \<exists>olxs'. olxs = LCons x (xs @@- olxs') \<and> P op' ilxs' olxs'
       | Some (Inr op') \<Rightarrow> olxs = exit op')"
    apply (auto split: option.splits sum.splits)
    subgoal
      by (rule nonterm)
    subgoal for op ilxs olxs op' x xs ilxs'
      apply (drule produce_inner_alt[where Q="\<lambda>(op, ilxs) zs. 
      case zs of Inl (op', x, xs, ilxs') \<Rightarrow> \<forall>olxs. P op ilxs olxs \<longrightarrow> (\<exists>olxs'. olxs = LCons x (xs @@- olxs') \<and> P op' ilxs' olxs') | Inr op' \<Rightarrow> True"])
      apply (auto dest!: step split: option.splits sum.splits)
      apply (subst (asm) produce_inner.simps)
      apply (auto dest!: step split: option.splits sum.splits)
      done
    subgoal for op ilxs olxs op'
      apply (drule produce_inner_alt[where Q="\<lambda>(op, ilxs) zs. 
      case zs of Inl (op', x, xs, ilxs') \<Rightarrow> True | Inr op' \<Rightarrow> \<forall>olxs. P op ilxs olxs \<longrightarrow> (\<exists>ilxs'. P op' LNil olxs)"])
      apply (auto dest!: step dest: exit split: option.splits sum.splits)
      done
    done
  from rel show ?thesis
    apply (coinduction arbitrary: op ilxs olxs rule: llist.coinduct_upto)
    apply (intro conjI impI)
    apply (drule coind)
    apply (subst produce.code)
    apply (auto split: option.splits sum.splits) []
    apply (drule coind)
    apply (subst produce.code)
    apply (auto split: option.splits sum.splits) []
    apply (frule coind)
    apply (subst (2) produce.code)
    apply (auto simp: produce_inner_None_produce_LNil
        intro!: llist.cong_lshift intro: llist.cong_refl split: option.splits sum.splits) []
    apply (rule  llist.cong_base exI conjI refl)+
    subgoal for op ilxs olxs op' x xs ilxs'
      apply (drule produce_inner_alt[where op_lxs = "(op, ilxs)" and Q = "\<lambda>(op, ilxs) zs. 
      case zs of Inl (op', x, xs, ilxs') \<Rightarrow> \<forall>olxs. P op ilxs olxs \<longrightarrow> (\<exists>olxs'. olxs = LCons x (xs @@- olxs') \<and> P op' ilxs' olxs') | Inr op' \<Rightarrow> True"])
      apply (auto dest!: step split: sum.splits)
      apply (subst (asm) produce_inner.simps)
      apply (auto dest!: step split: option.splits sum.splits)
      done
    done
qed

lemma produce_LCons[simp]:
  "produce op (LCons h lxs) = (let (op', out) = apply op h in out @@- produce op' lxs)"
  apply (subst produce.code)
  apply (auto split: option.splits sum.splits prod.splits)
  apply (subst (asm) produce_inner.simps)
  apply (auto split: list.splits)
  apply (simp add: produce_inner_None_produce_LNil)
  apply (subst (asm) produce_inner.simps)
  apply (auto split: list.splits)
  apply (subst (asm) produce_inner.simps)
  apply (auto split: list.splits)
  apply (drule produce_inner_alt[where Q="\<lambda>(op, lxs) z. case z of Inl _ \<Rightarrow> True | Inr op' \<Rightarrow> exit op' = produce op lxs"])
  apply (auto split: sum.splits)
  apply (subst (2) produce.code)
  apply (subst produce_inner.simps)
  apply (auto split: option.splits sum.splits)
  using produce_inner_None_produce_LNil apply blast
  by (simp add: produce.code)

lemma produce_lshift[simp]: 
  "produce op (xs @@- lxs) = (let (op', out) = finite_produce op xs in out @@- produce op' lxs)"
  apply (induct xs arbitrary: op)
  apply (auto simp: split: prod.splits list.splits)
  by (metis (mono_tags, lifting) finite_produce_to_shift_produce lshift_simps(2) old.prod.case produce_LCons)

lemma produce_compose_op_correctness':
  assumes "\<forall> n . produce_inner (skip_n_productions_op op1 n, lxs) \<noteq> None"
  shows "produce (compose_op op1 op2) lxs = produce op2 (produce op1 lxs)"
  using assms
  apply (coinduction arbitrary: op1 op2 lxs rule: produce_coinduction)
  subgoal for op1 op2 lxs
    apply (subst (1 2) produce.code)
    apply (auto split: option.splits sum.splits)
    apply (simp_all add: produce_inner_skip_n_productions_op_Some_None
        produce_inner_Some_Inr_compose_op)
    apply (metis produce_inner_Some_produce produce_inner_produce_Some)
    apply (metis option.simps(3) produce_inner_None_not_lfinite_aux
        produce_inner_Some_produce produce_inner_produce_Inr_lfinite)
    done
  subgoal for op1 op2 lxs
    by auto
  subgoal for h ilxs op' out op1 op2 lxs
    apply clarsimp
    apply (rule exI[of _ "produce (fst (finite_produce op2 (snd (apply op1 h)))) (produce (fst (apply op1 h)) ilxs)"] conjI)+
    apply (auto split: prod.splits)
    apply (rule exI conjI refl)+
    apply safe
    subgoal for n
      apply (drule spec[of _ "n + length (snd (apply op1 h))"])
      apply auto
      apply (subst (asm) produce_inner.simps)
      apply (auto split: if_splits list.splits)
      done
    done
  done

lemma produce_compose_op_correctness_alt:
  assumes "\<forall> xs op' old out. finite_produce op2 xs = (op', out) \<longrightarrow> exit op' = LNil" 
  shows "produce (compose_op op1 op2) lxs = produce op2 (produce op1 lxs)"
  using assms
  apply (coinduction arbitrary: op1 op2 lxs rule: produce_coinduction)
  subgoal for op1 op2 lxs
    apply (subst (1 2) produce.code)
    apply (auto split: option.splits sum.splits)
    apply (simp_all add: produce_inner_skip_n_productions_op_Some_None
        produce_inner_Some_Inr_compose_op)
    using finite_produce_Nil apply blast
    apply (metis produce_inner_Some_produce produce_inner_produce_Some)
    using produce_inner_Inr_finite_produce produce_inner_Some_Inr_lfinite surjective_pairing apply blast
    done
  apply fastforce
  subgoal for h ilxs op' out op1 op2 lxs
    apply clarsimp
    apply (rule exI[of _ "produce (fst (finite_produce op2 (snd (apply op1 h)))) (produce (fst (apply op1 h)) ilxs)"] conjI)+
    apply (auto split: prod.splits)
    apply (rule exI conjI refl)+
    apply safe
    apply hypsubst_thin
    apply (metis finite_produce_append fst_eqD surjective_pairing)
    done
  done

lemma fst_finite_produce_compose_op:
  "fst (finite_produce (compose_op op1 op2) xs) =
  compose_op (fst (finite_produce op1 xs)) (fst (finite_produce op2 (snd (finite_produce op1 xs))))"
  apply (induct xs arbitrary: op1 op2 )
  apply simp
  subgoal for x xs op1 op2
    apply (subst (1 2 3) finite_produce_simps)
    apply (auto split: prod.splits list.splits)
    apply (simp add: finite_produce_simps)
    apply (subst (asm) (5) finite_produce_simps)
    apply auto
    subgoal for x xs op' out op'' y
      apply (cases y)
      apply auto
      apply (subst (2) finite_produce_simps)
      apply auto
      apply (subst (2) finite_produce_simps)
      apply auto
      apply (simp add: finite_produce_append)
      done
    done
  done

lemma snd_finite_produce_compose_op:
  "snd (finite_produce (compose_op op1 op2) xs) = snd (finite_produce op2 (snd (finite_produce op1 xs)))"
  apply (induct xs arbitrary: op1 op2)
  apply simp
  subgoal for x xs op1 op2
    apply (subst (1 3) finite_produce_simps)
    apply (auto split: prod.splits list.splits)
    apply (simp add: finite_produce_append)
    done
  done

lemma finite_produce_compose_op:
  "finite_produce (compose_op op1 op2) xs = (compose_op (fst (finite_produce op1 xs)) (fst (finite_produce op2 (snd (finite_produce op1 xs)))), snd (finite_produce op2 (snd (finite_produce op1 xs))))"
  by (metis fst_finite_produce_compose_op prod.collapse snd_finite_produce_compose_op)

lemma compose_op_assoc:     
  "(\<forall>n lys. produce_inner (skip_n_productions_op op2 n, lys) \<noteq> None) \<Longrightarrow>
   compose_op (compose_op op1 op2) op3 = compose_op op1 (compose_op op2 op3)"
  apply (coinduction arbitrary: op1 op2 op3)
  apply (auto simp add:  rel_fun_def)
  subgoal for op1 op2 op3 x
    apply (intro exI conjI)
    apply (rule refl)+
    apply auto
    apply (simp add: fst_finite_produce_compose_op)
    subgoal for n lys
      apply (drule spec[of _ "n + length (snd (apply op1 x))"])
      apply (drule spec[of _ "snd (apply op1 x) @@- lys"])
      apply (elim exE)
      subgoal for y
        apply (rule exI[of _ y])
        apply (cases n)
        apply auto
        oops

lemma compose_op_assoc:
  "\<forall>xs op' old out. finite_produce op3 xs = (op', out) \<longrightarrow> exit op' = LNil \<Longrightarrow>
   compose_op (compose_op op1 op2) op3 = compose_op op1 (compose_op op2 op3)"
  apply (coinduction arbitrary: op1 op2 op3)
  apply (auto simp add: finite_produce_compose_op rel_fun_def)
  apply (metis finite_produce_append fst_conv)
  apply (subst produce_compose_op_correctness_alt)
  apply auto
  done

corecursive lconcat where
  "lconcat xss = (if \<forall>xs \<in> lset xss. xs = [] then LNil else case xss of LNil \<Rightarrow> LNil
     | LCons [] xss' \<Rightarrow> lconcat xss'
     | LCons (x # xs) xss' \<Rightarrow> LCons x (lshift xs (lconcat xss')))"
  by (relation "measure (\<lambda>xss. LEAST i. lnth xss i \<noteq> [])")
    (auto simp: lset_conv_lnth Least_Suc)

lemma lconcat_unique:
  assumes "\<And>xss. f xss = (if \<forall>xs \<in> lset xss. xs = [] then LNil else case xss of LNil \<Rightarrow> LNil
     | LCons [] xss' \<Rightarrow> f xss'
     | LCons (x # xs) xss' \<Rightarrow> LCons x (lshift xs (f xss')))"
  shows "f = lconcat"
proof(rule ext)
  show "f xss = lconcat xss" for xss
  proof(coinduction arbitrary: xss rule: llist.coinduct_upto)
    case (Eq_llist xss)
    show ?case
      apply(induction xss rule: lconcat.inner_induct)
      apply(subst (1 2 3 5) assms)
      apply(subst (1 2 3 5) lconcat.code)
      apply (auto split: llist.splits list.splits intro: llist.cong_intros)
      done
  qed
qed

lemma lconcat_all_Nil: "\<forall>xs\<in>lset xss. xs = [] \<Longrightarrow> lconcat xss = LNil"
  by (subst lconcat.code) (auto)

lemma lconcat_code:
  "lconcat xss = (case xss of LNil \<Rightarrow> LNil | LCons xs xss' \<Rightarrow> lshift xs (lconcat xss'))"
  apply (rule lconcat_unique[THEN sym, THEN fun_cong])
  apply (subst lconcat.code)
  apply (auto simp: lconcat_all_Nil split: llist.splits list.splits)
  done

lemma in_lset_lconcat_LNil_Nil:
  "xs \<in> lset xss \<Longrightarrow> lconcat xss = LNil \<Longrightarrow> xs = []"
  apply (induct xss arbitrary: rule: lset_induct)
  apply (subst (asm) lconcat_code)
  apply auto
  apply (subst (asm) lconcat_code)
  using lshift_LNil_split apply blast
  apply (metis LNil_eq_shift_iff lconcat_code llist.simps(5))
  done

lemma all_in_lset_lconcat_LNil_Nil: 
  "lconcat xss = LNil \<Longrightarrow> \<forall> xs \<in> lset xss. xs = []"
  using in_lset_lconcat_LNil_Nil apply auto
  done

lemma lconcat_not_all_Nil:
  "x \<in> lset (lconcat xss) \<Longrightarrow> \<not> (\<forall>xs\<in>lset xss. xs = [])"
  using lconcat_all_Nil by fastforce

lemma lconcat_eq_LNil[simp]: "lconcat xss = LNil \<longleftrightarrow> (\<forall>xs\<in>lset xss. xs = [])"
  using in_lset_lconcat_LNil_Nil lconcat_all_Nil by blast

lemma lconcat_LCons_ex:
  "lconcat lxs = LCons x lxs' \<Longrightarrow> \<exists>xa\<in>lset lxs. x \<in> set xa"
  apply (induct lxs rule: lconcat.corec.inner_induct)
  subgoal for xss
    apply (cases xss)
    apply (simp add: lconcat.code)
    subgoal for x xss'
      apply hypsubst_thin
      apply simp
      apply (subst (asm) (2) lconcat_code)
      apply (auto split: llist.splits)
      apply (metis lconcat_all_Nil llist.distinct(1) lshift_simps(1) shift_in_list)
      done
    done
  done

lemma lconcat_remove_head:
  "lconcat lxs = LCons x xs \<Longrightarrow>
   lconcat (LCons (tl (lhd (ldropWhile (\<lambda>xs. xs = []) lxs))) (ltl (ldropWhile (\<lambda> xs. xs = []) lxs))) = xs"
  apply (induct lxs arbitrary: x rule: lconcat.corec.inner_induct)
  subgoal for xss
    apply (cases xss)
    apply (simp add: lconcat.code)
    subgoal for x xss'
      apply hypsubst_thin
      apply simp
      apply (subst (asm) (3) lconcat_code)
      apply (auto split: llist.splits)
      apply (metis lconcat_all_Nil llist.distinct(1))
      apply (metis lconcat_code list.collapse llist.case(2) shift_LCons_Cons)
      done
    done
  done

lemma lconcat_inclusion:
  "x \<in> lset lys \<Longrightarrow> lys = lconcat lxs \<Longrightarrow> \<exists>xa\<in>lset lxs. x \<in> set xa"
  apply (induct lys arbitrary: lxs rule: lset_induct)
  using lconcat_LCons_ex apply metis
  subgoal for x' xs lxs
    apply (drule sym)
    apply (drule meta_spec[of _ "LCons (tl (lhd (ldropWhile (\<lambda> xs . xs = []) lxs))) (ltl (ldropWhile (\<lambda> xs . xs = []) lxs))"])
    apply (frule lconcat_LCons_ex)
    using lconcat_remove_head 
    apply (smt (verit, best) in_lset_ldropWhileD in_lset_ltlD lconcat_all_Nil lhd_LCons lhd_ldropWhile_in_lset list.sel(2) list.set_sel(2) llist.distinct(1) lset_cases ltl_simps(2))
    done
  done

lemma inclusion_lconcat:
  "xs \<in> lset lxs \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<in> lset (lconcat lxs)"
  apply (induct lxs arbitrary: rule: lset_induct)
  apply (auto simp add: lconcat_code)
  done

lemma lset_lconcat:
  "lset (lconcat xss) = (\<Union>xs\<in>lset xss. set xs)"
  apply safe
  subgoal for x
    apply (induct "(lconcat xss)" arbitrary: rule: lset_induct)
    apply (metis UN_I lconcat_LCons_ex)
    using lconcat_inclusion 
    apply (metis UN_iff in_lset_ltlD ltl_simps(2))
    done
  subgoal for x xs
    using inclusion_lconcat apply fast
    done
  done


lemma lfinite_lconcat:
  "lfinite lxs \<Longrightarrow>
   lfinite (lconcat lxs)"
  apply (induct lxs rule: lfinite.induct)
  apply (simp add: lconcat_all_Nil)
  apply (subst lconcat.code)
  apply (auto split: list.splits)
  done


lemma lconcat_lmap_LNil:
  "\<forall> x \<in> lset lxs . f x = LNil \<Longrightarrow>
   Coinductive_List.lconcat (lmap f lxs) = LNil"
  apply (auto simp add: Coinductive_List.lconcat_eq_LNil)
  done

lemma lconcat_correct:
  "lconcat lxs = Coinductive_List.lconcat (lmap llist_of lxs)"
  apply (rule lconcat_unique[THEN sym, THEN fun_cong])
  apply (auto simp add:  eq_Nil_null split: list.splits llist.splits)
  apply (simp add: lconcat_lmap_LNil null_def)
  subgoal
    by (simp add: null_def)
  subgoal
    by (simp add: null_rec(1))
  subgoal
    using lappend_llist_of by blast
  subgoal
    using lappend_llist_of by blast
  done

lemma finite_produce_Cons[simp]:
  "finite_produce op (x#xs) = (let (lgc', out) = apply op x in (\<lambda> (op', out'). (op', out@out')) (finite_produce lgc' xs))"
  apply (subst finite_produce_simps)
  apply (simp split: prod.splits)
  done

end