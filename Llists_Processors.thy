theory Llists_Processors
  imports
    "Coinductive.Coinductive_List"
    "Linear_Temporal_Logic_on_Llists"
    "HOL-Library.BNF_Corec"
    "HOL-Library.Code_Lazy"
    "HOL-Library.Numeral_Type"
    "HOL-Library.Simps_Case_Conv"
begin

code_lazy_type llist

codatatype ('i, 'o) op = Logic ("apply": "('i \<Rightarrow> ('i, 'o) op \<times> 'o list)") ("exit": "'o llist")

(* FIXME: uncurry this *)
partial_function (option) produce_inner_induct where
  "produce_inner_induct op_lxs = (case op_lxs of (op, lxs) \<Rightarrow>
    (case lxs of 
        LNil \<Rightarrow> Some (Inr op)
     | LCons h lxs' \<Rightarrow> (case apply op h of 
                         (lgc', []) \<Rightarrow> produce_inner_induct (lgc', lxs')
                       | (lgc', x#xs) \<Rightarrow> Some (Inl (lgc', x, xs, lxs')))))"
simps_of_case produce_inner_simps[simp]: produce_inner_induct.simps
declare produce_inner_induct.simps[code]

lemma produce_inner_LNil_None[simp]:
  "produce_inner_induct (op, LNil) = Some (Inr op)"
  apply simp
  done

lemma produce_inner_alt[consumes 1, case_names no_production produces terminates]:
  assumes "produce_inner_induct op_lxs = Some y"
    and "\<And>op h lxs op' zs . apply op h = (op', []) \<Longrightarrow> Q (op', lxs) zs \<Longrightarrow> Q (op, LCons h lxs) zs"
    and "\<And>op h x xs lxs lxs' op' . produce_inner_induct (op, LCons h lxs) = Some (Inl (op', x, xs, lxs')) \<Longrightarrow>
                                    apply op h = (op', x # xs) \<Longrightarrow> Q (op, LCons h lxs) (Inl (op', x, xs, lxs'))"
    and  "\<And>op. Q (op, LNil) (Inr op)"
  shows "Q op_lxs y"
  apply (rule produce_inner_induct.raw_induct[OF _ assms(1)])
  apply (simp split: llist.splits prod.splits list.splits)[1]
  using assms(4) apply blast  
  using assms(2) apply blast
  apply (metis (mono_tags, lifting) assms(3) list.simps(5) llist.case(2) prod.simps(2) produce_inner_induct.simps)
  done

corec produce where
  "produce op lxs = 
    (case produce_inner_induct (op, lxs) of
       None \<Rightarrow> LNil
    | Some (Inr op') \<Rightarrow> exit op'
    | Some (Inl (op', x, xs, lxs')) \<Rightarrow> LCons x (xs @@- produce op' lxs'))"

lemma produce_LNil_exit[simp]:
  "produce op LNil = exit op"
  apply (subst produce.code)
  apply auto
  done


lemma produce_LCons[simp]:
  "produce op (LCons h lxs) = snd (apply op h) @@- produce (fst (apply op h)) lxs"
  apply (subst produce.code)
  apply (simp split: option.splits sum.splits prod.splits list.splits)
  apply (simp add: produce.code)
  done


lemma produce_code[code]:
 "produce op lxs = (case lxs of LNil \<Rightarrow> exit op| LCons x lxs' \<Rightarrow> let (op', out) = apply op x in out @@- produce op' lxs')"
  apply (cases lxs)
  apply (simp_all split: prod.splits)
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

lemma produce_inner_None_produce_LNil[simp]:
  "produce_inner_induct (op, lxs) = None \<Longrightarrow>
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
  assumes "produce_inner_induct (skip_n_productions_op op n, input_stream) = Some (Inl (lgc', h, xs, lxs'))" (is "produce_inner_induct ?P = Some ?R")
    and "produce_inner_induct (skip_n_productions_op op (Suc n), input_stream) = Some (Inl (lgc'', h', xs', lxs''))"
  shows "LCons h' (xs' @@- produce lgc'' lxs'') = xs @@- produce lgc' lxs'"
  using assms proof (induction "?P" "?R" arbitrary: input_stream n op rule: produce_inner_alt)
  case (no_production h lxs op')
  then show ?case 
    apply -
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
    apply (simp split: option.splits prod.splits if_splits list.splits)
     apply hypsubst_thin
     apply (metis drop_Suc drop_all dual_order.refl list.sel(3) lshift_simps(1) tl_drop)
    apply hypsubst_thin
    apply safe
    subgoal
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
  assumes "produce_inner_induct (skip_n_productions_op op n, lxs) = Some (Inr lgc')" (is "produce_inner_induct ?P = Some ?R")
  shows "produce_inner_induct (skip_n_productions_op op (Suc n), lxs) = Some (Inr (skip_first_production_op lgc'))"
  using assms apply (induction "?P" "?R"  arbitrary: n op lxs rule: produce_inner_alt)
  subgoal
    apply (simp split: prod.splits llist.splits if_splits list.splits)
    apply (metis (mono_tags, lifting) Suc_diff_le less_or_eq_imp_le)
    done
  apply (simp_all split: if_splits)
  apply hypsubst_thin
  apply (simp flip: skip_first_production_op_eq_skip_n_productions_op)
  done

lemma produce_inner_skip_n_productions_op_Some_Some_Some_None:
  assumes "produce_inner_induct (skip_n_productions_op op n, lxs) = Some (Inl (lgc', h, xs, lxs'))" (is "produce_inner_induct ?P = Some ?R")
    and "produce_inner_induct (skip_n_productions_op op (Suc n), lxs) = Some (Inr lgc'')"
  shows "produce lgc' lxs' = exit lgc'' \<and> xs = []"
  using assms proof (induction "?P" "?R"  arbitrary: n op lxs rule: produce_inner_alt)
  case (no_production h lxs op')
  then show ?case 
    by (smt (verit) Pair_inject Suc_diff_le cancel_comm_monoid_add_class.diff_cancel drop_eq_Nil2 le_imp_less_Suc less_Suc_eq less_le_not_le list.simps(4) llist.case(2) prod.simps(2) produce_inner_induct.simps skip_n_productions_op.simps(1) skip_n_productions_op_0)
next
  case (produces h lxs)
  then show ?case 
    apply -
    apply (simp split: prod.splits llist.splits if_splits list.splits)
    apply (subst produce.code)
    apply (simp split: option.splits prod.splits if_splits)
    apply (metis append_eq_conv_conj length_Suc_conv_rev list.inject)
    done
qed

lemma produce_inner_skip_n_productions_op_Suc_skip_n_productions_op_n:
  assumes  "produce_inner_induct (skip_n_productions_op op (Suc n), lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner_induct ?P = Some ?R")
    and "produce_inner_induct (skip_n_productions_op op n, lxs) = None"
  shows "False"
  using assms proof (induct "?P" "?R" arbitrary: n op lxs rule: produce_inner_alt)
  case (no_production h lxs op')
  then show ?case 
    apply -
    apply (simp split: if_splits)
    subgoal
      apply (cases lxs)
       apply (simp_all split: if_splits list.splits)
      subgoal
        apply hypsubst_thin
        apply (subst (asm) Suc_diff_le)
         apply (simp split: llist.splits if_splits)
        apply fastforce
        done
      subgoal
        apply hypsubst_thin
        apply (subst (asm) Suc_diff_le)
         apply (simp split: llist.splits if_splits)
        apply fastforce
        done
      done
    subgoal
      apply (cases lxs)
       apply (simp_all split: if_splits list.splits)
      subgoal
        apply hypsubst_thin
        apply (subst (asm) Suc_diff_le)
         apply (simp split: llist.splits if_splits)
        apply fastforce+
        done
      done
    subgoal
      apply (simp_all split: if_splits list.splits)
      done
    done
next
  case (produces h lxs)
  then show ?case 
    apply -
    apply (simp split: if_splits list.splits)
    done
qed

lemma produce_inner_skip_n_productions_op_Some_None_Suc_None:
  assumes "produce_inner_induct (skip_n_productions_op op n, lxs) = Some (Inr lys)" (is "produce_inner_induct ?P = Some ?R")
    and "produce_inner_induct (skip_n_productions_op op (Suc n), lxs) = Some (Inl l)"
  shows " False"
  using assms apply (induction ?P ?R arbitrary: lxs n op rule: produce_inner_alt)
   apply (simp_all split: if_splits)
   apply (smt (verit) Suc_diff_le less_le_not_le list.simps(4) llist.case(2) not_less_eq prod.simps(2) produce_inner_induct.simps skip_n_productions_op.simps(1))
  apply fastforce
  done

lemma produce_inner_skip_n_productions_op_Suc_None_Inr_None:
  assumes  "produce_inner_induct (skip_n_productions_op op (Suc n), lxs) = Some (Inl l)" (is "produce_inner_induct ?P = Some ?R")
    and "produce_inner_induct (skip_n_productions_op op n, lxs) = None"
  shows False
  using assms apply (induction ?P ?R arbitrary: lxs n op rule: produce_inner_alt)
   apply (simp_all  add: list.case_eq_if split: if_splits; hypsubst_thin?)
    apply (smt (verit, del_insts) Suc_diff_Suc cancel_comm_monoid_add_class.diff_cancel diff_Suc_Suc drop_eq_Nil2 less_Suc_eq less_or_eq_imp_le list.simps(4) llist.case(2) prod.simps(2) produce_inner_induct.simps skip_n_productions_op.simps(1) skip_n_productions_op_0)
  subgoal
    using less_Suc_eq by fastforce
  subgoal
    by (meson produce_inner_skip_n_productions_op_Suc_skip_n_productions_op_n)
  done

lemma produce_inner_Some_produce[simp]:
  "produce_inner_induct (op, lxs) = Some (Inl (lgc', x, xs, lxs')) \<Longrightarrow>
   produce op lxs = LCons x (xs @@- produce lgc' lxs')"
  apply (subst produce.code)
  apply simp
  done

lemma produce_inner_Some_None_None_False:
  assumes "produce_inner_induct (skip_n_productions_op op n, lxs) = Some (Inr lys)" (is "produce_inner_induct ?P = Some ?R")
    and "produce_inner_induct (op, lxs) = None"
  shows False
  using assms apply (induct ?P ?R arbitrary: n op lxs rule: produce_inner_alt[consumes 1])
   apply (simp_all split: prod.splits list.splits if_splits)
   apply auto[1]
  apply (metis skip_n_productions_op_0)
  done

lemma produce_inner_None_Some_None_False:
  assumes "produce_inner_induct (op, lxs) = Some (Inr lys)" (is "produce_inner_induct ?P = Some ?R")
    and "produce_inner_induct (skip_n_productions_op op n, lxs) = None"
  shows False
  using assms apply (induct ?P ?R arbitrary: n op lxs  rule: produce_inner_alt)
   apply (simp_all split: if_splits)
   apply auto[1]
  apply (metis skip_n_productions_op_0)
  done

lemma produce_inner_skip_n_productions_op_Some_llength_le:
  assumes "produce_inner_induct (skip_n_productions_op op n, lxs) = Some (Inl (lgc'', y, ys, lxs''))" (is "produce_inner_induct ?P = Some ?R")
    and "llength (produce op lxs) \<le> enat n"
  shows False
  using assms  apply (induct ?P ?R arbitrary: n y ys lxs'' op lxs lgc'' rule: produce_inner_alt)
   apply (simp_all split: prod.splits list.splits llist.splits sum.splits option.splits if_splits)
    apply (metis LNil_eq_shift_iff ldropn_eq_LNil ldropn_shift)
   apply (metis add.right_neutral enat_less_enat_plusI2 leD linorder_le_less_linear llength_shift skip_n_productions_op_0)
  apply (metis ldropn_eq_LNil ldropn_shift llist.simps(3) lshift_simps(2))
  done

lemma produce_inner_skip_n_productions_op_Some_produce_inner_None:
  assumes "produce_inner_induct (skip_n_productions_op op n, lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner_induct ?P = Some ?R")
    and "produce_inner_induct (op, lxs) = None" shows False
  using assms apply (induct ?P ?R arbitrary: n xs op lxs x  lxs' lgc' rule: produce_inner_alt)
   apply (simp_all split: if_splits prod.splits list.splits)
   apply auto[1]
  apply (metis skip_n_productions_op_0)
  done

lemma produce_inner_skip_n_productions_op_Some_produce_inner_Some_None:
  assumes "produce_inner_induct (skip_n_productions_op op n, lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner_induct ?P = Some ?R")
    and "produce_inner_induct (op, lxs) = Some (Inr lys)"
  shows False
  using assms apply (induct ?P ?R arbitrary: n xs op lxs x  lxs' lgc' rule: produce_inner_alt)
   apply (simp_all split: if_splits prod.splits list.splits)
   apply fast
  apply (metis skip_n_productions_op_0)
  done

lemma produce_inner_Some_produce_inner_skip_n_productions_op_Suc_n_None:
  assumes "produce_inner_induct (skip_n_productions_op op n, lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner_induct ?P = Some ?R")
    and "produce_inner_induct (skip_n_productions_op op (Suc n), lxs) = None"
  shows "llength (produce op lxs) = enat (Suc n)"
  using assms apply (induct ?P ?R arbitrary: n op lxs lxs' x xs rule: produce_inner_alt)
   apply (simp_all split: if_splits prod.splits list.splits)
  subgoal
    by (metis Suc_diff_le add_diff_inverse_nat less_imp_le_nat llength_shift not_less_eq_eq plus_enat_simps(1))
  subgoal
    by (metis One_nat_def Suc_eq_plus1 llength_shift plus_enat_simps(1) skip_n_productions_op_0)
  done

lemma produce_inner_skip_n_productions_op_Some_None_aux:
  "produce_inner_induct (skip_n_productions_op op n, lxs) = Some r \<Longrightarrow>
   produce_inner_induct (op, lxs) = None \<Longrightarrow> False"
  by (metis obj_sumE prod_cases4 produce_inner_Some_None_None_False produce_inner_skip_n_productions_op_Some_produce_inner_None)

lemma produce_inner_skip_n_productions_op_Some_None[simp]:
  "produce_inner_induct (op, lxs) = None \<Longrightarrow>
   produce_inner_induct (skip_n_productions_op op n, lxs) = None"
  using produce_inner_skip_n_productions_op_Some_None_aux by fastforce

lemma produce_inner_skip_n_productions_op_Suc_Some_None_False:
  "produce_inner_induct (skip_n_productions_op op (Suc n), lxs) = Some r \<Longrightarrow>
   produce_inner_induct (skip_n_productions_op op n, lxs) = None \<Longrightarrow>
   False"
  apply (induct "(skip_n_productions_op op (Suc n), lxs)" r arbitrary: n op lxs rule: produce_inner_alt)
  subgoal
    apply (simp split: prod.splits if_splits list.splits)
     apply (metis Suc_diff_le less_or_eq_imp_le)
    apply (metis One_nat_def add_diff_cancel_right' less_SucE plus_1_eq_Suc skip_n_productions_op_0)
    done
   apply (auto split: prod.splits if_splits list.splits)
  done

lemma produce_inner_skip_n_productions_op_None_Suc:
  "produce_inner_induct (skip_n_productions_op op n, lxs) = None \<Longrightarrow>
   produce_inner_induct (skip_n_productions_op op (Suc n), lxs) = None"
  using produce_inner_skip_n_productions_op_Suc_Some_None_False by fastforce

lemma produce_inner_skip_n_productions_op_None_gt: 
  "produce_inner_induct (skip_n_productions_op op n, lxs) = None \<Longrightarrow>
   m > n \<Longrightarrow>
   produce_inner_induct (skip_n_productions_op op m, lxs) = None"
  apply (induct m arbitrary: n op lxs)
   apply simp
  apply (metis less_Suc_eq produce_inner_skip_n_productions_op_None_Suc)
  done

lemma produce_inner_Some_produce_inner_skip_n_productions_op_le_False:
  assumes "produce_inner_induct (op, lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner_induct ?P = Some ?R")
    and "produce_inner_induct (skip_n_productions_op op n, lxs) = Some (Inl l)"
    and "eSuc (llength (xs @@- produce lgc' lxs')) \<le> enat n"
  shows False
  using assms proof (induct ?P ?R arbitrary: n op lxs lxs' x xs lgc' rule: produce_inner_alt)
  case (no_production op h lxs op')
  then show ?case 
    apply (simp split: prod.splits if_splits list.splits sum.splits option.splits)
     apply force+
    done
next
  case (produces op h x xs lxs lxs' op')
  then show ?case 
    apply (simp split: prod.splits if_splits list.splits sum.splits option.splits)
    subgoal
      by (metis llength_LCons prod_cases4 produce_inner_Some_produce produce_inner_skip_n_productions_op_Some_llength_le produces.hyps(1) produces.prems(1))
    subgoal
      by (metis llength_LCons prod_cases4 produce_inner_Some_produce produce_inner_skip_n_productions_op_Some_llength_le produces.hyps(1) produces.prems(1))
    subgoal
      by (metis drop_eq_Nil2 dual_order.trans enat_le_plus_same(1) iless_Suc_eq leD le_add_diff_inverse length_Cons list.distinct(1) llength_shift not_less_eq_eq plus_enat_simps(1))
    done
qed

lemma produce_inner_skip_n_productions_op_None_le:
  "produce_inner_induct (skip_n_productions_op op n, lxs) = None \<Longrightarrow> llength (produce op lxs) \<le> enat n"
proof (induct n arbitrary: lxs op)
  case 0
  then show ?case by simp
next
  case (Suc n lxs op)
  then show ?case 
  proof (cases "produce_inner_induct (skip_n_productions_op op n, lxs)")
    case None
    then show ?thesis 
      by (metis Suc.hyps order.trans eSuc_enat ile_eSuc)
  next
    case (Some r)
    then show ?thesis 
    proof (cases r)
      case (Inl a)
      then show ?thesis 
        by (metis Some Suc.prems nle_le prod_cases4 produce_inner_Some_produce_inner_skip_n_productions_op_Suc_n_None)
    next
      case (Inr b)
      then show ?thesis 
        using Some Suc.prems produce_inner_skip_n_productions_op_Some_None_Suc produce_inner_skip_n_productions_op_Suc_Some_None_False by blast
    qed
  qed
qed

lemma produce_inner_skip_n_productions_op_Some_Inr_le:
  assumes "produce_inner_induct (skip_n_productions_op op n, lxs) = Some (Inr lys)" (is "produce_inner_induct ?P = Some ?R")
    and "lnull (exit lys)"
  shows "llength (produce op lxs) \<le> enat n"
  using assms proof (induct ?P ?R arbitrary: n op lxs rule: produce_inner_alt)
  case (no_production h lxs op')
  then show ?case 
    apply (simp split: if_splits)
    subgoal
      by (metis (no_types, lifting) LNil_eq_shift_iff drop_eq_Nil2 ldropn_eq_LNil ldropn_shift less_or_eq_imp_le)
    subgoal
      by (metis add.right_neutral enat_0 linorder_le_less_linear llength_shift nle_le not_less_zero skip_n_productions_op_0)
    done
next
  case terminates
  then show ?case by force
qed

lemma produce_inner_skip_n_productions_op_Some_Inr_le_lnull:
  assumes "produce_inner_induct (skip_n_productions_op op n, lxs) = Some (Inr lys)" (is "produce_inner_induct ?P = Some ?R")
    and "llength (produce op lxs) \<le> enat n"
  shows  "lnull (exit lys)"
  using assms proof (induct ?P ?R arbitrary: n op lxs rule: produce_inner_alt)
  case (no_production h lxs op')
  then show ?case 
    apply (simp split: if_splits)
    subgoal
      by (metis (no_types, lifting) LNil_eq_shift_iff ldropn_eq_LNil ldropn_shift)
    subgoal
      by (metis diff_self_eq_0 ldrop_eq_LNil ldrop_shift lshift_LNil_split skip_n_productions_op_0)
    done
next
  case terminates
  then show ?case by force
qed

lemma produce_inner_skip_n_productions_op_Inl_lnth:
  assumes  "produce_inner_induct (skip_n_productions_op op n, lxs) = Some (Inl (lgc', y, ys, lys))" (is "produce_inner_induct ?P = Some ?R")
    and "n < llength (produce op lxs)"
  shows "y = lnth (produce op lxs) n"
  using assms proof (induct ?P ?R arbitrary: n op lxs rule: produce_inner_alt)
  case (no_production h lxs op')
  then show ?case 
    apply (simp split: if_splits)
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (metis drop_eq_Nil2 ldropn_eq_LNil ldropn_shift leD less_or_eq_imp_le linorder_le_less_linear lshift_simps(1))
      apply simp
      apply (metis lappend_llist_of llength_llist_of lnth_lappend2 nless_le)
      done
    subgoal
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (simp_all add: enat_0 llength_shift)
      apply (metis diff_is_0_eq lappend_llist_of less_or_eq_imp_le llength_llist_of lnth_lappend2)
      done
    done
next
  case (produces h lxs)
  then show ?case 
    apply (simp split: if_splits)
    apply (metis drop_all less_or_eq_imp_le list.simps(3) lnth_shift not_less_iff_gr_or_eq nth_via_drop)
    done
qed

lemma produce_inner_skip_n_productions_Inr_op_ldropn:
  assumes "produce_inner_induct (skip_n_productions_op op n, lxs) = Some (Inr y)" (is "produce_inner_induct ?P = Some ?R")
  shows "exit y = ldropn n (produce op lxs)"
  using assms proof (induct ?P ?R arbitrary: n op lxs rule: produce_inner_alt)
  case (no_production h lxs op')
  then show ?case 
    apply (simp add: ldropn_shift split: if_splits)
    subgoal
      by (metis ldropn_0 skip_n_productions_op_0)
    done
next
  case terminates
  then show ?case 
    by (auto simp add: ldrop_enat)
qed

lemma produce_inner_skip_n_productions_op_llength_LNil:
  assumes  "produce_inner_induct (skip_n_productions_op op n, lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner_induct ?P = Some ?R")
    and "\<not> llength (produce op lxs) \<le> enat n"
    and "produce_inner_induct (skip_n_productions_op op (Suc n), lxs) = None"
  shows "xs @@- produce lgc' lxs' = LNil" 
  using assms proof (induct ?P ?R arbitrary: op lxs x xs lxs' n rule: produce_inner_alt)
  case (no_production h lxs op')
  then show ?case 
    apply (simp split: if_splits)
    subgoal
      by (metis Suc_diff_le drop_eq_Nil dual_order.strict_iff_not ldropn_eq_LNil ldropn_shift lshift_LNil_split)
    subgoal
      by (metis add_left_mono enat_0 llength_LNil llength_llist_of llength_shift shift_LNil skip_n_productions_op_0)
    done
next
  case (produces h x xs lxs lxs')
  then show ?case 
    apply (simp split: if_splits list.splits)
    apply (metis add_implies_diff add_is_1 length_0_conv length_drop list.size(4) llist_of_eq_LNil_conv plus_1_eq_Suc)
    done
qed

theorem produce_skip_n_productions_op_correctness:
  "produce (skip_n_productions_op op n) lxs = ldropn n (produce op lxs)"
proof (coinduction arbitrary: op lxs n rule: llist.coinduct_upto)
  case (Eq_llist op' lxs' n')
  then show ?case 
  proof -
    have "lnull (produce (skip_n_productions_op op' n') lxs') = lnull (ldropn n' (produce op' lxs'))"
      apply (subst (1 2) produce.code)
      apply (simp split: prod.splits list.splits option.splits sum.splits)
      apply (intro impI allI conjI)
      subgoal
        by (metis llength_LCons produce_inner_Some_produce produce_inner_skip_n_productions_op_None_le)
      subgoal
        by (meson produce_inner_Some_produce_inner_skip_n_productions_op_le_False)
      subgoal
        by (metis llength_LCons produce_inner_Some_produce produce_inner_skip_n_productions_op_Some_Inr_le produce_inner_skip_n_productions_op_Some_Inr_le_lnull)
      subgoal
        using produce_inner_None_Some_None_False by blast
      subgoal
        by (meson produce_inner_skip_n_productions_op_Some_produce_inner_Some_None)
      subgoal
        by (simp add: produce.code produce_inner_skip_n_productions_Inr_op_ldropn)
      done
    moreover have "lhd (produce (skip_n_productions_op op' n') lxs') = lhd (ldropn n' (produce op' lxs'))"
      if "\<not> lnull (produce (skip_n_productions_op op' n') lxs')"
        and "\<not> lnull (ldropn n' (produce op' lxs'))"
      using that 
      apply (subst (1 2) produce.code)
      apply (simp add: split: prod.splits list.splits option.splits sum.splits)
      apply (intro impI allI conjI)
           apply simp_all
      subgoal
        by (metis leI lhd_ldropn llength_LCons produce_inner_Some_produce produce_inner_skip_n_productions_op_Inl_lnth)
      subgoal
        by (simp add: produce_inner_skip_n_productions_Inr_op_ldropn)
      subgoal
        by (meson produce_inner_skip_n_productions_op_Some_produce_inner_Some_None)
      subgoal
        by (simp add: produce.code produce_inner_skip_n_productions_Inr_op_ldropn)
      done
    moreover have "llist.v1.congclp (\<lambda>llist llist'. \<exists>op lxs n. llist = produce (skip_n_productions_op op n) (lxs::'b llist) \<and> llist' = ldropn n (produce op lxs)) (ltl (produce (skip_n_productions_op op' n') lxs')) (ltl (ldropn n' (produce op' lxs')))"
      if "\<not> lnull (produce (skip_n_productions_op op' n') lxs')"
        and "\<not> lnull (ldropn n' (produce op' lxs'))"
      using that 
      apply -
      apply (rule lshift.cong_base)
      apply (rule exI[of _ op'])
      apply (rule exI[of _ lxs'])
      apply (rule exI[of _ "Suc n'"])
      apply (intro conjI)
      subgoal 
        apply (subst (1 2) produce.code)
        apply (simp add: split: prod.splits list.splits option.splits sum.splits)
        apply (intro impI allI conjI)
               apply simp_all
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
    ultimately show ?thesis
      by (intro conjI impI)
  qed
qed

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
    apply (simp split: list.splits prod.splits)
    apply (metis (mono_tags, lifting) append.assoc fold_apply_old)
    done
  done

lemma finite_produce_Nil[simp]:
  "finite_produce op [] = (op, [])"
  apply (subst finite_produce_simps)
  apply simp
  done

lemma finite_produce_Cons[simp]:
  "finite_produce op (x # xs) = (fst (finite_produce (fst (apply op x)) xs), snd (apply op x) @ snd (finite_produce (fst (apply op x)) xs))"
  apply (subst finite_produce_simps)
  apply (auto split: prod.splits)
  done

lemma finite_produce_Cons_alt:
  "finite_produce op (x#xs) = (let (lgc', out) = apply op x in (\<lambda> (op', out'). (op', out@out')) (finite_produce lgc' xs))"
  apply (subst finite_produce_simps)
  apply (simp split: prod.splits)
  done

primcorec compose_op where
  "compose_op op1 op2 = Logic (\<lambda> ev.
       let (op1', out) = apply op1 ev in
       let (op2', out') = finite_produce op2 out in
       (compose_op op1' op2', out'))
   (produce op2 (exit op1))
  "

lemma produce_inner_compose_op_Some_produce_inner_None:
  "produce_inner_induct (compose_op op1 op2, lxs) = Some r \<Longrightarrow>
   produce_inner_induct (op1, lxs) = None \<Longrightarrow> False"
  apply (induct "(compose_op op1 op2, lxs)" r arbitrary: op1 op2 lxs rule: produce_inner_alt[consumes 1])
    apply (auto split: prod.splits list.splits llist.splits)
  done

lemma produce_inner_None_produce_inner_compose_op_None[simp]:
  "produce_inner_induct (op1, lxs) = None \<Longrightarrow> produce_inner_induct (compose_op op1 op2, lxs) = None"
  using produce_inner_compose_op_Some_produce_inner_None by fastforce


lemma produce_inner_compose_op_Some_production:
  "apply op1 h = (op1', x#xs) \<Longrightarrow>
   finite_produce op2 (x#xs) = (op2', y#ys) \<Longrightarrow>
   produce_inner_induct (compose_op op1 op2, LCons h lxs) = Some (Inl (compose_op op1' op2', y, ys, lxs))"
  apply (subst produce_inner_induct.simps)
  apply (auto split: option.splits list.splits)
  done

lemma produce_inner_compose_op_finite_produce_no_production[simp]:
  assumes "produce_inner_induct (op1, lxs) = Some (Inl (op1', x, xs, lxs'))" (is "produce_inner_induct ?P = Some ?R")
    and "finite_produce op2 (x#xs) = (op2', [])"
  shows "produce_inner_induct (compose_op op1 op2, lxs) = produce_inner_induct (compose_op op1' op2', lxs')"
  using assms apply (induct ?P ?R arbitrary: op1 op2 lxs rule: produce_inner_alt)
   apply (auto split: option.splits list.splits llist.splits prod.splits)
  done

lemma produce_inner_LCons_Some_cases:
  "produce_inner_induct (op1, LCons h hs) = Some (Inl (op, x, xs, lxs')) \<Longrightarrow>
   (apply op1 h = (op, x#xs) \<and> lxs' = hs) \<or> produce_inner_induct (fst (apply op1 h), hs) = Some (Inl (op, x, xs, lxs'))"
  apply (subst (asm) produce_inner_induct.simps)
  apply (auto split: prod.splits list.splits)
  done

lemma produce_inner_Some_Inl_compose_op:
  assumes "produce_inner_induct (op1, lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner_induct ?P = Some ?R")
    and "finite_produce op2 (x # xs) = (lgc'', y # ys)"
  shows "produce_inner_induct (compose_op op1 op2, lxs) = Some (Inl (compose_op lgc' lgc'', y, ys, lxs'))"
  using assms apply (induct ?P ?R arbitrary: op1 op2 lxs rule: produce_inner_alt)
   apply auto
  done

lemma produce_inner_Some_Inr_compose_op:
  assumes "produce_inner_induct (op1, lxs) = Some (Inr lgc')" (is "produce_inner_induct ?P = Some ?R")
  shows "produce_inner_induct (compose_op op1 op2, lxs) = Some (Inr (compose_op lgc' op2))"
  using assms apply (induct ?P ?R arbitrary: op1 op2 lxs rule: produce_inner_alt)
   apply auto
  done

lemma produce_inner_compose_op:
  "produce_inner_induct (compose_op op1 op2, lxs) =
   (case (produce_inner_induct (op1, lxs)) of
      None \<Rightarrow> None
    | Some (Inr lgc') \<Rightarrow> Some (Inr (compose_op lgc' op2))
    | Some (Inl (op, x, xs, lxs')) \<Rightarrow> (
      let (lgc', out) = finite_produce op2 (x#xs) in
      (case out of 
         [] \<Rightarrow> produce_inner_induct (compose_op op lgc', lxs') 
       | y#ys \<Rightarrow> Some (Inl (compose_op op lgc', y, ys, lxs')))))"
  apply (cases "produce_inner_induct (op1, lxs)")
   apply simp
  subgoal for p
    apply (cases p)
     apply simp
     apply hypsubst_thin
     apply (simp_all add: produce_inner_Some_Inl_compose_op split:  prod.splits list.splits)
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
  "produce_inner_induct (op, xs @@- lxs) = Some (Inl (lgc', y, ys, lxs')) \<Longrightarrow>
   finite_produce op xs = (lgc'', []) \<Longrightarrow>
   produce_inner_induct (lgc'', lxs) = Some (Inl (lgc', y, ys, lxs'))"
  apply (induct xs arbitrary: op)
   apply (simp_all split: option.splits llist.splits list.splits prod.splits)
  subgoal
    by (metis prod.collapse)
  done

lemma apply_compose_op_Cons:
  "apply (compose_op op1 op2) h = (lgc', x # xs) \<Longrightarrow>
   \<exists> y ys op1' op2' .apply op1 h = (op1', y#ys) \<and> finite_produce op2 (y#ys) = (op2', x#xs) \<and> lgc' = compose_op op1' op2'"
  apply (cases "apply op1 h")
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
  "finite_produce op xs = (lgc', ys) \<Longrightarrow> ys = snd (finite_produce op xs)"
  apply (induct xs arbitrary: op ys lgc')
   apply simp
  apply (subst (asm) (3) finite_produce_simps)
  apply (subst finite_produce_simps)
  apply (simp split: prod.splits)
  done


lemma produce_coinduction:
  assumes rel: "P op ilxs olxs"
    and nonterm: "\<And>op ilxs olxs. P op ilxs olxs \<Longrightarrow> produce_inner_induct (op, ilxs) = None \<Longrightarrow> olxs = LNil"
    and exit: "\<And>op olxs. P op LNil olxs \<Longrightarrow> olxs = exit op"
    and step: "\<And>op h ilxs olxs op' out.
    P op (LCons h ilxs) olxs \<Longrightarrow> apply op h = (op', out) \<Longrightarrow> \<exists>olxs'. olxs = out @@- olxs' \<and> P op' ilxs olxs'"
  shows "produce op ilxs = olxs"
proof -
  have coind: "\<And>op ilxs olxs. P op ilxs olxs \<Longrightarrow>
    (case produce_inner_induct (op, ilxs) of None \<Rightarrow> olxs = LNil
       | Some (Inl (op', x, xs, ilxs')) \<Rightarrow> \<exists>olxs'. olxs = LCons x (xs @@- olxs') \<and> P op' ilxs' olxs'
       | Some (Inr op') \<Rightarrow> olxs = exit op')"
    apply (simp split: option.splits sum.splits)
    apply (intro conjI allI impI)
    subgoal
      by (rule nonterm)
    subgoal for op ilxs olxs op' x xs ilxs'
      apply (drule produce_inner_alt[where Q="\<lambda>(op, ilxs) zs. 
      case zs of Inl (op', x, xs, ilxs') \<Rightarrow> \<forall>olxs. P op ilxs olxs \<longrightarrow> (\<exists>olxs'. olxs = LCons x (xs @@- olxs') \<and> P op' ilxs' olxs') | Inr op' \<Rightarrow> True"])
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
      apply (simp_all split: prod.splits option.splits sum.splits)
      apply (intro conjI impI)
    apply auto[1]
     apply (drule coind)
     apply (subst produce.code)
     apply (simp_all split: prod.splits option.splits sum.splits)
      apply (intro conjI impI allI)
    apply auto[1]
     apply (frule coind)
    apply (subst (2) produce.code)
    apply (simp split: option.splits sum.splits)
  apply (intro conjI impI allI)
     apply auto[1]
    apply (metis (mono_tags, lifting) lshift.cong_base lshift.cong_lshift)
    using lshift.cong_refl apply blast
    done
qed


lemma finite_produce_to_shift_produce:
  "finite_produce op xs = (lgc', zs) \<Longrightarrow>
   produce op (xs @@- lxs) = zs @@- produce lgc' lxs"
  apply (induct xs arbitrary: op lxs zs)
   apply simp
  subgoal for a xs op lxs zs
    apply (simp split: prod.splits list.splits option.splits)
    apply (metis lshift_append prod.collapse)
    done
  done

lemma produce_lshift[simp]: 
  "produce op (xs @@- lxs) = (let (op', out) = finite_produce op xs in out @@- produce op' lxs)"
  apply (induct xs arbitrary: op)
   apply (auto simp: split: prod.splits list.splits)
  done


lemma produce_inner_compose_op_apply_Nil:
  "produce_inner_induct (compose_op op1 op2, lxs) = None \<Longrightarrow>
   produce op1 lxs = LCons y lys \<Longrightarrow>
   \<exists> op2' . apply op2 y = (op2', [])"
  apply (subst (asm) produce.code)
  apply (simp split: option.splits prod.splits list.splits)
  apply (subst (asm) produce_inner_compose_op)
  apply (simp split: prod.splits list.splits)
  apply (subst (asm) finite_produce_simps)
  apply (simp split: prod.splits sum.splits list.splits)
  done


lemma produce_inner_to_finite_produce:
  "produce_inner_induct (op, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
   \<exists> zs. lxs = zs @@- lxs' \<and> finite_produce op zs = (lgc', x#xs)"
  apply (induct "(op, lxs)" r arbitrary: op lxs lgc' x xs lxs'  rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs' lgc' lgc'a x xs lxs''
    apply (simp split: option.splits prod.splits list.splits)
    apply (metis finite_produce_Cons finite_produce_def fold_apply_old fst_eqD lshift_simps(2) snd_eqD)
    done
   apply simp_all
  apply (metis append.right_neutral finite_produce_Cons finite_produce_Nil fst_conv lshift_simps(1) lshift_simps(2) snd_conv)
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
  apply (simp split: prod.splits)
  subgoal for a xs zs op lgc' lxs lys lgc'' 
    apply (cases zs)
     apply simp_all
    apply (smt (verit, ccfv_SIG) finite_produce_LCons_Nil finite_produce_move_old_out prod.collapse)
    done
  done


lemma produce_inner_compose_op_Inl_skip_n_productions_op:
  assumes  "produce_inner_induct (compose_op (skip_n_productions_op op1 n) lgc2'', lxs) = Some (Inl (lgc', y, ys, lys))" (is "produce_inner_induct ?P = Some ?R")
    and "produce_inner_induct (compose_op op1 op2, lxs) = None"
    and "n = length zs"
    and "produce op1 lxs = zs @@- lzs"
    and "finite_produce op2 zs = (lgc2'', [])"
  shows  False
  using assms
  apply (induct ?P ?R arbitrary: n zs op1 op2 lgc2'' lxs ys y lys lzs rule: produce_inner_alt)
  subgoal for h lxs op' n op1 lgc2'' ys y lys zs op2 lzs
    apply (subst (asm) (2) produce_inner_compose_op)
    apply (simp add: less_Suc_eq not_less_eq  LNil_eq_shift_iff split: list.splits option.splits if_splits prod.splits sum.splits)
    subgoal
      by (metis finite_produce_Nil list.size(3) lshift_simps(1) produce_inner_None_produce_inner_compose_op_None skip_n_productions_op_0)
    subgoal
      by (metis (no_types, lifting) finite_produce_Cons finite_produce_def fold_apply_old prod.collapse produce_inner_Some_produce produce_inner_compose_op_finite_produce_no_production)
    subgoal for x xs op1'
      apply hypsubst_thin
      apply (subst (asm) length_drop[symmetric])
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ lzs])
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       defer
       apply (drule meta_mp)
      subgoal
        by (metis (no_types, lifting) append_self_conv2 finite_produce_Cons finite_produce_finite_produce_drop length_Cons lshift_simps(2))
       apply simp
      apply (metis length_Cons lshift_simps(2) shift_eq_shift_drop_length)
      done
    subgoal
      by (metis append_self_conv2 finite_produce_Cons finite_produce_Nil list.size(3) lshift_simps(1) produce_inner_compose_op_finite_produce_no_production skip_n_productions_op_0)
    subgoal for x xs op''
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_spec[of _ "[]"])
      apply (drule meta_spec)
      apply (drule meta_spec)
      apply (drule meta_mp)
       apply (elim conjE)
      apply hypsubst_thin
       apply simp
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       defer
       apply (drule meta_mp)
      subgoal
        apply (simp split: prod.splits)
        apply (cases zs)
         apply simp_all
   apply (elim conjE)
        apply hypsubst_thin
        apply (smt (verit, ccfv_threshold) drop_eq_Nil2 eq_snd_iff finite_produce_Nil finite_produce_finite_produce_drop fst_conv le_eq_less_or_eq lessI order_less_trans shift_same_prefix)
        done
       apply simp_all
      done
    done
  subgoal
    apply (simp split: if_splits list.splits)
    apply (metis (no_types, lifting) drop_all finite_produce_Nil finite_produce_finite_produce_drop less_or_eq_imp_le list.distinct(1) not_less_iff_gr_or_eq prod.exhaust_sel sndI)
    done
  done

lemma produce_inner_compose_op_Inr_skip_n_productions_op:
  assumes "produce_inner_induct (compose_op (skip_n_productions_op op1 n) lgc2'', lxs) = Some (Inr lys)" (is "produce_inner_induct ?P = Some ?R")
    and "produce_inner_induct (compose_op op1 op2, lxs) = None"
    and "n = length zs"
    and "produce op1 lxs = zs @@- lzs"
    and "finite_produce op2 zs = (lgc2'', [])"
  shows False
  using assms apply (induct ?P ?R arbitrary: n zs op1 op2 lgc2'' lxs lzs lys  rule: produce_inner_alt)
  subgoal for h lxs op' n op1 lgc2'' lys zs op2 lzs
    apply (simp add: less_Suc_eq not_less_eq LNil_eq_shift_iff split: list.splits option.splits if_splits prod.splits sum.splits; (elim conjE disjE)?; hypsubst_thin)
    subgoal
      by (metis (no_types, lifting) finite_produce_finite_produce_drop length_drop prod.collapse shift_eq_shift_drop_length)
    subgoal
      by (metis (no_types, lifting) finite_produce_Nil finite_produce_finite_produce_drop list.size(3) lshift_simps(1) prod.collapse skip_n_productions_op_0)
    subgoal
      by (metis drop_eq_Nil2 finite_produce_Nil less_or_eq_imp_le list.size(3) lshift_simps(1) shift_same_prefix skip_n_productions_op_0)
    done
  subgoal
    by simp
  done

lemma produce_inner_compose_op_None_produce_shift_finite_produce: 
  "produce_inner_induct (compose_op op1 op2, lxs) = None \<Longrightarrow>
   produce op1 lxs = ys @@- lys \<Longrightarrow>
   snd (finite_produce op2 ys) = []"
  apply (induct ys arbitrary: op1 op2 lys lxs)
   apply auto[1]
  subgoal premises prems for a ys op1 op2 lys lxs
    using prems(2-) apply -
    apply simp
    apply (frule produce_inner_compose_op_apply_Nil)
     apply assumption
    apply (elim exE)
    subgoal for lgc2''
      apply (cases "produce_inner_induct (compose_op (skip_n_productions_op op1 (Suc 0)) lgc2'', lxs)")
      subgoal
        by (simp add: prems(1) produce_skip_n_productions_op_correctness)
      subgoal for r
        apply simp
        apply (cases r)
        subgoal for p
          apply (cases p)
          using produce_inner_compose_op_Inl_skip_n_productions_op[where n=1 and zs="[a]", of op1 lgc2'' lxs  _ _ _ _ op2, where lzs="ys @@- lys"] apply simp
          done
        subgoal for t
          using produce_inner_compose_op_Inr_skip_n_productions_op[where n=1 and zs="[a]", of op1 lgc2'' lxs  _ op2, where lzs="ys @@- lys"] apply simp
          done
        done
      done
    done
  done

lemma produce_inner_produce_Some:
  "produce_inner_induct (op2, produce op1 lxs) = Some (Inl (op2', x, xs, lxs')) \<Longrightarrow>
   produce_inner_induct (compose_op op1 op2, lxs) = None \<Longrightarrow> False"
  by (metis neq_Nil_conv produce_inner_compose_op_None_produce_shift_finite_produce produce_inner_to_finite_produce snd_conv)

lemma produce_inner_Inr_finite_produce:
  "produce_inner_induct (op, lxs) = Some r \<Longrightarrow>
   r = Inr op' \<Longrightarrow>
   lfinite lxs \<Longrightarrow>
   op' = fst (finite_produce op (list_of lxs))"
  apply (induct "(op, lxs)" r arbitrary: op lxs op' rule: produce_inner_alt[consumes 1])
    apply (auto simp add: finite_produce_simps split: option.splits sum.splits prod.splits list.splits)
  done


lemma produce_inner_Some_Inr_lfinite:
  "produce_inner_induct (op, lxs) = Some r \<Longrightarrow>
   r = Inr lgc' \<Longrightarrow>
   lfinite lxs"
  apply (induct "(op, lxs)" r arbitrary: op lxs rule: produce_inner_alt[consumes 1])
    apply auto
  done

lemma finite_produce_append:
  "finite_produce op (xs @ ys) = (fst (finite_produce (fst (finite_produce op xs)) ys), snd (finite_produce op xs) @ snd (finite_produce (fst (finite_produce op xs)) ys))"
  apply (induct xs arbitrary: ys op)
   apply simp
  apply (subst (1 2 4) finite_produce_simps)
  apply (auto split: prod.splits)
  done

lemma produce_compose_op_correctness_alt:
  assumes "\<forall> xs op' old out. finite_produce op2 xs = (op', out) \<longrightarrow> exit op' = LNil" 
  shows "produce (compose_op op1 op2) lxs = produce op2 (produce op1 lxs)"
  using assms
  apply (coinduction arbitrary: op1 op2 lxs rule: produce_coinduction)
  subgoal for op1 op2 lxs
    apply (subst (1 2) produce.code)
    apply (simp_all add: produce_inner_Some_Inr_compose_op split: split: option.splits sum.splits prod.splits list.splits)
    apply (intro conjI impI allI)
    using finite_produce_Nil apply blast
    subgoal
      by (smt (verit) append_self_conv2 finite_produce_Cons finite_produce_to_shift_produce fst_conv prod.collapse produce_inner_compose_op_None_produce_shift_finite_produce produce_inner_compose_op_finite_produce_no_production produce_inner_prefix_no_production produce_inner_produce_Some produce_inner_to_finite_produce snd_conv)
    subgoal
      using produce_inner_Inr_finite_produce produce_inner_Some_Inr_lfinite surjective_pairing  
      by (metis finite_produce_Cons fst_conv)
    subgoal
      by (metis list.simps(3) prod.inject produce_inner_Some_produce produce_inner_compose_op_apply_Nil)
    subgoal
      by (simp add: produce_inner_Some_Inr_compose_op)
    subgoal
      by (simp add: produce_inner_Some_Inr_compose_op)
    done
   apply fastforce
  subgoal for h ilxs op' out op1 op2 lxs
    apply clarsimp
    apply (rule exI[of _ "produce (fst (finite_produce op2 (snd (apply op1 h)))) (produce (fst (apply op1 h)) ilxs)"] conjI)+
     apply (simp split: prod.splits)
    apply (rule exI conjI refl)+
    apply safe
    apply hypsubst_thin
    apply (metis finite_produce_append fst_eqD surjective_pairing)
    done
  done


lemma produce_inner_None_not_lfinite_aux:
  "lfinite lxs \<Longrightarrow>
   produce_inner_induct (op, lxs) = None \<Longrightarrow>
   False"
  apply (induct lxs arbitrary: op rule: lfinite_induct)
  using llist.collapse(1) apply fastforce
  subgoal for lxs op
    apply (subst (asm) (2) produce_inner_induct.simps)
    apply (auto split: llist.splits prod.splits list.splits)
    done
  done


lemma produce_inner_None_not_lfinite:
  "produce_inner_induct (op, lxs) = None \<Longrightarrow>
   \<not> lfinite lxs"
  using produce_inner_None_not_lfinite_aux by blast

lemma produce_inner_produce_Inr_lfinite:
  "produce_inner_induct (op2, produce op1 lxs) = Some r \<Longrightarrow>
   r = Inr lgc' \<Longrightarrow>
   \<forall> n . produce_inner_induct (skip_n_productions_op op1 n, lxs) \<noteq> None \<Longrightarrow>
   lfinite lxs"
  apply (induct "(op2, produce op1 lxs)" r arbitrary: op1 op2 lxs lgc' rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs lgc' zs op1 lxsa lgc''
    apply (drule meta_spec[of _ "skip_n_productions_op op1 (Suc 0)"])
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
   apply (simp_all split: option.splits llist.splits prod.splits list.splits sum.splits if_splits)
  apply (subst (asm) produce.code)
  apply (simp split: option.splits llist.splits prod.splits list.splits sum.splits if_splits)
  using produce_inner_None_not_lfinite produce_inner_Some_Inr_lfinite apply blast
  done

lemma produce_compose_op_correctness:
  assumes "\<forall> n . produce_inner_induct (skip_n_productions_op op1 n, lxs) \<noteq> None"
  shows "produce (compose_op op1 op2) lxs = produce op2 (produce op1 lxs)"
  using assms
  apply (coinduction arbitrary: op1 op2 lxs rule: produce_coinduction)
  subgoal for op1 op2 lxs
    apply (subst (1) produce.code)
       apply (simp_all add: produce_inner_Some_Inr_compose_op split: list.splits prod.splits option.splits sum.splits; hypsubst_thin?)
    apply (intro conjI allI impI)
    subgoal
      by (meson produce_inner_produce_Some)
    subgoal
      by (metis option.distinct(1) produce_inner_None_not_lfinite_aux produce_inner_produce_Inr_lfinite)
    done
  subgoal for op1 op2 lxs
    by auto
  subgoal for h ilxs op' out op1 op2 lxs
    apply clarsimp
    apply (rule exI[of _ "produce (fst (finite_produce op2 (snd (apply op1 h)))) (produce (fst (apply op1 h)) ilxs)"] conjI)+
     apply (simp split: prod.splits)
    apply (rule exI conjI refl)+
    apply safe
    subgoal for n
      apply (drule spec[of _ "n + length (snd (apply op1 h))"])
      apply (auto split: if_splits list.splits)
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

lemma fst_finite_produce_skip_n_productions_op:
  "fst (finite_produce (skip_n_productions_op op n) xs) =
   skip_n_productions_op (fst (finite_produce op xs)) (n - length (snd (finite_produce op xs)))"
  apply (induct xs arbitrary: op n)
   apply auto
  done

lemma length_snd_finite_produce_skip_n_productions_op_le_n:
  "length (snd (finite_produce op xs)) < n \<Longrightarrow>
   snd (finite_produce (skip_n_productions_op op n) xs) = []"
  apply (induct xs arbitrary: op n)
   apply auto
  done

lemma snd_finite_produce_skip_n_productions_op:
  "n \<le> length (snd (finite_produce op xs)) \<Longrightarrow>
   snd (finite_produce (skip_n_productions_op op n) xs) = drop n (snd (finite_produce op xs))"
  apply (induct xs arbitrary: op n)
   apply auto
  done

lemma produce_skip_n_productions_op_compose_op[simp]:
  "\<forall> n . produce_inner_induct (skip_n_productions_op op1 n, lxs) \<noteq> None \<Longrightarrow>
   produce (skip_n_productions_op (compose_op op1 op2) n) lxs = produce (compose_op op1 (skip_n_productions_op op2 n)) lxs"
  apply (subst produce_compose_op_correctness)
   apply assumption
  apply (simp add: produce_compose_op_correctness produce_skip_n_productions_op_correctness)
  done

lemma produce_inner_Some_lfinite_produce_lfinite:
  "produce_inner_induct (op, lxs) = Some (Inl (lgc', x, xs, lxs')) \<Longrightarrow> lfinite (produce op lxs) \<Longrightarrow> lfinite lxs \<Longrightarrow> lfinite (produce lgc' lxs')"
  by simp

lemma ltake_enat_Suc[simp]:
  "ltake (enat (Suc n)) (LCons x lxs) = LCons x (ltake n lxs)"
  apply (cases n)
   apply simp
   apply (metis One_nat_def enat_0 ltake_eSuc_LCons one_eSuc one_enat_def)
  apply simp
  apply (metis eSuc_enat ltake_eSuc_LCons)
  done

lemma produce_inner_skip_n_productions_op_Suc_Nil_LNil:
  "produce_inner_induct (skip_n_productions_op op n, input_stream) = Some r \<Longrightarrow>
   r = Inl (lgc', h, xs, lxs') \<Longrightarrow>
   produce_inner_induct (skip_n_productions_op op (Suc n), input_stream) = None \<Longrightarrow>
   xs = [] \<and> produce lgc' lxs' = LNil"
  apply (induction "(skip_n_productions_op op n, input_stream)" r arbitrary: input_stream n op rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' n opc
    apply (subst (asm) (2) produce_inner_induct.simps)
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
    apply (subst (asm) (1 2) produce_inner_induct.simps)
    apply (simp split: option.splits prod.splits if_splits list.splits)
    apply safe
    apply (metis append_eq_conv_conj length_Suc_conv_rev list.inject)
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
     apply auto[1]
  using produce_inner_skip_n_productions_op_Some_Some_Some_None apply fastforce
  using produce_inner_None_not_lfinite_aux produce_inner_Some_Inr_lfinite apply blast
  using produce_inner_skip_n_productions_op_Some_None_Suc_None apply blast
  apply (metis ldropn_Suc_conv_ldropn ldropn_eq_LConsD llist.inject produce_inner_skip_n_productions_Inr_op_ldropn)
  done

lemma produce_inner_skip_n_productions_op_Suc_Inr:
  "produce_inner_induct (skip_n_productions_op op i, lxs) = Some r \<Longrightarrow>
   r = Inr op' \<Longrightarrow>
   produce_inner_induct (skip_n_productions_op op (Suc i), lxs) = Some (Inr (skip_n_productions_op op' 1))"
  by (metis produce_inner_skip_n_productions_op_Some_None_Suc skip_first_production_op_eq_skip_n_productions_op_1)

lemma fst_finite_produce_compose_op:
  "fst (finite_produce (compose_op op1 op2) xs) =
  compose_op (fst (finite_produce op1 xs)) (fst (finite_produce op2 (snd (finite_produce op1 xs))))"
  apply (induct xs arbitrary: op1 op2 )
   apply simp
  subgoal for x xs op1 op2
    by (auto simp add: finite_produce_append split: prod.splits list.splits)
  done

lemma snd_finite_produce_compose_op:
  "snd (finite_produce (compose_op op1 op2) xs) = snd (finite_produce op2 (snd (finite_produce op1 xs)))"
  apply (induct xs arbitrary: op1 op2)
   apply simp
  subgoal for x xs op1 op2
    apply (subst (1 3) finite_produce_simps)
    apply (simp add: finite_produce_append split: prod.splits list.splits)
    done
  done

lemma finite_produce_compose_op:
  "finite_produce (compose_op op1 op2) xs = (compose_op (fst (finite_produce op1 xs)) (fst (finite_produce op2 (snd (finite_produce op1 xs)))), snd (finite_produce op2 (snd (finite_produce op1 xs))))"
  by (metis fst_finite_produce_compose_op prod.collapse snd_finite_produce_compose_op)

lemma compose_op_assoc:
  "\<forall>xs op' old out. finite_produce op3 xs = (op', out) \<longrightarrow> exit op' = LNil \<Longrightarrow>
   compose_op (compose_op op1 op2) op3 = compose_op op1 (compose_op op2 op3)"
  apply (coinduction arbitrary: op1 op2 op3)
  apply (simp add: finite_produce_compose_op rel_fun_def)
  apply (rule conjI impI allI)
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

simps_of_case lconcat_simps[simp]: lconcat_code

lemma in_lset_lconcat_LNil_Nil:
  "xs \<in> lset xss \<Longrightarrow> lconcat xss = LNil \<Longrightarrow> xs = []"
  apply (induct xss arbitrary: rule: lset_induct)
   apply (subst (asm) lconcat_code)
   apply simp
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
      apply (metis Llists_Processors.lconcat_eq_LNil llist.distinct(1) lshift_simps(1) shift_in_list)
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
      apply (intro impI conjI)
      apply (metis eq_LConsD lconcat.code lshift_simps(1))
      apply (metis list.exhaust_sel shift_LCons_Cons)
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
    apply (smt (verit) empty_iff in_lset_ldropWhileD in_lset_ltlD lconcat_remove_head lhd_LCons lhd_ldropWhile lhd_ldropWhile_in_lset list.set(1) list.set_sel(2) lset_cases ltl_simps(2))
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
  apply (simp add:  eq_Nil_null split: list.splits llist.splits)
  apply (simp add: lconcat_lmap_LNil null_def)
  apply (intro allI impI)
  subgoal
    using lappend_llist_of by blast
  done

end