theory Cycles_3
  imports
    "Coinductive.Coinductive_List"
    "../Linear_Temporal_Logic_on_Llists"
    "HOL-Library.BNF_Corec"
    "HOL-Library.Code_Lazy"
    "HOL-Library.Numeral_Type"
    "HOL-Library.Simps_Case_Conv"
    "HOL-ex.Sketch_and_Explore"
    "../Llist_CCPO"
begin

(* code_lazy_type llist
 *)


codatatype ('i, 'o) op = Logic ("apply": "('i \<Rightarrow> (('i, 'o) op, 'o) res)") ("exit": "(('i, 'o) op, 'o) res")

abbreviation "produce_step op lxs \<equiv> (
   case lxs of
    LNil \<Rightarrow> (case exit op of VAL op' out \<Rightarrow> VAL (op', LNil) out | DIV lxs \<Rightarrow> DIV lxs)
  | LCons ev lxs' \<Rightarrow> (case apply op ev of VAL op' out \<Rightarrow> VAL (op', lxs') out | DIV lxs \<Rightarrow> DIV lxs))"

definition produce_res_aux where
  "produce_res_aux op lxs \<equiv> do_while (\<lambda> (op, lxs). \<not> lnull lxs) (\<lambda> (op, lxs). do {
     produce_step op lxs
  }) (op, lxs)"

lemma produce_res_aux_LNil[simp]:
  "produce_res_aux op LNil = (case exit op of VAL op' out \<Rightarrow> VAL (op', LNil) out | DIV lxs \<Rightarrow> DIV lxs)"
  by (auto simp add: produce_res_aux_def while_unfold split: res.splits)

lemma produce_res_aux_LCons[simp]:
  "produce_res_aux op (LCons x lxs) = (case apply op x of VAL op' out \<Rightarrow> VAL (op', lxs) out | DIV lxs \<Rightarrow> DIV lxs) \<bind> (while (\<lambda>(op, lxs). \<not> lnull lxs) (\<lambda>(op, y). produce_step op y))"
  apply (subst produce_res_aux_def)
  apply simp
  done
 
abbreviation "produce_res op lxs \<equiv> (case produce_res_aux op lxs of VAL (op', lxs') out \<Rightarrow> VAL op' out | DIV out \<Rightarrow> DIV out)"

definition "produce op lxs = (case produce_res op lxs of VAL op' out \<Rightarrow> llist_of out | DIV out \<Rightarrow> out)"


definition lnil_div_op where
  "lnil_div_op = Logic (\<lambda> _. DIV LNil) (DIV LNil)"

abbreviation "VAL' (x::'i) xs \<equiv> map_res (\<lambda> _. x) id (VAL (undefined::'i) xs)"

primcorec nil_val_op :: "('i, 'o) op" where
  "nil_val_op = Logic (\<lambda> _. VAL' nil_val_op []) (VAL' nil_val_op [])"

lemma nil_op_simp:
  "nil_val_op = Logic (\<lambda> _. (VAL nil_val_op [])) (VAL nil_val_op [])"
  apply (coinduction rule: op.coinduct)
  apply (clarsimp simp add: rel_fun_def)
  apply(subst nil_val_op.code)
  apply simp
  done

lemma
  "nil_val_op \<noteq> lnil_div_op"
  unfolding not_def
  apply (intro impI)
  apply (drule arg_cong[where f="exit"])
  apply (subst (asm) nil_op_simp)
  apply (subst (asm) lnil_div_op_def)
  apply simp
  done

lemma produce_res_nil_val_op[simp]:
  "produce_res nil_val_op lxs = (if lfinite lxs then VAL nil_val_op [] else DIV LNil)"
  apply (auto split: if_splits)
  subgoal
    apply (induct lxs rule: lfinite_induct)
     apply (auto simp add: lnull_def)
    apply (smt (verit) llist.exhaust_sel nil_op_simp nil_val_op.code nil_val_op.sel(1) old.prod.case op.inject produce_res_aux_LCons produce_res_aux_def res.simps(5) return_bind_res while_unfold)
    done
  subgoal
    unfolding produce_res_aux_def
    apply (induct arbitrary: lxs rule: while.fixp_induct)
    subgoal 
      apply (rule ccpo.admissibleI)
      apply (auto split: if_splits res.splits llist.splits)
      subgoal
        by (smt (verit) chain_fun chain_res_ord_res_Sup_l fun_lub_def is_VAL_def mem_Collect_eq res.distinct(1) res_Sup_def res_ord.simps(1))
      subgoal
        by (smt (verit, ccfv_SIG) chain_fun chain_lhead_lSup_eX fun_lub_def lnull_def mem_Collect_eq res.inject(2) res_Sup_empty_conv)
      done
    subgoal
      by (auto split: if_splits res.splits llist.splits)
    subgoal
      apply (auto split: if_splits res.splits llist.splits)
      subgoal
        by (metis (no_types, lifting) case_prod_conv lfinite_code(2) llist.simps(5) res.distinct(1) res.simps(5) return_bind_res)
      subgoal
        by (metis (no_types, lifting) lfinite_code(2) llist.simps(5) res.case_eq_if res.disc(2) res.sel(3) return_bind_res)
      subgoal
        by (metis (no_types, lifting) case_prod_conv lfinite_code(2) llist.simps(5) res.distinct(1) res.simps(5) return_bind_res)
      subgoal
        by (metis (no_types, lifting) lfinite_code(2) llist.simps(5) res.case_eq_if res.disc(2) res.sel(3) return_bind_res)
      done
    done
  done

primcorec id_op :: "('i, 'i) op" where
  "id_op = Logic (\<lambda> ev. VAL' id_op [ev]) (VAL' id_op [])"


lemma
  "produce_res id_op lxs = (if lfinite lxs then VAL ip_op (list_of lxs) else DIV lxs)"
  apply (auto split: if_splits)
  subgoal
    sorry
  subgoal
    unfolding produce_res_aux_def
   apply (induct rule: while.fixp_induct)
    subgoal 
      apply (rule ccpo.admissibleI)
      apply (auto split: if_splits res.splits llist.splits)
      subgoal
        by (smt (verit, best) chain_fun chain_res_ord_res_Sup_l fun_lub_def mem_Collect_eq res.distinct(1) res_Sup_not_flat res_ord.simps(1))
      subgoal
        by (smt (verit) Coinductive_List.lprefix_nitpick_simps fun_ord_def partial_function_definitions.lub_upper res.distinct(1) res_ord.elims(2) res_pfd_old)

      oops
      done
    subgoal
      unfolding produce_res_aux_def  lnull_def
      apply (subst while_unfold)
      apply (auto split: if_splits res.splits llist.splits)
      

      oops
      apply (simp add: produce_res_aux_def lnull_def while_unfold split: if_splits res.splits llist.splits)
      sledgehammer



primcorec compose_op :: "('a, 'b) op \<Rightarrow> ('b, 'c) op \<Rightarrow> ('a, 'c) op" where
  "compose_op op1 op2 = Logic (\<lambda> ev.
      map_res (case_sum (case_prod compose_op) (compose_op nil_val_op)) id (case apply op1 ev of
         VAL op1' out1 \<Rightarrow> (case produce_res op2 (llist_of out1) of VAL op2' out2' \<Rightarrow> VAL (Inl (op1', op2')) out2' | DIV lxs \<Rightarrow> DIV lxs)
       | DIV out1 \<Rightarrow> map_res Inr id (produce_res op2 out1)
       )) (map_res (case_sum (case_prod compose_op) (compose_op nil_val_op)) id (case exit op1 of
         VAL op1' out1 \<Rightarrow> (case produce_res op2 (llist_of out1) of VAL op2' out2' \<Rightarrow> VAL (Inl (op1', op2')) out2' | DIV lxs \<Rightarrow> DIV lxs)
       | DIV out1 \<Rightarrow> map_res Inr id (produce_res op2 out1)
    ))"

lemma compose_op_id_1[simp]:
  "compose_op id_op op = op"
  apply (coinduction arbitrary: op rule: op.coinduct)
  apply (auto simp add: list.rel_eq while_unfold rel_fun_def produce_res_aux_def lnull_def  split: llist.splits res.splits)
  done

lemma compose_op_id_2[simp]:
  "compose_op op id_op = op"
  apply (coinduction arbitrary: op rule: op.coinduct)
  apply (auto simp add: list.rel_eq while_unfold rel_fun_def  lnull_def  split: llist.splits res.splits)
  subgoal

      subgoal
        apply hypsubst_thin

        oops

    apply auto
    apply hypsubst_thin
    using Llist_CCPO.res.rel_intros


    find_theorems rel_res name: intr

  apply(subst nil_val_op.code)



primcorec compose_op :: "('i1, 'i1) op \<Rightarrow> ('i1, 'i1) op \<Rightarrow> ('i1, 'i1) op" where
  "compose_op op1 op2 = Logic (\<lambda> ev.
       case apply op1 ev of
         VAL op1' out1 \<Rightarrow> (case produce_res op2 (llist_of out1) of VAL op2' out2' \<Rightarrow> VAL (compose_op op1' op2') out2' | DIV lxs \<Rightarrow> DIV lxs)
       | DIV out1 \<Rightarrow> produce_res op2 out1
       )
   undefined"



corec compose_op :: "('i, 'i) op \<Rightarrow> ('i, 'i) op \<Rightarrow> ('i, 'i) op" where
  "compose_op op1 op2 = Logic (\<lambda> ev.
   bind_res (apply op1 ev) undefined)
   undefined"

end

partial_function (res) produce_inner where
  "produce_inner op lxs = (
    (case lxs of 
        LNil \<Rightarrow> VAL (Inr op) []
     | LCons h lxs' \<Rightarrow> (case apply op h of
                         DIV lxs \<Rightarrow> DIV lxs
                       | VAL op' [] \<Rightarrow> produce_inner op' lxs'
                       | VAL op' (x#xs) \<Rightarrow> VAL (Inl (op', lxs', x, xs)) [])))"
simps_of_case produce_inner_simps[simp]: produce_inner.simps
declare produce_inner.simps[code]


corec produce where
  "produce op lxs = 
    (case produce_inner op lxs of
       DIV lxs \<Rightarrow> lxs
    | VAL (Inr op') _ \<Rightarrow>  (exit op'))"

term produce_inner

lemma produce_inner_LNil_None[simp]:
  "produce_inner (op, LNil) = Some (Inr op)"
  apply simp
  done

lemma produce_inner_induct[consumes 1, case_names no_production produces terminates]:
  assumes "produce_inner op_lxs = Some y"
    and "\<And>op h lxs op' zs . apply op h = (op', LNil) \<Longrightarrow> Q (op', lxs) zs \<Longrightarrow> Q (op, LCons h lxs) zs"
    and "\<And>op h x xs lxs lxs' op' . produce_inner (op, LCons h lxs) = Some (Inl (op', x, xs, lxs')) \<Longrightarrow>
                                    apply op h = (op', LCons x xs) \<Longrightarrow> Q (op, LCons h lxs) (Inl (op', x, xs, lxs'))"
    and  "\<And>op. Q (op, LNil) (Inr op)"
  shows "Q op_lxs y"
  apply (rule produce_inner.raw_induct[OF _ assms(1)])
  apply (simp split: llist.splits prod.splits list.splits)[1]
  using assms(4) apply blast  
  using assms(2) apply blast
  apply (metis (mono_tags, lifting) assms(3) llist.case(2) prod.simps(2) produce_inner.simps)
  done

term lshift

friend_of_corec lappend where
"lappend lxs lys = (case lxs of LNil \<Rightarrow> (case lys of LNil \<Rightarrow> LNil | LCons x lxs' \<Rightarrow> LCons x lxs' )
| LCons x xs' \<Rightarrow> LCons x (lappend xs' lys))"
  by (auto split: list.splits llist.splits) (transfer_prover)

corec produce where
  "produce op lxs = 
    (case produce_inner (op, lxs) of
       None \<Rightarrow> LNil
    | Some (Inr op') \<Rightarrow> exit op'
    | Some (Inl (op', x, xs, lxs')) \<Rightarrow> LCons x (lappend xs (produce op' lxs')))"

lemma produce_LNil_exit[simp]:
  "produce op LNil = exit op"
  apply (subst produce.code)
  apply auto
  done

lemma produce_LCons[simp]:
  "produce op (LCons h lxs) = lappend (snd (apply op h)) (produce (fst (apply op h)) lxs)"
  apply (subst produce.code)
  apply (simp split: option.splits sum.splits prod.splits llist.splits)
  apply (simp add: produce.code)
  done

lemma produce_code[code]:
 "produce op lxs = (case lxs of LNil \<Rightarrow> exit op| LCons x lxs' \<Rightarrow> let (op', out) = apply op x in lappend out (produce op' lxs'))"
  apply (cases lxs)
  apply (simp_all split: prod.splits)
  done

primcorec skip_first_production_op :: "(_, 'i) op \<Rightarrow> (_, 'i) op" where
  "skip_first_production_op op = Logic (\<lambda> ev.
                                     let (lgc', out::_ llist) = apply op ev in
                                     case out of
                                      LNil \<Rightarrow> (skip_first_production_op lgc', LNil)
                                     | _ \<Rightarrow> (lgc', ltl out)) (ltl (exit op))"

primcorec skip_n_productions_op :: "(_, 'i) op \<Rightarrow> nat \<Rightarrow> (_, 'i) op" where
  "skip_n_productions_op op n = Logic (\<lambda> ev.
                                     let (lgc', out) = apply op ev in
                                       if llength out < n 
                                       then (skip_n_productions_op lgc' (n - the_enat (llength out)), LNil)
                                       else (lgc', ldrop n out)
                                     ) (ldrop n (exit op))"

lemma skip_n_productions_op_0[simp,intro]:
  "skip_n_productions_op op 0 = op"
  apply (subst skip_n_productions_op.ctr)
  using zero_enat_def apply auto
  done

lemma produce_inner_None_produce_LNil[simp]:
  "produce_inner (op, lxs) = None \<Longrightarrow>
   produce op lxs = LNil"
  apply (subst produce.code)
  apply auto
  done

(*
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

lemma skip_n_productions_op_op_eq_Suc_skip_n_productions:
  "skip_n_productions_op (skip_n_productions_op op n) 1 = skip_n_productions_op op (Suc n)"
  by (metis One_nat_def skip_first_production_op_eq_skip_n_productions_op_aux skip_n_productions_op_0)

lemma skip_first_production_op_eq_skip_n_productions_op:
  "(skip_first_production_op ^^ n) op = skip_n_productions_op op n"
  apply (induct n)
   apply (simp_all add: skip_first_production_op_eq_skip_n_productions_op_aux)
  done
*)

lemma skip_n_productions_op_sum[simp]:
  "skip_n_productions_op (skip_n_productions_op op m) n = skip_n_productions_op op (n + m)"
  sorry
(*   apply (simp flip: skip_first_production_op_eq_skip_n_productions_op)
  apply (simp add: funpow_add)
  done *)

lemma skip_first_production_op_eq_skip_n_productions_op_1:
  "skip_n_productions_op op 1 = skip_first_production_op op"
  sorry
(*   using skip_first_production_op_eq_skip_n_productions_op[where n=1 and op=op] by simp *)

lemma produce_inner_skip_n_productions_op_Suc_LCons:
  assumes "produce_inner (skip_n_productions_op op n, input_stream) = Some (Inl (lgc', h, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "produce_inner (skip_n_productions_op op (Suc n), input_stream) = Some (Inl (lgc'', h', xs', lxs''))"
  shows "LCons h' (lappend xs' (produce lgc'' lxs'')) = lappend xs (produce lgc' lxs')"
  using assms proof (induction "?P" "?R" arbitrary: input_stream n op rule: produce_inner_induct)
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
      apply (metis Suc_diff_le enat_iless enat_ord_simps(2) linorder_le_less_linear order_less_imp_not_less the_enat.simps)
      apply (simp add: Suc_diff_le)
      done
    subgoal
      by (meson Suc_ile_eq linorder_le_less_linear order_less_imp_not_less)
    subgoal
      by (metis skip_n_productions_op_0)
    done
next
  case (produces h lxs)
  then show ?case 
    apply -
    apply (subst (2) produce.corec.code)
    apply (simp split: option.splits prod.splits if_splits llist.splits)
     apply hypsubst_thin
     apply (metis eSuc_enat ileI1 ldrop_eq_LConsD verit_comp_simplify1(3))
    apply hypsubst_thin
    apply safe
    subgoal
      by (metis lappend_lnull1 ldrop_enat ldrop_eq_LConsD ldropn_Suc_conv_ldropn llist.inject lnull_ldropn nle_le)
    subgoal
      by (metis eSuc_enat ldrop_eSuc_conv_ltl ltl_simps(2))
    subgoal
      apply (subst produce.code)
      apply (simp split: sum.splits option.splits prod.splits if_splits llist.splits)
      apply (metis eSuc_enat lappend_code(2) ldrop_eSuc_conv_ltl ltl_simps(2))
      done
    done
qed

lemma produce_inner_skip_n_productions_op_Some_None_Suc:
  assumes "produce_inner (skip_n_productions_op op n, lxs) = Some (Inr lgc')" (is "produce_inner ?P = Some ?R")
  shows "produce_inner (skip_n_productions_op op (Suc n), lxs) = Some (Inr (skip_first_production_op lgc'))"
  using assms apply (induction "?P" "?R"  arbitrary: n op lxs rule: produce_inner_induct)
  subgoal
    apply (simp split: prod.splits llist.splits if_splits llist.splits)
    apply (metis (no_types, opaque_lifting) Suc_diff_le Suc_ile_eq less_enatE linorder_le_less_linear not_less_iff_gr_or_eq the_enat.simps)
    done
  subgoal
  apply (simp_all split: if_splits)
    apply hypsubst_thin
    apply (metis plus_1_eq_Suc skip_first_production_op_eq_skip_n_productions_op_1 skip_n_productions_op_sum)
    done
  done

lemma produce_inner_skip_n_productions_op_Some_Some_Some_None:
  assumes "produce_inner (skip_n_productions_op op n, lxs) = Some (Inl (lgc', h, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "produce_inner (skip_n_productions_op op (Suc n), lxs) = Some (Inr lgc'')"
  shows "produce lgc' lxs' = exit lgc'' \<and> xs = LNil"
  using assms proof (induction "?P" "?R" arbitrary: n op lxs rule: produce_inner_induct)
  case (no_production h lxs op')
  then show ?case 
    apply (clarsimp split: if_splits llist.splits)
    subgoal
      by (metis Suc_diff_le less_enatE order.strict_iff_not the_enat.simps)
    subgoal
      by force
        done
    next
  case (produces h lxs)
  then show ?case 
    apply -
    apply (simp split: prod.splits llist.splits if_splits list.splits)
    apply (subst produce.code)
     apply (clarsimp simp add: Suc_ile_eq ldrop_eq_LConsD leD split: option.splits prod.splits if_splits sum.splits)
    subgoal
      by (smt (verit) dual_order.refl ldrop_eSuc_ltl ldrop_enat ldrop_eq_LNil ltl_ldropn ltl_simps(2) option.case(2) produce.code sum.case(2))  
    done
qed

lemma produce_inner_skip_n_productions_op_Suc_skip_n_productions_op_n:
  assumes  "produce_inner (skip_n_productions_op op (Suc n), lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "produce_inner (skip_n_productions_op op n, lxs) = None"
  shows "False"
  using assms proof (induct "?P" "?R" arbitrary: n op lxs rule: produce_inner_induct)
  case (no_production h lxs op')
  then show ?case 
    apply -
    apply (simp split: if_splits llist.splits)
    subgoal
      apply (cases lxs)
      apply simp
       apply (clarsimp split: if_splits llist.splits)
      subgoal
        by (metis (no_types, lifting) Suc_diff_Suc case_prod_conv diff_Suc_Suc less_enatE llist.simps(4) no_production.hyps(2) no_production.prems produce_inner_simps(2) skip_n_productions_op.simps(1) the_enat.simps)
      subgoal
        by (metis (no_types, lifting) Suc_diff_Suc case_prod_conv diff_Suc_Suc less_enatE llist.simps(4) no_production.hyps(2) no_production.prems produce_inner_simps(2) skip_n_productions_op.simps(1) the_enat.simps)
      done
    subgoal
      by fastforce
    done
next
  case (produces h lxs)
  then show ?case 
    apply -
    apply (simp split: if_splits llist.splits prod.splits)
    apply (meson Suc_ile_eq dual_order.refl dual_order.strict_trans)
    done
qed

lemma produce_inner_skip_n_productions_op_Some_None_Suc_None:
  assumes "produce_inner (skip_n_productions_op op n, lxs) = Some (Inr lys)" (is "produce_inner ?P = Some ?R")
    and "produce_inner (skip_n_productions_op op (Suc n), lxs) = Some (Inl l)"
  shows " False"
  using assms apply (induction ?P ?R arbitrary: lxs n op rule: produce_inner_induct)
   apply (simp_all split: if_splits llist.splits)
  subgoal
    by (metis Suc_diff_le less_enatE less_or_eq_imp_le the_enat.simps)
  subgoal
    by (meson Suc_ile_eq linorder_le_less_linear order_less_imp_not_less)
  subgoal
    by fastforce
  done

lemma produce_inner_skip_n_productions_op_Suc_None_Inr_None:
  assumes  "produce_inner (skip_n_productions_op op (Suc n), lxs) = Some (Inl l)" (is "produce_inner ?P = Some ?R")
    and "produce_inner (skip_n_productions_op op n, lxs) = None"
  shows False
  using assms apply (induction ?P ?R arbitrary: lxs n op rule: produce_inner_induct)
   apply (simp_all  add: list.case_eq_if split: llist.splits if_splits; hypsubst_thin?)
  subgoal
    by (metis Suc_diff_le enat_ord_code(4) enat_ord_simps(1) enat_the_enat order_less_imp_le order_less_imp_not_less)
  subgoal
    by fastforce
  subgoal
    by (meson produce_inner_skip_n_productions_op_Suc_skip_n_productions_op_n)
  done

lemma produce_inner_Some_produce[simp]:
  "produce_inner (op, lxs) = Some (Inl (lgc', x, xs, lxs')) \<Longrightarrow>
   produce op lxs = LCons x (lappend xs (produce lgc' lxs'))"
  apply (subst produce.code)
  apply simp
  done

lemma produce_inner_Some_None_None_False:
  assumes "produce_inner (skip_n_productions_op op n, lxs) = Some (Inr lys)" (is "produce_inner ?P = Some ?R")
    and "produce_inner (op, lxs) = None"
  shows False
  using assms apply (induct ?P ?R arbitrary: n op lxs rule: produce_inner_induct)
   apply (simp_all split: prod.splits llist.splits if_splits)
   apply auto[1]
  apply (metis skip_n_productions_op_0)
  done

lemma produce_inner_None_Some_None_False:
  assumes "produce_inner (op, lxs) = Some (Inr lys)" (is "produce_inner ?P = Some ?R")
    and "produce_inner (skip_n_productions_op op n, lxs) = None"
  shows False
  using assms apply (induct ?P ?R arbitrary: n op lxs  rule: produce_inner_induct)
   apply (simp_all split: if_splits)
   apply auto[1]
  apply (metis skip_n_productions_op_0)
  done

lemma produce_inner_skip_n_productions_op_Some_llength_le:
  assumes "produce_inner (skip_n_productions_op op n, lxs) = Some (Inl (lgc'', y, ys, lxs''))" (is "produce_inner ?P = Some ?R")
    and "llength (produce op lxs) \<le> enat n"
  shows False
  using assms  apply (induct ?P ?R arbitrary: n y ys lxs'' op lxs lgc'' rule: produce_inner_induct)
   apply (simp_all split: prod.splits llist.splits llist.splits sum.splits option.splits if_splits)
  subgoal
    using iadd_le_enat_iff by fastforce
  subgoal
    by (metis enat_0 le_numeral_extra(3) llength_LNil llist.disc(1) llist.expand skip_n_productions_op_0)
  subgoal
    by (metis dual_order.trans enat_le_plus_same(1) ldrop_eq_LConsD nless_le)
  done

lemma produce_inner_skip_n_productions_op_Some_produce_inner_None:
  assumes "produce_inner (skip_n_productions_op op n, lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "produce_inner (op, lxs) = None" shows False
  using assms apply (induct ?P ?R arbitrary: n xs op lxs x  lxs' lgc' rule: produce_inner_induct)
   apply (simp_all split: if_splits prod.splits llist.splits)
   apply auto[1]
  apply (metis skip_n_productions_op_0)
  done

lemma produce_inner_skip_n_productions_op_Some_produce_inner_Some_None:
  assumes "produce_inner (skip_n_productions_op op n, lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "produce_inner (op, lxs) = Some (Inr lys)"
  shows False
  using assms apply (induct ?P ?R arbitrary: n xs op lxs x  lxs' lgc' rule: produce_inner_induct)
   apply (simp_all split: if_splits prod.splits llist.splits)
   apply fast
  apply (metis skip_n_productions_op_0)
  done

lemma produce_inner_Some_produce_inner_skip_n_productions_op_Suc_n_None:
  assumes "produce_inner (skip_n_productions_op op n, lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "produce_inner (skip_n_productions_op op (Suc n), lxs) = None"
  shows "llength (produce op lxs) = enat (Suc n)"
  using assms apply (induct ?P ?R arbitrary: n op lxs lxs' x xs rule: produce_inner_induct)
   apply (simp_all split: if_splits prod.splits llist.splits)
  subgoal
    by (smt (verit, ccfv_threshold) add_Suc_right add_diff_cancel_left' less_enatE less_imp_Suc_add plus_enat_simps(1) the_enat.simps)
  subgoal
    by (metis One_nat_def eSuc_enat one_enat_def plus_1_eSuc(2) skip_n_productions_op_0)
  subgoal
    by (meson Suc_ile_eq ldrop_eq_LConsD leD)
  done

lemma produce_inner_skip_n_productions_op_Some_None_aux:
  "produce_inner (skip_n_productions_op op n, lxs) = Some r \<Longrightarrow>
   produce_inner (op, lxs) = None \<Longrightarrow> False"
  by (metis obj_sumE prod_cases4 produce_inner_Some_None_None_False produce_inner_skip_n_productions_op_Some_produce_inner_None)

lemma produce_inner_skip_n_productions_op_Some_None[simp]:
  "produce_inner (op, lxs) = None \<Longrightarrow>
   produce_inner (skip_n_productions_op op n, lxs) = None"
  using produce_inner_skip_n_productions_op_Some_None_aux by fastforce

lemma produce_inner_skip_n_productions_op_Suc_Some_None_False:
  "produce_inner (skip_n_productions_op op (Suc n), lxs) = Some r \<Longrightarrow>
   produce_inner (skip_n_productions_op op n, lxs) = None \<Longrightarrow>
   False"
  apply (induct "(skip_n_productions_op op (Suc n), lxs)" r arbitrary: n op lxs rule: produce_inner_induct)
  subgoal
    apply (simp split: prod.splits if_splits llist.splits)
    subgoal
      by (metis Suc_diff_le less_enatE less_or_eq_imp_le the_enat.simps)
    subgoal
      by (metis skip_n_productions_op_0)
    done
  subgoal
    apply (simp split: prod.splits if_splits llist.splits)
    apply (meson Suc_ile_eq linorder_le_less_linear not_less_iff_gr_or_eq)
    done
  apply auto
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
  assumes "produce_inner (op, lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "produce_inner (skip_n_productions_op op n, lxs) = Some (Inl l)"
    and "eSuc (llength (lappend xs (produce lgc' lxs'))) \<le> enat n"
  shows False
  using assms proof (induct ?P ?R arbitrary: n op lxs lxs' x xs lgc' rule: produce_inner_induct)
  case (no_production op h lxs op')
  then show ?case 
    apply (simp split: prod.splits if_splits list.splits sum.splits option.splits)
     apply force+
    done
next
  case (produces op h x xs lxs lxs' op')
  then show ?case 
    apply (simp split: prod.splits if_splits llist.splits sum.splits option.splits)
    subgoal
      by (metis llength_LCons prod_cases4 produce_inner_Some_produce produce_inner_skip_n_productions_op_Some_llength_le produces.hyps(1) produces.prems(1) produces.prems(2))
    subgoal
      by (metis (no_types, opaque_lifting) add.right_neutral co.enat.sel(2) eSuc_ile_mono enat_add1_eq enat_le_plus_same(1) epred_enat ldropn_0 ldropn_eq_LNil llist.simps(3) nle_le prod_cases4 produce_inner_Some_produce zero_enat_def)
    subgoal
      by (metis antisym_conv2 eSuc_ile_mono enat_le_plus_same(1) llength_LCons llist.disc(2) lnull_ldrop order_le_less_trans)
    done
qed

lemma produce_inner_skip_n_productions_op_None_le:
  "produce_inner (skip_n_productions_op op n, lxs) = None \<Longrightarrow> llength (produce op lxs) \<le> enat n"
proof (induct n arbitrary: lxs op)
  case 0
  then show ?case by simp
next
  case (Suc n lxs op)
  then show ?case 
  proof (cases "produce_inner (skip_n_productions_op op n, lxs)")
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
  assumes "produce_inner (skip_n_productions_op op n, lxs) = Some (Inr lys)" (is "produce_inner ?P = Some ?R")
    and "lnull (exit lys)"
  shows "llength (produce op lxs) \<le> enat n"
  using assms proof (induct ?P ?R arbitrary: n op lxs rule: produce_inner_induct)
  case (no_production h lxs op')
  then show ?case 
    apply (simp split: if_splits)
    subgoal
      by (metis ldropn_eq_LNil ldropn_lappend llength_lappend not_less_iff_gr_or_eq)
    subgoal
      by (metis enat_0 ile0_eq llength_eq_0 skip_n_productions_op_0)
    done
next
  case terminates
  then show ?case by force
qed

lemma produce_inner_skip_n_productions_op_Some_Inr_le_lnull:
  assumes "produce_inner (skip_n_productions_op op n, lxs) = Some (Inr lys)" (is "produce_inner ?P = Some ?R")
    and "llength (produce op lxs) \<le> enat n"
  shows  "lnull (exit lys)"
  using assms proof (induct ?P ?R arbitrary: n op lxs rule: produce_inner_induct)
  case (no_production h lxs op')
  then show ?case 
    apply (simp split: if_splits)
    subgoal
      by (metis ldropn_eq_LNil ldropn_lappend llength_lappend not_less_iff_gr_or_eq)
    subgoal
      by (metis enat_0 ile0_eq llength_eq_0 skip_n_productions_op_0)
    done
next
  case terminates
  then show ?case by force
qed

lemma produce_inner_skip_n_productions_op_Inl_lnth:
  assumes  "produce_inner (skip_n_productions_op op n, lxs) = Some (Inl (lgc', y, ys, lys))" (is "produce_inner ?P = Some ?R")
    and "n < llength (produce op lxs)"
  shows "y = lnth (produce op lxs) n"
  using assms proof (induct ?P ?R arbitrary: n op lxs rule: produce_inner_induct)
  case (no_production h lxs op')
  then show ?case 
    apply (simp split: if_splits)
    subgoal
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      apply (metis ldropn_eq_LNil ldropn_lappend2 no_production.prems order.strict_iff_order produce_LCons verit_comp_simplify1(3))
      apply simp
      apply (metis lnth_lappend order_less_imp_triv)
      done
    subgoal
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (simp_all add: enat_0 llength_shift)
      apply (metis diff_is_0_eq less_or_eq_imp_le lnth_lappend2)
      done
    done
next
  case (produces h lxs)
  then show ?case 
    apply (simp split: if_splits)
    apply (metis ldrop_enat ldrop_eq_LConsD ldropn_Suc_conv_ldropn lnth_0 lnth_lappend1)
    done
qed

lemma produce_inner_skip_n_productions_Inr_op_ldropn:
  assumes "produce_inner (skip_n_productions_op op n, lxs) = Some (Inr y)" (is "produce_inner ?P = Some ?R")
  shows "exit y = ldropn n (produce op lxs)"
  using assms proof (induct ?P ?R arbitrary: n op lxs rule: produce_inner_induct)
  case (no_production h lxs op')
  then show ?case 
    apply (simp add: ldropn_shift ldropn_lappend2 split: if_splits)
    subgoal
      by (metis ldropn_0 skip_n_productions_op_0)
    done
next
  case terminates
  then show ?case 
    by (auto simp add: ldrop_enat)
qed

lemma produce_inner_skip_n_productions_op_llength_LNil:
  assumes  "produce_inner (skip_n_productions_op op n, lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "\<not> llength (produce op lxs) \<le> enat n"
    and "produce_inner (skip_n_productions_op op (Suc n), lxs) = None"
  shows "lappend xs (produce lgc' lxs') = LNil" 
  using assms proof (induct ?P ?R arbitrary: op lxs x xs lxs' n rule: produce_inner_induct)
  case (no_production h lxs op')
  then show ?case 
    apply (simp split: if_splits llist.splits)
    subgoal
      by (metis Suc_diff_le enat_ord_code(4) enat_ord_simps(1) enat_the_enat ldropn_eq_LNil ldropn_lappend no_production.prems(1) order_less_imp_le order_less_imp_not_less produce_LCons)
    subgoal
      by (metis le_zero_eq llength_eq_0 skip_n_productions_op_0 zero_enat_def)
    done
next
  case (produces h x xs lxs lxs')
  then show ?case 
    apply (simp split: if_splits llist.splits)
    subgoal
      by (meson Suc_ile_eq ldrop_eq_LConsD leD)
    subgoal
      by (metis dual_order.refl eSuc_enat eq_LConsD ldrop_all ldrop_eSuc_conv_ltl)
    done
qed

theorem produce_skip_n_productions_op_correctness:
  "produce (skip_n_productions_op op n) lxs = ldropn n (produce op lxs)"
proof (coinduction arbitrary: op lxs n rule: llist.coinduct_upto)
  case (Eq_llist op' lxs' n')
  then show ?case 
    apply (intro conjI impI)
    subgoal
      apply (subst (1 2) produce.code)
      apply (simp split: prod.splits llist.splits option.splits sum.splits)
      apply (intro impI allI conjI)
      subgoal
        by (metis (no_types, lifting) llength_LCons llength_lappend produce_inner_Some_produce produce_inner_skip_n_productions_op_None_le)
      subgoal
        by (metis llength_lappend produce_inner_Some_produce_inner_skip_n_productions_op_le_False)
      subgoal
        by (simp add: produce_inner_skip_n_productions_Inr_op_ldropn)
      subgoal
        using produce_inner_None_Some_None_False by blast
      subgoal
        by (meson produce_inner_skip_n_productions_op_Some_produce_inner_Some_None)
      subgoal
        by (simp add: produce.code produce_inner_skip_n_productions_Inr_op_ldropn)
      done
    subgoal
      apply (subst (1 2) produce.code)
      apply (simp add: split: prod.splits list.splits option.splits sum.splits)
      apply (intro impI allI conjI)
           apply simp_all
      subgoal
        by (metis (no_types, lifting) lhd_ldropn linorder_not_less llength_LCons llength_lappend produce_inner_Some_produce produce_inner_skip_n_productions_op_Inl_lnth)
      subgoal
        by (simp add: produce_inner_skip_n_productions_Inr_op_ldropn)
      subgoal
        by (meson produce_inner_skip_n_productions_op_Some_produce_inner_Some_None)
      subgoal
        by (simp add: produce.code produce_inner_skip_n_productions_Inr_op_ldropn)
      done
    subgoal
      apply (simp add: ldrop_eSuc_ltl ltl_ldropn)
      apply (rule lappend.cong_base)
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
          by (metis lappend_code(1) produce_inner_skip_n_productions_op_Some_Some_Some_None)
        subgoal
          by (simp add: produce_inner_skip_n_productions_op_Some_None_Suc)
        subgoal
          using produce_inner_skip_n_productions_op_Some_None_Suc_None by blast
        subgoal
          using produce_inner_skip_n_productions_op_Some_None_Suc by fastforce
        done
      by (simp add: ldrop_eSuc_ltl ltl_ldropn)
    done
qed

 definition "finite_produce op xs = fold (\<lambda> ev (op, out) . let (lgc', out') = apply op ev in (lgc', lappend out out')) xs (op, LNil)"
 
(* 
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
  done  *)


lemma finite_produce_simps:
  "finite_produce op xs = (case xs of
                                 [] \<Rightarrow> (op, LNil)
                                | (x#xs) \<Rightarrow>
                                   (let (lgc', out) = apply op x in 
                                   (fst (finite_produce lgc' xs), lappend out (snd (finite_produce lgc' xs)))))"
  unfolding finite_produce_def
  apply (induct xs arbitrary: op)
   apply simp
  subgoal for h xs op
    apply (clarsimp split: prod.splits list.splits llist.splits prod.splits)
    sorry
  done

lemma finite_produce_Nil[simp]:
  "finite_produce op [] = (op, LNil)"
  apply (subst finite_produce_simps)
  apply simp
  done

lemma finite_produce_Cons[simp]:
  "finite_produce op (x # xs) = (fst (finite_produce (fst (apply op x)) xs), lappend (snd (apply op x)) (snd (finite_produce (fst (apply op x)) xs)))"
  apply (subst finite_produce_simps)
  apply (auto split: prod.splits)
  done

lemma
  "apply op1 x = (op1', lys) \<Longrightarrow>
   \<not> lfinite lys \<Longrightarrow>
   produce op2 (produce op1 (LCons x lxs)) = produce op2 lys"
  apply (simp add: lappend_inf)
  done

lemma
  "produce_inner (op1, lxs) = Some (Inl (op1', x, xs, lxs')) \<Longrightarrow>
   \<not> lfinite xs \<Longrightarrow>
   produce op2 (produce op1 lxs) = produce op2 (LCons x xs)"
  apply (subst (2) produce.code)
  apply (auto simp add: llist.splits prod.splits lappend_inf)
  done

primcorec nil_val_op where "nil_val_op = Logic (\<lambda> ev . (nil_val_op, LNil)) LNil"

lemma produce_inner_nil_op_Inl:
  assumes "produce_inner (nil_val_op, lxs) = Some (Inl (op, x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
  shows False
  using assms apply (induct ?P ?R arbitrary: lxs  rule: produce_inner_induct)
   apply auto
  done

lemma produce_inner_nil_op_Inr:
  assumes "produce_inner (nil_val_op, lxs) = Some (Inr op)" (is "produce_inner ?P = Some ?R")
  shows "exit op = LNil"
  using assms apply (induct ?P ?R arbitrary: lxs  rule: produce_inner_induct)
   apply auto
  done


lemma produce_nil_op[simp]:
  "produce nil_val_op lxs = LNil"
  apply (subst produce.code)
  by (auto dest: produce_inner_nil_op_Inl produce_inner_nil_op_Inr split: option.split sum.splits)

primcorec compose_op where
  "compose_op op1 op2 = Logic (\<lambda> ev.
       let (op1', out) = apply op1 ev in
       (if lfinite out
         then let (op2', out') = finite_produce op2 (list_of out) in
         (compose_op op1' op2', out')
         else (nil_val_op, produce op2 out)))
   (produce op2 (exit op1))"

lemma
  assumes "produce_inner (op1, lxs) = Some (Inl (op1', x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "\<not> lfinite xs"
  shows "produce (compose_op op1 op2) lxs = produce op2 (LCons x xs)"
  using assms apply (induct ?P ?R arbitrary: op1 op2 lxs  rule: produce_inner_induct)
  subgoal
    by (auto split: llist.splits prod.splits)
  subgoal for op h lxs op2
    apply (clarsimp split: llist.splits prod.splits)
    done
  done

lemma produce_inner_compose_op_Some_produce_inner_None:
  "produce_inner (compose_op op1 op2, lxs) = Some r \<Longrightarrow>
   produce_inner (op1, lxs) = None \<Longrightarrow> False"
  apply (induct "(compose_op op1 op2, lxs)" r arbitrary: op1 op2 lxs rule: produce_inner_induct)
    apply (auto split: prod.splits list.splits llist.splits)
  done

lemma produce_inner_None_produce_inner_compose_op_None[simp]:
  "produce_inner (op1, lxs) = None \<Longrightarrow> produce_inner (compose_op op1 op2, lxs) = None"
  using produce_inner_compose_op_Some_produce_inner_None by fastforce

lemma produce_inner_compose_op_finite_produce_no_production[simp]:
  assumes "produce_inner (op1, lxs) = Some (Inl (op1', x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "lfinite xs"
    and "finite_produce op2 (x#(list_of xs)) = (op2', LNil)"
  shows "produce_inner (compose_op op1 op2, lxs) = produce_inner (compose_op op1' op2', lxs')"
  using assms apply (induct ?P ?R arbitrary: op1 op2 lxs rule: produce_inner_induct)
   apply (auto split: option.splits list.splits llist.splits prod.splits)
  done

lemma produce_inner_LCons_Some_cases:
  "produce_inner (op1, LCons h hs) = Some (Inl (op, x, xs, lxs')) \<Longrightarrow>
   (apply op1 h = (op, LCons x xs) \<and> lxs' = hs) \<or> produce_inner (fst (apply op1 h), hs) = Some (Inl (op, x, xs, lxs'))"
  apply (subst (asm) produce_inner.simps)
  apply (auto split: prod.splits llist.splits list.splits)
  done

lemma produce_inner_Some_Inl_compose_op:
  assumes "produce_inner (op1, lxs) = Some (Inl (lgc', x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "lfinite xs"
    and "finite_produce op2 (x # (list_of xs)) = (lgc'', LCons y ys)"
  shows "produce_inner (compose_op op1 op2, lxs) = Some (Inl (compose_op lgc' lgc'', y, ys, lxs'))"
  using assms apply (induct ?P ?R arbitrary: op1 op2 lxs rule: produce_inner_induct)
   apply auto
  done

        
lemma produce_inner_Some_Inr_compose_op:
  assumes "produce_inner (op1, lxs) = Some (Inr lgc')" (is "produce_inner ?P = Some ?R")
  shows "produce_inner (compose_op op1 op2, lxs) = Some (Inr (compose_op lgc' op2))"
  using assms apply (induct ?P ?R arbitrary: op1 op2 lxs rule: produce_inner_induct)
   apply auto
  done

lemma not_lfinite_produce_inner_Some_Inl_compose_op:
  assumes "produce_inner (op1, lxs) = Some (Inl (op1', x, xs, lxs'))" (is "produce_inner ?P = Some ?R")
    and "\<not> lfinite xs"
  shows "produce_inner (compose_op op1 op2, lxs) = produce_inner (op2, LCons x xs)"
  using assms apply (induct ?P ?R arbitrary: op1 op2 lxs  rule: produce_inner_induct)
  subgoal
    by (auto split: llist.splits prod.splits)
  subgoal for op h lxs op2
    apply (auto split: llist.splits prod.splits)
    subgoal
      apply (subst (asm) produce.code)
    apply (auto split: llist.splits option.splits prod.splits sum.splits)
      subgoal
        apply hypsubst_thin
        sorry
      oops
   

lemma produce_inner_compose_op:
  "produce_inner (compose_op op1 op2, lxs) =
   (case (produce_inner (op1, lxs)) of
      None \<Rightarrow> None
    | Some (Inr lgc') \<Rightarrow> Some (Inr (compose_op lgc' op2))
    | Some (Inl (op, x, xs, lxs')) \<Rightarrow> (
      if lfinite xs
      then let (lgc', out) = finite_produce op2 (x#list_of xs) in
      (case out of 
         LNil \<Rightarrow> produce_inner (compose_op op lgc', lxs') 
       | LCons y ys \<Rightarrow> Some (Inl (compose_op op lgc', y, ys, lxs')))
      else produce_inner (op2, LCons x xs) ))"
  apply (cases "produce_inner (op1, lxs)")
   apply simp
  subgoal for p
    apply (cases p)
     apply simp
     apply hypsubst_thin
    subgoal for p
      apply (cases p)
      apply hypsubst_thin
      apply simp
      subgoal for op' y lys lzs
        apply (cases "lfinite lys")
        subgoal
          by (clarsimp simp add: produce_inner_Some_Inl_compose_op split: llist.splits if_splits prod.splits list.splits)
        subgoal
          apply  (auto simp add:  split: llist.splits if_splits prod.splits list.splits)

          oops

lemma finite_produce_LCons_Nil:
  "finite_produce op (x # xs) = (lgc', LNil) \<Longrightarrow>
   apply op x = (lgc'', LNil) \<Longrightarrow> finite_produce lgc'' xs = (lgc', LNil)"
  apply (subst (asm) finite_produce_simps)
  apply simp
  done

lemma produce_inner_prefix_no_production:
  "produce_inner (op, xs @@- lxs) = Some (Inl (lgc', y, ys, lxs')) \<Longrightarrow>
   finite_produce op xs = (lgc'', LNil) \<Longrightarrow>
   produce_inner (lgc'', lxs) = Some (Inl (lgc', y, ys, lxs'))"
  apply (induct xs arbitrary: op)
   apply (simp_all split: option.splits llist.splits list.splits prod.splits)
  subgoal
    by (metis prod.collapse)
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
    and nonterm: "\<And>op ilxs olxs. P op ilxs olxs \<Longrightarrow> produce_inner (op, ilxs) = None \<Longrightarrow> olxs = LNil"
    and exit: "\<And>op olxs. P op LNil olxs \<Longrightarrow> olxs = exit op"
    and step: "\<And>op h ilxs olxs op' out.
    P op (LCons h ilxs) olxs \<Longrightarrow> apply op h = (op', out) \<Longrightarrow> \<exists>olxs'. olxs = lappend out olxs' \<and> P op' ilxs olxs'"
  shows "produce op ilxs = olxs"
proof -
  have coind: "\<And>op ilxs olxs. P op ilxs olxs \<Longrightarrow>
    (case produce_inner (op, ilxs) of None \<Rightarrow> olxs = LNil
       | Some (Inl (op', x, xs, ilxs')) \<Rightarrow> \<exists>olxs'. olxs = LCons x (lappend xs olxs') \<and> P op' ilxs' olxs'
       | Some (Inr op') \<Rightarrow> olxs = exit op')"
    apply (simp split: option.splits sum.splits)
    apply (intro conjI allI impI)
    subgoal
      by (rule nonterm)
    subgoal for op ilxs olxs op' x xs ilxs'
      apply (drule produce_inner_induct[where Q="\<lambda>(op, ilxs) zs. 
      case zs of Inl (op', x, xs, ilxs') \<Rightarrow> \<forall>olxs. P op ilxs olxs \<longrightarrow> (\<exists>olxs'. olxs = LCons x (lappend xs olxs') \<and> P op' ilxs' olxs') | Inr op' \<Rightarrow> True"])
         apply (auto dest!: step split: option.splits sum.splits)
      done
    subgoal for op ilxs olxs op'
      apply (drule produce_inner_induct[where Q="\<lambda>(op, ilxs) zs. 
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
     apply (metis (mono_tags, lifting) lappend.cong_base lappend.cong_lappend lappend.cong_refl)
    using lappend.cong_refl apply blast
    done
qed


lemma finite_produce_to_shift_produce:
  "finite_produce op xs = (lgc', zs) \<Longrightarrow>
   produce op (xs @@- lxs) = lappend zs (produce lgc' lxs)"
  apply (induct xs arbitrary: op lxs zs)
   apply simp
  subgoal for a xs op lxs zs
    apply (simp split: prod.splits list.splits option.splits)
    apply (metis fst_swap lappend_assoc prod.swap_def swap_swap)
    done
  done

(* lemma produce_lshift[simp]: 
  "produce op (xs @@- lxs) = (let (op', out) = finite_produce op xs in out @@- produce op' lxs)"
  apply (induct xs arbitrary: op)
   apply (auto simp: split: prod.splits list.splits)
  done *)


lemma produce_inner_compose_op_apply_Nil:
  "produce_inner (compose_op op1 op2, lxs) = None \<Longrightarrow>
   produce op1 lxs = LCons y lys \<Longrightarrow>
   \<exists> op2' . apply op2 y = (op2', LNil)"
  apply (subst (asm) produce.code)
  apply (simp split: option.splits prod.splits list.splits sum.splits)
  oops
(*   apply (subst (asm) produce_inner_compose_op)
  apply (simp split: prod.splits list.splits)
  apply (subst (asm) finite_produce_simps)
  apply (simp split: prod.splits sum.splits list.splits)
  done *)


lemma produce_inner_to_finite_produce:
  "produce_inner (op, lxs) = Some r \<Longrightarrow>
   r = Inl (lgc', x, xs, lxs') \<Longrightarrow>
   \<exists> zs. lxs = zs @@- lxs' \<and> finite_produce op zs = (lgc', LCons x xs)"
  apply (induct "(op, lxs)" r arbitrary: op lxs lgc' x xs lxs'  rule: produce_inner_induct)
  subgoal for op h lxs' lgc' lgc'a x xs lxs''
    apply (simp split: option.splits prod.splits list.splits)
    oops
(*     apply (metis finite_produce_Cons finite_produce_def fst_eqD lshift_simps(2) snd_eqD)
    done
   apply simp_all
  apply (metis append.right_neutral finite_produce_Cons finite_produce_Nil fst_conv lshift_simps(1) lshift_simps(2) snd_conv)
  done
 *)

(* lemma finite_produce_finite_produce_drop:
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
 *)

lemma produce_inner_compose_op_Inl_skip_n_productions_op:
  assumes  "produce_inner (compose_op (skip_n_productions_op op1 n) lgc2'', lxs) = Some (Inl (lgc', y, ys, lys))" (is "produce_inner ?P = Some ?R")
    and "produce_inner (compose_op op1 op2, lxs) = None"
    and "n = length zs"
    and "produce op1 lxs = zs @@- lzs"
    and "finite_produce op2 zs = (lgc2'', LNil)"
  shows  False
  using assms
  apply (induct ?P ?R arbitrary: n zs op1 op2 lgc2'' lxs ys y lys lzs rule: produce_inner_induct)
  subgoal for h lxs op' n op1 lgc2'' ys y lys zs op2 lzs
(*     apply (subst (asm) (2) produce_inner_compose_op)
 *)
    apply (simp add: less_Suc_eq not_less_eq  LNil_eq_shift_iff split: llist.splits option.splits if_splits prod.splits sum.splits)
    subgoal
      apply hypsubst_thin
      oops
(* 
      oops
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
  done *)

lemma produce_inner_compose_op_Inr_skip_n_productions_op:
  assumes "produce_inner (compose_op (skip_n_productions_op op1 n) lgc2'', lxs) = Some (Inr lys)" (is "produce_inner ?P = Some ?R")
    and "produce_inner (compose_op op1 op2, lxs) = None"
    and "n = length zs"
    and "produce op1 lxs = zs @@- lzs"
    and "finite_produce op2 zs = (lgc2'', LNil)"
  shows False
  using assms apply (induct ?P ?R arbitrary: n zs op1 op2 lgc2'' lxs lzs lys  rule: produce_inner_induct)
  subgoal for h lxs op' n op1 lgc2'' lys zs op2 lzs
    apply (simp add: less_Suc_eq not_less_eq LNil_eq_shift_iff split: llist.splits option.splits if_splits prod.splits sum.splits; (elim conjE disjE)?; hypsubst_thin)
    oops
(*     subgoal
      by (metis (no_types, lifting) finite_produce_finite_produce_drop length_drop prod.collapse shift_eq_shift_drop_length)
    subgoal
      by (metis (no_types, lifting) finite_produce_Nil finite_produce_finite_produce_drop list.size(3) lshift_simps(1) prod.collapse skip_n_productions_op_0)
    subgoal
      by (metis drop_eq_Nil2 finite_produce_Nil less_or_eq_imp_le list.size(3) lshift_simps(1) shift_same_prefix skip_n_productions_op_0)
    done
  subgoal
    by simp
  done *)

lemma produce_inner_compose_op_None_produce_shift_finite_produce: 
  "produce_inner (compose_op op1 op2, lxs) = None \<Longrightarrow>
   produce op1 lxs = ys @@- lys \<Longrightarrow>
   snd (finite_produce op2 ys) = LNil"
  apply (induct ys arbitrary: op1 op2 lys lxs)
   apply auto[1]
  subgoal premises prems for a ys op1 op2 lys lxs
    using prems(2-) apply -
    apply simp
    oops
(*     apply (frule produce_inner_compose_op_apply_Nil)
     apply assumption
    apply (elim exE)
    subgoal for lgc2''
      apply (cases "produce_inner (compose_op (skip_n_productions_op op1 (Suc 0)) lgc2'', lxs)")
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
  done *)

(* lemma produce_inner_produce_Some:
  "produce_inner (op2, produce op1 lxs) = Some (Inl (op2', x, xs, lxs')) \<Longrightarrow>
   produce_inner (compose_op op1 op2, lxs) = None \<Longrightarrow> False"
  by (metis neq_Nil_conv produce_inner_compose_op_None_produce_shift_finite_produce produce_inner_to_finite_produce snd_conv) *)

lemma produce_inner_Inr_finite_produce:
  "produce_inner (op, lxs) = Some r \<Longrightarrow>
   r = Inr op' \<Longrightarrow>
   lfinite lxs \<Longrightarrow>
   op' = fst (finite_produce op (list_of lxs))"
  apply (induct "(op, lxs)" r arbitrary: op lxs op' rule: produce_inner_induct)
    apply (auto simp add: finite_produce_simps split: option.splits sum.splits prod.splits list.splits)
  done


lemma produce_inner_Some_Inr_lfinite:
  "produce_inner (op, lxs) = Some r \<Longrightarrow>
   r = Inr lgc' \<Longrightarrow>
   lfinite lxs"
  apply (induct "(op, lxs)" r arbitrary: op lxs rule: produce_inner_induct)
    apply auto
  done

lemma finite_produce_append:
  "finite_produce op (xs @ ys) = (fst (finite_produce (fst (finite_produce op xs)) ys), lappend (snd (finite_produce op xs)) (snd (finite_produce (fst (finite_produce op xs)) ys)))"
  apply (induct xs arbitrary: ys op)
   apply simp
  apply (subst (1 2 4) finite_produce_simps)
  apply (auto split: prod.splits)
  apply (simp add: lappend_assoc)
  done

lemma produce_lappend:
  "produce op (lappend lxs lys) =
  (if lfinite lxs 
   then let (op', out) = finite_produce op (list_of lxs) in
   lappend out (produce op' lys)
   else produce op lxs)"
  apply (auto split: if_splits)
  subgoal 
    apply (induct lxs arbitrary: op lys rule: lfinite_induct)
     apply (auto simp add: lnull_def split: prod.splits)
    by (metis finite_produce_to_shift_produce lappend_llist_of llist_of_list_of)
  subgoal
    by (simp add: lappend_inf)
  done

lemma produce_compose_op_correctness_alt:
  assumes "\<forall> xs op' old out. finite_produce op2 xs = (op', out) \<longrightarrow> exit op' = LNil" 
  shows "produce (compose_op op1 op2) lxs = produce op2 (produce op1 lxs)"
  using assms
  apply (coinduction arbitrary: op1 op2 lxs rule: produce_coinduction)
  subgoal for op1 op2 lxs
    apply (subst (1 2) produce.code)
    apply (simp_all add: produce_inner_Some_Inr_compose_op split: split: llist.splits option.splits sum.splits prod.splits list.splits)
    apply (intro conjI impI allI)
    using finite_produce_Nil apply blast
    subgoal
      apply hypsubst_thin
      sorry
(*       by (smt (verit) append_self_conv2 finite_produce_Cons finite_produce_to_shift_produce fst_conv prod.collapse produce_inner_compose_op_None_produce_shift_finite_produce produce_inner_compose_op_finite_produce_no_production produce_inner_prefix_no_production produce_inner_produce_Some produce_inner_to_finite_produce snd_conv)
 *)
      subgoal
      using produce_inner_Inr_finite_produce produce_inner_Some_Inr_lfinite surjective_pairing  
      by (metis finite_produce_Cons fst_conv)
    subgoal
      sorry

(*       by (metis list.simps(3) prod.inject produce_inner_Some_produce produce_inner_compose_op_apply_Nil)
 *)
      subgoal
      by (simp add: produce_inner_Some_Inr_compose_op)
    subgoal
      by (simp add: produce_inner_Some_Inr_compose_op)
    done
   apply fastforce
  subgoal for h ilxs op' out op1 op2 lxs
    apply (clarsimp split: if_splits)
    subgoal
      apply (rule exI[of _ "produce (fst (finite_produce op2 (list_of (snd (apply op1 h))))) (produce (fst (apply op1 h)) ilxs)"] conjI)+
      apply (metis finite_produce_to_shift_produce lappend_llist_of llist_of_list_of prod.collapse)
    apply (rule exI conjI refl)+
    apply safe
    apply hypsubst_thin
    apply (metis finite_produce_append fst_eqD surjective_pairing)
      done
    subgoal
      apply (simp add: produce_lappend)
      apply (rule exI[of _ "LNil"] conjI)+
       apply simp_all
            apply (rule exI[of _ "nil_val_op"])+
      apply auto
      subgoal sorry
      subgoal 
        by (metis LNil_eq_lappend_iff finite_produce_to_shift_produce produce_LNil_exit produce_nil_op)


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

lemma produce_inner_produce_Inr_lfinite:
  "produce_inner (op2, produce op1 lxs) = Some r \<Longrightarrow>
   r = Inr lgc' \<Longrightarrow>
   \<forall> n . produce_inner (skip_n_productions_op op1 n, lxs) \<noteq> None \<Longrightarrow>
   lfinite lxs"
  apply (induct "(op2, produce op1 lxs)" r arbitrary: op1 op2 lxs lgc' rule: produce_inner_induct)
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
  assumes "\<forall> n . produce_inner (skip_n_productions_op op1 n, lxs) \<noteq> None"
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
  "\<forall> n . produce_inner (skip_n_productions_op op1 n, lxs) \<noteq> None \<Longrightarrow>
   produce (skip_n_productions_op (compose_op op1 op2) n) lxs = produce (compose_op op1 (skip_n_productions_op op2 n)) lxs"
  apply (subst produce_compose_op_correctness)
   apply assumption
  apply (simp add: produce_compose_op_correctness produce_skip_n_productions_op_correctness)
  done

lemma produce_inner_Some_lfinite_produce_lfinite:
  "produce_inner (op, lxs) = Some (Inl (lgc', x, xs, lxs')) \<Longrightarrow> lfinite (produce op lxs) \<Longrightarrow> lfinite lxs \<Longrightarrow> lfinite (produce lgc' lxs')"
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
  "produce_inner (skip_n_productions_op op n, input_stream) = Some r \<Longrightarrow>
   r = Inl (lgc', h, xs, lxs') \<Longrightarrow>
   produce_inner (skip_n_productions_op op (Suc n), input_stream) = None \<Longrightarrow>
   xs = [] \<and> produce lgc' lxs' = LNil"
  apply (induction "(skip_n_productions_op op n, input_stream)" r arbitrary: input_stream n op rule: produce_inner_induct)
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
  "produce_inner (skip_n_productions_op op i, lxs) = Some r \<Longrightarrow>
   r = Inr op' \<Longrightarrow>
   produce_inner (skip_n_productions_op op (Suc i), lxs) = Some (Inr (skip_n_productions_op op' 1))"
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