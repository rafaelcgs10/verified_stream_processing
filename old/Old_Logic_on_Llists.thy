theory Old_Logic_on_Llists
  imports
    "Coinductive.Coinductive_List"
    "Linear_Temporal_Logic_on_Llists"
    "HOL-Library.BNF_Corec"
begin

codatatype ('o, 'i) op = Logic ("apply": "('i \<Rightarrow> ('o, 'i) op \<times> 'o list)")

partial_function (option) produce_inner :: "('a, 'b) op \<times> 'b llist \<Rightarrow> (('a, 'b) op \<times> 'a \<times> 'a list \<times> 'b llist) option" where
  "produce_inner op_lxs = (case op_lxs of (op, lxs) \<Rightarrow>
    (case lxs of 
        LNil \<Rightarrow> None
     | LCons h lxs' \<Rightarrow> (case apply op h of 
                         (lgc', []) \<Rightarrow> produce_inner (lgc', lxs')
                       | (lgc', x#xs) \<Rightarrow> Some (lgc', x, xs, lxs'))))"

corec produce where
  "produce op lxs = 
    (case produce_inner (op, lxs) of
       None \<Rightarrow> LNil
    | Some (lgc', x, xs, lxs') \<Rightarrow> LCons x (xs @@- produce lgc' lxs'))"

primcorec count_op where
  "count_op P n = Logic (\<lambda> ev. if P ev then (count_op P (n + 1), [n+1]) else (count_op P n, []))"

primcorec skip_first_production_op :: "(_, 'i) op \<Rightarrow> (_, 'i) op" where
  "skip_first_production_op op = Logic (\<lambda> ev.
                                     let (lgc', out::_ list) = apply op ev in
                                     case out of
                                       [] \<Rightarrow> (skip_first_production_op lgc', [])
                                     | _ \<Rightarrow> (lgc', tl out))"

lemma produce_inner_alt:
  assumes "produce_inner op_lxs = Some y"
  assumes "\<And>op h lxs' lgc' zs. apply op h = (lgc', []) \<Longrightarrow> Q (lgc', lxs') zs \<Longrightarrow> Q (op, LCons h lxs') zs"
  assumes "\<And>op h x xs lxs' lgc'. apply op h = (lgc', x # xs) \<Longrightarrow> Q (op, LCons h lxs') (lgc', x, xs, lxs')"
  shows "Q op_lxs y"
  by (rule produce_inner.raw_induct[OF _ assms(1)])
    (auto elim: assms(2,3) split: llist.splits prod.splits list.splits)

lemma produce_inner_LNil_None[simp]:
  "produce_inner (op, LNil) = None"
  apply (subst produce_inner.simps)
  apply simp
  done

primcorec skip_n_productions_op :: "(_, 'i) op \<Rightarrow> nat \<Rightarrow> (_, 'i) op" where
  "skip_n_productions_op op n = Logic (\<lambda> ev.
                                     let (lgc', out::_ list) = apply op ev in
                                       if length out < n 
                                       then (skip_n_productions_op lgc' (n - length out), [])
                                       else (lgc', drop n out)
                                     )"

lemma skip_n_productions_op_0[simp]:
  "skip_n_productions_op op 0 = op"
  apply (subst skip_n_productions_op.ctr)
  apply simp
  done

lemma produce_inner_None_produce_LNil:
  "produce_inner (op, lxs) = None \<Longrightarrow>
  produce op lxs = LNil"
  apply (subst produce.code)
  apply auto
  done

lemma produce_inner_skip_n_productions_op_Suc_Nil_LNil:
  "produce_inner (skip_n_productions_op op n, input_stream) = Some (lgc', h, xs, lxs') \<Longrightarrow>
   produce_inner (skip_n_productions_op op (Suc n), input_stream) = None \<Longrightarrow>
   xs = [] \<and> produce lgc' lxs' = LNil"
  apply (induction "(skip_n_productions_op op n, input_stream)" "(lgc', h, xs, lxs')" arbitrary: input_stream n op rule: produce_inner_alt[consumes 1])
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
    apply (subst (asm) produce_inner.simps)
    apply (simp split: option.splits prod.splits if_splits list.splits)
    apply safe
     apply (metis drop_Suc drop_all dual_order.refl list.sel(3) tl_drop)
    apply (subst produce.corec.code)
    apply (simp split: option.splits prod.splits if_splits list.splits)
    done
  done

lemma produce_inner_skip_n_productions_op_Suc_LCons:
  "produce_inner (skip_n_productions_op op n, input_stream) = Some (lgc', h, xs, lxs') \<Longrightarrow>
   produce_inner (skip_n_productions_op op (Suc n), input_stream) = Some (lgc'', h', xs', lxs'') \<Longrightarrow>
   LCons h' (xs' @@- produce lgc'' lxs'') = xs @@- produce lgc' lxs'"
  apply (induction "(skip_n_productions_op op n, input_stream)" "(lgc', h, xs, lxs')" arbitrary: input_stream n op rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' n op
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
    apply (subst (2) produce.corec.code)
    apply (subst (asm) produce_inner.simps)
    apply (simp split: option.splits prod.splits if_splits list.splits)
     apply hypsubst_thin
     apply (metis drop_Suc drop_all dual_order.refl list.sel(3) lshift.simps(1) tl_drop)
    apply hypsubst_thin
    apply safe
    subgoal
      apply (subst produce.corec.code)
      apply (simp split: option.splits prod.splits if_splits list.splits)
      apply (simp add: drop_Suc drop_tl)
      done
    subgoal
      apply (subst produce.corec.code)
      apply (simp split: option.splits prod.splits if_splits list.splits)
      apply (simp add: drop_Suc drop_tl)
      done
    done
  done

lemma produce_skip_n_productions_op_LCons:
  "produce (skip_n_productions_op op n) lxs = LCons h lxs' \<Longrightarrow> produce (skip_n_productions_op op (Suc n)) lxs = lxs'"
  apply (subst (asm) produce.code)
  apply (subst produce.code)
  apply (simp split: option.splits prod.splits)
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
  done

lemma produce_inner_skip_n_productions_op_Suc_skip_n_productions_op_n:
  "produce_inner (skip_n_productions_op op (Suc n), lxs) = Some (lgc', x, xs, lxs') \<Longrightarrow>
   produce_inner (skip_n_productions_op op n, lxs) = None \<Longrightarrow>
   False"
  apply (induct "(skip_n_productions_op op (Suc n), lxs)" "(lgc', x, xs, lxs')" arbitrary: n op lxs rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' n op
    apply (simp split: if_splits)
    subgoal
      apply (subst (asm) (2) produce_inner.simps)
      apply (simp split: if_splits)
      subgoal
        apply hypsubst_thin
        apply (subst (asm) Suc_diff_le)
         apply simp
        apply blast
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
  subgoal for h n op
    apply (subst (asm) produce_inner.simps)
    apply (simp split: if_splits list.splits)
    done
  done

lemma produce_skip_n_productions_op_n_LNil_skip_n_productions_op_Suc_n_LNil:
  "produce (skip_n_productions_op op n) lxs = LNil \<Longrightarrow> produce (skip_n_productions_op op (Suc n)) lxs = LNil"
  apply (subst (asm) produce.code)
  apply (subst produce.code)
  apply (simp split: option.splits prod.splits)
  apply safe
  subgoal for lgc' x xs lxs'
    using produce_inner_skip_n_productions_op_Suc_skip_n_productions_op_n apply metis
    done
  done

lemma produce_skip_n_productions_op_ltl_alt:
  "produce (skip_n_productions_op op (Suc n)) lxs = ltl (produce (skip_n_productions_op op n) lxs)"
  apply (cases "produce (skip_n_productions_op op n) lxs")
   apply simp
  using produce_skip_n_productions_op_n_LNil_skip_n_productions_op_Suc_n_LNil apply blast
  apply (simp add: produce_skip_n_productions_op_LCons)
  done

definition "finite_produce op xs old =
  fold (\<lambda> ev (op, out) . let (lgc', out') = apply op ev in (lgc', out@out')) xs (op, old)"

lemma finite_produce_simps:
  "finite_produce op xs old = (case xs of
                                 [] \<Rightarrow> (op, old)
                                | (x#xs) \<Rightarrow>
                                   (let (lgc', out) = apply op x in 
                                   finite_produce lgc' xs (old@out)))"
  apply (induct xs arbitrary: op old)
   apply (simp add: finite_produce_def)
  subgoal for h xs op
    apply (rule prod_eqI)
    subgoal
      apply (subst finite_produce_def)
      apply (cases "apply op h")
      subgoal for lgc' out
        apply (auto simp add: Let_def finite_produce_def split_beta split: prod.splits list.splits)
        done
      done
    subgoal
      apply (subst finite_produce_def)
      apply (cases "apply op h")
      subgoal for lgc' out
        apply (auto simp add: Let_def finite_produce_def split_beta split: prod.splits list.splits)
        done
      done
    done
  done


lemma finite_produce_Nil[simp]:
  "finite_produce op [] old = (op, old)"
  apply (subst finite_produce_simps)
  apply simp
  done

primcorec compose_op where
  "compose_op lgc1 lgc2 = Logic (\<lambda> ev.
       let (lgc1', out) = apply lgc1 ev in
       let (lgc2', out') = finite_produce lgc2 out [] in
       (compose_op lgc1' lgc2', out')
   )"

lemma produce_inner_compose_op_Some_produce_inner_None:
  "produce_inner (compose_op lgc1 lgc2, lxs) = Some (lgc3, x, xs, lxs') \<Longrightarrow> produce_inner (lgc1, lxs) = None \<Longrightarrow> False"
  apply (induct "(compose_op lgc1 lgc2, lxs)" "(lgc3, x, xs, lxs')" arbitrary: lgc1 lgc2 lxs rule: produce_inner_alt[consumes 1])
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
    done
  done

lemma produce_inner_None_produce_inner_compose_op_None[simp]:
  "produce_inner (lgc1, lxs) = None \<Longrightarrow> produce_inner (compose_op lgc1 lgc2, lxs) = None"
  by (metis not_Some_eq prod_cases4 produce_inner_compose_op_Some_produce_inner_None)

lemma produce_inner_compose_op_Some_production:
  "apply lgc1 h = (lgc1', x#xs) \<Longrightarrow>
   finite_produce lgc2 (x#xs) [] = (lgc2', y#ys) \<Longrightarrow>
   produce_inner (compose_op lgc1 lgc2, LCons h lxs) = Some (compose_op lgc1' lgc2', y, ys, lxs)"
  apply (subst produce_inner.simps)
  apply (auto split: option.splits list.splits)
  done

lemma produce_inner_compose_op_finite_produce_no_production[simp]:
  "produce_inner (lgc1, lxs) = Some (lgc1', x, xs, lxs') \<Longrightarrow>
   finite_produce lgc2 (x#xs) [] = (lgc2', []) \<Longrightarrow>
   produce_inner (compose_op lgc1 lgc2, lxs) = produce_inner (compose_op lgc1' lgc2', lxs')"
  apply (induct "(lgc1, lxs)" "(lgc1', x, xs, lxs')" arbitrary: lgc1 lgc2 lxs rule: produce_inner_alt[consumes 1])
  subgoal
    apply (subst produce_inner.simps)
    apply (auto split: option.splits list.splits llist.splits prod.splits)
    done
  subgoal
    apply (subst produce_inner.simps)
    apply (auto split: option.splits list.splits llist.splits prod.splits)
    done
  done

lemma produce_inner_LCons_Some_cases:
  "produce_inner (lgc1, LCons h hs) = Some (op, x, xs, lxs') \<Longrightarrow>
   (apply lgc1 h = (op, x#xs) \<and> lxs' = hs) \<or> produce_inner (fst (apply lgc1 h), hs) = Some (op, x, xs, lxs')"
  apply (subst (asm) produce_inner.simps)
  apply (auto split: prod.splits list.splits)
  done

lemma produce_inner_compose_op:
  "produce_inner (compose_op lgc1 lgc2, lxs) =
   (case (produce_inner (lgc1, lxs)) of
      None \<Rightarrow> None 
    | Some (op, x, xs, lxs') \<Rightarrow> (
      let (lgc', out) = finite_produce lgc2 (x#xs) [] in
      (case out of 
        [] \<Rightarrow> produce_inner (compose_op op lgc', lxs') 
       | y#ys \<Rightarrow> Some (compose_op op lgc', y, ys, lxs'))))"
  apply (cases "produce_inner (lgc1, lxs)")
   apply simp
  subgoal for p
    apply (cases p)
    apply simp
    apply hypsubst_thin
    subgoal for op x xs lxs'
      apply (induct "(lgc1, lxs)" "(op, x, xs, lxs')" arbitrary: lgc1 lgc2 lxs rule: produce_inner_alt[consumes 1])
      subgoal
        apply (subst produce_inner.simps)
        apply (auto split: option.splits llist.splits list.splits prod.splits)
        done
      subgoal for lgca h lgc2
        apply (subst produce_inner.simps)
        apply (auto split: option.splits llist.splits list.splits prod.splits)
        done
      done
    done
  done

lemma finite_produce_LCons_Nil:
  "finite_produce op (x # xs) [] = (lgc', []) \<Longrightarrow>
   apply op x = (lgc'', []) \<Longrightarrow> finite_produce lgc'' xs [] = (lgc', [])"
  apply (subst (asm) finite_produce_simps)
  apply simp
  done

lemma finite_produce_Some_old_empty_out_False:
  "finite_produce op xs (y # ys) = (lgc', []) \<Longrightarrow> False"
  apply (induct xs arbitrary: op ys y)
   apply simp
  apply (subst (asm) (2) finite_produce_simps)
  apply (auto split: prod.splits list.splits)
  done

lemma produce_inner_prefix_no_production:
  "produce_inner (op, xs @@- lxs) = Some (lgc', y, ys, lxs') \<Longrightarrow>
   finite_produce op xs [] = (lgc'', []) \<Longrightarrow>
   produce_inner (lgc'', lxs) =  Some (lgc', y, ys, lxs')"
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
    using finite_produce_Some_old_empty_out_False apply fastforce
    done
  done

lemma apply_compose_op_Cons:
  "apply (compose_op lgc1 lgc2) h = (lgc', x # xs) \<Longrightarrow>
   \<exists> y ys lgc1' lgc2' .apply lgc1 h = (lgc1', y#ys) \<and> finite_produce lgc2 (y#ys) [] = (lgc2', x#xs) \<and> lgc' = compose_op lgc1' lgc2'"
  apply (cases "apply lgc1 h")
  subgoal for op out
    apply (cases out)
     apply simp
    subgoal for y ys
      apply (rule exI[of _ y])
      apply (rule exI[of _ ys])
      apply (rule exI[of _ op])
      apply (metis compose_op.sel fst_conv prod.collapse prod.sel(2))
      done
    done
  done

lemma finite_produce_move_old_out:
  "finite_produce op xs old = (lgc', ys) \<Longrightarrow> ys = old@(snd (finite_produce op xs []))"
  apply (induct xs arbitrary: old op ys lgc')
   apply simp
  apply (subst (asm) (3) finite_produce_simps)
  apply (subst finite_produce_simps)
  apply (simp split: prod.splits)
  apply (metis append.assoc prod.collapse)
  done

lemma produce_inner_prefix_Some_production:
  "produce_inner (op, xs @@- lxs) = Some (lgc', y, ys, lxs') \<Longrightarrow>
   finite_produce op xs [] = (lgc'', y'#ys') \<Longrightarrow>
   y = y' \<and> (ys = take (length ys) ys') \<and> (\<exists> xs .lxs' = xs @@- lxs \<and> finite_produce lgc' xs (y#ys) = (lgc'',  y'#ys'))"
  apply (induct "(op, xs @@- lxs)" "(lgc', y, ys, lxs')" arbitrary: op xs lxs lgc'  rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs' lgc' xs lxs lgc''
    apply (cases xs)
     apply simp
    subgoal for x xs'
      apply simp
      apply (elim conjE)
      apply (subst (asm) (3) finite_produce_simps)
      apply simp
      apply blast
      done
    done
  subgoal for op h lgc' xs lxs
    apply (cases xs)
     apply simp
    subgoal for x xs'
      apply simp
      apply (elim conjE)
      apply safe
      subgoal
        apply (subst (asm) (1) finite_produce_simps)
        apply simp
        apply hypsubst_thin
        apply (drule finite_produce_move_old_out)
        apply simp
        done
      subgoal
        apply (subst (asm) (1) finite_produce_simps)
        apply simp
        apply hypsubst_thin
        apply (drule finite_produce_move_old_out)
        apply simp
        done
      subgoal
        apply (rule exI[of _ xs'])
        apply simp
        apply (simp add: finite_produce_simps)
        done
      done
    done
  done


lemma produce_inner_Some_produce[simp]:
  "produce_inner (op, lxs) = Some (lgc', x, xs, lxs') \<Longrightarrow>
   produce op lxs = LCons x (xs @@- produce lgc' lxs')"
  apply (subst produce.code)
  apply simp
  done

lemma produce_inner_compose_op_produce_inner_produce:
  "produce_inner (compose_op lgc1 lgc2, lxs) = Some (lgc', x, xs, lxs') \<Longrightarrow>
   produce_inner (lgc2, produce lgc1 lxs) = Some (lgc'', y, ys, lys') \<Longrightarrow>
   x = y \<and> (ys = take (length ys) xs)"
  apply (induct "(compose_op lgc1 lgc2, lxs)" "(lgc', x, xs, lxs')" arbitrary: lgc1 lgc2 lxs lgc' x xs lxs' lgc'' y ys lys' rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' lgc1 lgc2 lgc'a x xs lxs'' lgc'' y ys lys'
    apply (subst (asm) (2) produce.code)
    apply (subst (asm) (3) produce_inner.simps)
    apply (auto split: option.splits prod.splits list.splits)
    using produce_inner_prefix_no_production apply (metis prod.collapse lshift.simps(2))+
    done
  subgoal for h x xs lxs' lgc' lgc1 lgc2 lgc'' y ys lys'
    apply (frule apply_compose_op_Cons)
    apply (elim conjE exE)
    subgoal for y' ys' lgc1' lgc2'
      apply (subst (asm) (1) produce.code)
      apply (subst (asm) (1) produce_inner.simps)
      apply (simp split: option.splits prod.splits list.splits)
       apply hypsubst_thin
       apply simp
      subgoal for lgc1'' y'' ys'' lxs'' lgc2''
        apply (subst (asm) (1) produce_inner.simps)
        apply (simp split: option.splits prod.splits list.splits)
        apply (elim conjE)
        apply hypsubst_thin
        apply (subst (asm) finite_produce_simps)
        apply simp
        apply (drule produce_inner_prefix_Some_production)
         apply assumption
        apply (elim conjE)
        apply simp
        done
      subgoal for x2 x1 x2a x1a x2b x1b x2c x2d
        apply hypsubst_thin
        apply (subst (asm) (1) produce_inner.simps)
        apply (simp split: option.splits prod.splits list.splits)
        apply (elim conjE)
        apply hypsubst_thin 
        apply (subst (asm) finite_produce_simps)
        apply simp
        apply (metis append_Cons append_eq_conv_conj finite_produce_move_old_out list.sel(1) list.sel(3))
        done
      done
    done
  done

lemma finite_produce_extend_old:
  "finite_produce x xs ys = (lgc1', ys') \<Longrightarrow> finite_produce x xs (zs @ ys) = (lgc1', zs @ ys')"
  apply (induct xs arbitrary: x ys zs)
   apply simp
  apply (subst (asm) (3) finite_produce_simps)
  apply (subst finite_produce_simps)
  apply (auto split: prod.splits)
  done

lemma finite_produce_append:
  "finite_produce op (xs @ ys) zs = finite_produce (fst (finite_produce op xs zs)) ys ((snd (finite_produce op xs zs)))"
  apply (induct xs arbitrary: ys zs op)
   apply simp
  apply (subst (1 2 4) finite_produce_simps)
  apply (auto split: prod.splits)
  done

lemma produce_inner_to_finite_produce:
  "produce_inner (op, lxs) = Some (lgc', x, xs, lxs') \<Longrightarrow>
   \<exists> zs. lxs = zs @@- lxs' \<and> finite_produce op zs [] = (lgc', x#xs)"
  apply (induct "(op, lxs)" "(lgc', x, xs, lxs')" arbitrary: op lxs lgc' x xs lxs'  rule: produce_inner_alt[consumes 1])
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
    done
  done

lemma finite_produce_drop:
  "finite_produce op xs ys = (lgc', zs) \<Longrightarrow>
   finite_produce op xs [] = (lgc', drop (length ys) zs)"
  apply (induct xs arbitrary: ys zs op)
   apply simp
  apply (subst (asm) (3) finite_produce_simps)
  apply (subst finite_produce_simps)
  apply (auto split: prod.splits)
  apply (metis append_eq_conv_conj eq_fst_iff finite_produce_extend_old snd_eqD)
  done

lemma finite_produce_to_shift_produce:
  "finite_produce op xs [] = (lgc', zs) \<Longrightarrow>
   produce op (xs @@- lxs) = zs @@- produce lgc' lxs"
  apply (induct xs arbitrary: op lxs zs)
   apply simp
  subgoal for a xs op lxs zs
    apply simp
    apply (subst produce.code)
    apply (subst produce_inner.simps)
    apply (subst (asm) (2) finite_produce_simps)
    apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits list.splits option.splits)
       apply (metis produce_inner_None_produce_LNil)
    subgoal for lgc' x xs'
      apply (drule meta_spec[of _ lgc'])
      apply (drule meta_spec[of _ lxs])
      apply (drule meta_spec[of _ "drop (length (x # xs')) zs"])
      apply (drule meta_mp)
      using finite_produce_drop apply fast
      apply (metis (no_types, lifting) LNil_eq_shift_iff add_Suc_shift append_eq_conv_conj finite_produce_move_old_out id_take_nth_drop length_Cons length_append lessI list.size(3) list.size(4) llist_of.simps(2) produce_inner_None_produce_LNil shift_LNil take_Suc_conv_app_nth)
      done
    subgoal for x1 aa aaa ab b
      apply (metis produce_inner_Some_produce)
      done
    subgoal for lgc' aa aaa ab b x xs'
      apply (drule meta_spec[of _ lgc'])
      apply (drule meta_spec[of _ lxs])
      apply (drule meta_spec[of _ "drop (length (x # xs')) zs"])
      apply (drule meta_mp)
      using finite_produce_drop apply fast
      using finite_produce_move_old_out apply fastforce
      done
    done
  done

lemma finite_produce_output_not_empty_cases:
  "finite_produce op xs ys = (lgc', zs) \<Longrightarrow>
   zs \<noteq> [] \<Longrightarrow>
   ys \<noteq> [] \<or> xs \<noteq> []"
  apply (cases ys)
   apply (subst (asm) finite_produce_simps)
   apply (auto split: prod.splits)
  done

lemma finite_produce_same_lgc_diff_old:
  "fst (finite_produce op xs old1) = fst (finite_produce op xs old2)"
  apply (induct xs arbitrary: op old1 old2)
   apply simp
  apply (subst (1 2) finite_produce_simps)
  apply (auto split: list.splits prod.splits)
  done

lemma produce_inner_shift_none_finite_produce:
  "produce_inner (op, xs @@-lxs) = None \<Longrightarrow>
   snd (finite_produce op xs []) = [] \<and> produce_inner (fst (finite_produce op xs []), lxs) = None"
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
  "finite_produce op ys [] = (lgc', []) \<Longrightarrow>
   produce_inner (op, ys @@- lys) = produce_inner (lgc', lys)"
  apply (induct ys arbitrary: op)
   apply simp
  apply simp
  apply (subst produce_inner.simps)
  apply (subst (asm) (2) finite_produce_simps)
  apply (auto split: prod.splits list.splits)
  apply (meson finite_produce_Some_old_empty_out_False)
  done

lemma produce_inner_produce_Some_finite_produce:
  "produce_inner (lgc2, produce lgc1 lxs) = Some (lgc2', x, xs, lxs') \<Longrightarrow>
   \<exists> zs lgc1' lxs'' ys.  produce lgc1 lxs = zs @@- lxs' \<and> zs \<noteq> [] \<and> finite_produce lgc2 zs [] = (lgc2', x#xs) \<and> produce_inner (lgc1, lxs) = Some (lgc1', hd zs, ys, lxs'')"
  apply (frule produce_inner_to_finite_produce)
  apply (elim exE)
  subgoal for zs
    apply (rule exI[of _ zs])
    apply simp
    apply (subst (asm) produce.code)
    apply (auto split: option.splits prod.splits list.splits)
    apply (metis finite_produce_output_not_empty_cases list.discI list.exhaust_sel shift_LCons_Cons)
    done
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
  apply (simp split: prod.splits)
  using finite_produce_move_old_out apply force
  done

lemma finite_produce_old_empty:       
  "finite_produce lgc1 xs old = (lgc1', []) \<Longrightarrow> old = []"
  by (meson Nil_is_append_conv finite_produce_move_old_out)

lemma finite_produce_out_empty:
  "finite_produce lgc'' xs (old @ out) = (lgc', old) \<Longrightarrow> out = []"
  by (metis finite_produce_move_old_out prefixI same_prefix_nil)

lemma finite_produce_finite_produce_drop:
  "finite_produce op xs old = (lgc', old) \<Longrightarrow>
   length xs < length zs \<Longrightarrow>
   xs @@- lxs = zs @@- lys \<Longrightarrow>
   finite_produce op zs old = (lgc'', old) \<Longrightarrow>
   finite_produce lgc' (drop (length xs) zs) old = (lgc'', old)"
  apply (induct xs arbitrary: zs op lgc' lxs lys lgc'' old)
   apply simp
  apply (subst (asm) (4) finite_produce_simps)
  apply (auto split: prod.splits)
  subgoal for a xs zs op lgc' lxs lys lgc'' old x1 x2
    apply (cases zs)
     apply simp
    apply auto
    apply (smt (verit, ccfv_SIG) finite_produce_LCons_Nil finite_produce_move_old_out finite_produce_out_empty finite_produce_same_lgc_diff_old prod.collapse)
    done
  done

lemma produce_inner_compose_op_skip_n_productions_op:
  "produce_inner (compose_op (skip_n_productions_op lgc1 n) lgc2'', lxs) = Some (lgc', y, ys, lys) \<Longrightarrow>
   produce_inner (compose_op lgc1 lgc2, lxs) = None \<Longrightarrow>
   n = length zs \<Longrightarrow>
   produce lgc1 lxs = zs @@- lzs \<Longrightarrow>
   finite_produce lgc2 zs [] = (lgc2'', []) \<Longrightarrow>
   False"
  apply (induct "(compose_op (skip_n_productions_op lgc1 n) lgc2'', lxs)" "(lgc', y, ys, lys)" arbitrary: n zs lgc1 lgc2 lgc2'' lxs ys y lzs lys  rule: produce_inner_alt[consumes 1])
  subgoal premises prems for h lxs' lgc' n lgc1 lgc2'' ys y lys zs lgc2 lzs
    using prems apply -
    apply (subst (asm) (2) produce.code)
    apply (subst (asm) (2) produce_inner_compose_op)
    apply (subst (asm) (3 4 ) produce_inner.simps)
    apply (auto simp add: less_Suc_eq not_less_eq produce_inner_None_produce_LNil LNil_eq_shift_iff split: list.splits option.splits if_splits prod.splits)
          apply (metis finite_produce_Nil prems(4) produce_inner_None_produce_inner_compose_op_None lshift.simps(1) skip_n_productions_op_0)
         apply (metis produce_inner_Some_produce produce_inner_compose_op_finite_produce_no_production)
    subgoal for x xs lgc1' lgc2'
      apply hypsubst_thin
      apply (subst (asm) (1) length_drop[symmetric])
      apply (drule meta_spec[of _ "lgc1'"])
      apply (drule meta_spec)
      apply (drule meta_spec[of _ lgc2''])
      apply (drule meta_spec[of _ lgc2'])
      apply (drule meta_spec[of _ "drop (Suc (length xs)) zs"])
      apply (drule meta_spec[of _ lzs])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (metis length_Cons lshift.simps(2) shift_eq_shift_drop_length)
      apply (drule meta_mp)
      using finite_produce_finite_produce_drop apply fastforce
      apply simp
      done
    subgoal
      by (metis prems(4) prems(6) produce_inner_compose_op_finite_produce_no_production lshift.simps(1) skip_n_productions_op_0)
    subgoal for x xs lgc1' lgc2'
      apply hypsubst_thin
      apply (drule meta_spec[of _ "lgc1'"])
      apply (drule meta_spec[of _ 0])
      apply (drule meta_spec[of _ "fst (finite_produce lgc2'' (drop (length zs) (x#xs)) [])"])
      apply (drule meta_spec[of _ lgc2'])
      apply (drule meta_spec[of _ "[]"])
      apply (drule meta_spec[of _ "ldropn (length (x # xs)) (zs @@- lzs)"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using shift_eq_shift_ldropn_length[where ys=zs and zs=xs and lxs="produce lgc1' lxs'" and lys=lzs and xs="x#xs"]
       apply (metis lshift.simps(1) lshift.simps(2))
      apply (drule meta_mp)
       apply (smt (verit, ccfv_SIG) finite_produce_Nil finite_produce_finite_produce_drop fst_eqD length_Cons less_SucI lshift.simps(2))
      apply simp
      done
    subgoal
      by (smt (verit, ccfv_SIG) finite_produce_Nil finite_produce_finite_produce_drop fst_conv length_Cons lessI list.size(3) lshift.simps(1) lshift.simps(2) skip_n_productions_op_0)
    subgoal for x xs lgc1' lgc2'
      apply hypsubst_thin
      apply (cases zs)
       apply auto[1]
      subgoal for z zs'
        apply auto
        apply hypsubst_thin
        apply (drule sym[where s="length zs'"])
        apply (frule shift_same_prefix[where lxs="produce lgc1' lxs'"])
         apply auto
        apply hypsubst_thin
        apply (drule meta_spec[of _ "lgc1'"])
        apply (drule meta_spec[of _ 0])
        apply (drule meta_spec[of _ "lgc2''"])
        apply (drule meta_spec[of _ lgc2''])
        apply (drule meta_spec[of _ "[]"])
        apply (drule meta_spec)
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
         apply simp
        apply simp
        done
      done
    done
  subgoal for h x xs lxs' n lgc1 lgc2'' zs lgc2 lzs
    apply (cases zs)
    subgoal
      apply auto[1]
      apply (subst (asm) produce.code)
      apply (auto simp add: LNil_eq_shift_iff split: if_splits option.splits)
       apply (subst (asm) produce_inner.simps)
       apply (auto simp add: LNil_eq_shift_iff split: if_splits option.splits prod.splits list.splits)
      apply hypsubst_thin
      apply (metis apply_compose_op_Cons compose_op.simps produce_inner_LNil_None produce_inner_compose_op_Some_produce_inner_None produce_inner_compose_op_Some_production)
      done
    subgoal for z zs'
      apply auto[1]
      apply (subst (asm) produce.code)
      apply (auto simp add: LNil_eq_shift_iff split: if_splits option.splits)
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: LNil_eq_shift_iff split: if_splits option.splits prod.splits list.splits)
      apply hypsubst_thin
      apply (subst (asm) produce_inner.simps)
      apply (auto simp add: LNil_eq_shift_iff split: if_splits option.splits prod.splits list.splits)
      using drop_all finite_produce_Nil finite_produce_append finite_produce_finite_produce_drop finite_produce_old_empty less_or_eq_imp_le linorder_neqE_nat list.discI prod.collapse
      apply (smt (verit, best) add_diff_cancel_right' append_Cons append_take_drop_id diff_diff_cancel fst_conv length_append length_drop lshift_append shift_same_prefix)
      done
    done
  done


lemma  produce_inner_compose_op_None_produce_shift_finite_produce: 
  "produce_inner (compose_op lgc1 lgc2, lxs) = None \<Longrightarrow>
   produce lgc1 lxs = ys @@- lys \<Longrightarrow>
   \<exists> lgc2' .finite_produce lgc2 ys [] = (lgc2', [])"
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
      using produce_inner_compose_op_skip_n_productions_op[where n=1 and zs="[a]", of lgc1 lgc2'' lxs _ _ _ _ lgc2] apply -
      apply simp
      apply (subst (asm) finite_produce_simps)
      apply (simp split: prod.splits list.splits)
      apply (metis option.exhaust prod_cases4)
      done
    subgoal
      apply (simp add: produce_skip_n_productions_op_LCons)
      done
    done
  done

lemma produce_inner_produce_Some:
  "produce_inner (lgc2, produce lgc1 lxs) = Some (lgc2', x, xs, lxs') \<Longrightarrow>
   produce_inner (compose_op lgc1 lgc2, lxs) = None \<Longrightarrow> False"
  by (metis finite_produce_Nil finite_produce_Some_old_empty_out_False produce_inner_compose_op_None_produce_shift_finite_produce produce_inner_to_finite_produce)

lemma apply_compose_op:
  "apply (compose_op lgc1 lgc2) h = (lgc', x#xs) \<Longrightarrow>
   \<exists> lgc1' y ys lgc2' .apply lgc1 h = (lgc1', y#ys) \<and> finite_produce lgc2 (y#ys) [] = (lgc2', x#xs) \<and> lgc' = compose_op lgc1' lgc2'"
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
  "finite_produce op zs [] = (lgc', x#xs) \<Longrightarrow>
   zs \<noteq> [] \<Longrightarrow>
   \<exists>ac aaa aba ba. produce_inner (op, (zs @@- lxs)) = Some (ac, aaa, aba, ba)"
  apply (induct zs arbitrary: x xs op lgc' lxs )
   apply simp
  subgoal for a zs x xs op lgc' lxs'
    apply (subst (asm) (2) finite_produce_simps)
    apply (auto split: prod.splits)
    subgoal for lgc'' out
      apply (cases out)
      subgoal
        apply (metis finite_produce_LCons_Nil finite_produce_Nil finite_produce_Some_old_empty_out_False not_None_eq prod.exhaust_sel produce_inner_shift_none_finite_produce lshift.simps(2))
        done
      subgoal for o out'
        apply simp
        apply hypsubst_thin
        apply (subst produce_inner.simps)
        apply auto
        done
      done
    done
  done

lemma produce_inner_compose_op_Some:
  "produce_inner (compose_op lgc1 lgc2, lxs) = Some (lgc1', x, xs, lxs') \<Longrightarrow>
   \<exists>a aa ab b. produce_inner (lgc2, produce lgc1 lxs) = Some (a, aa, ab, b)"
  apply (induct "(compose_op lgc1 lgc2, lxs)" "(lgc1', x, xs, lxs')" arbitrary: lgc1 lgc2 lxs x xs lxs' lgc1' rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' lgc1 lgc2 x xs lxs'' lgc1'
    apply (subst produce.code)
    apply (auto split: option.splits)
    subgoal
      apply (subst produce_inner.simps)
      apply (auto split: prod.splits list.splits)
      using produce_inner_produce_Some_finite_produce apply fastforce
      done
    subgoal for a aa ab b
      apply (subst produce_inner.simps)
      apply (auto split: prod.splits list.splits)
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto split: prod.splits list.splits)
      using produce_inner_LCons_Some_cases apply fastforce
      apply (metis finite_produce_LCons_Nil finite_produce_prefix_no_production_produce_inner prod.collapse)
      done
    done
  subgoal for h x xs lxs' lgc' lgc1 lgc2
    apply (frule apply_compose_op)
    apply (elim exE conjE)
    apply (subst produce.code)
    apply (auto split: option.splits)
    subgoal
      apply (subst produce_inner.simps)
      apply auto
      done
    apply hypsubst_thin
    subgoal for lgc1' y ys lgc2' a aa ab b
      apply (subst (asm) produce_inner.simps)
      apply (auto split: prod.splits list.splits)
      apply hypsubst_thin
      using finite_produce_produce_inner_Some apply fastforce
      done
    done
  done

lemma produce_compose_op_correctness:
  "produce (compose_op lgc1 lgc2) lxs = produce lgc2 (produce lgc1 lxs)"
  apply (coinduction arbitrary: lgc1 lgc2 lxs rule: llist.coinduct_upto)
  apply (intro conjI impI)
  subgoal for lgc1 lgc2 lxs
    apply (subst (1 2) produce.code)
    apply (auto simp add: split: prod.splits list.splits option.splits)
     apply (metis produce_inner_produce_Some)
    using produce_inner_compose_op_Some apply fast
    done
  subgoal for lgc1 lgc2 lxs
    apply (subst (1 2) produce.code)
    apply (auto simp add:  produce_inner_None_produce_LNil split: prod.splits list.splits option.splits)
    apply (drule produce_inner_compose_op_produce_inner_produce)
     apply assumption
    apply simp
    done
  subgoal for lgc1 lgc2 lxs
    apply (subst (4 5) produce.code)
    apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits list.splits option.splits)
    subgoal for lgc12 x xs lxs' lgc2' y ys lys
      apply (induct "(compose_op lgc1 lgc2, lxs)" "(lgc12, x, xs, lxs')" arbitrary: lgc1 lgc2 lxs x xs lxs'  rule: produce_inner_alt[consumes 1])
      subgoal for h lxs' lgc' lgc1 lgc2 x xs lxs''
        apply (subst (asm) (2) produce_inner.simps)
        apply (auto split: prod.splits list.splits llist.splits)
        subgoal
          apply (subst (asm) (7) produce.code)
          apply (simp split: option.splits prod.splits)
          apply hypsubst_thin
          apply (subst (asm) (3) produce_inner.simps)
          apply (simp split: list.splits prod.splits) 
          subgoal
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (rule refl)
            apply (drule meta_mp)
             apply hypsubst_thin
             apply (metis (mono_tags, lifting) list.simps(4) llist.simps(5) prod.simps(2) produce_inner.simps produce_inner_Some_produce)
            apply simp
            done
          subgoal
            apply (metis (no_types, lifting) finite_produce_LCons_Nil prod.collapse produce_inner_prefix_no_production)
            done
          done
        subgoal
          apply (subst (asm) (7) produce.code)
          apply (simp split: option.splits prod.splits)
          apply hypsubst_thin
          apply (subst (asm) (2) produce_inner.simps)
          apply (simp split: list.splits prod.splits) 
           apply (smt (verit, del_insts) list.simps(5) llist.simps(5) old.prod.case produce_inner.simps produce_inner_Some_produce)
          apply hypsubst_thin
          apply (subst (asm) (2) finite_produce_simps)
          apply simp
          apply (rule FalseE)
          apply (metis finite_produce_Some_old_empty_out_False prod.exhaust_sel)
          done
        done
      subgoal for h x xs lxs' lgc1 lgc2
        apply (subst (asm) (1) produce.code)
        apply (simp split: option.splits prod.splits)
        apply hypsubst_thin
        apply (subst (asm) (1 2) produce_inner.simps)
        apply (simp split: list.splits prod.splits) 
        subgoal for x1 x1a x1b x2c x2 x1c x2a
          apply hypsubst_thin
          apply (subst (asm) (1) finite_produce_simps)
          apply simp
          apply (frule produce_inner_prefix_Some_production[where y'=x and ys'=xs and lgc''="fst (finite_produce x1c x1b [])"])
           apply (metis prod.collapse)
          apply (elim conjE exE)
          apply (subst (1) append_take_drop_id[symmetric, where n="length ys"])
          apply (simp only: )
          apply (subst finite_produce_to_shift_produce[where zs="drop (length ys) xs", of _ _  "fst (finite_produce x1c x1b [])"])
           apply (simp add: finite_produce_drop)
          apply (subst finite_produce_simps)
          apply simp
          apply (metis (mono_tags, lifting) lshift.cong_base lshift.cong_lshift)
          done
        subgoal for x1 x1a x1b x2c x2 x2a
          apply (subst (asm) (1) finite_produce_simps)
          apply (subst finite_produce_simps)
          apply simp
          apply hypsubst_thin
          apply (subst (1) append_take_drop_id[symmetric, where n="length ys"])
          apply (subst finite_produce_to_shift_produce[where zs="drop (length ys) xs", of _ _  "fst (finite_produce lgc2' x1b [])"])
           apply (metis append_eq_conv_conj finite_produce_move_old_out list.discI list.sel(3) prod.collapse tl_append2)
          apply (subst (asm) (1) finite_produce_simps)
          apply (auto split: list.splits prod.splits)
           apply (metis (mono_tags, lifting) lshift.cong_base lshift.cong_lshift)
          apply hypsubst_thin
          apply (subst shift_shift)
          apply (intro llist.cong_lshift)
           apply (metis append.assoc append_Cons append_eq_conv_conj finite_produce_move_old_out list.inject prod.collapse)
          apply (intro llist.cong_base)
          apply (metis finite_produce_same_lgc_diff_old)
          done
        done
      done
    done
  done

lemma produce_inner_skip_n_productions_op_Some_produce_inner_None:
  "produce_inner (skip_n_productions_op op n, lxs) = Some (lgc', x, xs, lxs') \<Longrightarrow> produce_inner (op, lxs) = None \<Longrightarrow> False"
  apply (induct "(skip_n_productions_op op n, lxs)" "(lgc', x, xs, lxs')" arbitrary: n xs op lxs x  lxs' lgc' rule: produce_inner_alt[consumes 1])
  subgoal
    apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: if_splits prod.splits list.splits)
    apply (metis skip_n_productions_op_0)
    done
  subgoal for h x xs lxs' lgc' n op
    apply (subst (asm) produce_inner.simps)
    apply (auto split: if_splits prod.splits list.splits)
    done
  done

lemma produce_inner_skip_n_productions_op_Some_llength_le:
  "produce_inner (skip_n_productions_op op n, lxs) = Some (lgc'', y, ys, lxs'') \<Longrightarrow>
   llength (produce op lxs) \<le> enat n \<Longrightarrow> False"
  apply (induct "(skip_n_productions_op op n, lxs)" "(lgc'', y, ys, lxs'')" arbitrary: n y ys lxs'' op lxs lgc'' rule: produce_inner_alt[consumes 1])
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
      apply (auto split: prod.splits list.splits llist.splits if_splits)
       apply (metis llength_LCons produce_inner_Some_produce)
      apply hypsubst_thin
      apply (metis drop_eq_Nil2 ldropn_eq_LNil ldropn_shift length_Cons less_or_eq_imp_le llength_LCons lshift.simps(1) lshift.simps(2))
      done
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (auto split: prod.splits list.splits llist.splits if_splits)
      using zero_enat_def apply auto[1]
      apply hypsubst_thin
      apply (metis dual_order.refl eSuc_enat eSuc_ile_mono ldropn_eq_LNil length_Cons lessI llength_LNil shift_eq_shift_ldropn_length skip_n_productions_op_0 zero_enat_def)
      done
    done
  subgoal for op h x xs lxs' lgc' n
    apply (subst (asm) produce.code)
    apply (auto split:option.splits if_splits)
     apply (subst (asm) produce_inner.simps)
     apply (auto split: prod.splits list.splits llist.splits if_splits)
    apply (subst (asm) produce_inner.simps)
    apply (auto split: prod.splits list.splits llist.splits if_splits)
    apply (metis eq_LConsD ldropn_eq_LNil ldropn_shift llength_LCons lshift.simps(2))
    done
  done

lemma produce_inner_Some_produce_inner_skip_n_productions_op_Suc_n_None:
  "produce_inner (skip_n_productions_op op n, lxs) = Some (lgc', x, xs, lxs') \<Longrightarrow>
   produce_inner (skip_n_productions_op op (Suc n), lxs) = None \<Longrightarrow>
   llength (produce op lxs) \<le> enat (Suc n)"
  apply (induct "(skip_n_productions_op op n, lxs)" "(lgc', x, xs, lxs')" arbitrary: n op lxs lxs' x xs rule: produce_inner_alt[consumes 1])
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
      apply (auto split: prod.splits if_splits list.splits)
      apply (metis Suc_diff_Suc Suc_lessD drop_eq_Nil2 eSuc_enat eSuc_ile_mono ldropn_eq_LNil ldropn_shift less_or_eq_imp_le lshift.simps(1))
      done
    subgoal
      apply hypsubst_thin
      apply (subst produce.code)
      apply (auto split: option.splits) 
      apply (subst (asm) (3) produce_inner.simps)
      apply (auto split: prod.splits if_splits list.splits)
       apply (metis eSuc_enat eSuc_ile_mono le_zero_eq llength_LNil produce_inner_skip_n_productions_op_Suc_Nil_LNil lshift.simps(1) skip_n_productions_op_0 zero_enat_def)
      apply (smt (z3) add.commute add_0 eSuc_enat eSuc_plus enat_ile enat_ord_simps(1) i0_lb llength_shift nle_le not_less_eq_eq skip_n_productions_op_0 zero_enat_def)
      done
    done
  subgoal for h x xs lxs' n op
    apply (subst (asm) produce_inner.simps)
    apply (auto split: prod.splits if_splits list.splits)
    subgoal
      apply hypsubst_thin
      apply (subst produce.code)
      apply (auto split: option.splits)
      apply (subst (asm) (2) produce_inner.simps)
      apply (auto split: prod.splits if_splits list.splits)
      apply (subst produce.code)
      apply (auto split: option.splits simp flip: eSuc_enat)
      done
    done
  done

lemma skip_first_production_op_eq_skip_n_productions_op:
  "(skip_first_production_op ^^ n) op = skip_n_productions_op op n"
  apply (induct n arbitrary: op)
   apply (simp add: op.expand)
  apply simp
  subgoal premises prems for n op
    apply (coinduction arbitrary: op n)
    using Suc_diff_le apply (auto simp: fun_eq_iff rel_fun_def not_less Suc_le_eq  split: list.splits)
      apply (intro exI conjI[rotated])
       apply (rule refl)
      apply (rule op.expand)
      apply (simp add: fun_eq_iff split: list.splits)
    subgoal for op n x x21 x22
      apply (rule exI[of _ "Logic (\<lambda> ev . let (lgc', out) = apply (fst (apply op x)) ev in (lgc', replicate n undefined @ x21# out))"])
      apply (rule exI[of _ "n"])
      apply (safe intro!:op.expand)
       defer
       apply (subst skip_n_productions_op.code)
       apply (auto simp add: Let_def fun_eq_iff split: prod.splits)
      done
    apply (metis Cons_nth_drop_Suc list.sel(3))
    done
  done

lemma skip_first_production_op_eq_skip_n_productions_op_1:
  "skip_n_productions_op op 1 = skip_first_production_op op"
  using skip_first_production_op_eq_skip_n_productions_op[where n=1 and op=op] apply simp
  done

lemma produce_inner_skip_n_productions_op_n_Some_skip_n_productions_op_nm_None:
  "produce_inner (skip_n_productions_op op n, lxs) = Some (lgc', x, xs, lxs') \<Longrightarrow>
   produce_inner (skip_n_productions_op op (n+m), lxs) = None \<Longrightarrow>
   llength (produce op lxs) > enat (n+m) \<Longrightarrow>
   False"
  apply (induct m arbitrary: op n lxs)
   apply simp
  subgoal
    apply simp
    apply (metis Suc_ile_eq leD option.exhaust order_less_imp_le prod_cases4 produce_inner_Some_produce_inner_skip_n_productions_op_Suc_n_None)
    done
  done

lemma produce_skip_n_productions_op_correctness:
  "produce (skip_n_productions_op op n) lxs = ldropn n (produce op lxs)"
  apply (coinduction arbitrary: op lxs n rule: llist.coinduct_upto)
  apply (intro conjI impI)
  subgoal for op lxs n
    apply (subst (1 2) produce.code)
    apply (auto split: prod.splits list.splits option.splits)
      apply (meson produce_inner_skip_n_productions_op_Some_produce_inner_None)
    subgoal 
      using produce_inner_skip_n_productions_op_n_Some_skip_n_productions_op_nm_None[where n=0 and m=n] apply simp
      apply (smt (verit, best) add.commute add.right_neutral leI llength_LCons produce_inner_Some_produce produce_inner_skip_n_productions_op_n_Some_skip_n_productions_op_nm_None skip_n_productions_op_0)
      done
    subgoal for lgc' x xs lxs'
      apply (metis llength_LCons produce_inner_Some_produce produce_inner_skip_n_productions_op_Some_llength_le)   
      done
    done
  subgoal for op lxs n
    apply (subst (1 2) produce.code)
    apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits list.splits option.splits)
    subgoal premises prems for lgc' x xs lxs' lgc'' y ys lxs''
      using prems(3,2,1) apply -
      apply (drule not_le_imp_less)
      apply (induct "(skip_n_productions_op op n, lxs)" "(lgc'', y, ys, lxs'')" arbitrary: n xs op lxs x  lxs' lgc'' y ys lxs'' lgc' rule: produce_inner_alt[consumes 1])
      subgoal for h lxs' lgc''' n op lgc'' y ys lxs'' xs x lxs''' lgc'
        apply (subst (asm) (2) produce_inner.simps)
        apply (auto split: prod.splits list.splits llist.splits if_splits)
          apply hypsubst_thin
          apply (metis eq_LConsD ldropn_0 skip_n_productions_op_0)
        subgoal
          apply (subst (asm) (3) produce.code)
          apply (subst produce.code)
          apply (auto split: option.splits)
          apply (metis (no_types, lifting) drop_eq_Nil2 iless_Suc_eq ldropn_eq_LNil ldropn_shift length_Cons less_le_not_le linorder_le_less_linear llength_LCons lshift.simps(1) lshift.simps(2))
          done
        subgoal
          apply hypsubst_thin
          apply (subst (asm) (3) produce.code)
          apply (subst produce.code)
          apply (auto split: option.splits)
          apply (metis append.right_neutral append_eq_conv_conj cancel_comm_monoid_add_class.diff_cancel enat_ile enat_ord_simps(1) ldropn_shift le_zero_eq lshift.simps(1) skip_n_productions_op_0 zero_le)
          done
        done
      subgoal for h x xs lxs' lgc'a op n xa xsa lxs'a
        apply (subst (asm) produce_inner.simps)
        apply (auto split: prod.splits list.splits llist.splits if_splits)
        apply hypsubst_thin
        apply (metis ldropn_shift lhd_LCons lshift.simps(2))
        done
      done
    done
  subgoal for op lxs n
    apply (subst (3 4) produce.code)
    apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits list.splits option.splits)
    subgoal premises prems for lgc' x xs lxs' lgc'' y ys lxs''
      using prems(2,3,1) apply -
      apply (induct "(op, lxs)" "(lgc', x, xs, lxs')" arbitrary: op lxs x xs lxs' n lgc'' rule: produce_inner_alt[consumes 1])
      subgoal for op h lxs' lgc'a x xs lxs'a n lgc''
        apply (subst (asm) (2) produce_inner.simps)
        apply (auto split: prod.splits list.splits llist.splits if_splits)
        apply force
        done
      subgoal
        apply (subst (asm) produce_inner.simps)
        apply (auto split: prod.splits list.splits llist.splits if_splits)
          apply (smt (z3) Suc_diff_Suc Suc_lessD drop_eq_Nil2 ldropn_Suc_LCons ldropn_ltl ldropn_shift less_or_eq_imp_le ltl_ldropn produce_inner_Some_produce produce_skip_n_productions_op_LCons lshift.cong_base lshift.simps(1))
         apply (metis (no_types, lifting) length_Cons lessI ltl_simps(2) lshift.cong_refl shift_eq_shift_ldropn_length)
        apply (smt (verit, best) ldropn_0 ldropn_Suc_LCons ldropn_ltl ldropn_shift length_Cons length_drop list.sel(3) ltl_ldropn not_gr_zero not_less_eq lshift.cong_refl tl_drop zero_less_Suc zero_less_diff)
        done
      done
    done
  done

lemma produce_skip_n_productions_op_compose_op[simp]:
  "produce (skip_n_productions_op (compose_op lgc1 lgc2) n) lxs = produce (compose_op lgc1 (skip_n_productions_op lgc2 n)) lxs"
  apply (subst produce_compose_op_correctness)
  apply (simp add: produce_compose_op_correctness produce_skip_n_productions_op_correctness)
  done

lemma produce_inner_Some_lfinite_produce_lfinite:
  "produce_inner (op, lxs) = Some (lgc', x, xs, lxs') \<Longrightarrow> lfinite (produce op lxs) \<Longrightarrow> lfinite lxs \<Longrightarrow> lfinite (produce lgc' lxs')"
  apply (induct "(op, lxs)" "(lgc', x, xs, lxs')" arbitrary: op lxs rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs'' lgc''
    apply (subst (asm) (3) produce.code)
    apply (auto split: option.splits)
     apply (subst (asm) produce_inner.simps)
     apply (simp add: produce_inner_None_produce_LNil)
    apply (subst (asm) produce_inner.simps)
    apply simp
    done
  subgoal for op h
    apply (subst (asm) produce.code)
    apply (auto split: option.splits)
     apply (subst (asm) produce_inner.simps)
     apply simp
    apply (subst (asm) produce_inner.simps)
    apply simp
    done
  done

lemma lfinite_produce:
  "lfinite lxs \<Longrightarrow> lfinite (produce op lxs)"
  apply (induct lxs arbitrary: op rule: lfinite_induct)
   apply (metis lfinite_LNil lnull_def produce_inner_LNil_None produce_inner_None_produce_LNil)
  apply (subst produce.code)
  apply (auto split: option.splits)
  apply (metis ltl_simps(2) not_lnull_conv produce_inner_LCons_Some_cases produce_inner_Some_lfinite_produce_lfinite produce_inner_Some_produce)
  done


inductive prefix_production_LE where
  pf_LE_stop: "apply op h = (lgc', out) \<Longrightarrow> m \<le> length out \<Longrightarrow>
            prefix_production_LE op (LCons h lxs) m (Suc 0)"
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
  "produce_inner (skip_n_productions_op op m, lxs) = Some (lgc', x, xs, lxs') \<Longrightarrow>
   \<exists>n. prefix_production_LE op lxs (Suc m) (Suc n) \<and> lnth (produce op (ltake (Suc n) lxs)) m = x \<and> Suc n \<le> llength lxs"
  apply (induct "(skip_n_productions_op op m, lxs)" "(lgc', x, xs, lxs')" arbitrary: op lxs lgc' lxs' m rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' op lgc'a lxs'a m
    apply (auto split: if_splits)
    subgoal
      apply (drule meta_spec)+
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
         apply (auto simp add:  Suc_ile_eq   enat_0_iff(1) ltake_eq_LNil_iff produce_inner_None_produce_LNil split: prod.splits list.splits option.splits llist.splits)
        apply (metis diff_Suc_eq_diff_pred diff_is_0_eq lappend_llist_of leD less_or_eq_imp_le lnth_LCons' lnth_lappend_llist_of not_less_zero)
        done
      done
    subgoal 
      apply (drule meta_spec[of _ "fst (apply op h)"])
      apply (drule meta_spec[of _ 0])
      apply (drule meta_mp)
       apply simp
      apply safe
      subgoal for n'
        apply (rule exI[of _ "Suc n'"])
        apply safe
          apply (metis One_nat_def add_diff_cancel_right' lessI pf_LE_step plus_1_eq_Suc prod.collapse)
         apply (subst produce.code)
         apply (auto split: option.splits)
          apply (subst (asm) produce_inner.simps)
          apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits list.splits)
         apply (subst (asm) produce_inner.simps)
         apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits list.splits)
         apply (metis cancel_comm_monoid_add_class.diff_cancel lappend_llist_of less_not_refl lnth_lappend_llist_of)
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
     apply (auto simp add: produce_inner_None_produce_LNil split: prod.splits list.splits)
     apply (metis drop_Cons' drop_all linorder_not_less list.discI lnth_LCons' lnth_shift nth_via_drop)
    apply (metis One_nat_def iless_eSuc0 linorder_not_less one_eSuc one_enat_def zero_ne_eSuc)
    done
  done

lemma produce_skip_n_productions_op_LCons_prefix_production_EQ_Ex:
  "produce (skip_n_productions_op op m) lxs = LCons x lxs' \<Longrightarrow>
   \<exists> n . prefix_production_LE op lxs (Suc m) (Suc n) \<and> lnth (produce op (ltake (Suc n) lxs)) m = x \<and> Suc n \<le> llength lxs"
  apply (subst (asm) produce.code)
  apply (auto split: option.splits)
  apply (simp add: produce_inner_skip_n_productions_op_Some_prefix_production_EQ_ex)
  done

lemma lnth_produce_prefix_production_EQ_Ex:
  "lnth (produce op lxs) m = x \<Longrightarrow>
   m < llength (produce op lxs) \<Longrightarrow>
   \<exists> n . prefix_production_LE op lxs (Suc m) (Suc n) \<and> lnth (produce op (ltake (Suc n) lxs)) m = x \<and> Suc n \<le> llength lxs"
  apply (metis ldropn_Suc_conv_ldropn produce_skip_n_productions_op_LCons_prefix_production_EQ_Ex produce_skip_n_productions_op_correctness)
  done

end