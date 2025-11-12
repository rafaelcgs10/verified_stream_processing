theory Input_top

imports
  "../Timely_Infrastructure"
  "Source_op"
begin 

corec input_op where
  "input_op n inps = Choice (cimage (\<lambda> p. case ldropWhile ((=) []) (inps p) of
     LCons (x # xs) lxs \<Rightarrow> 
     Write 
     (input_op (n(p := n p + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (inps (p := LCons xs lxs)))
       p (x, n p + the_enat (llength (ltakeWhile ((=) []) (inps p)))))
      (cfilter (\<lambda> p. ldropWhile ((=) []) (inps p) \<noteq> LNil) c\<UU>))"

lemma step_input_op_elim:
  assumes "step io (input_op n inps) op"
  obtains p x xs lxs where "io = Out p (x, n p + the_enat (llength (ltakeWhile ((=) []) (inps p))))" "ldropWhile ((=) []) (inps p) = LCons (x # xs) lxs"
    "op = input_op (n (p := n p + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (inps(p := LCons xs lxs))" "p \<notin> defaults"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) input_op.code)
  apply (clarsimp split: llist.splits list.splits)
   apply (metis (full_types) ldropWhile_LConsD)
  apply auto
  done

lemma step_input_op_Out_intro[intro]:
  "inps p = LCons (x # xs) lxs \<Longrightarrow>
   ys = inps(p := LCons xs lxs) \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   step (Out p (x, n p)) (input_op n inps) (input_op n ys)"
  apply (subst input_op.code)
  apply (clarsimp split: llist.splits)
  apply (rule SC)
   apply (rule cimage_eqI[rotated])
    apply force
   apply (rule refl)
  apply simp
  apply force
  done

lemma step_input_op_Out_intro2[intro]:
  "ldropWhile ((=) []) (inps p) = LCons (x # xs) lxs \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   step (Out p (x, (n p) + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (input_op n inps) (input_op (n (p := n p + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (inps(p := LCons xs lxs)))"
  apply (subst input_op.code)
  apply (clarsimp split: llist.splits)
  apply (rule SC)
   apply (rule cimage_eqI[rotated])
    apply force
   apply (rule refl)
  apply simp
  apply force
  done

lemma step_input_op_not_Tau[simp]:
  "\<not> step Tau (input_op n inps) op"
  apply (subst input_op.code)
  apply (auto split: llist.splits list.splits dest!: ldropWhile_LConsD)
  done

lemma step_input_op_not_Inp[simp]:
  "\<not> step (Inp p x) (input_op n inps) op"
  apply (subst input_op.code)
  apply (auto split: llist.splits list.splits dest!: ldropWhile_LConsD)
  done

lemma wstep_input_op_simp[simp]:
  "io \<noteq> Tau \<Longrightarrow>
   wstep io (input_op n inps) op = step io (input_op n inps) op"
  unfolding wstep_def
  apply (cases io; simp)
  using converse_rtranclpE apply fastforce
  subgoal
    apply (rule iffI)
    subgoal
      apply clarsimp
      apply (metis converse_rtranclpE step_input_op_elim step_input_op_not_Tau)
      done
    subgoal
      by auto
    done
  done

corec input_top where
  "input_top os caps inps = 
   choice3
     (Choice (cimage (\<lambda> p. case inps p of
          LCons batch lxs \<Rightarrow> (let cap = Cap (caps p) p  in 
                              let os' = produce os cap batch in
                              let os'' = if lxs = LNil then drop_cap os' cap else delay_cap os' cap 1 in
                              Silent (input_top os'' (caps( p := caps p + 1)) (inps(p := lxs)))))
     (cfilter (\<lambda> p. inps p \<noteq> LNil) c\<UU>)))
     (Choice (cimage (\<lambda> p. (case outpu os p of
         x # xs \<Rightarrow> send_output (input_top (os\<lparr> outpu := (outpu os)(p := xs ) \<rparr>) caps inps) p x)) 
     (cfilter (\<lambda> p. outpu os p \<noteq> []) c\<UU>)))
    (let (os', st) = obtain_progress os in
     send_progress (input_top os' caps inps) st)"


lemma step_input_top_elim:
  assumes "step io (input_top os caps inps) op'"
  obtains
    batch lxs p cap os' os'' where "io = Tau" "inps p = LCons batch lxs" 
    "cap = Cap (caps p) p" "os' = produce os cap batch" 
    "os'' = (if lxs = LNil then drop_cap os' cap else delay_cap os' cap 1)"
    "op' = input_top os'' (caps( p := caps p + 1)) (inps(p := lxs))" "p \<notin> defaults"
  | x xs p where "io = Out (Some p) (Inr x)" "outpu os p = x # xs"
    "op'= input_top (os\<lparr> outpu := (outpu os)(p := xs ) \<rparr>) caps inps" "p \<notin> defaults"
  | os' st where "io = Out None (Inl (Inl st))" "obtain_progress os = (os', st)"
    "op'= input_top os' caps inps"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) input_top.code)
  apply (cases io)
  subgoal
    by (auto split: llist.splits prod.splits option.splits list.splits)
  subgoal
    by (force split: llist.splits prod.splits option.splits list.splits)
  subgoal
    by (fastforce simp flip: cin.rep_eq del: disjCI split: llist.splits prod.splits option.splits if_splits list.splits; hypsubst_thin?)
  done



lemma step_input_top_Out_Some_intro[intro!]:
  "outpu os p = x # xs \<Longrightarrow>
   op = input_top (os\<lparr> outpu := (outpu os)(p := xs) \<rparr>) caps inps \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   step (Out (Some p) (Inr x)) (input_top os caps inps) op"
  apply (subst input_top.code)
  apply simp
  apply fastforce
  done

lemma step_input_top_Out_None_intro[intro!]:
  "(os', st) = obtain_progress os \<Longrightarrow>
   op = input_top os' caps inps \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   step (Out None (Inl (Inl st))) (input_top os caps inps) op"
  apply (subst input_top.code)
  apply simp
  apply fast
  done

lemma step_input_top_Tau_intro1[intro]:
  "inps p = LCons batch lxs \<Longrightarrow>
   lxs \<noteq> LNil \<Longrightarrow>
   cap = Cap (caps p) p  \<Longrightarrow>
   os' = produce os cap batch \<Longrightarrow>
   os'' = delay_cap os' cap 1 \<Longrightarrow>
   op = input_top os'' (caps( p := caps p + 1)) (inps(p := lxs)) \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   step Tau (input_top os caps inps) op"
  apply hypsubst_thin
  apply (subst input_top.code)
  apply simp
  apply fastforce
  done

lemma step_input_top_Tau_intro2[intro]:
  "inps p = LCons batch LNil \<Longrightarrow>
   cap = Cap (caps p) p  \<Longrightarrow>
   os' = produce os cap batch \<Longrightarrow>
   os'' = drop_cap os' cap \<Longrightarrow>
   op = input_top os'' (caps( p := caps p + 1)) (inps(p := LNil)) \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   step Tau (input_top os caps inps) op"
  apply hypsubst_thin
  apply (subst input_top.code)
  apply simp
  apply fastforce
  done

lemma step_input_top_Tau_intro3[intro]:
  "inps p = LCons batch lxs \<Longrightarrow>
   cap = Cap (caps p) p  \<Longrightarrow>
   os' = produce os cap batch \<Longrightarrow>
   os'' = (if lxs = LNil then drop_cap os' cap else delay_cap os' cap 1) \<Longrightarrow>
   op = input_top os'' (caps( p := caps p + 1)) (inps(p := lxs)) \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   step Tau (input_top os caps inps) op"
  apply (cases lxs)
   apply (rule step_input_top_Tau_intro2)
        apply simp_all
   apply force
  apply (rule step_input_top_Tau_intro1)
        apply simp_all
  apply force
  done

lemma steps_input_top_Out[intro]:
  "p \<notin> defaults \<Longrightarrow>
   os' = (os\<lparr> outpu := (outpu os)(p := []) \<rparr>) \<Longrightarrow>
   xs = outpu os p \<Longrightarrow>
   steps (map (\<lambda> e. Out (Some p) (Inr e)) xs) (input_top os n inps) (input_top os' n inps)"
  apply (induct "outpu os p" arbitrary: os os' xs)
   apply (simp add: fun_upd_idem)
  subgoal premises prems for a x os os' xs
    using prems(2,3,5) apply -
    apply (drule sym)
    apply simp
    apply (intro relcomppI[rotated])
    apply (rule prems(1))
        apply simp_all
    prefer 4
     apply (rule step_input_top_Out_Some_intro)
       apply assumption
      apply simp_all
    using prems(4) apply simp_all
    done
  done

lemma pred_induct:
  "P 0 \<Longrightarrow> (\<And>nat. P (Nat.nat.pred nat) \<Longrightarrow> P nat) \<Longrightarrow> P n"
  apply (induct n)
   apply auto
  done

lemma relpowpp_commute:
  "step Tau ^^ n OO step Tau =  step Tau OO step Tau ^^ n"
  using relpowp_commute by metis

lemma step_pow_input_top_Tau[intro]:
  "p \<notin> defaults \<Longrightarrow>
   llength (inps p) > n \<Longrightarrow>
   (\<forall> xs \<in> lset (ltake n (inps p)). xs = []) \<Longrightarrow>
   os' = os\<lparr> inter := inter os @ concat ([[(p, t', -1), (p, t' + 1, 1)] .t' \<leftarrow> [cap p..< cap p + n]]) \<rparr> \<Longrightarrow>
   op = input_top os' (cap(p := cap p + n)) (inps(p := ldropn n (inps p))) \<Longrightarrow>
   (step Tau ^^ n) (input_top os cap inps) op"
  apply (induct n arbitrary: os os' cap inps op)
   apply simp
  subgoal premises prems for n os os' cap inps op
    apply (cases "inps p"; simp)
    subgoal
      apply (rule FalseE)
      using prems(2-) apply -
      using enat_0_iff(2) apply force
      done
    subgoal for x lxs
      using prems(2-) apply -
      apply hypsubst_thin
      apply (subst relpowpp_commute)
      apply simp
      apply (rule relcomppI)
       apply (rule step_input_top_Tau_intro1[where p=p and batch=x])
             apply assumption
            apply simp_all
      using enat_0_iff(1) apply force
      apply (rule prems(1))
          apply simp_all
      using Suc_ile_eq apply blast
       apply (metis (no_types, opaque_lifting) eSuc_enat_iff lset_intros(2) ltake_eSuc_LCons)      
      apply (auto simp add: produce_def)
      subgoal
        using upt_conv_Cons by force
      subgoal
        apply (cases os)
        apply clarsimp
        apply (metis eSuc_enat lset_intros(1) ltake_eSuc_LCons)
        done
      subgoal
        apply (cases os)
        apply clarsimp
        apply (metis eSuc_enat lset_intros(1) ltake_eSuc_LCons)
        done
      done
    done
  done

lemma ldropWhile_lshift:
  "x \<in> set xs \<Longrightarrow>
   \<not> P x \<Longrightarrow>
   ldropWhile P (xs @@- lxs) = dropWhile P xs @@- lxs"
  apply (induct xs)
   apply auto
  done

lemma ldropWhile_lshift2:
  "\<forall> x \<in> set xs. P x \<Longrightarrow>
   ldropWhile P (xs @@- lxs) = ldropWhile P lxs"
  apply (induct xs)
   apply auto
  done

lemma concat_eq_Cons_conv:
  "concat ys = x # xs = (\<exists>xs' xss' xss''. ys = xss' @ (x # xs') # xss'' \<and> xs = xs' @ concat xss'' \<and> (\<forall> x \<in> set xss'. x = []))"
  apply (induct ys)
   apply simp
  apply simp
  subgoal for y ys
    apply safe
    subgoal
      apply simp
      apply (metis append_Cons set_ConsD)
      done
    subgoal
      apply simp
      apply (metis append_Cons concat.simps(2) concat_append concat_eq_Nil_conv self_append_conv2)
      done
    subgoal
      apply simp
      apply (metis (no_types, opaque_lifting) List.set_empty append_eq_Cons_conv empty_iff)
      done
    subgoal
      apply simp
      apply (metis Cons_eq_appendI Nil_eq_concat_conv concat.simps(2) concat_append empty_append_eq_id)
      done
    done
  done

lemma ldropWhile_LCons:
  "ldropWhile P lxs = LCons y lys = (\<exists> zs. lxs = zs @@- LCons y lys \<and> (\<forall> z \<in> set zs. P z) \<and> \<not> P y)"
  apply (intro iffI)
  subgoal
    apply (subgoal_tac "lfinite (ltakeWhile P lxs)")
    subgoal
      apply rotate_tac
      apply (induct "ltakeWhile P lxs" arbitrary: lxs rule: lfinite_induct)
      subgoal
        by (metis dropWhile.simps(1) dropWhile_eq_Nil_conv lappend_code(1) lappend_ltakeWhile_ldropWhile llist.collapse(1) llist.sel(1) llist.simps(3) lshift.simps(1) ltakeWhile_eq_LNil_iff)
      subgoal for lxs
        apply (cases lxs; clarsimp split: if_splits)
        apply (metis lshift.simps(2) set_ConsD)
        done
      done
    subgoal
      using lfinite_ltakeWhile by fastforce
    done
  subgoal
    apply (elim conjE exE)
    subgoal for zs
      apply (induct zs arbitrary: lxs)
       apply auto
      done
    done
  done

(* FIXME: move me *)
lemma lshift_assoc:
  "xs @@- ys @@- lxs = (xs @ ys) @@- lxs"
  apply (induct xs arbitrary: ys)
   apply auto
  done
lemma ltakeWhile_lfshift:
  "x \<in> set xs \<Longrightarrow>
   \<not> P x \<Longrightarrow>
   ltakeWhile P (xs @@- lxs) = llist_of (takeWhile P xs)"
  apply (induct xs arbitrary: lxs)
   apply auto
  done


definition "input_invar t xs outp = (\<forall> p. outp p = concat (map (\<lambda> (xs, t). map (\<lambda> x. (x, t)) xs) (zip (xs p) ([t p..< t p + length (xs p)]))))"

lemma upt_append_length:
  "xs @ y # ys = [a..<b] \<Longrightarrow>
   y = length xs + a"
  by (metis Groups.add_ac(2) diff_add_inverse length_upt nat_le_iff_add upt_eq_lel_conv)

lemma input_invar_elim:
  "input_invar t buf outp \<Longrightarrow>
   outp p = (y, t') # xs \<Longrightarrow>
   \<exists> l ys zs. (\<forall> x \<in> fst ` set l. x = []) \<and> t' = t p + length l \<and>
   buf p = map fst (l @ (y # ys, t') # zs) \<and>
   [t p..< (t p) + (length (buf p))] = map snd (l @ (y # ys, t') # zs) \<and> input_invar (t(p := t p + length l)) (buf( p := ys # map fst zs)) (outp(p := xs))"
  unfolding input_invar_def
  apply (simp add: concat_eq_Cons_conv map_eq_append_conv del: upt_Suc)
  apply safe
  apply (subst (asm) zip_eq_conv)
   apply (simp del: upt_Suc)
  apply (elim conjE)
  apply (drule sym[of _ "buf p"])
  apply hypsubst_thin
  subgoal for xs' xss' xss'' l l' a b zs z zsa
    apply (rule exI[of _ l])
    apply (intro conjI ballI)
    subgoal for x
      apply (cases x)
      subgoal for xs t''
        apply (drule bspec[of _ _ "map (\<lambda> x. (x, t'')) xs"])
         apply auto
        done
      done
    subgoal
      apply (simp del: upt_Suc)
      apply (drule upt_append_length)
      apply simp
      done
    subgoal
      apply (rule exI[of _ zsa])
      apply (rule exI[of _ zs])
      apply (auto simp del: upt_Suc)
      apply (subst upt_conv_Cons)
       apply (auto simp del: upt_Suc)
      subgoal
        apply (drule upt_append_length)
        apply simp
        done
      subgoal
        by (metis (no_types, lifting) dataflow_topology_from_tree.followed_by_summary diff_add_inverse le_Suc_ex length_map length_upt upt_eq_lel_conv zip_map_fst_snd)
      done
    done
  done

lemma input_invar_extend[intro]:
  "input_invar t buf outp \<Longrightarrow>
   input_invar t (buf(p := buf p @ [batch])) (outp(p := outp p @ map (\<lambda>os. (os, (t p) + (length (buf p)))) batch))"
  unfolding input_invar_def
  apply auto
  done

lemma input_invar_Cons[intro]:
  "input_invar t (buf(p := [] # buf')) outp \<Longrightarrow>
   input_invar (t(p := Suc (t p))) (buf(p := buf')) outp"
  unfolding input_invar_def
  apply (simp del: upt.upt_Suc)
  apply (subst upt_conv_Cons)
   apply simp_all
  done

lemma input_invar_cong:
  "input_invar t' buf' op' \<Longrightarrow>
   t = t' \<Longrightarrow> buf = buf' \<Longrightarrow> op = op' \<Longrightarrow>
   input_invar t buf op"
  by simp

(* FIXME: move me *)
lemma ltakeWhile_lshift:
  "\<forall> x \<in> set xs. P x \<Longrightarrow>
   ltakeWhile P (xs @@- lxs) = xs @@- ltakeWhile P lxs"
  apply (induct xs)
   apply auto
  done
lemma llenght_lshift[simp]:
  "llength (xs @@- lxs) = length xs + llength lxs"
  apply (induct xs)
  using enat_0 apply fastforce
  apply clarsimp
  apply (metis eSuc_enat iadd_Suc)
  done

(* FIXME: move me *)
lemma bisim_refl_alt:
  "op = op' \<Longrightarrow> bisim op op'"
  using bisim_refl by auto

end
