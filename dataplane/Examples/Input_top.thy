theory Input_top

imports
  "../Timely_Infrastructure"
  "../Utils"
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


lemma input_top_correctness:
  "wtraced (compile_dataflow (Logic (input_top (Cap i 1) inps)) :: (1 \<times> 1, 1 \<times> 1, 'b \<times> nat) op) ios \<Longrightarrow>
   ios = (lmap (\<lambda> (n, t). VOut (1, 0) (n, t)) (lconcat (lmap (\<lambda> (xs, t). map (\<lambda> n. (n, t)) xs) (lzip inps (iterates Suc i)))))"
  oops

abbreviation "send_output op p x \<equiv> Write op (Some p) (Inr x)"
abbreviation "send_progress op st \<equiv> Write op None (Inl (Inl st))"

abbreviation "obtain_progress os \<equiv> (os\<lparr> consu := [], inter := [], produ := [] \<rparr>, \<lparr> cons = consu os, inte = inter os, prod = produ os\<rparr>)"

abbreviation "drop_cap os cap \<equiv> (os\<lparr> inter := inter os @ [(out cap, time cap, -1)] \<rparr>)"

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

lemma ldropWhile_steps_input_top:
  "lfinite (ltakeWhile ((=) []) (inps p)) \<Longrightarrow>
   ldropWhile ((=) []) (inps p) = LCons (x # xs) lxs \<Longrightarrow>
   offset = the_enat (llength (ltakeWhile ((=) []) (inps p))) \<Longrightarrow>
   ints = concat (map (\<lambda> t. [(p, t, -1), (p, Suc t, 1)]) [caps p..<caps p + offset]) \<Longrightarrow>
   prods = concat (map (\<lambda> t. [(p, t, 0)]) [caps p..<caps p + offset]) \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   os' = os\<lparr> inter := inter os @ ints, produ := produ os @ prods \<rparr> \<Longrightarrow>
   caps' = caps(p := caps p + offset) \<Longrightarrow>
   inps'= inps(p := LCons (x # xs) lxs) \<Longrightarrow>
   steps (replicate offset Tau)
   (input_top os caps inps) (input_top os' caps' inps')"
  apply (induct "ltakeWhile ((=) []) (inps p)"  arbitrary: inps ints prods caps offset os os' caps' inps' rule: lfinite_induct)
  subgoal for inps c
    apply (cases "ltakeWhile ((=) []) (inps p)"; simp; hypsubst_thin)
    apply (metis fun_upd_triv ldropWhile_simps(1,2) ltakeWhile_simps(2) neq_LNil_conv)
    done
  subgoal premises prems for inps ints prods caps offset os os' caps' inps'
    using prems(1,2,4-) apply -
    apply (cases "inps p"; simp flip: upt.upt_Suc split: if_splits; hypsubst?)
    subgoal for x lxs
      apply (subst (1 2 3 4) the_enat_eSuc)
      using llength_eq_infty_conv_lfinite apply blast
      using llength_eq_infty_conv_lfinite apply blast
      apply (subst (asm) (1 2) the_enat_eSuc)
      using llength_eq_infty_conv_lfinite apply blast
      using llength_eq_infty_conv_lfinite apply blast
      apply (simp flip: upt.upt_Suc)
      apply (cases offset; simp flip: upt.upt_Suc)
      subgoal for offset'
        apply (rule relcomppI)
         apply (rule step_input_top_Tau_intro1)
               apply assumption
              apply force
             apply (rule refl)+
         apply assumption
        apply (simp del: upt.upt_Suc)
        apply (rule prems(3))
                apply simp
               apply simp
              apply simp
             apply (rule refl)+
           apply assumption
          defer
          apply simp
         apply simp
        apply (cases os; auto simp flip: upt.upt_Suc simp add: upt_conv_Cons)
        done
      done
    done
  done

(* 
abbreviation "inp_top c ints prds inps \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, (p :: 1)))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, (p :: 1)))) (input_top c ints prds inps)"
abbreviation "id_top buf \<equiv> map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, (p :: 1)))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, (p :: 1)))) (id_op buf)"

lemma dataflow_op_input_top_input_op:
  "inrbufs1 = buf1 (Inr (1, 1)) \<Longrightarrow>
   \<forall> x \<in> set inrbufs1. is_Inr x \<Longrightarrow>
   inrbufs2 = buf2 (Some 1) \<Longrightarrow>
   \<forall> x \<in> set inrbufs2. is_Inr x \<Longrightarrow>
   xs = map projr inrbufs1 \<Longrightarrow>
   ys = map projr inrbufs2 \<Longrightarrow>
   ys @@- xs @@- lconcat (lmap (\<lambda> (xs, t). map (\<lambda> n. (n, t)) xs) (lzip inps2 (iterates Suc i))) =
   lconcat (lmap (\<lambda> (xs, t). map (\<lambda> n. (n, t)) xs) (lzip inps1 (iterates Suc j))) \<Longrightarrow>
   edges sg = (\<lambda> _. []) \<Longrightarrow>
   dataflow_op sg ((map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0 :: 2, 1 :: 1) \<mapsto> Inr (1, 1)] buf1 (inp_top (Cap i (1 :: 1)) ints prds inps2) (id_top buf2)))) \<approx>
   dataflow_op sg (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, p))) (case_option (Inl 1) (\<lambda>p. Inr (1, p))) (input_top (Cap j (1 :: 1)) ints prds inps1))"
proof (coinduction arbitrary: inps1 inps2 i j buf1 buf2 ints prds sg rule: weakBisimWeakUptoBisimCong)
  case SIM1
  then show ?case 
    apply -
    unfolding wsim_def
    apply safe
    subgoal for io op1'
      apply (elim step_map_op_elim step_dataflow_op_elim step_input_top_elim step_comp_op_elim step_id_op_cases conjE; simp split: if_splits option.splits; hypsubst_thin)
      defer
      subgoal for op'' io' op''a p op1' q io'a op''b xa xs lxs
       apply (intro exI conjI)
         apply force
    apply (simp add: comp_def)
        apply (intro relcomppI)
        defer
        oops
 *)



lemma ldropWhile_lshift:
  "x \<in> set xs \<Longrightarrow>
   \<not> P x \<Longrightarrow>
   ldropWhile P (xs @@- lxs) = dropWhile P xs @@- lxs"
  apply (induct xs)
   apply auto
  done

thm lconcat_eq_LCons_conv[of "llist_of (map llist_of ys)", unfolded lconcat_llist_of llist_of_eq_LCons_conv, simplified, no_vars]

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
   \<exists> l ys zs. (\<forall> x \<in> set l. fst x = []) \<and> t' = t p + length l \<and>
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

lemma dataflow_op_input_top_input_op:
  "edges sg = (\<lambda> _. []) \<Longrightarrow>
   input_invar caps xs (outpu os) \<Longrightarrow>
   dataflow_op sg (map_op (case_option (Inl nid) (\<lambda>p. Inr (nid, p))) (case_option (Inl nid) (\<lambda>p. Inr (nid, p))) (input_top os (\<lambda> p. caps p + length (xs p)) inps)) \<approx>
   map_op (\<lambda> p. (nid, p)) (\<lambda> p. (nid, p)) (input_op caps (\<lambda> p. xs p @@- inps p ))"
proof (coinduction arbitrary: inps caps os xs sg rule: weakBisimWeakUptoBisimCong)
  case SIM1
  then show ?case 
    apply -
    unfolding wsim_def
    apply safe
    subgoal for io op1'
      apply (elim step_map_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp split: list.splits if_splits; hypsubst_thin)
      subgoal for nida p op'' x io' op''a xs
        apply (cases x)
        subgoal premises prems for y t'
          using prems apply -
          apply hypsubst_thin
          apply (drule input_invar_elim)
           apply assumption
          apply (elim exE conjE)
          subgoal for l ys zs
            apply (intro exI conjI)
             apply (rule step_wstep)
             apply (rule step_map_op)
              apply (rule step_input_op_Out_intro2[where p=p and x=y])
               apply (subst ldropWhile_LCons)
               apply simp
               apply (rule exI[of _ "map fst l"])
               apply (auto simp add: comp_def split: prod.splits)
              apply (subst lshift_simps(2)[symmetric])
              apply (auto simp only: lshift_assoc)
             apply (subst ltakeWhile_lfshift[where x="y # ys"])
               apply simp_all
             apply (subst takeWhile_append2)
              apply force
             apply (auto split: prod.splits)
            subgoal
              apply (intro relcomppI)
                defer
                apply (rule wb_upto_b_base)
                defer
                apply (rule wbisim_refl)
               apply (rule bisim_refl)
              apply (rule exI[of _ "inps"]) 
              apply (rule exI[of _ ])
              apply (rule exI[of _ "os\<lparr> outpu := (outpu os)(p := xs) \<rparr>"])
              apply (intro exI conjI[rotated])
                apply simp
               apply simp_all
               apply (rule arg_cong3[where f=map_op])
                 apply simp_all
               apply (rule arg_cong2[where f=input_op])
                apply (subst ltakeWhile_lfshift[where x="y # ys"])
                  apply simp_all
                apply (subst takeWhile_append2)
                 apply force
                apply (auto split: prod.splits)   
              apply (rule arg_cong2[where f=dataflow_op])
               apply simp_all
              apply (rule arg_cong3[where f=map_op])
                apply simp_all
              apply (rule arg_cong3[where f=input_top])
                apply simp_all
              apply (cases os; simp)
              apply (intro conjI ext)
              apply auto
              done
            done
          done
        done
      subgoal for op'' io' op''a batch lxs p cap os' os''
        apply (intro exI conjI)
         apply force
        apply (intro relcomppI)
          defer
          apply (rule wb_upto_b_base)
          defer
          apply (rule wbisim_refl)
         apply (rule bisim_refl)
        apply (rule exI[of _ "inps(p := LNil)"])
        apply (rule exI[of _ "caps"])
        apply (rule exI[of _ "os\<lparr> outpu := (outpu os)(p := outpu os p @ _), produ := _, inter := _ \<rparr>"])
        apply (rule exI[of _ "xs( p := xs p @ [batch])"])
        apply (intro exI conjI[rotated])
          apply simp
          apply (rule input_invar_extend[where batch=batch])
          apply assumption               
         apply simp_all
         apply (rule arg_cong3[where f=map_op])
           apply simp_all
         apply (rule arg_cong2[where f=input_op])
          apply simp_all
         apply (rule ext)
         apply clarsimp
         apply (metis shift_LNil snoc_shift)
        apply (rule arg_cong2[where f=dataflow_op])
         apply simp_all
        apply (rule arg_cong3[where f=map_op])
          apply simp_all
        apply (rule arg_cong3[where f=input_top])
          apply simp_all
        apply (cases os; simp)
        apply auto
        done
      subgoal for op'' io' op''a batch lxs p cap os' os''
        apply (intro exI conjI)
         apply force
        apply (intro relcomppI)
          defer
          apply (rule wb_upto_b_base)
          defer
          apply (rule wbisim_refl)
         apply (rule bisim_refl)
        apply (rule exI[of _ "inps(p := lxs)"])
        apply (rule exI[of _ "caps"])
        apply (rule exI[of _ "os\<lparr> outpu := (outpu os)(p := outpu os p @ _), produ := _, inter := _ \<rparr>"])
        apply (rule exI[of _ "xs( p := xs p @ [batch])"])
        apply (intro exI conjI[rotated])
          apply simp
          apply (rule input_invar_extend[where batch=batch])
          apply assumption               
         apply simp_all
         apply (rule arg_cong3[where f=map_op])
           apply simp_all
         apply (rule arg_cong2[where f=input_op])
          apply simp_all
         apply (rule ext)
         apply clarsimp
        apply (rule arg_cong2[where f=dataflow_op])
         apply simp_all
        apply (rule arg_cong3[where f=map_op])
          apply simp_all
        apply (rule arg_cong3[where f=input_top])
          apply simp_all
        apply (cases os; simp)
        apply auto
        done
      subgoal for nida op'' st io' op''a
     apply (intro exI conjI)
         apply force
        apply (intro relcomppI)
          defer
          apply (rule wb_upto_b_base)
          defer
          apply (rule wbisim_refl)
         apply (rule bisim_refl)
                apply (intro exI conjI[rotated])
           defer
        defer
          apply (rule refl)
          apply auto[1]
         apply auto
        done
      done
    done
next
  case SIM2
  then show ?case 
    apply -
    unfolding wsim_def
    apply safe
    apply (elim step_map_op_elim step_input_op_elim conjE; simp split: list.splits if_splits; hypsubst_thin)
    apply (intro conjI exI)
    unfolding wstep_def
    apply (intro relcomppI)

    find_theorems steps


end