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


(* 
lemma compile_dataflow_input_top_input_op:
  "(compile_dataflow (Logic (input_top (Cap i 1) inps)) :: (1 \<times> 1, 1 \<times> 1, 'b \<times> nat) op) \<approx> map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (input_op i inps)"
  unfolding compile_dataflow_def Let_def
  apply (simp split: prod.splits)
  apply (intro conjI allI impI)
  subgoal for su op
    oops
    using dataflow_op_input_top_input_op[where sg="init_subgraph su", simplified, where i=i and inps=inps] apply -
    apply (drule meta_mp)
    subgoal
      unfolding compile_dataflow_tree_def Let_def 
      apply (simp split: if_splits)
      subgoal
        unfolding compile_dataflow_tree_def Let_def weights_to_graph_fun_def no_self_loop_checker_def implementation_graph_checker_def enum_location_def enum_num1_def enum_port_def 
        by (clarsimp split: if_splits)
      subgoal
        unfolding compile_dataflow_tree_def Let_def weights_to_graph_fun_def no_self_loop_checker_def implementation_graph_checker_def enum_location_def enum_num1_def enum_port_def 
        by (clarsimp split: if_splits)
      done
    subgoal premises prems
      apply (rule wbisim_trans[rotated])
      apply (rule prems(2))
      apply (rule wbisim_refl_alt)
      apply (rule arg_cong2[where f=dataflow_op])
      subgoal
        using prems(1) apply -
        apply (clarsimp simp add: compile_dataflow_tree_Logic)
        subgoal premises
          apply (rule ext)+
          unfolding enum_location_def enum_num1_def enum_port_def 
          apply (auto simp add: compile_dataflow_tree_Logic split: if_splits)
          done
        done
      subgoal
        using prems(1) apply -
        apply (clarsimp simp add: compile_dataflow_tree_Logic)
        done
      done
    done
  done *)

lemma input_top_correctness:
  "wtraced (compile_dataflow (Logic (input_top (Cap i 1) inps)) :: (1 \<times> 1, 1 \<times> 1, 'b \<times> nat) op) ios \<Longrightarrow>
   ios = (lmap (\<lambda> (n, t). VOut (1, 0) (n, t)) (lconcat (lmap (\<lambda> (xs, t). map (\<lambda> n. (n, t)) xs) (lzip inps (iterates Suc i)))))"
  oops

abbreviation "send_output op p x \<equiv> Write op (Some p) (Inr x)"
abbreviation "send_progress op st \<equiv> Write op None (Inl (Inl st))"

abbreviation "obtain_progress os \<equiv> (os\<lparr> consu := [], inter := [], produ := [] \<rparr>, \<lparr> cons = consu os, inte = inter os, prod = produ os\<rparr>)"


corec input_top where
  "input_top os inps = 
   choice2 
     (Choice (cimage (\<lambda> p. 
     choice2
       (case inps p of
         LNil \<Rightarrow> Silent (input_top (deactivate_port os p) inps)
       | LCons batch lxs \<Rightarrow> (let last_t = stash os p in 
                             case obtain_cap os last_t p of
                               (_, None) \<Rightarrow> Silent \<oslash>
                             | (os', Some cap) \<Rightarrow>
                                let os'' = produce os' cap batch in
                                let os''' = delay_cap os'' cap 1 in
                                Silent (input_top (os'''\<lparr> stash := (stash os)(p := last_t + 1) \<rparr>) (inps(p := lxs)))))
       (case get_output os p of
         (os', None) \<Rightarrow> Silent (input_top os' inps)
       | (os', Some x) \<Rightarrow> send_output (input_top os' inps) p x)
     ) c\<UU>))
    (let (os', st) = obtain_progress os in
     send_progress (input_top os' inps) st)"

thm step_id_op_cases

lemma step_input_top_elim:
  assumes "step io (input_top os inps) op'"
  obtains
    batch lxs p last_t os' os'' os''' cap where "io = Tau" "inps p = LCons batch lxs" "last_t = stash os p"
    "obtain_cap os last_t p = (os', Some cap)" "os'' = produce os' cap batch"
    "os''' = delay_cap os'' cap 1" "op' = input_top (os'''\<lparr> stash := (stash os)(p := last_t + 1) \<rparr>) (inps(p := lxs))" "p \<notin> defaults"
  | batch lxs p last_t os' where "io = Tau" "inps p = LCons batch lxs" "last_t = stash os p"
    "obtain_cap os last_t p = (os', None)" "op' = \<oslash>" "p \<notin> defaults"
  | p where "io = Tau" "inps p = LNil" "op' = input_top (deactivate_port os p) inps" "p \<notin> defaults"
  | p os' where "io = Tau" "get_output os p = (os', None)" "op' = input_top os' inps" "p \<notin> defaults"
  | p os' x where "io = Out (Some p) (Inr x)" "get_output os p = (os', Some x)"
    "op' = input_top os' inps" "p \<notin> defaults"
  | os' st where "io = Out None (Inl (Inl st))" "obtain_progress os = (os', st)"
    "op' = input_top os' inps"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) input_top.code)
  apply (cases io)
  subgoal
    by (auto split: llist.splits prod.splits option.splits)
  subgoal
    by (auto split: llist.splits prod.splits option.splits)
  subgoal
    apply (clarsimp simp flip: cin.rep_eq del: disjCI split: llist.splits prod.splits option.splits if_splits; hypsubst_thin?)
    apply (elim disjE)
    subgoal
      apply (clarsimp simp flip: cin.rep_eq del: disjCI split: llist.splits prod.splits option.splits if_splits; hypsubst_thin?)
           apply force+
      done
    subgoal
      apply (auto simp flip: cin.rep_eq del: disjCI split: llist.splits prod.splits option.splits if_splits; hypsubst_thin?)
      done
    done
  done

(* 
lemma step_input_top_Out_Some_intro[intro!]:
  "inps = LCons (x # xs) inps' \<Longrightarrow>
   op = push (Silent (input_top (Cap (time c + 1) 1) (ints @ [(1, time c, -1), (1, time c + 1, 1)]) (prds @ [(1, time c, int (length (x # xs)))]) inps')) (1 :: 1) (map (\<lambda> x. (x, c)) xs) \<Longrightarrow>
   io = Out (Some 1) (Inr (x, time c)) \<Longrightarrow>
   step io (input_top c ints prds inps) op"
  apply (subst input_top.code)
  apply (auto simp add: comp_def)
  done

lemma step_input_top_Tau_intro[intro!]:
  "inps = LCons [] inps' \<Longrightarrow> 
   op = input_top (Cap (time c + 1) 1) (ints @ [(1, time c, -1), (1, time c + 1, 1)]) (prds @ [(1, time c, 0)]) inps' \<Longrightarrow>
   step Tau (input_top c ints prds inps) op"
  apply (subst input_top.code)
  apply (auto simp add: comp_def)
  done

lemma step_input_top_Out_None_intro[intro]:
  "op = input_top c [] [] inps \<Longrightarrow>
   step (Out None (Inl (Inl \<lparr> cons = [], inte = ints, prod = prds\<rparr>))) (input_top c ints prds inps) op"
  apply (subst input_top.code)
  apply (auto simp add: comp_def)
  done


lemma step_input_top_Out_None_end_intro[intro]:
  "op = \<oslash> \<Longrightarrow>
   inps = LNil \<Longrightarrow>
   step (Out None (Inl (Inl \<lparr> cons = [], inte = ints, prod = prds @ [(1, time c, -1)]\<rparr>))) (input_top c ints prds inps) op"
  apply (subst input_top.code)
  apply (auto simp add: comp_def)
  done
 *)
(* 
lemma ldropWhile_steps_input_top:
  "lfinite (ltakeWhile ((=) []) inps) \<Longrightarrow>
   ldropWhile ((=) []) inps = LCons (x # xs) inps' \<Longrightarrow>
   ints' = concat (map (\<lambda> t. [(out c, t, -1), (out c, Suc t, 1)]) [time c..<time c + the_enat (llength (ltakeWhile ((=) []) inps))]) \<Longrightarrow>
   steps (replicate (the_enat (llength (ltakeWhile ((=) []) inps))) Tau)
  (input_top c ints prds inps) (input_top (Cap (time c + the_enat (llength (ltakeWhile ((=) []) inps))) (out c)) (ints @ ints') prds (LCons (x # xs) inps'))"
  apply (induct "ltakeWhile ((=) []) inps"  arbitrary: c inps ints ints' rule: lfinite_induct)
  subgoal for inps c
    apply (cases "ltakeWhile ((=) []) inps"; simp; hypsubst_thin)
    apply (metis ldropWhile_simps(1,2) ltakeWhile_simps(2) neq_LNil_conv)
    done
  subgoal premises prems for inps c ints ints'
    using prems(1,2,4-) apply -
    apply (cases inps; simp split: if_splits; hypsubst)
    subgoal for z lxs
      apply (rule steps_intro[where xs="replicate (the_enat (llength (ltakeWhile ((=) []) lxs))) Tau"])
      apply (rule step_input_top_Tau_intro)
         apply (rule refl)+
      defer
      subgoal
        apply simp
        apply (metis (no_types, lifting) llength_ltakeWhile_eq_infinity replicate.simps(2) the_enat_eSuc)
        done
      subgoal
        apply (subst (1 2) the_enat_eSuc)
        using llength_eq_infty_conv_lfinite apply blast
        apply (rule steps_append_intro)
          apply (rule prems(3))
            apply force
        apply simp
        apply (rule refl)+
         defer
         apply simp
        apply (simp del: upt_Suc)
        apply (rule arg_cong3[where f="input_top (Cap (Suc (dataflow_topology_from_tree.followed_by (time c) (the_enat (llength (ltakeWhile ((=) []) lxs))))) (out c))"])
          apply simp_all
        apply (intro impI)
        apply (subst (2) upt_conv_Cons)
         apply auto
        done
      done
    done
  done *)


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


find_theorems zipf

definition "input_invar t xs outp = (\<forall> p. outp p = concat (map (\<lambda> (xs, t). map (\<lambda> x. (x, t)) xs) (zip (xs p) ([t p..< t p + length (xs p)]))))"

lemma upt_append_length:
  "xs @ y # ys = [a..<b] \<Longrightarrow>
   y = length xs + a"
  by (metis Groups.add_ac(2) diff_add_inverse length_upt nat_le_iff_add upt_eq_lel_conv)

(* input_invar (t(p := dataflow_topology_from_tree.followed_by (t p) (the_enat (llength (ltakeWhile ((=) []) (xs p @@- inps p)))))) (xs(p := ys # map fst zs)) (outpu (os\<lparr>outpu := (outpu os)(p := xs')\<rparr>)) *)

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

lemma dataflow_op_input_top_input_op:
  "edges sg = (\<lambda> _. []) \<Longrightarrow>
   input_invar t xs (outpu os) \<Longrightarrow>
   dataflow_op sg (map_op (case_option (Inl nid) (\<lambda>p. Inr (nid, p))) (case_option (Inl nid) (\<lambda>p. Inr (nid, p))) (input_top (os\<lparr> stash := (\<lambda> p. t p + length (xs p)) \<rparr>) inps)) \<approx>
   map_op (\<lambda> p. (nid, p)) (\<lambda> p. (nid, p)) (input_op t (\<lambda> p. xs p @@- inps p ))"
proof (coinduction arbitrary: inps t os xs rule: weakBisimWeakUptoBisimCong)
  case SIM1
  then show ?case 
    apply -
    unfolding wsim_def
    apply safe
    subgoal for io op1'
    apply (elim step_map_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp split: list.splits if_splits; hypsubst_thin)
      subgoal for nida p op'' x io' op''a os' xs'
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
                apply (rule exI[of _ "t(p := dataflow_topology_from_tree.followed_by (t p) (the_enat (llength (ltakeWhile ((=) []) (xs p @@- inps p)))))"])
              apply (rule exI[of _ "os\<lparr> outpu := (outpu os)(p := xs') \<rparr>"])
              apply (rule exI[of _ "xs(p := ys # map fst zs)"])
                apply (intro exI conjI[rotated])
                prefer 2
              subgoal
                apply (rule arg_cong3[where f=map_op])
                  apply simp_all
                apply (rule arg_cong2[where f=input_op])
                 apply simp_all
                apply (rule ext)
                apply auto
                done
              defer
              subgoal
                apply (rule arg_cong2[where f=dataflow_op])
                 apply simp_all
                apply (rule arg_cong3[where f=map_op])
                  apply simp_all
                apply (rule arg_cong2[where f=input_top])
                 apply simp_all
                apply (cases os; simp)
               apply (intro conjI ext)
                apply auto
            apply (subst ltakeWhile_lfshift[where x="y # ys"])
               apply simp_all
             apply (subst takeWhile_append2)
              apply force
             apply (auto split: prod.splits)                  
                done
              subgoal
            apply (subst ltakeWhile_lfshift[where x="y # ys"])
                  apply simp_all
            apply (subst takeWhile_append2)
                 apply force
                apply auto
                done
              done
            done
          done
        done


end
                apply (drule sym[of _ "xs p"])
                  apply auto
        apply (subst ltakeWhile_lfshift[where x="y # zsa"])
                    apply (auto simp add: takeWhile_map takeWhile_tail comp_def)
                  apply (metis (mono_tags, lifting) takeWhile_eq_all_conv)
                  done
                subgoal
                  by auto
                done
              subgoal
                apply auto
                subgoal
                  
                  

                find_theorems "concat (map _ _) = _"




                defer
                apply (intro allI)
                apply (rule refl)
               defer
              subgoal premises prems3
                using prems(3) prems3(6)[symmetric] apply -
                apply (rule bisim_dataflow_op_cong)
                apply (rule bisim_map_op)



              find_theorems bisim name: refl
              


end
      defer
           apply assumption
              apply simp
          apply (intro conjI)
               apply (rule refl)+
              apply (drule spec[of _ p])
              apply (simp add: lconcat_correct)



          find_theorems Coinductive_List.lconcat ltakeWhile





end
      apply simp
      apply (simp add: comp_def)
      apply (intro relcomppI)
        defer
        apply (rule wb_upto_b_writes)
        apply (rule wb_upto_b_Silent)
      apply (rule wb_upto_b_base)
        apply (rule exI[of _ lxs])
      apply (rule exI[of _ "Suc i"])
      apply (rule exI[of _ "ints @ [(1, i, - 1), (1, Suc i, 1)]"])
      apply (rule exI[of _ "prds @ [(1, i, 1 + int (length xs))]"])
      apply (intro exI conjI[rotated])
            apply assumption
           apply (rule refl)+
       apply (simp add: input_op_LCons_write_simp)
      apply (rule wbisim_writes_cong)
      apply (rule wbisim_Silent_cong)
       apply (rule wbisim_refl)
      apply (rule bisim_trans)
      apply (rule dataflow_writes_comm)
      apply (rule bisim_writes_cong)
      apply (rule dataflow_Silent_comm)
      done

         apply (rule bisim_refl)


          apply (rule dataflow_op_wbisim_cong[where sg=sg])
         apply (rule wbisim_map_op[where f="case_option (Inl nid) (\<lambda>p. Inr (nid, 1))"])
          apply assumption       
          apply assumption


      defer
          defer
        apply (rule wb_upto_b_writes)
        apply (rule wb_upto_b_Silent)
        apply (rule wb_upto_b_base)
      apply (rule exI[of _ lxs])
      apply (rule exI[of _ "Suc i"])
      apply (rule exI[of _ "ints @ [(1, i, - 1), (1, Suc i, 1)]"])
      apply (rule exI[of _ "prds @ [(1, i, 1 + int (length xs))]"])
      apply (intro exI conjI[rotated])
            apply assumption
         apply (rule refl)+
       apply (simp add: input_op_LCons_write_simp)
       apply (rule wbisim_writes_cong)
      apply (rule wbisim_Silent_cong)
       apply (rule wbisim_refl)
      subgoal premises
        apply (induct xs)
        subgoal
          apply simp
          apply (subst dataflow_op.code)
          apply simp
          using Choice_singleton_bisim apply blast
          done
        subgoal for x xs'
          apply (simp add: writes_Cons_simp)
          apply (subst dataflow_op.code)
          apply simp
          apply (rule Choice_singleton_bisim_alt)
          sledgehammer
          
       


          find_theorems writes Cons



end

      apply (rule step_bisim)
      apply safe
      subgoal
    apply (elim step_map_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp; hypsubst_thin)
        sledgehammer

      find_theorems writes bisim

          defer
          defer
          apply (rule bisim_refl)
      defer
      apply auto[1]




      find_theorems Choice bisim

         apply (rule bisim_refl)
        apply (rule bc_Choice)
      unfolding rel_cset_def
        apply simp
      apply (rule rel_setI; simp; hypsubst_thin?)

      thm rel_setI

      find_theorems rel_cset name: I


      defer
      apply (rule wbisim_refl)
      subgoal
        apply (rule wb_upto_b_Sim)
        subgoal
      unfolding sim_def
       apply auto

      find_theorems steps name: elim

      apply (rule wb_upto_b_base)
      apply (intro exI conjI[rotated])
        apply assumption
       apply (rule refl)+

      term wbisim_cong

      apply simp


       apply (rule refl)

      find_theorems writes map_op

      apply (subst (2) input_top.code)
      apply (auto split: list.splits)

end
      apply force
      done
    subgoal
      apply (intro exI conjI[rotated])
       apply (rule wbcr_base)
       apply (intro conjI exI)
         apply (rule refl)+
       apply (simp_all add: input_op_LCons_Nil)
      done
    subgoal for nida op'' io' op''a
      apply (simp add: input_op_LNil)
      using dataflow_op_end_op apply blast
      done
    subgoal
      apply (intro exI conjI[rotated])
       apply (rule wbcr_base)
       apply (intro conjI exI)
         apply (rule refl)+
       apply simp_all
      done
    done
next
  case SIM2
  then show ?case 
    apply -
    apply (elim step_map_op_elim step_input_op_elim conjE; simp; hypsubst_thin)
    subgoal for io' op'' x xs inps'
      apply (intro exI conjI[rotated])
       apply (intro conjI wbcr_base)
       apply (rule exI)
      apply (rule exI)
       apply (rule exI[of _ "ints @ concat (map (\<lambda> t. [(1, t, -1), (1, Suc t, 1)]) [ i..<i + the_enat (llength (ltakeWhile ((=) []) inps))])"]) 
      apply (rule exI[of _ "prds @ [(1, dataflow_topology_from_tree.followed_by i (the_enat (llength (ltakeWhile ((=) []) inps))), 1)]"])
      apply (intro exI conjI[rotated])
      apply assumption
        apply (rule refl)+
      unfolding wstep_def
      apply simp
      apply (rule relcomppI)
      apply (rule relpowp_imp_rtranclp) 
      apply (rule steps_Tau_dataflow_op_Tau_intro[where sg=sg])
         apply (rule steps_map_op)
         apply (rule refl)+
      defer
      apply (rule ldropWhile_steps_input_top[where  c="Cap i 1", simplified])
            apply (meson ldropWhile_LCons_lfinite_ltakeWhile)
      apply assumption+
           apply (rule refl)+
      apply (rule relcomppI[rotated])
      apply (rule rtranclp.intros(1))
      apply (rule step_Out_dataflow_op_Out_Inr_intro)
      apply (rule step_map_op[where f="case_option (Inl nid) (\<lambda>p. Inr (nid, 1))" and g="case_option (Inl nid) (\<lambda>p. Inr (nid, 1))"])
      apply simp_all
      apply (rule step_input_top_Out_Some_intro)
      apply (rule refl)+
       apply simp_all
      done
    done
qed

end