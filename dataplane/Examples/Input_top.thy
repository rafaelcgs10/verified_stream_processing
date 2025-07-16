theory Input_top

imports
  "../Timely_Infrastructure"
  "../Utils"
begin 


corec input_top where
  "input_top c inps = (case inps of
    LNil \<Rightarrow> drop_cap c \<oslash>
  | LCons xs lxs \<Rightarrow>
     push 
     (Write (input_top (Cap (time c + 1) (out c)) lxs) (trace (STR ''Managing caps'') None) (Inl (Inl \<lparr> cons = [], inte = [(out c, time c, -1), (out c, time c + 1, 1)], prod = case xs of [] => [] | _ \<Rightarrow> [(out c, time c, length xs)]\<rparr>)))
      (1 :: 1) (map (\<lambda> x. (x, c)) xs))"

lemma step_input_top_elim:
  assumes "step io (input_top c inps) op'"
  obtains
    x xs where "io = Out (Some 1) (Inr (x, time c))" "lhd inps = xs" "hd xs = x" "inps \<noteq> LNil" "xs \<noteq> []"
    "op' = writes (Write (input_top (Cap (time c + 1) (out c)) (ltl inps)) None (Inl (Inl \<lparr> cons = [], inte = [(out c, time c, -1), (out c, time c + 1, 1)], prod = [(out c, time c, length xs)]\<rparr>))) (Some 1) (map (\<lambda> x. Inr (x, time c)) (tl xs))"
  | "io = Out None (Inl (Inl \<lparr>cons = [], inte = [(out c, time c, - 1), (out c, time c + 1, 1)], prod = []\<rparr>)) " "inps \<noteq> LNil" "lhd inps = []" "op' = input_top (Cap (time c + 1) (out c)) (ltl inps)"
  | "inps = LNil" "io = Out None (Inl (Inl \<lparr> cons = [], inte = [(out c, time c, -1)], prod = [] \<rparr>))" "op' = \<oslash>"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) input_top.code)
  apply (simp split: llist.splits)
  apply force
  subgoal for xs lxs
    apply hypsubst_thin
    apply (cases io; simp)
    subgoal
      using step_writes_reads_buf_empty by fastforce
    subgoal for p x
      apply hypsubst_thin
      apply (cases xs; simp)
      subgoal
        by auto
      subgoal
        apply (drule step_Out_writes)
        apply (auto simp add: comp_def)
        done
      done
    subgoal
      apply (cases xs; simp)
      apply force
      apply (drule step_Out_writes)
      apply auto
      done
    done
  done

lemma step_input_top_Out_Some_intro[intro]:
  "inps = LCons xs inps' \<Longrightarrow>
   xs = x # xs' \<Longrightarrow>
   op = writes (Write (input_top (Cap (time c + 1) (out c)) inps') None (Inl (Inl \<lparr> cons = [], inte = [(out c, time c, -1), (out c, time c + 1, 1)], prod = [(out c, time c, length xs)]\<rparr>))) (Some 1) (map (\<lambda> x. Inr (x, time c)) xs') \<Longrightarrow>
   step (Out (Some 1) (Inr (x, time c))) (input_top c inps) op"
  apply (subst input_top.code)
  apply (auto simp add: comp_def)
  done

lemma step_input_top_Out_None_intro[intro]:
  "inps = LCons [] inps' \<Longrightarrow> 
   step (Out None (Inl (Inl \<lparr> cons = [], inte = [(out c, time c, -1), (out c, Suc (time c), 1)], prod = []\<rparr>))) (input_top c inps) (input_top (Cap (Suc (time c)) (out c)) inps')"
  apply (subst input_top.code)
  apply (auto simp add: comp_def)
  done

lemma ldropWhile_LCons_lfinite_ltakeWhile:
  "ldropWhile ((=) []) inps = LCons (x # xs) inps' \<Longrightarrow> lfinite (ltakeWhile ((=) []) inps)"
  by (metis ldropWhile_eq_LNil_iff lfinite_ltakeWhile llist.simps(2))

lemma ldropWhile_steps_input_top:
  "lfinite (ltakeWhile ((=) []) inps) \<Longrightarrow>
   ldropWhile ((=) []) inps = LCons (x # xs) inps' \<Longrightarrow>
   steps (map (\<lambda> t. Out None (Inl (Inl \<lparr> cons = [], inte = [(out c, t, -1), (out c, Suc t, 1)], prod = []\<rparr>))) [time c..<time c + the_enat (llength (ltakeWhile ((=) []) inps))])
  (input_top c inps) (input_top (Cap (time c + the_enat (llength (ltakeWhile ((=) []) inps))) (out c)) (LCons (x # xs) inps'))"
  apply (induct "ltakeWhile ((=) []) inps"  arbitrary: c inps rule: lfinite_induct)
  subgoal for inps c
    apply (cases "ltakeWhile ((=) []) inps"; simp)
    apply (metis ldropWhile_simps(1,2) ltakeWhile_simps(2) neq_LNil_conv)
    done
  subgoal premises prems for inps c
    using prems(1,2,4-) apply -
    apply (cases inps; simp split: if_splits; hypsubst)
    subgoal for z lxs
      apply (rule steps_intro[where xs="map (\<lambda>t. Out None (Inl (Inl \<lparr>cons = [], inte = [(out c, t, - 1), (out c, Suc t, 1)], prod = []\<rparr>))) [Suc (time c)..<time c + the_enat (eSuc (llength (ltakeWhile ((=) []) lxs)))]"])
      apply (rule step_input_top_Out_None_intro)
      apply (rule refl)+
      defer
      subgoal
        apply simp
        apply (subst map_eq_Cons_conv)
        apply auto
        apply (intro exI conjI[rotated])
        apply (rule refl)
        apply (rule upt_conv_Cons)
        apply (metis dataflow_topology_from_tree.le_plus(1) impossible_Cons le_neq_implies_less length_list_of_conv_the_enat lfinite.simps list_of_LCons llength_LCons nat_add_left_cancel_le)
        done
      subgoal
        apply (subst (1 2) the_enat_eSuc)
        using llength_eq_infty_conv_lfinite apply blast
        using prems(3)[where c="Cap (time c + 1) (out c)" and inps=lxs] apply -
        apply (simp split: if_splits)
        done
      done
    done
  done

abbreviation "ex1 \<equiv> Logic (input_top (Cap 0 (1 :: 1)) (LCons [Suc 0, 3] (LCons [9] LNil))) :: (2, 1, (1, _) shared_state + 'c, nat \<times> _) dataflow_tree"
(* 
value [GHC] "eval 20 (compile_dataflow ex1)"
 *)
(*value [GHC] "cfilter ((\<noteq>) []) (eval 20 (compile_dataflow (Comp [ (0, 0) \<mapsto> (0, 0) ] ex1 (Logic \<I>))))" *)

(* value [GHC] "eval 17 (dataflow_op True init_subgraph (input_top (Cap (0 :: nat) 0) (LCons [Suc 0, 2, 3, 9] (LCons [8, 1, 0] LNil))))"
value [GHC] "eval 5 (dataflow_op True init_subgraph (input_top (Cap (0 :: nat) 0) (LCons [Suc 0] (LNil))))"
 *)


(* value [GHC] "eval 20 (compile_dataflow ex13)"

value [GHC] "eval 20 (input_op 0 (LCons [Suc 0, 3] (LCons [] (LCons [9] (LCons [9] LNil)))))"
 *)

abbreviation "ex13 \<equiv> Logic (input_top (Cap 0 (1 :: 1)) (LCons [Suc 0, 3] (LCons [] (LCons [9] (LCons [9] LNil))))) :: (2, 1, (1, _) shared_state + 'c, nat \<times> _) dataflow_tree"

corec input_op :: "nat \<Rightarrow> 'a buf llist \<Rightarrow> (1, 1, 'a \<times> nat) op" where
  "input_op n inps = (case ldropWhile ((=) []) inps of
     LNil \<Rightarrow> \<oslash>
   | LCons (x # xs) lxs \<Rightarrow> Write (input_op (n + the_enat (llength (ltakeWhile ((=) []) inps))) (LCons xs lxs)) 1 (x, n + the_enat (llength (ltakeWhile ((=) []) inps))))"

lemma step_input_op_elim:
  assumes "step io (input_op n inps) op"
  obtains x xs inps' where "io = Out 1 (x, n + the_enat (llength (ltakeWhile ((=) []) inps)))" "ldropWhile ((=) []) inps = LCons (x # xs) inps'" "op = input_op (n + the_enat (llength (ltakeWhile ((=) []) inps))) (LCons xs inps')"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) input_op.code)
  apply (simp split: llist.splits list.splits)
  using ldropWhile_LConsD apply fast
  apply auto
  done

lemma step_input_op_Out_intro[intro]:
  "inps = LCons (x # xs) lxs \<Longrightarrow>
   ys = LCons xs lxs \<Longrightarrow>
   step (Out 1 (x, n)) (input_op n inps) (input_op n ys)"
  apply (subst input_op.code)
  apply (auto split: llist.splits)
  done

lemma step_input_op_not_Tau[simp]:
  "\<not> step Tau (input_op n inps) op"
  apply (subst input_op.code)
  apply (auto split: llist.splits list.splits dest: ldropWhile_LConsD)
  done

lemma step_input_op_not_Inp[simp]:
  "\<not> step (Inp p x) (input_op n inps) op"
  apply (subst input_op.code)
  apply (auto split: llist.splits list.splits dest: ldropWhile_LConsD)
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

lemma input_op_LCons_Nil:
  "input_op i (LCons [] lxs) = input_op (Suc i) lxs"
  apply (cases "llength (ltakeWhile ((=) []) lxs) \<noteq> \<infinity>")
  subgoal
    apply (subst (1 2) input_op.code)
    apply (simp split: llist.splits list.splits)
    apply (subst (1 2) the_enat_eSuc)
    apply simp_all
    done
  subgoal
    apply (subst (1 2) input_op.code)
    apply (simp split: llist.splits list.splits)
    apply (meson ldropWhile_LCons_lfinite_ltakeWhile llength_eq_infty_conv_lfinite)
    done
  done

lemma input_op_LNil:
  "input_op i LNil = \<oslash>"
  apply (subst input_op.code)
  apply simp
  done

lemma dataflow_op_input_top_input_op:
  "edges sg = (\<lambda> _. []) \<Longrightarrow>
   dataflow_op sg (map_op (case_option (Inl nid) (\<lambda>p. Inr (nid, p))) (case_option (Inl nid) (\<lambda>p. Inr (nid, p))) (input_top (Cap i (1 :: 1)) inps)) \<approx>
   map_op (\<lambda> p. (nid, p)) (\<lambda> p. (nid, p)) (input_op i inps)"
proof (coinduction arbitrary: inps i sg rule: wbisim_coinduct)
  case SIM1
  then show ?case
    apply -
    apply (elim step_map_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp; hypsubst_thin)
    subgoal for nida op'' io' op''a xa xs
      apply (cases inps)
      apply simp
      subgoal for xs lxs
        apply (cases xs; simp)
        subgoal for x xs'
          apply (intro exI conjI)
          apply (rule step_wstep)
          apply fastforce
          apply hypsubst_thin
          apply (rule wbcr_base)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI[of _ "sg\<lparr> lo_pt := (lo_pt sg) @ extract_progress nid (edges sg) \<lparr>cons = [], inte = [], prod = [(1, i, 1)]\<rparr> \<rparr>"])
          apply (intro conjI[rotated])
          apply simp
          apply (rule refl)
          apply (subst (2) input_top.code)
          apply (simp add: comp_def split: if_splits)
          apply (cases xs')
          subgoal
            apply simp
            apply (subst (1 2) dataflow_op.code)
            apply (auto simp add: extract_progress_def split: if_splits option.splits)
            done
          subgoal
            apply simp
            apply (rule box_equals) 
            defer
            apply (rule dataflow_writes_extract_progress_from_push[symmetric, where p="1 :: 1", simplified])
            apply (rule refl)
            apply (rule dataflow_writes_extract_progress_from_push[symmetric, where p="1 :: 1", simplified])
            apply (rule refl)
            apply (clarsimp simp add: extract_progress_def split: option.splits)
            done
          done
        done
      done
    subgoal 
      apply (cases inps; simp)
      subgoal for x lxs
        apply (intro exI conjI)
        apply (subst input_op_LCons_Nil)
        apply (rule rtranclp.intros(1))
        apply (rule wbcr_base)
        apply (rule exI)
        apply (rule exI)
        apply (rule exI[of _ "sg\<lparr> lo_pt := (lo_pt sg) @ extract_progress nid (edges sg) \<lparr>cons = [], inte = [(1, i, - 1), (1, Suc i, 1)], prod = []\<rparr> \<rparr>"])
        apply (intro conjI[rotated])
        defer
        apply (rule refl)+
        apply simp_all
        done
      done
    subgoal
      apply (auto simp add: dataflow_op_end_op input_op_LNil)
      done
    done
next
  case SIM2
  then show ?case
    apply -
    apply (elim step_map_op_elim step_input_op_elim conjE; simp; hypsubst_thin)
    subgoal for io' op'' x xs inps'
      apply (intro exI conjI)
      unfolding wstep_def
      apply simp
      apply (rule relcomppI[rotated])
      apply (rule relcomppI[rotated])
      apply (rule rtranclp.intros(1))
      apply (rule step_Out_dataflow_op_Out_Inr_intro)
      apply (rule step_map_op[where f="case_option (Inl nid) (\<lambda>p. Inr (nid, 1))" and g="case_option (Inl nid) (\<lambda>p. Inr (nid, 1))"])
      apply simp_all
      apply (rule step_input_top_Out_Some_intro[where c="Cap (i + the_enat (llength (ltakeWhile ((=) []) inps))) 1" and xs="x # xs"])
      apply assumption
      apply (rule refl)+
      apply simp
      apply (rule relpowp_imp_rtranclp) 
      apply (rule steps_Tau_dataflow_op_Out_Inl_intro[where nid=nid and sg=sg and xs="map (\<lambda> t. \<lparr> cons = [], inte = [(1, t, -1), (1, Suc t, 1)], prod = [] \<rparr>) ([i..< i + (the_enat (llength (ltakeWhile ((=) []) inps)))])" ])
      apply (rule steps_map_op)
           apply simp
      defer
      apply (rule ldropWhile_steps_input_top[where  c="Cap i 1", simplified])
      apply (meson ldropWhile_LCons_lfinite_ltakeWhile)
      apply simp
      apply simp
      apply (rule refl)+
      apply (intro conjI wbcr_base)
      apply (rule exI[of _ "LCons xs inps'"])
      apply (rule exI[of _ "i + the_enat (llength (ltakeWhile ((=) []) inps))"])
      apply (rule exI[of _ "sg\<lparr> lo_pt := (lo_pt sg) @ extract_progress nid (edges sg) \<lparr>cons = [], inte = concat (map (\<lambda> t. [(1, t, -1), (1, Suc t, 1)]) [i..< i + (the_enat (llength (ltakeWhile ((=) []) inps)))]), prod = [(1, i, 1)]\<rparr> \<rparr>"])
      apply (intro conjI)
      apply simp
      apply (clarsimp simp add: extract_progress_def split: option.splits)
      apply (subst dataflow_writes_extract_progress_from_push[where p="1 :: 1", simplified])
      apply (rule refl)
      apply (clarsimp simp add: extract_progress_def split: option.splits)
      apply simp_all
      apply (cases xs)
      subgoal
        apply (subst (2) input_top.code)
        apply (simp add: comp_def)
        apply (subst (1 2) dataflow_extract_progress_from_push[simplified])
        apply (clarsimp simp add: extract_progress_def split: option.splits)
        apply (rule arg_cong2[where f=dataflow_op])
        apply simp_all
        apply (cases sg; simp)
        apply (simp add: map_concat)
        apply (rule arg_cong[where f=concat])
        apply (rule map_cong)
        apply simp_all
        done
      subgoal
        apply (subst (2) input_top.code)
        apply (simp add: comp_def)
        apply (subst (1 2) dataflow_writes_extract_progress_from_push[simplified])
        apply (clarsimp simp add: extract_progress_def split: option.splits)
        apply (rule refl)+
        apply force
        apply (rule arg_cong2[where f=dataflow_op])
        apply simp_all
        apply (cases sg; simp)
        apply (simp add: map_concat extract_progress_def)
        apply (simp add: map_concat)
        apply (rule arg_cong[where f=concat])
        apply (rule map_cong)
        apply simp_all
        done
      done
    done
qed

lemma compile_dataflow_input_top_input_op:
  "(compile_dataflow (Logic (input_top (Cap i 1) inps)) :: (1 \<times> 1, 1 \<times> 1, 'b \<times> nat) op) \<approx> map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (input_op i inps)"
  unfolding compile_dataflow_def Let_def
  apply (simp split: prod.splits)
  apply (intro conjI allI impI)
  subgoal for su op
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
  done

lemma input_top_correctness:
  "wtraced (compile_dataflow (Logic (input_top (Cap i 1) inps)) :: (1 \<times> 1, 1 \<times> 1, 'b \<times> nat) op) ios \<Longrightarrow>
   ios = (lmap (\<lambda> (n, t). VOut (1, 0) (n, t)) (lconcat (lmap (\<lambda> (xs, t). map (\<lambda> n. (n, t)) xs) (lzip inps (iterates Suc i)))))"
  apply (drule wbisim_wtraced[OF compile_dataflow_input_top_input_op])
  apply (coinduction arbitrary: ios inps i)
  subgoal for ios inps i
    apply (cases ios)
    subgoal
      apply (erule wtraced.cases)
      apply simp_all
      apply (subst (asm) wfinished_map_op)
      apply simp_all
      apply (erule wfinished.cases)
      subgoal for ops
       apply (clarsimp simp add: input_op.code lnull_def split: llist.splits list.splits prod.splits)
        apply (metis (full_types) ldropWhile_eq_LNil_iff lset_lzipD1)
        apply (metis (full_types) ldropWhile_LConsD)
        done
      subgoal for op
       apply (clarsimp simp add: input_op.code lnull_def split: llist.splits list.splits prod.splits)
        apply (metis (full_types) ldropWhile_LConsD)
        done
      done
    subgoal for io ios'
      apply simp
      apply (erule wtraced.cases)
      apply simp_all
      apply hypsubst_thin
      apply (elim wstep_map_op_elim)
      apply (subst (asm) wstep_input_op_simp)
      apply force
      apply (elim step_input_op_elim)
      apply (cases io; simp)
      apply hypsubst_thin
      apply safe
      subgoal premises prems
        using prems(2-) apply -
        unfolding lnull_def
        apply (auto simp add: lset_lzip split: prod.splits)
        apply (metis (full_types) in_lset_conv_lnth ldropWhile_eq_LNil_iff llist.distinct(1))
        done
      subgoal premises prems for op' io' op'' x xs inps' a b
        using prems(2-) apply -
        apply (subst lhd_lconcat_lmap_zip)
        apply simp_all
        apply (meson ldropWhile_LCons_lfinite_ltakeWhile)
        done
      subgoal for op' io' op'' x xs inps' a b
        apply (intro conjI[rotated] exI)
        apply assumption
        apply simp
        subgoal premises prems
          using prems(2) apply -
          apply (rule llist.map_cong)
          apply simp_all
          apply (rule ltl_lconcat_lmap_zip)
          apply simp_all
          apply (meson ldropWhile_LCons_lfinite_ltakeWhile)
          done
        done
      done
    done
  done

corec nd_input_top where
  "nd_input_top c ints prds inps = choice2 
  (case inps of
    LNil \<Rightarrow> Write \<oslash> None (Inl (Inl \<lparr> cons = [], inte = ints, prod = prds @ [(out c, time c, -1)]\<rparr>))
  | LCons [] lxs \<Rightarrow> Silent (nd_input_top (Cap (time c + 1) (out c)) (ints @ [(out c, time c, -1), (out c, time c + 1, 1)]) prds lxs)
  | LCons (x # xs) lxs \<Rightarrow> Write (nd_input_top c ints (prds @ [(out c, time c, 1)]) (LCons xs lxs)) (Some (1 :: 1)) (Inr (x, time c)))
  (Write (nd_input_top c [] [] inps) None (Inl (Inl \<lparr> cons = [], inte = ints, prod = prds\<rparr>)))"

lemma step_nd_input_top_elim:
  assumes "step io (nd_input_top c ints prds inps) op'"
  obtains
    x xs lxs where "io = Out (Some 1) (Inr (x, time c))" "inps = LCons (x # xs) lxs"
    "op' = nd_input_top c ints (prds @ [(out c, time c, 1)]) (LCons xs lxs)"
  | lxs where "io = Tau" "inps = LCons [] lxs" "op' = nd_input_top (Cap (time c + 1) (out c)) (ints @ [(out c, time c, -1), (out c, time c + 1, 1)]) prds (ltl inps)"
  | "io = Out None (Inl (Inl \<lparr> cons = [], inte = ints, prod = prds @ [(out c, time c, -1)]\<rparr>))" "inps = LNil" "op' = \<oslash>"
  | "io = Out None (Inl (Inl \<lparr> cons = [], inte = ints, prod = prds\<rparr>))" "op' = nd_input_top c [] [] inps"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) nd_input_top.code)
  apply (simp split: llist.splits)
   apply force
  subgoal for xs lxs
    apply hypsubst_thin
    apply (cases io; simp)
    subgoal for p x
      apply (cases xs; simp)
      subgoal
        by auto
      subgoal
        by (auto simp add: comp_def)
      done
    subgoal
      apply (cases xs; simp)
       apply auto
      done
    subgoal
      apply (cases xs; simp)
       apply auto
      done
    done
  done

lemma step_nd_input_top_Out_Some_intro[intro!]:
  "inps = LCons (x # xs) inps' \<Longrightarrow>
   op = nd_input_top c ints (prds @ [(out c, time c, 1)]) (LCons xs inps') \<Longrightarrow>
   step (Out (Some 1) (Inr (x, time c))) (nd_input_top c ints prds inps) op"
  apply (subst nd_input_top.code)
  apply (auto simp add: comp_def)
  done

lemma step_nd_input_top_Tau_intro[intro!]:
  "inps = LCons [] inps' \<Longrightarrow> 
   op = nd_input_top (Cap (time c + 1) (out c)) (ints @ [(out c, time c, -1), (out c, time c + 1, 1)]) prds inps' \<Longrightarrow>
   step Tau (nd_input_top c ints prds inps) op"
  apply (subst nd_input_top.code)
  apply (auto simp add: comp_def)
  done

lemma step_nd_input_top_Out_None_intro[intro]:
  "op = nd_input_top c [] [] inps \<Longrightarrow>
   step (Out None (Inl (Inl \<lparr> cons = [], inte = ints, prod = prds\<rparr>))) (nd_input_top c ints prds inps) op"
  apply (subst nd_input_top.code)
  apply (auto simp add: comp_def)
  done


lemma step_nd_input_top_Out_None_end_intro[intro]:
  "op = \<oslash> \<Longrightarrow>
   inps = LNil \<Longrightarrow>
   step (Out None (Inl (Inl \<lparr> cons = [], inte = ints, prod = prds @ [(out c, time c, -1)]\<rparr>))) (nd_input_top c ints prds inps) op"
  apply (subst nd_input_top.code)
  apply (auto simp add: comp_def)
  done


lemma ldropWhile_steps_nd_input_top:
  "lfinite (ltakeWhile ((=) []) inps) \<Longrightarrow>
   ldropWhile ((=) []) inps = LCons (x # xs) inps' \<Longrightarrow>
   ints' = concat (map (\<lambda> t. [(out c, t, -1), (out c, Suc t, 1)]) [time c..<time c + the_enat (llength (ltakeWhile ((=) []) inps))]) \<Longrightarrow>
   steps (replicate (the_enat (llength (ltakeWhile ((=) []) inps))) Tau)
  (nd_input_top c ints prds inps) (nd_input_top (Cap (time c + the_enat (llength (ltakeWhile ((=) []) inps))) (out c)) (ints @ ints') prds (LCons (x # xs) inps'))"
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
      apply (rule step_nd_input_top_Tau_intro)
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
        apply (rule arg_cong3[where f="nd_input_top (Cap (Suc (dataflow_topology_from_tree.followed_by (time c) (the_enat (llength (ltakeWhile ((=) []) lxs))))) (out c))"])
          apply simp_all
        apply (intro impI)
        apply (subst (2) upt_conv_Cons)
         apply auto
        done
      done
    done
  done

lemma dataflow_op_nd_input_top_input_op:
  "edges sg = (\<lambda> _. []) \<Longrightarrow>
   dataflow_op sg (map_op (case_option (Inl nid) (\<lambda>p. Inr (nid, p))) (case_option (Inl nid) (\<lambda>p. Inr (nid, p))) (nd_input_top (Cap i (1 :: 1)) ints prds inps)) \<approx>
   map_op (\<lambda> p. (nid, p)) (\<lambda> p. (nid, p)) (input_op i inps)"
proof (coinduction arbitrary: inps i ints prds sg rule: wbisim_coinduct)
  case SIM1
  then show ?case 
    apply -
    apply -
    apply (elim step_map_op_elim step_dataflow_op_elim step_nd_input_top_elim conjE; simp; hypsubst_thin)
    subgoal
      apply (intro exI conjI)
       apply (rule step_wstep)
       apply fastforce
      apply (rule wbcr_base)
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
      apply (rule ldropWhile_steps_nd_input_top[where  c="Cap i 1", simplified])
            apply (meson ldropWhile_LCons_lfinite_ltakeWhile)
      apply assumption+
           apply (rule refl)+
      apply (rule relcomppI[rotated])
      apply (rule rtranclp.intros(1))
      apply (rule step_Out_dataflow_op_Out_Inr_intro)
      apply (rule step_map_op[where f="case_option (Inl nid) (\<lambda>p. Inr (nid, 1))" and g="case_option (Inl nid) (\<lambda>p. Inr (nid, 1))"])
      apply simp_all
      apply (rule step_nd_input_top_Out_Some_intro)
      apply (rule refl)+
       apply simp_all
      done
    done
qed

end