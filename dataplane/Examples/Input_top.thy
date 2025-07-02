theory Input_top

imports
  "../Timely_Infrastructure"
begin 


corec input_top where
  "input_top c inps = (case inps of
    LNil \<Rightarrow> drop_cap c \<oslash>
  | LCons xs lxs \<Rightarrow>
     push 
     (Write (input_top (Cap (time c + 1) (out c)) lxs) (trace (STR ''Managing caps'') None) (Inl (Inl \<lparr> cons = [], inte = [(out c, time c, -1), (out c, time c + 1, 1)], prod = if xs = [] then [] else [(out c, time c, length xs)]\<rparr>)))
      (1 :: 1) (map (\<lambda> x. (x, c)) xs))"

lemma step_input_top_elim:
  assumes "step io (input_top c inps) op'"
  obtains
    op'' x xs where "io = Out (Some 1) (Inr (x, time c))" "lhd inps = xs" "hd xs = x" "inps \<noteq> LNil" "xs \<noteq> []"
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
lemma ldropWhile_LConsD:
  "ldropWhile P lxs = LCons x lxs' \<Longrightarrow>
   \<not> P x"
  by (metis lhd_ldropWhile llist.disc(2) llist.sel(1) lnull_ldropWhile)

corec input_op :: "nat \<Rightarrow> 'a buf llist \<Rightarrow> (1, 1, 'a \<times> nat) op" where
  "input_op n inps = (case ldropWhile ((=) []) inps of
     LNil \<Rightarrow> \<oslash>
   | LCons (x # xs) lxs \<Rightarrow> Write (input_op (n + the_enat (llength (ltakeWhile ((=) []) inps))) (LCons xs lxs)) 1 (x, n + the_enat (llength (ltakeWhile ((=) []) inps))))"

abbreviation "ex13 \<equiv> Logic (input_top (Cap 0 (1 :: 1)) (LCons [Suc 0, 3] (LCons [] (LCons [9] (LCons [9] LNil))))) :: (2, 1, (1, _) shared_state + 'c, nat \<times> _) dataflow_tree"

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

lemma dataflow_writes_extract_progress_from_push:
  "g = (case_option (Inl nid) (\<lambda>p. Inr (nid, p))) \<Longrightarrow>
   dataflow_op sg
     (map_op f g
       (writes (Write op None (Inl (Inl \<lparr>cons = cs, inte = is, prod = ps\<rparr>))) (Some p) xs)) =
    dataflow_op (sg\<lparr>lo_pt := (lo_pt sg) @ extract_progress nid (edges sg) \<lparr>cons = cs, inte = is, prod = ps\<rparr> \<rparr>)
     (map_op f g
       (writes (Write op None (Inl (Inl \<lparr>cons = [], inte = [], prod = []\<rparr>))) (Some p) xs))"
  apply (induct xs arbitrary: ps "is" cs)
  subgoal 
    apply simp
    apply (subst (1 2) dataflow_op.code)
    apply (auto simp add: extract_progress_def split: if_splits option.splits)
    done
  subgoal for a xs' 
    apply (subst (1 2) writes.code)
    apply simp
    apply (subst (1 2) dataflow_op.code)
    apply (simp add: extract_progress_def split: option.splits sum.splits)
    done
  done

lemma dataflow_extract_progress_from_push:
  "dataflow_op sg
     ((Write op (Inl nid) (Inl (Inl \<lparr>cons = cs, inte = is, prod = ps\<rparr>)))) =
    dataflow_op (sg\<lparr>lo_pt := (lo_pt sg) @ extract_progress nid (edges sg) \<lparr>cons = cs, inte = is, prod = ps\<rparr> \<rparr>)
     ((Write op (Inl nid) (Inl (Inl \<lparr>cons = [], inte = [], prod = []\<rparr>))))"
  apply (subst (1 2) dataflow_op.code)
  apply (auto simp add: extract_progress_def split: if_splits option.splits)
  done

lemma dataflow_op_simps[simp]:
  "\<not> is_Read (dataflow_op sg op)"
  "\<not> is_Write (dataflow_op sg op)"
  "\<not> is_Silent (dataflow_op sg op)"
  "is_Choice (dataflow_op sg op)"
  by (subst dataflow_op.code; simp)+

(* FIXME: move me *)
lemma rel_set_image:
  "rel_set R (f ` A) B \<longleftrightarrow> rel_set (\<lambda> x. R (f x)) A B"
  "rel_set S A (g ` B) \<longleftrightarrow> rel_set (\<lambda> x y. S x (g y)) A B"
  unfolding rel_set_def
  apply auto
  done
lemma rel_set_reflI:
  "(\<And>x. x \<in> A \<Longrightarrow> R x x) \<Longrightarrow> rel_set R A A"
  unfolding rel_set_def
  apply auto
  done

lemma change_multiplicities_append:
  "change_multiplicities su (xs @ ys) = (\<lambda> c. change_multiplicities su ys (change_multiplicities su xs c))"
  unfolding change_multiplicities_def 
  apply (rule ext)
  apply simp
  done

lemma change_multiplicities_append_comp:
  "change_multiplicities su (xs @ ys) = change_multiplicities su ys o change_multiplicities su xs"
  unfolding change_multiplicities_def
  apply simp
  done

lemma take_step_comm:
  "(take_step su (CM l2 t2 m2) \<circ>\<circ>\<circ> take_step) su (CM l1 t1 m1) = (take_step su (CM l1 t1 m1) \<circ>\<circ>\<circ> take_step) su (CM l2 t2 m2)"
  apply (rule ext)
  apply (auto simp add: fun_upd_twist update_zmultiset_comm)
  done

lemma take_step_plus[simp]:
  "take_step su (CM l t m) (take_step su (CM l t n) c) = take_step su (CM l t (m + n)) c"
  by (cases c; auto simp add: add.commute)

lemma change_multiplicitie_rev[simp]:
  "change_multiplicities su (rev xs) c = change_multiplicities su xs c"
  unfolding change_multiplicities_def
  apply (subst fold_rev)
  apply (clarsimp simp add: take_step_comm)+
  done

lemma change_multiplicities_comm:
  "change_multiplicities su (xs @ ys) c = change_multiplicities su (ys @ xs) c"
  unfolding change_multiplicities_def
  by (metis (mono_tags, lifting) change_multiplicitie_rev change_multiplicities_append change_multiplicities_def rev_append)

lemma change_multiplicities_simps[simp]:
  "change_multiplicities su [] c = c"
  "change_multiplicities su ((l, t, m) # xs) c = change_multiplicities su xs (take_step summary (CM l t m) c)"
  unfolding change_multiplicities_def by simp+

lemma change_multiplicities_simp_alt:
  "change_multiplicities su ((l, t, m) # xs) c = take_step su (CM l t m) (change_multiplicities su xs c)"
proof -
  have "change_multiplicities su ((l, t, m) # xs) c = change_multiplicities su (rev ((l, t, m) # xs)) c" using change_multiplicitie_rev by metis
  also have "\<dots> = take_step su (CM l t m) (change_multiplicities su (rev xs) c)" by (simp add: change_multiplicities_def foldr_conv_fold)
  ultimately show ?thesis by (metis change_multiplicitie_rev)
qed

lemma change_multiplicities_same_pointstamps_aux:
  "(\<forall> x \<in> set xs. \<forall> y \<in> set xs. fst x = fst y \<and> (fst o snd) x = (fst o snd) y) \<Longrightarrow>
   change_multiplicities su xs c = fold (\<lambda> m c. take_step su (CM ((fst o hd) xs) ((fst o snd o hd) xs) m) c) (map (snd o snd) xs) c"
  unfolding change_multiplicities_def
  apply (induct xs arbitrary: c)
  apply simp
  subgoal premises prems for a xs c
    using prems(2-) apply -
    apply (cases a; clarsimp)
    subgoal using prems(1) by (smt (verit) List.fold_cong fold_map fun_comp_eq_conv list.sel(1) list.set_cases list.set_intros(1))
    done
  done

lemma change_multiplicities_same_pointstamps:
  "(\<forall> x \<in> set xs. \<forall> y \<in> set xs. fst x = l \<and> (fst o snd) x = t) \<Longrightarrow>
   m = sum_list (map (snd o snd) xs) \<Longrightarrow>
   change_multiplicities su xs c = take_step su (CM l t m) c"
  apply (induct xs arbitrary: c m)
  apply simp
  subgoal premises prems for x xs c m
    using prems(2-) apply -
    apply hypsubst_thin
    apply (cases x)
    subgoal for l t m
      apply (simp only: change_multiplicities_simp_alt)
      apply (subst prems(1))
      apply force
      apply (rule refl)
      apply clarsimp
      apply (intro conjI impI)
      subgoal by (metis (no_types) group_cancel.sub1 uminus_add_add_uminus update_zmultiset_comm update_zmultiset_plus)
      subgoal
        by blast 
      done
    done
  done

lemma dataflow_op_change_multiplicities:
  "change_multiplicities (summ sg) (lo_pt sg) (pt_tr sg) = change_multiplicities (summ sg') (lo_pt sg') (pt_tr sg') \<Longrightarrow>
   summ sg = summ sg' \<Longrightarrow>
   pt_tr sg = pt_tr sg' \<Longrightarrow>
   edges sg = edges sg' \<Longrightarrow>
   dataflow_op sg op = dataflow_op sg' op"
  apply (coinduction arbitrary: sg sg' op rule: op.coinduct_upto)
  subgoal for sg sg' op
    apply simp
    apply (subst (3 4) dataflow_op.code)
    apply (simp add: rel_set_image split: sum.splits option.splits op.splits)
    apply (rule rel_set_reflI)
    apply (auto 0 0 simp add: rel_set_image split: sum.splits option.splits op.splits)
    subgoal for f nid c c'
      apply (subgoal_tac "c = c'")
      subgoal
        apply (rule op.cong_Silent)
        apply (rule op.cong_base)
        apply (rule exI[of _ "sg\<lparr>pt_tr := c, lo_pt := []\<rparr>"])
        apply (rule exI[of _ "sg'\<lparr>pt_tr := c', lo_pt := []\<rparr>"])
        apply (intro conjI exI)
        apply (rule refl)+
        apply simp_all
        done
      subgoal
        unfolding propagate_pointstamps_def Let_def
        apply simp
        done
      done
    subgoal
      by (force intro: op.cong_Read op.cong_base)
    subgoal
      apply (rule op.cong_Silent)
      apply (rule op.cong_base)
      apply (intro conjI exI)
      apply (rule refl)+
      apply (simp_all add: change_multiplicities_append)
      done
    subgoal
      by (simp add: op.cong_intros(2))
    subgoal
      by (simp add: op.cong_intros(2))
    subgoal
      by (simp add: op.cong_intros(2))
    subgoal
      by (force intro: op.cong_Write op.cong_base)
    subgoal
      by (force intro: op.cong_Silent op.cong_base)
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
    subgoal   
      apply (rule FalseE)
      apply (subst (asm) input_top.code)
      apply (simp split: llist.splits)
      subgoal for xs lxs
        apply (cases xs; simp add: writes_Cons_simp)
        done
      done
    subgoal   
      apply (rule FalseE)
      apply (subst (asm) input_top.code)
      apply (simp split: llist.splits)
      subgoal for xs lxs
        apply (cases xs; simp add: writes_Cons_simp)
        done
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

lemma compile_dataflow_tree_aux_Logic_simp[simp]:
  "compile_dataflow_tree_aux n (Logic op) = (n + 1, \<lambda> l1 l2. 
    if n = node l1 \<and> n = node l2 \<and> is_Trg (port l1) \<and> is_Src (port l2) 
    then frontier (abs_zmultiset (mset [0], {#})) 
    else frontier {#}\<^sub>z, map_op (case_option (Inl n) (\<lambda> p. Inr (n, p))) (case_option (Inl n) (\<lambda> p. Inr (n, p))) op)"
  apply auto
  done

lemma compile_dataflow_tree_Logic:
  "compile_dataflow_tree (Logic op) = 
  (\<lambda> l1 l2. 
    if 1 = node l1 \<and> (1 :: 1) = node l2 \<and> is_Trg (port l1) \<and> is_Src (port l2) 
    then frontier (abs_zmultiset (mset [0], {#})) 
    else frontier {#}\<^sub>z, map_op (case_option (Inl 1) (\<lambda> p. Inr (1, p))) (case_option (Inl 1) (\<lambda> p :: 1. Inr (1, p))) op)"
  unfolding compile_dataflow_tree_def
  apply (simp only: Let_def compile_dataflow_tree_aux.simps prod.case)
  apply (subst (7) if_P)
  apply eval
  apply simp
  done

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

lemma lhd_concat_ldropWhile:
  "lfinite (ltakeWhile ((=) []) lxs) \<Longrightarrow>
   \<exists> xs lxs'. ldropWhile ((=) []) lxs = LCons (x # xs) lxs' \<Longrightarrow>
   lhd (lconcat lxs) = x"
  apply (induct "ltakeWhile ((=) []) lxs"  arbitrary: lxs rule: lfinite_induct)
  subgoal
    apply (simp add: lconcat_correct split: prod.splits)
    apply (smt (z3) ldropWhile_LNil ldropWhile_simps(2) lhd_LCons lhd_lconcat llist.map_disc_iff llist.map_sel(1) llist_of.simps(2) lnull_def not_lnull_conv)
    done
  subgoal for lxs
    apply (cases lxs; simp split: if_splits)
    done
  done

lemma lhd_concat_ldropWhile_alt:
  "lfinite (ltakeWhile ((=) []) lxs) \<Longrightarrow>
   \<not> lnull (ldropWhile ((=) []) lxs) \<Longrightarrow>
   lhd (lconcat lxs) = hd (lhd (ldropWhile ((=) []) lxs))"
  apply (induct "ltakeWhile ((=) []) lxs"  arbitrary: lxs rule: lfinite_induct)
  subgoal
    apply (simp add: lconcat_correct split: prod.splits)
    apply (smt (z3) Coinductive_List_Auxiliary.lconcat_eq_LNil Coinductive_List_Auxiliary.lconcat_simps(1) lconcat_correct lhd_concat_ldropWhile lhd_ldropWhile list.collapse llist.collapse(2) lnull_imp_lfinite lnull_ldropWhile lset_LNil
        lset_eq_empty ltakeWhile_eq_LNil_iff)
    done
  subgoal for lxs
    apply (cases lxs; simp split: if_splits)
    done
  done

lemma lhd_lconcat_lmap_zip:
  "lfinite (ltakeWhile ((=) []) inps) \<Longrightarrow>
   ldropWhile ((=) []) inps = LCons (x # xs) inps' \<Longrightarrow>
   lhd (lconcat (lmap (\<lambda>(xs, t). map (\<lambda>n. (n, t)) xs) (lzip inps (iterates Suc i)))) = (x, i + (the_enat (llength (ltakeWhile ((=) []) inps))))"
  apply (induct "ltakeWhile ((=) []) inps"  arbitrary: inps i rule: lfinite_induct)
  subgoal
    apply (simp add: lconcat_correct lnull_def split: prod.splits)
    apply (smt (z3) case_prod_conv iterates_lmap lappend_code(1) lappend_ltakeWhile_ldropWhile lhd_LCons lhd_lconcat lhd_llist_of list.map_disc_iff list.map_sel(1) llist.distinct(1) llist.map_disc_iff llist.map_sel(1) llist_of.simps(2)
        llist_of_eq_LNil_conv lzip.ctr(1) lzip.disc_iff(2) lzip.sel(1) lzip_eq_LNil_conv)
    done
  subgoal for lxs i
    apply (cases lxs; simp split: if_splits)
    subgoal for x lxs'
      apply (drule meta_spec[of _ lxs'])
      apply (drule meta_spec[of _ "Suc i"])
      apply simp
      apply (subst iterates.code)
      apply simp
      apply (metis eSuc_enat lfinite_llength_enat the_enat.simps)
      done
    done
  done

lemma ltl_lconcat_lmap_zip:
  "lfinite (ltakeWhile ((=) []) inps) \<Longrightarrow>
   ldropWhile ((=) []) inps = LCons (x # xs) inps' \<Longrightarrow>
   ltl (Coinductive_List_Auxiliary.lconcat (lmap (\<lambda>z. case z of (xs, t) \<Rightarrow> map (\<lambda>n. (n, t)) xs) (lzip inps (iterates Suc i)))) =
   Coinductive_List_Auxiliary.lconcat (lmap (\<lambda>z. case z of (xs, t) \<Rightarrow> map (\<lambda>n. (n, t)) xs) (lzip (LCons xs inps') (iterates Suc (dataflow_topology_from_tree.followed_by i (the_enat (llength (ltakeWhile ((=) []) inps)))))))"
  apply (induct "ltakeWhile ((=) []) inps"  arbitrary: inps i rule: lfinite_induct)
  subgoal
    apply (simp add: lconcat_correct lnull_def split: prod.splits)
    apply (subst ltl_lconcat)
    apply simp_all
    apply (metis (lifting) ldropWhile_LNil llist.distinct(1) lnull_def)
    apply (smt (z3) case_prod_conv ldropWhile_LNil list.map_disc_iff llist.distinct(1) llist.map_disc_iff llist.map_sel(1) llist_of.simps(1) llist_of_inject lnull_def lnull_iterates ltakeWhile_eq_LNil_iff lzip.sel(1)
        lzip_eq_LNil_conv)
    apply (smt (z3) lappend_code(1) lappend_ltakeWhile_ldropWhile lconcat_LCons lhd_LCons lhd_LCons_ltl lhd_lzip list.sel(3) llist.disc(2) llist.map_disc_iff llist.map_sel(1) lnull_iterates ltl_llist_of ltl_lmap ltl_lzip ltl_simps(2)
        lzip.disc(2) map_tl prod.simps(2))
    done
  subgoal for lxs i
    apply (cases lxs; simp split: if_splits)
    subgoal for x lxs'
      apply (drule meta_spec[of _ lxs'])
      apply (drule meta_spec[of _ "Suc i"])
      apply simp
      apply (subst the_enat_eSuc)
      using llength_eq_infty_conv_lfinite apply blast
      apply simp
      apply (subst iterates.code)
      apply simp
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

end