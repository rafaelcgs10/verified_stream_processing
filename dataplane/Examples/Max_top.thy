theory Max_top

imports
  "../Timely_Infrastructure"
  Input_top
begin 

definition "maxs buf = [(n, c) \<leftarrow> buf. n = Max (set (map fst ((filter (\<lambda> (n' :: nat, c'). time c = time c') buf))))]"

(* FIXME: move me *)
abbreviation "choice4 op1 op2 op3 op4 \<equiv> choice2 (choice2 op1 op2) (choice2 op3 op4)"


corec max_top' where
  "max_top' fron cosm ints prods buf = choice4
   (Read None (\<lambda> st. if is_Inl st \<and> is_Inr (projl st) then max_top' ((projr (projl st)) (0 :: 1)) cosm ints prods buf else \<oslash>))
   (let below = [(n, c) \<leftarrow> buf. less_than_frontier fron (time c)] in
    let result = maxs below in
    push (max_top' fron cosm ints prods [(n, c) \<leftarrow> buf. \<not> less_than_frontier fron (time c)]) (0 :: 1) result)
   undefined
   undefined"

corec max_top' where
  "max_top' fron cons ints prods buf = choice2
   (Read (trace (STR ''Reading frontier'') None) (\<lambda> st.
    if is_Inl st \<and> is_Inr (projl st)
    then let impf = projr (projl st) in
      let ft = impf (0 :: 1) in
      if print_frontier ft  is_empty_antichain ft 
      then trace (STR ''Empty frontier'') \<oslash> 
      else let below = [(n, c) \<leftarrow> buf. less_than_frontier ft (time c)] in
      let result = trace (STR ''Non empty frontier'') (maxs below) in
      push 
      (Write (max_top' [(n, c) \<leftarrow> buf. \<not> less_than_frontier ft (time c)]) None (Inl (Inl \<lparr> cons = [], inte = map (\<lambda> c. (out c, time c, -1)) (map snd below), prod = map (\<lambda> c. (out c, time c, 1)) (map snd result) \<rparr>)))
      (0 :: 1) result
    else
      \<oslash>))
   (pull (1 :: 1) (\<lambda> x. max_top' (buf @ [x])))"


lemma step_max'_top_elim:
  assumes "step io (max_top' buf) op"
  obtains
  x where  "io = Inp None (Inl (Inl x))" "op = \<oslash>"
| x where  "io = Inp None (Inr x)" "op = \<oslash>"
| impf ft where "io = Inp None (Inl (Inr impf))" "ft = impf (0 :: 1)"
  "is_empty_antichain ft" "op = \<oslash>"
| impf ft below result where "io = Inp None (Inl (Inr impf))" "ft = impf (0 :: 1)"
  "\<not> is_empty_antichain ft" "below = [(n, c) \<leftarrow> buf. less_than_frontier ft (time c)]" "result = maxs below"
  "op = push (Write (max_top' [(n, c) \<leftarrow> buf. \<not> less_than_frontier ft (time c)]) None (Inl (Inl \<lparr> cons = [], inte = map (\<lambda> c. (out c, time c, -1)) (map snd below), prod = map (\<lambda> c. (out c, time c, 1)) (map snd result)\<rparr>)) ) 0 result"
| x t n where "io = Inp (Some 0) (Inr (n, t))"
 "op = Write (max_top' (buf @ [(n, Cap t 1)])) None (Inl (Inl \<lparr> cons = [(1, t, 1)], inte = [(1, t, 1)], prod = [] \<rparr>))"
| x where "io = Inp (Some 0) (Inl x)" "op = \<oslash>"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) max_top'.code)
  apply (cases io; simp split: option.splits sum.splits if_splits)
  subgoal for p x
    apply (cases p; cases x; simp)
    subgoal for p
      by (cases p; fastforce)
    subgoal for p
      by (cases p; fastforce)
    subgoal for p
      by (cases p; fastforce)
    subgoal for p
      by (cases p; fastforce)
    done
   apply auto
  done

abbreviation "max_top \<equiv> max_top' []"

abbreviation "ex3 \<equiv> Comp [ (0 :: 2, 0) \<mapsto> (0, 0) ] ex1 (Logic max_top)"

(* value [GHC] "approx_in 32 [VOut (1, 0) (3, 0), VOut (1, 0) (9, 1)] (compile_dataflow ex3)"
 *)
abbreviation "ex4 \<equiv> Comp (\<lambda> _. None) (Logic (input_top (Cap 0 (1 :: 1)) (LCons [0] LNil))) (Logic (input_top (Cap 0 (1 :: 1)) (LCons [Suc 0] LNil)))"

abbreviation "ex5 \<equiv> Comp (\<lambda> _. None) (Logic (\<I> :: (1 option, 1 option, _) op)) (Logic (\<I> :: (1 option, 1 option, _) op))"

abbreviation "ex6 \<equiv> Comp [ (0 :: 4, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex4 ex5"

(* value [GHC] "approx_in 15 [VOut (3, 0) (0, 0), VOut (2, 0) (1, 0)] (compile_dataflow ex6)"
 *)
corec cp_op :: "(1 option, 1 option, 'a) op" where "cp_op = Read (Some 1) (\<lambda>x. Write cp_op (Some 1) x)"

abbreviation "ex7 \<equiv> Comp (\<lambda> _. None) (Logic cp_op) (Logic cp_op)"

abbreviation "ex8 \<equiv> Comp [ (0 :: 4, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex4 ex7"

(* value [GHC] "approx_in 15 [VOut (3, 0) (0, 0), VOut (2, 0) (1, 0)] (compile_dataflow ex8)"
 *)
abbreviation "ex9 \<equiv> Comp [ (0, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex7 ex7"

abbreviation "ex10 \<equiv> Comp [ (0 :: 6, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex4 ex9"

corec max_op :: "nat \<Rightarrow> _ buf llist \<Rightarrow> (1, 1, _ \<times> nat) op" where
  "max_op n inps = (case ldropWhile ((=) []) inps of
     LNil \<Rightarrow> \<oslash>
   | LCons xs lxs \<Rightarrow> Write (max_op (n + the_enat (llength (ltakeWhile ((=) []) inps))) (LCons xs lxs)) 1 (Max (set xs), n + the_enat (llength (ltakeWhile ((=) []) inps))))"

abbreviation "inp_top c inps \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, (p :: 1)))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, (p :: 1)))) (input_top c inps)"
abbreviation "m_top buf \<equiv>  map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, (p :: 1)))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, (p :: 1)))) (max_top' buf)"

abbreviation "inp_m_top i inps buf1 buf2 \<equiv> map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0 :: 2, 1 :: 1) \<mapsto> Inr (1, 1)] buf1 (inp_top (Cap i 1) inps) (m_top buf2))"




lemma bisim_step_elim:
  "op1 ~ op2 \<Longrightarrow>
   step io op1 op1' \<Longrightarrow>
   \<exists> op2'. step io op2 op2' \<and> op1' ~ op2'"
  by (meson bisim.simps sim_def)

fun extract_update where
  "extract_update (Write op (Inl nid) (Inl (Inl st))) = (Write op (Inl nid) (Inl (Inl \<lparr> cons = [], inte = [], prod = [] \<rparr>)), st)"
| "extract_update op = (op, \<lparr> cons = [], inte = [], prod = [] \<rparr>)"

abbreviation "no_Choice op \<equiv> is_Read op \<or> is_Write op \<or> is_Silent op"

corec subst_Out_op where
  "subst_Out_op p x y op = Choice (cimage (\<lambda> op.
      case op of 
       Write op' p' x' \<Rightarrow> (if p = p' \<and> x = x' then Write op' p y else Write (subst_Out_op p x y op') p' x')
     | Read p' f \<Rightarrow> Read p' (\<lambda> x'. (subst_Out_op p x y (f x')))
     | Silent op' \<Rightarrow> Silent (subst_Out_op p x y op')) (choices op))"

lemma subst_Out_op_cases_simp[simp]:
  "\<not> is_Read (subst_Out_op p x y op)"
  "\<not> is_Write (subst_Out_op p x y op)"
  "\<not> is_Silent (subst_Out_op p x y op)"
  "is_Choice (subst_Out_op p x y op)"
  by (subst subst_Out_op.code; simp)+


lemma step_subst_op_Tau_intro[intro!]:
  "step Tau op op' \<Longrightarrow>
   step Tau (subst_Out_op p x y op) (subst_Out_op p x y op')"
  apply (erule step_choicesE; simp del: cin.rep_eq)
    apply (subst subst_Out_op.code)
  apply force
  done

lemma step_subst_op_Inp_intro[intro!]:
  "step (Inp p' x') op op' \<Longrightarrow>
   step (Inp p' x') (subst_Out_op p x y op) (subst_Out_op p x y op')"
  apply (erule step_choicesE; simp del: cin.rep_eq)
    apply (subst subst_Out_op.code)
  apply force
  done

lemma step_subst_op_Out_intro1[intro]:
  "step (Out p x) op op' \<Longrightarrow>
   step (Out p y) (subst_Out_op p x y op) op'"
  apply (erule step_choicesE; simp del: cin.rep_eq)
    apply (subst subst_Out_op.code)
    apply force
  done

lemma step_subst_op_Out_intro2[intro]:
  "step (Out p' x') op op' \<Longrightarrow>
   x \<noteq> x' \<or> p \<noteq> p' \<Longrightarrow>
   step (Out p' x') (subst_Out_op p x y op) (subst_Out_op p x y op')"
  apply (erule step_choicesE; simp del: cin.rep_eq)
    apply (subst subst_Out_op.code)
  apply force
  done


lemma step_subst_op_elim[elim]:
  assumes "step io (subst_Out_op p x y op) op'"
  obtains 
    op'' where "step io op op''" "io = Tau" "op' = subst_Out_op p x y op''"
  | p' x' op'' where "step io op op''" "io = Inp p' x'" "op' = subst_Out_op p x y op''"
  | p' x' op'' where "step io op op''" "io = Out p' x'" "p \<noteq> p' \<or> x \<noteq> x'" "op' = subst_Out_op p x y op''"
  | p' x' op'' io' where "step io' op op''" "io' = Out p x" "io = Out p y" "p = p'" "x = x'" "op' = op''"
  using assms apply atomize_elim
  apply (subst (asm) subst_Out_op.code)
  apply (erule step_choicesE)
  subgoal for p' f x 
    apply (clarsimp simp del: cin.rep_eq; hypsubst_thin?)
    subgoal for op'
      by (cases op'; force split: if_splits)
    done
  subgoal for p' x'
    apply (simp del: de_Morgan_conj cin.rep_eq; hypsubst_thin?)
    apply (elim cBexE)
    subgoal for op''
      by (cases op''; simp del: de_Morgan_conj cin.rep_eq split: if_splits; force)
    done
  subgoal
    apply (clarsimp simp del: cin.rep_eq; hypsubst_thin?)
    subgoal for op'
      apply (cases op'; simp del: de_Morgan_conj cin.rep_eq split: if_splits)
       apply force+
      done
    done
  done

coinductive io_ev_inv for io where
  [intro]: "step io op' op \<Longrightarrow> io_ev_inv io op"
| [intro]: "(\<And> io' op'. io \<noteq> io' \<Longrightarrow> step io' op op' \<Longrightarrow> io_ev_inv io op') \<Longrightarrow> step io op op' \<Longrightarrow> io_ev_inv io op"

lemma io_ev_map_op:
  "io_ev_inv io op \<Longrightarrow> map_IO f g id io = io' \<Longrightarrow> io_ev_inv io' (map_op f g op)"
  apply (coinduction arbitrary: op)
  subgoal for op
    apply simp
    apply (erule io_ev_inv.cases; simp)
     apply blast
    apply (rule disjI2)
    apply (intro conjI[rotated] impI exI allI)
    apply blast
    apply (metis step_map_op_elim)
    done
  done

lemma io_ev_Out_Inl_comp_op:
  "io_ev_inv (Out p x) op1 \<Longrightarrow>
   p \<notin> dom wire \<Longrightarrow>
   io_ev_inv (Out (Inl p) x) (comp_op wire buf op1 op2)"
  apply (coinduction arbitrary: buf op1 op2)
  subgoal for buf op1 op2
    apply simp
    apply (erule io_ev_inv.cases; simp)
    subgoal 
      by blast
    subgoal
    apply (rule disjI2)
    apply (intro conjI[rotated] impI exI allI)
     apply blast
    apply (elim step_comp_op_elim; simp; hypsubst_thin; simp)
           apply force
          apply force
         apply force
        apply force
    subgoal
      by blast
      apply force
    apply force
    apply force
    done
  done
  done

(* FIXME: move me *)
lemma dataflow_op_extract_progress_append:
  "dataflow_op (sg\<lparr>lo_pt := lo_pt sg @ extract_progress nid (edges sg) \<lparr>cons = cs, inte = is, prod = ps\<rparr> @ extract_progress nid (edges sg) \<lparr>cons = cs', inte = is', prod = ps'\<rparr>\<rparr>) op =
   dataflow_op (sg\<lparr>lo_pt := lo_pt sg @ extract_progress nid (edges sg) \<lparr>cons = cs @ cs', inte = is @ is', prod = ps @ ps'\<rparr>\<rparr>) op"
  apply (rule dataflow_op_change_multiplicities)
     apply simp_all
  unfolding extract_progress_def
  apply simp
  apply (smt (verit, del_insts) change_multiplicities_append change_multiplicities_comm)
  done

lemma propagate_pointstamps_comm:
  "propagate_pointstamps summary conf (cbs1 @ cbs2) = propagate_pointstamps summary conf (cbs2 @ cbs1)"
    unfolding propagate_pointstamps_def Let_def
    by (simp add: change_multiplicities_comm)


lemma propagate_pointstamps_append:
  "propagate_pointstamps summary conf cbs1 = Some conf' \<Longrightarrow>
   propagate_pointstamps summary conf (cbs1 @ cbs2) = propagate_pointstamps summary conf' cbs2"
  apply (induct cbs2 arbitrary: cbs1 conf conf' rule: rev_induct) 
  subgoal for cbs1 conf conf'
    unfolding propagate_pointstamps_def change_multiplicities_def propagate_all_def
    apply simp
    apply (metis (no_types, lifting) while_option_stop while_option_unfold)
    done
  subgoal for a cbs2 cbs1 conf conf'
    apply (drule meta_spec)+
    apply (drule meta_mp)
    apply assumption
    unfolding propagate_pointstamps_def Let_def
    apply (simp; hypsubst_thin?)
    apply (subst change_multiplicities_append_comp)
    apply simp
    sorry
  done

lemma
  "(frontier \<circ>\<circ> c_imp) (the (propagate_pointstamps summary conf A)) =
   (frontier \<circ>\<circ> c_imp) (the (propagate_pointstamps summary conf B)) \<Longrightarrow>
   (frontier \<circ>\<circ> c_imp) (the (propagate_pointstamps summary conf (A @ C))) =
   (frontier \<circ>\<circ> c_imp) (the (propagate_pointstamps summary conf (B @ C)))"
  apply (induct C arbitrary: A B conf)
  subgoal
    by simp
  subgoal for x xs A B conf
    apply (drule meta_spec[of _ "A @ [x]"])
    apply (drule meta_spec[of _ "B @ [x]"])
    apply (drule meta_spec[of _ conf])
    apply (drule meta_mp)
    apply (subst (1 2) propagate_pointstamps_append)
       defer
       defer
    apply (rule refl)
      apply simp
    oops

lemma aux:
  "(frontier \<circ>\<circ> c_imp) (the (propagate_pointstamps (summ sg) (pt_tr sg) (lo_pt sg))) =
   (frontier \<circ>\<circ> c_imp) (the (propagate_pointstamps (summ sg) (pt_tr sg) (lo_pt sg @ extract_progress nid (edges sg) \<lparr>cons = cs, inte = is, prod = ps\<rparr>))) \<Longrightarrow>
    dataflow_op sg op ~
    dataflow_op (sg\<lparr>lo_pt := lo_pt sg @ extract_progress nid (edges sg) \<lparr>cons = cs, inte = is, prod = ps\<rparr>\<rparr>)
     (subst_Out_op (Inl nid) (Inl (Inl \<lparr>cons = cs @ cs', inte = is @ is', prod = ps @ ps'\<rparr>)) (Inl (Inl \<lparr>cons = cs', inte = is', prod = ps'\<rparr>)) op)"
proof (coinduction arbitrary: sg op rule: bisim_coinduct)
  case SIM1
  then show ?case 
    apply -                
    apply (elim step_dataflow_op_elim; simp)
    subgoal for nida p op'' x
      apply (intro exI conjI[rotated])
       apply (rule b_base)
       apply (intro exI conjI)
         apply (rule refl)+
       apply hypsubst_thin
      subgoal 
         apply force+
        done
      subgoal
        by blast
      done
    subgoal
      apply (intro exI conjI[rotated])
       apply (rule b_base)
       apply (intro exI conjI)
         apply (rule refl)+
       apply hypsubst_thin
      subgoal 
         apply force+
        done
      subgoal
        by blast
      done
    subgoal
      apply (intro exI conjI[rotated])
       apply (rule b_base)
       apply (intro exI conjI)
         apply (rule refl)+
       apply hypsubst_thin
      subgoal 
         apply force+
        done
      subgoal
        by blast
      done
    subgoal for nid' op'' st'
      apply hypsubst_thin
      apply (cases "nid' = nid \<and> st' = \<lparr>cons = cs @ cs', inte = is @ is', prod = ps @ ps'\<rparr>")
      subgoal
        apply (elim conjE; hypsubst_thin)
        apply (intro exI conjI)
         apply (rule step_Tau_dataflow_op_Out_Inl_intro[where nid=nid])
          apply (rule step_subst_op_Out_intro1)
          apply assumption
         apply (rule refl)
        apply simp
        apply (subgoal_tac 
    "(dataflow_op (sg\<lparr>lo_pt := lo_pt sg @ extract_progress nid (edges sg) \<lparr>cons = cs, inte = is, prod = ps\<rparr> @ extract_progress nid (edges sg) \<lparr>cons = cs', inte = is', prod = ps'\<rparr>\<rparr>) op'') =
     (dataflow_op (sg\<lparr>lo_pt := lo_pt sg @ extract_progress nid (edges sg) \<lparr>cons = cs @ cs', inte = is @ is', prod = ps @ ps'\<rparr>\<rparr>) op'')")
         apply force
        apply (rule dataflow_op_change_multiplicities)
           apply simp_all
        unfolding extract_progress_def
        apply simp
        apply (smt (verit, del_insts) change_multiplicities_append change_multiplicities_comm)
        done
      subgoal
        apply (intro exI conjI)
        apply blast
        apply (rule b_base)
        apply (intro conjI exI)
          apply (rule refl)+
        defer
        subgoal 
          apply simp
          oops
(* 
end
              apply (subst propagate_pointstamps_append[symmetric])
              defer

            term minimal_antichain

              find_theorems frontier c_imp
              
              sorry
            done
          done
        apply simp
        apply (rule dataflow_op_change_multiplicities)
           apply simp_all
        apply (metis (no_types, lifting) change_multiplicities_append change_multiplicities_comm)
        done
      done
    subgoal for nid' op'' imp_fron sg'
      apply (simp_all split: option.splits)
      apply hypsubst_thin
      apply (intro exI conjI)
        apply (rule step_Tau_dataflow_op_Inp_Inl_intro)
          apply (rule step_subst_op_Inp_intro)
      apply assumption
         apply (rule refl)+
      subgoal for conf
        apply simp
        sorry
      subgoal for conf
        apply simp
        apply (rule b_base)
        apply (intro conjI exI)
         apply (rule refl)+
          apply simp_all
        apply (rule dataflow_op_propagate_pointstamps)
            apply simp_all
        using propagate_pointstamps_append apply force
        done
      done
    subgoal
      by blast
    subgoal
      by blast
    subgoal
      by blast
    done
next
  case SIM2
  then show ?case sorry
qed
 *)

lemma aux:
  "op ~ subst_Out_op (Inl nid) (Inl (Inl \<lparr>cons = cs @ cs', inte = is @ is', prod = ps @ ps'\<rparr>)) (Inl (Inl \<lparr>cons = cs', inte = is', prod = ps'\<rparr>)) op' \<Longrightarrow>
   dataflow_op sg op ~
   dataflow_op (sg\<lparr>lo_pt := lo_pt sg @ extract_progress nid (edges sg) \<lparr>cons = cs, inte = is, prod = ps\<rparr>\<rparr>)
     (subst_Out_op (Inl nid) (Inl (Inl \<lparr>cons = cs @ cs', inte = is @ is', prod = ps @ ps'\<rparr>)) (Inl (Inl \<lparr>cons = cs', inte = is', prod = ps'\<rparr>)) op')"
  sorry

lemma
  \<open>ys @@- xs @@- lconcat (lmap (\<lambda> (xs, t). map (\<lambda> n. (n, t)) xs) (lzip inps1 (iterates Suc i))) =
   lconcat (lmap (\<lambda> (xs, t). map (\<lambda> n. (n, t)) xs) (lzip inps2 (iterates Suc j))) \<Longrightarrow>
   inrbufs1 = buf1 (Inr (1, 1)) \<Longrightarrow>
   \<forall> x \<in> set inrbufs1. is_Inr x \<Longrightarrow>
   xs = map projr inrbufs1 \<Longrightarrow>
   ys = map (\<lambda> (n, c). (n, time c)) buf2 \<Longrightarrow>
   edges sg = (\<lambda> l. if node l = 0 \<and> port l = Src 1 then [Loc 1 (Trg 0)] else []) \<Longrightarrow>
   dataflow_op sg (inp_m_top i inps1 buf1 buf2) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (max_op j inps2)\<close>
proof (coinduction arbitrary: inps1 inps2 buf1 buf2 inrbufs1 xs ys i j sg rule: weakBisimWeakUptoBisim)
  case SIM2
  then show ?case
    apply -
    unfolding wsim_def
    apply safe
    apply (elim step_max'_top_elim step_map_op_elim step_comp_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp split: if_splits option.splits; hypsubst_thin)
    defer
  (*   subgoal for op'' io' op''a p op1' q io'a op''b xa xs
      apply (cases inps1; simp)
      subgoal for xs inps1'
        apply (cases xs; simp)
        subgoal for n xs'
          apply hypsubst_thin
          apply (rule exI)
          apply (rule conjI)
           apply (rule rtranclp.intros(1))
          apply (intro relcomppI)
            defer
          apply (rule exI[of _ "LCons xs' inps1'"])
          apply (rule exI[of _ "inps2"])
          apply (rule exI[of _ "BENQ (Inr (1, 1)) (Inr (n, i)) buf1"])
          apply (rule exI[of _ "buf2"])
          apply (rule exI[of _ "i"])
          apply (rule exI[of _ "j"])
          apply (rule exI[of _ "sg\<lparr> lo_pt := (lo_pt sg) @ extract_progress 0 (edges sg) \<lparr>cons = [], inte = [], prod = [(1, i, 1)]\<rparr> \<rparr>"])
          apply simp
          apply (intro conjI[rotated])
          subgoal
            apply (drule sym)
            apply simp
            subgoal premises prems
              apply (rule arg_cong2[where f=lshift])
               apply simp_all
              apply (rule arg_cong2[where f=lshift])
               apply (simp_all add: lconcat_correct)
              apply (subst (1 2) iterates.code)
              apply simp
              done
            done
             apply (rule refl)+
          apply (rule wbisim_refl)
          subgoal
            apply (subst (2) input_top.code)
            apply (simp add: comp_def)
            apply (cases xs'; simp)
            subgoal 
              apply (rule bisim_trans)
              apply (rule aux[where ps="[(1, i, 1)]" and ?is="[]" and cs="[]" and cs="[]" and ?is'="[(1, i, - 1), (1, Suc i, 1)]" and ?cs'="[]" and ?ps'="[]" and nid="0", simplified])
 *)


    subgoal for io op1' op'' io' op''a p x op2' io'a op''b t n
          apply (rule exI)
          apply (rule conjI)
           apply (rule rtranclp.intros(1))
          apply (intro relcomppI)
            defer
          apply (rule exI[of _ "inps1"])
          apply (rule exI[of _ "inps2"])
          apply (rule exI[of _ "BTL (Inr (1, 1)) buf1"])
          apply (rule exI[of _ "buf2 @ [(n, Cap t 1)]"])
          apply (rule exI[of _ "i"])
        apply (rule exI[of _ "j"])
        apply (rule exI[of _ "sg\<lparr> lo_pt := (lo_pt sg) @ extract_progress 1 (edges sg) \<lparr>cons = [(1, t, 1)], inte = [(1, t, 1)], prod = []\<rparr> \<rparr>"])
      apply (intro conjI exI)
            apply (rule refl)+
      subgoal sorry
      subgoal
        unfolding BTL_def
        by simp (meson in_set_tlD)
      subgoal 
        by simp
       apply (rule wbisim_refl)
      sorry
    prefer 5
    subgoal for io op1' nid op'' imp_fron sg' io' op''a p op2' io'a op''b ft below result
         apply (rule exI)
          apply (rule conjI)


