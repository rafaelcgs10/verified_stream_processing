theory Max_top

imports
  "../Timely_Infrastructure"
  Input_top
begin 

abbreviation "maxs buf \<equiv> [(n, c) \<leftarrow> buf. n = Max (set (map fst ((filter (\<lambda> (n' :: nat, c'). time c = time c') buf))))]"

corec max_top' where
  "max_top' buf = choice2
   (Read (trace (STR ''Reading frontier'') None) (\<lambda> st.
    if is_Inl st \<and> is_Inr (projl st)
    then let impf = projr (projl st) in
      let ft = frontier (impf (0 :: 1)) in
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
| impf ft where "io = Inp None (Inl (Inr impf))" "ft = frontier (impf (0 :: 1))"
  "is_empty_antichain ft" "op = \<oslash>"
| impf ft below result where "io = Inp None (Inl (Inr impf))" "ft = frontier (impf (0 :: 1))"
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



lemma wbcr_aux:
  "bisim_cong R x y \<Longrightarrow> \<W> R x z"
  oops

find_theorems "\<W>"

term bisim_cong

inductive wbisim_cong_alt for R where
  wbc_base[intro]:  "R x y \<Longrightarrow> wbisim_cong_alt R x y"
| wbc_bisim:  "wbisim x y \<Longrightarrow> wbisim_cong_alt R x y"
| wbc_refl[intro]: "x = y \<Longrightarrow> wbisim_cong_alt R x y"
| wbc_sym[intro]: "wbisim_cong_alt R x y \<Longrightarrow> wbisim_cong_alt R y x"
| wbc_Read:"x1 = y1 \<Longrightarrow> rel_fun (=) (wbisim_cong_alt R) x2 y2 \<Longrightarrow> wbisim_cong_alt R (Read x1 x2) (Read y1 y2)"
| wbc_Write: "wbisim_cong_alt R x1 y1 \<Longrightarrow> wbisim_cong_alt R (Write x1 x2 x3) (Write y1 x2 x3)"
| wbc_Silent: "wbisim_cong_alt R x1 y1 \<Longrightarrow> wbisim_cong_alt R (Silent x1) (Silent y1)"
| wbc_bisim_cong: "bisim_cong R x y \<Longrightarrow> wbisim_cong_alt R x y"

lemma wbisim_cong_alt_disj:
  "(wbisim_cong_alt R x y \<or> wbisim x y) = wbisim_cong_alt R x y"
  by (auto intro: wbc_bisim)


lemma wbisim_coinduct_upto[consumes 1, case_names BISIM]:
  "R op1 op2 \<Longrightarrow>
   (\<And>s t. R s t \<Longrightarrow> wsim (wbisim_cong_alt R) s t \<and> wsim (wbisim_cong_alt R) t s) \<Longrightarrow>
   op1 \<approx> op2"
  apply (rule wbisim.coinduct[where X="wbisim_cong_alt R", unfolded wbisim_cong_alt_disj, of op1 op2])
  subgoal
    by (auto intro: wbc_bisim)
  subgoal premises prems for s' t'
    using prems(3) apply -
    apply (induct s' t' rule: wbisim_cong_alt.induct)
    subgoal for op1 op2
      by (drule prems(2)) auto
    subgoal for op1 op2
      using wsim_mono[of wbisim "wbisim_cong_alt R"]
      apply (auto simp: le_fun_def wbc_bisim elim: wbisim.cases)
      done
    subgoal for op1 op2
      by (auto simp: wsim_def wstep_def)
    subgoal for op1 op2
      by fastforce
    subgoal for p q f g
      by (auto simp: rel_fun_def intro!: step_wstep[OF SR])
    subgoal for op1 op2 p x
      by (auto intro!: step_wstep[OF SW])
    subgoal for op1 op2
      by (auto intro: wsim_SilentI)
    subgoal for op1 op2
      oops

inductive converges where
  ceq[intro]: "op1 = op2 \<Longrightarrow> converges op1 op2"
| cstep: "(\<And>io. step io op1 op1' \<Longrightarrow> step io op2 op2' \<Longrightarrow> converges op1' op2') \<Longrightarrow> converges op1 op2"


lemma
  "converges 
   (dataflow_op sg
     (map_op (case_sum id id) (case_sum id id)
       (comp_op [Inr (0 :: 2, 1 :: 1) \<mapsto> Inr (1 :: 2, 1)] (BENQ (Inr (1, 1)) (Inr (n, i)) buf1)
         (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1)))
           (writes (Write (input_top (Cap (Suc i) 1) inps1') None (Inl (Inl \<lparr>cons = [], inte = [(1, i, - 1), (1, Suc i, 1)], prod = [(1, i, 1 + int (length xs))]\<rparr>))) (Some 1) (map (\<lambda>x. Inr (x, i)) xs)))
         (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (max_top' buf2)))))
    (dataflow_op (sg\<lparr>lo_pt := lo_pt sg @ extract_progress 0 (\<lambda>l. if node l = 0 \<and> port l = Src 1 then [Loc 1 (Trg 0)] else []) \<lparr>cons = [], inte = [], prod = [(1, i, 1)]\<rparr>\<rparr>)
     (map_op (case_sum id id) (case_sum id id)
       (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] (BENQ (Inr (1, 1)) (Inr (n, i)) buf1) (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (input_top (Cap i 1) (LCons xs inps1')))
         (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (max_top' buf2)))))"
  apply (cases xs)
  subgoal
    apply simp
  apply (rule cstep)
  subgoal for io
    apply (cases io)
    defer
    subgoal for p x
      apply (cases p; simp)
      apply (erule step_dataflow_op_elim)
      apply (elim step_map_op_elim conjE step_comp_op_elim; simp; hypsubst_thin)
      subgoal for a nid pa op1' xa
        apply hypsubst_thin
        oops

lemma aux2:
  "step io op1 (Write opf (Inl nid) (Inl (Inl st))) \<Longrightarrow>
   step io op2 (Write opf (Inl nid) (Inl (Inl \<lparr>cons = [], inte = [], prod = []\<rparr>))) \<Longrightarrow>
   dataflow_op sg op1 = dataflow_op (sg\<lparr> lo_pt := lo_pt sg @ extract_progress nid (edges sg) st \<rparr>) op2"
  apply (coinduction arbitrary: op1 op2 rule: op.coinduct_upto)
  apply simp
  subgoal for op1 op2
    apply (subst (3 4) dataflow_op.code)
    apply (simp add: rel_set_image split: sum.splits option.splits op.splits)
    apply (rule rel_setI)
    subgoal for op
(*       apply (auto 0 0 simp add: rel_set_image split: sum.splits option.splits op.splits)
      subgoal for f p opp
        apply hypsubst_thin *)
        oops

(* FIXME: move me *)
lemma steps_writes:
  "ios = map (Out p) xs \<Longrightarrow>
   steps ios (writes op p xs) op"
  apply (induct ios arbitrary: xs)
   apply (force simp add: writes_Cons_simp)+
  done

lemma
  "dataflow_op sg
     (map_op (case_sum id id) (case_sum id id)
       (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
         (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1)))
           (writes (Write op1 None (Inl (Inl \<lparr>cons = cs, inte = is, prod = ps\<rparr>))) (Some 1) (map (\<lambda>x. Inr (x, i)) xs)))
         (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) op2))) =
    dataflow_op (sg\<lparr>lo_pt := lo_pt sg @ extract_progress 0 (\<lambda>l. if node l = 0 \<and> port l = Src 1 then [Loc 1 (Trg 0)] else []) \<lparr>cons = cs, inte = is, prod = ps\<rparr>\<rparr>)
     (map_op (case_sum id id) (case_sum id id)
       (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
         (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1)))
           (writes
             (Write op1 None
               (Inl (Inl \<lparr>cons = [], inte = [], prod = []\<rparr>)))
             (Some 1) (map ((\<lambda>(x, c). Inr (x, time c)) \<circ> (\<lambda>x. (x, Cap i 1))) xs)))
         (map_op (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) (case_option (Inl 1) (\<lambda>p. Inr (1, 1))) op2)))"
  apply (induct xs arbitrary: ps "is" cs)
  subgoal 
    apply simp
    apply (subst (1 2) dataflow_op.code)
    apply (auto 0 0 simp del: cfilter_eq simp add: extract_progress_def split: op.splits if_splits option.splits)
    subgoal for p f
      apply (cases p; auto split: option.splits)
      subgoal for p x
        apply (rule cimage_eqI[simplified, of _ _ "Read (Inl p) f"])
         apply simp_all
        subgoal
          oops

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
proof (coinduction arbitrary: inps1 inps2 buf1 buf2 inrbufs1 xs ys i j sg rule: wbisim_coinduct)
  case SIM1
  then show ?case
    apply -
    apply (elim step_max'_top_elim step_map_op_elim step_comp_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp split: if_splits; hypsubst_thin)
    subgoal for op'' io' op''a p op1' q io'a op''b xa xs
      apply (cases inps1; simp)
      subgoal for xs inps1'
        apply (cases xs; simp)
        subgoal for n xs'
          apply hypsubst_thin
          apply (rule exI)
          apply (rule conjI)
           apply (rule rtranclp.intros(1))
          apply (rule wbcr_base)
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
          subgoal premises
            apply (cases xs')
            subgoal
              apply simp
            apply (coinduction rule: op.coinduct_upto)
            apply simp
            apply (rule rel_setI)
            subgoal for op
              apply (auto 0 0 split: op.splits)
              subgoal for p f
                apply (cases p; simp split: option.splits sum.splits)
                subgoal for p' pttr
                  apply hypsubst_thin
                  apply (rule bexI[of _ "Read (Inl p') f"])
                   apply simp
                  subgoal
                    apply auto
        apply (rule op.cong_Silent)
                    apply (rule op.cong_base)
                    apply auto
                    subgoal for pttr'
                      apply (drule Read_in_choices_step[simplified, where x="Inl (Inr (\<lambda>p. c_imp pttr (Loc p' (Trg 1))))"])
                      apply (elim exE step_map_op_elim step_comp_op_elim conjE step_max'_top_elim; simp; hypsubst_thin)
                      subgoal for x io' op'' p 
                        by auto
                      subgoal for x io' op'' p op2' io'a op''a
                        apply (drule sym[of _ "f (Inl (Inr (\<lambda>p. c_imp pttr (Loc 1 (Trg 1)))))"])
                        apply simp
                        apply (subst (2) comp_op_code)
                        apply simp

end
                        apply (cases x; simp)
                        subgoal for a
                        apply (cases a; simp)
                          subgoal
                            apply hypsubst_thin
                            apply (subgoal_tac "c_imp pttr (Loc 1 (Trg 1)) = c_imp pttr' (Loc 1 (Trg 1))")
                            subgoal
                            apply auto

                            apply (cases io; simp split: option.splits)

                      find_theorems choices step


end
    done
  subgoal for a xs' 
    apply (subst (1 2) writes.code)
    apply simp
    apply (subst (1 2) dataflow_op.code)
    apply (simp add: extract_progress_def split: option.splits sum.splits)
    done
  done

end
              apply (subst ( ) aux)
              apply (simp add: extract_progress_def)
              apply (rule dataflow_op_change_multiplicities)
              apply simp_all

end
              apply (smt (verit, del_insts) Cons_eq_appendI append.left_neutral change_multiplicities_append change_multiplicities_comm)
              done
            subgoal
              apply (subst (1 2) aux)
              

              find_theorems dataflow_op change_multiplicities



          apply (rule wbcr_bisim)

          done
        done
      done



              find_theorems Coinductive_List_Auxiliary.lconcat name: cor


end
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

end