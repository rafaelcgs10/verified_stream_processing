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

term monotone

inductive wbisim_cong_alt for R where
  wbc_base[intro]:  "R x y \<Longrightarrow> wbisim_cong_alt R x y"
| wbc_bisim:  "wbisim x y \<Longrightarrow> wbisim_cong_alt R x y"
| wbc_refl[intro]: "x = y \<Longrightarrow> wbisim_cong_alt R x y"
| wbc_sym[intro]: "wbisim_cong_alt R x y \<Longrightarrow> wbisim_cong_alt R y x"
| wbc_Read:"x1 = y1 \<Longrightarrow> rel_fun (=) (wbisim_cong_alt R) x2 y2 \<Longrightarrow> wbisim_cong_alt R (Read x1 x2) (Read y1 y2)"
| wbc_Write: "wbisim_cong_alt R x1 y1 \<Longrightarrow> wbisim_cong_alt R (Write x1 x2 x3) (Write y1 x2 x3)"
| wbc_Silent: "wbisim_cong_alt R x1 y1 \<Longrightarrow> wbisim_cong_alt R (Silent x1) (Silent y1)"
| wbc_bisim_trans:"x ~ y \<Longrightarrow> wbisim_cong_alt R y z \<Longrightarrow> wbisim_cong_alt R x z"


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
    subgoal for x y z
      unfolding wsim_def
      apply auto
      subgoal for io op1'
        apply (erule bisim.cases)
        subgoal for op1 op2
          apply hypsubst_thin
          apply (metis simE wbisim_cong_alt.intros(8))
          done
        done
      subgoal for io op1'
        apply (drule spec2, drule mp, assumption)
        oops

        find_theorems  wbisimulation


lemma
  "((~) OO R OO (~)) op1 op2 \<longleftrightarrow> (\<exists> op1' op2'. op1 ~ op1' \<and> R op1' op2' \<and> op2 ~ op2')"
  apply (intro iffI)
  subgoal
    using bisim_sym by blast
  subgoal
    using bisim_sym by blast
  done

lemma X[consumes 1, case_names cSim cSym]:
  fixes op1 op2 R
  assumes "R op1 op2"
  "\<And>op1 op2. R op1 op2 \<Longrightarrow> wsim R op1 op2"
  "\<And>op1 op2. R op1 op2 \<Longrightarrow> R op2 op1"
shows "op1 \<approx> op2"
  using assms apply -
  apply (rule wbisim_coinduct_upto)
   apply assumption
  apply (intro conjI)
   apply (metis wbisim_cong.intros(1) wsim_def)
  apply (metis wbisim_cong.intros(1) wsim_def)
  done

lemma strongAppend:
  assumes PSimQ: "wsim Rel Q P"
  and     QSimR: "sim Rel' R Q"
  and     Trans: "Rel' OO Rel \<le> Rel''"
shows "wsim Rel'' R P"
 using assms
  unfolding wsim_def sim_def
  apply blast
  done

lemma weakBisimulationE:
  assumes "P \<approx> Q"
  shows "wsim (\<approx>) P Q"
  and   "Q \<approx> P"
using assms
  apply (meson wbisim.cases wbisim_sym)+
  done

lemma weakSimI[case_names Sim]:
  assumes "\<And>io Q'. step io Q Q' \<Longrightarrow> \<exists>P'. wstep io P P' \<and> Rel Q' P'"
  shows "wsim Rel Q P"
  using assms unfolding wsim_def by blast


lemma weakSimE:
  assumes "wsim Rel Q P"
  and     "step io Q Q'"

  obtains P' where "wstep io P P'" and "Rel Q' P'"
  using assms apply -
  apply atomize_elim
  apply (auto simp add: wsim_def)
  done

lemma simE2:
  assumes "Rel Q P"
  and     "wstep io Q Q'"
  and     Sim: "\<And>R S. Rel S R \<Longrightarrow> wsim Rel S R"
  obtains P' where "wstep io P P'" and "Rel Q' P'"
  sorry

lemma wsimTransitive:
  assumes "Rel Q P"
    and     "wsim Rel' R Q"
    and     "Rel' OO Rel \<le> Rel''"
    and     "\<And>S T. Rel T S \<Longrightarrow> wsim Rel T S"
  shows "wsim Rel'' R P"
proof(induct rule: weakSimI)
  case(Sim io R')
  thus ?case using assms
    apply(drule_tac Q=R in weakSimE, auto)
    by(drule_tac Q=Q in simE2, auto)
qed


lemma
  assumes p: "X Q P"
 and rSim: "(\<And>Q P. X Q P \<Longrightarrow> wsim ((\<approx>) OO X OO (~)) Q P)"
 and rSym: "(\<And>Q P. X Q P \<Longrightarrow> X Q P)"
  shows "P \<approx> Q"
proof -
  let ?X = "(\<approx>) OO X OO (\<approx>)"
  let ?Y = "(\<approx>) OO X OO (~)"
  from assms have "?X Q P" by (metis relcompp_apply wbisim_refl)
  thus ?thesis
  proof (coinduction arbitrary: Q P rule: X)
    case(cSim Q P)
    {
      fix P P' Q' Q
    assume "P \<approx> P'" and "X P' Q'" and "Q' \<approx> Q"
    from \<open>X P' Q'\<close> have "?Y P' Q'" by (metis bisim_refl relcompp_apply wbisim_refl_alt)
    moreover from \<open>Q' \<approx> Q\<close> have "wsim (\<approx>) Q' Q" by (meson wbisim.cases)
    moreover have "?Y OO (\<approx>) \<le> ?X" 
      by (smt (z3) bisim_wbisim predicate2I_obj relcompp.inducts relcompp_assoc relcompp_mono
          wbisim_trans)
     moreover {
       fix Q P
        assume "?Y Q P"
        then obtain P' Q' where "Q \<approx> Q'" and "X Q' P'" and "P' ~ P" by auto
        from \<open>X Q' P'\<close> have "wsim ?Y Q' P'"  by(rule rSim)
        moreover from \<open>P' ~ P\<close> have "sim (~) P' P" by (meson bisim.cases)
        moreover have "?Y OO (~) \<le> ?Y" using bisim_trans by blast
        ultimately have "wsim (?Y) Q P'" 
          apply -
          apply (rule strongAppend)
          apply assumption
          

end
        moreover note \<open>P \<approx> P'\<close>
        moreover have "(\<approx>) OO ?Y \<le> ?Y" using wbisim_trans by blast
        ultimately have "wsim ?Y P Q"
          by (metis wbisimulation_wbisim wsimTransitive)
      }
      ultimately have "wsim ?X P' Q" 
        by (smt (verit, ccfv_SIG) wsimTransitive)
      moreover note \<open>P \<approx> P'\<close>
      moreover have "(\<approx>) OO ?X \<le> ?X"
        by (metis (no_types, opaque_lifting) predicate2I_obj relcompp.inducts relcompp_assoc relcompp_mono
            wbisim_trans)
      ultimately have "wsim ?X P Q" by (metis wbisimulation_wbisim wsimTransitive)
    }
    with \<open>?X P Q\<close> show ?case by auto
  next
    case(cSym P Q)
    thus ?case 
      apply auto
      by (metis assms(3) relcompp.intros wbisim'_alt wbisim'_sym)
  qed
qed



end


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
          apply (rule aux3[where S=bisim and F=id, simplified])
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
          subgoal premises prems1
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
                          apply (simp add: extract_progress_def)
                          subgoal premises prems2
                          apply (subst (2) comp_op_code)
                            apply simp
                            apply (subst (1 2) dataflow_op.code)
                            apply simp
                            apply safe
                            subgoal





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