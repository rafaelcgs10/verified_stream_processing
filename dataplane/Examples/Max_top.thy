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
| wbc_bisim_trans:"((~) OO R) op1 op2 \<Longrightarrow> wbisim_cong_alt R op1 op2"


lemma wbisim_cong_alt_disj:
  "(wbisim_cong_alt R x y \<or> wbisim x y) = wbisim_cong_alt R x y"
  by (auto intro: wbc_bisim)

definition sim_set (\<open>_ \<leadsto>[_] _\<close> [80, 80, 80] 80)
where
  "P \<leadsto>[Rel] Q \<equiv> \<forall>io Q'. step io Q Q' \<longrightarrow> (\<exists>P'. step io P P' \<and> (P', Q') \<in> Rel)"

definition wsim_set (\<open>_ \<leadsto>\<^sup>^<_> _\<close> [80, 80, 80] 80)
where
  "P \<leadsto>\<^sup>^<Rel> Q \<equiv> \<forall>io Q'. step io Q Q' \<longrightarrow> (\<exists>P'. wstep io P P' \<and> (P', Q') \<in> Rel)"

lemma rel2_in_rel[simp]:
  "in_rel = rel2p"
  unfolding rel2p_def by force

lemma in_p2_rel_simp[simp]:
  "(op1, op2) \<in> p2rel X \<longleftrightarrow> X op1 op2"
  by (metis case_prodI mem_Collect_eq p2relD p2rel_def)

lemma wsim_set_wsim:
  "P \<leadsto>\<^sup>^<p2rel R> Q \<longleftrightarrow> wsim (conversep R) Q P"
  unfolding wsim_def wsim_set_def
  apply auto
  done

lemma sim_set_sim:
  "P \<leadsto>[p2rel R] Q \<longleftrightarrow> sim (conversep R) Q P"
  unfolding sim_def sim_set_def
  apply auto
  done

lemma bisim_converse[simp]:
  "(~)\<inverse>\<inverse> = (~)"
  using bisim_sym by blast

lemma wbisim_converse[simp]:
  "(\<approx>)\<inverse>\<inverse> = (\<approx>)"
  using wbisim_sym by blast

lemma p2rel_relcompp:
  "p2rel (R1 OO R2) = p2rel R1 O p2rel R2"
  by force


lemma wsim_set_wsim_ex:
  "P \<leadsto>\<^sup>^<((p2rel (\<approx>)) O (p2rel X) O (p2rel (~)))> Q \<longleftrightarrow> wsim ((~) OO (conversep X) OO (\<approx>)) Q P"
  using wsim_set_wsim[where P=P and Q=Q and R="(\<approx>) OO X OO (~)", simplified]
  by (simp add: p2rel_relcompp relcompp_assoc converse_relcompp)

lemma strongAppend:
  assumes PSimQ: "P \<leadsto>\<^sup>^<Rel> Q"
  and     QSimR: "Q \<leadsto>[Rel'] R"
  and     Trans: "Rel O Rel' \<subseteq> Rel''"
  shows "P \<leadsto>\<^sup>^<Rel''> R"
 using assms
  unfolding wsim_set_def sim_set_def
  apply blast
  done

lemma weakSimE:
  assumes "P \<leadsto>\<^sup>^<Rel> Q"
  and     "step io Q Q'"

  obtains P' where "wstep io P P'" and "(P', Q') \<in> Rel"
  using assms apply -
  apply atomize_elim
  apply (auto simp add: wsim_set_def)
  done

lemma weakSimI[case_names Sim]:
  assumes "\<And>io Q'. step io Q Q' \<Longrightarrow> \<exists>P'. wstep io P P' \<and> (P', Q') \<in> Rel"

  shows "P \<leadsto>\<^sup>^<Rel> Q"
using assms
  by(auto simp add: wsim_set_def)

term "p2rel (wbisim_cong X)"

lemma weakBisimWeakCoinduct[consumes 1, case_names cSim cSym]:
  assumes "(P, Q) \<in> X"
    and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<X> Q"
    and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> Q \<leadsto>\<^sup>^<X> P"
  shows "P \<approx> Q"
  using assms apply -
  apply (rule wbisim_coinduct_upto)
   apply assumption
  apply (intro conjI)
  apply (metis (mono_tags, lifting) conversep_wbc predicate2I rel2pD rel2p_inv(2) rev_predicate2D wbisim_cong.intros(1) wsim_conversep_mono wsim_set_wsim)+
  done

lemma
  "(\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto>\<^sup>^<Rel> S) \<Longrightarrow>
   (\<And>R S. (R, S) \<in> (converse Rel) \<Longrightarrow> R \<leadsto>\<^sup>^<converse Rel> S)"
  apply (auto simp add: wsim_set_def wstep_def)
  oops


lemma
  "(\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto>\<^sup>^<Rel> S) \<Longrightarrow> wbisimulation (rel2p Rel)"
  apply (auto simp add: wsim_def wsim_set_def rel2p_def)
  oops

lemma rel2p_converse_simp:
  "rel2p (Rel\<inverse>) = conversep (rel2p Rel)"
  unfolding rel2p_def by force

lemma wbisim_wstep_Tau_stronger:
  assumes "wsimulation_canonical R"
    and "R op1 op2"
    and "(step Tau)\<^sup>*\<^sup>* op1 op1'"
  shows "\<exists>op2'. wstep Tau op2 op2' \<and> R op1' op2'"
  using assms(3,2)
proof (induct op1 arbitrary: op2 rule: converse_rtranclp_induct)
  case (step op1 op1'')
  with assms(1) obtain op2'' where "wstep Tau op2 op2''" "R op1'' op2''"
    unfolding wsim_def by (metis wsimulation_canonical_def)
  moreover from step(3)[OF \<open>R op1'' op2''\<close>] obtain op2' where "wstep Tau op2'' op2'" "R op1' op2'"
    by blast
  ultimately show ?case by (auto intro!: exI[of _ op2'])
qed force

lemma wbisim_wstep_stronger:
  assumes "wsimulation_canonical R"
    and "R op1 op2"
    and "wstep io op1 op1'"
  obtains op2' where "wstep io op2 op2'" and "R op1' op2'"
proof -
  from assms(3) obtain opi opj where \<open>(step Tau)\<^sup>*\<^sup>* op1 opi\<close> \<open>estep io opi opj\<close> \<open>(step Tau)\<^sup>*\<^sup>* opj op1'\<close> unfolding wstep_def by blast
  moreover from assms(1,2) obtain \<open>wsim R op1 op2\<close> unfolding wsim_def by (simp add: that wsim_correct)
  ultimately have \<open>\<exists>op2'. wstep io op2 op2' \<and> R op1' op2'\<close> using assms(2)
  proof (induct op1 arbitrary: op2 rule: converse_rtranclp_induct)
    case base
    show ?case
    proof (cases "io = Tau \<and> opi = opj")
      case True
      with base(2,3,4) show ?thesis
        using wbisim_wstep_Tau_stronger[OF assms(1), of opi op2 op1'] by auto
    next
      case False
      with base obtain opj' where H1: \<open>wstep io op2 opj'\<close> \<open>R opj opj'\<close> unfolding wsim_def by (cases io) force+
      with assms(1) have \<open>wsim R opj opj'\<close> unfolding wsim_def by (simp add: wsimulation_canonical_def)
      with base(2) H1(2) have \<open>\<exists>op2'. (step Tau)\<^sup>*\<^sup>* opj' op2' \<and> R op1' op2'\<close>
        using wbisim_wstep_Tau_stronger[OF assms(1), of opj opj' op1'] by auto
      with \<open>wstep io op2 opj'\<close> show ?thesis unfolding wstep_def
        by (smt (verit, best) relcompp_apply rtranclp_trans)
    qed
  next
    case (step op1 opk)
    from step(1) obtain opk' where "(step Tau)\<^sup>*\<^sup>* op2 opk'" "R opk opk'"
      by (auto dest!: step(6)[unfolded wsim_def, rule_format])
    with step(3)[of opk'] step(4,5) assms(1) show ?case unfolding wstep_def
      by (smt (verit, ccfv_SIG) estep.elims transitive_closurep_trans'(2) wsim_correct wstep_def wstep_steps_Tau wstep_trans'(1,2))
  qed
  then show ?thesis using that by force
qed


lemma wsimTransitive:
  assumes "(P, Q) \<in> Rel"
  and     "Q \<leadsto>\<^sup>^<Rel'> R"
  and     "Rel O Rel' \<subseteq> Rel''"
  and     "\<And>S T. (S, T) \<in> Rel \<Longrightarrow> S \<leadsto>\<^sup>^<Rel> T"
  shows "P \<leadsto>\<^sup>^<Rel''> R"
proof(induct rule: weakSimI)
  case(Sim io R')
  thus ?case using assms
    apply(drule_tac Q=R in weakSimE, auto)
    subgoal for Q'
      apply (rule wbisim_wstep_stronger[rotated, of "rel2p (converse Rel)" Q P io Q', unfolded rel2p_def, simplified])
         apply assumption+
       apply blast
      apply (auto simp add: wsim_set_def  wsimulation_canonical_def wstep_def wsim_def)
      done
    done
qed

lemma p2rel_converse[simp]:
  "(p2rel R)\<inverse> = p2rel (conversep R)"
  by auto

lemma wsim_set_wbisim_l:
  assumes "P' \<leadsto>\<^sup>^<(p2rel (\<approx>) O X)> Q" 
    and p: "P \<approx> P'" 
  shows "P \<leadsto>\<^sup>^<(p2rel (\<approx>) O X)> Q"
proof -
  let ?Y = "p2rel (\<approx>) O X"
  show ?thesis
  proof -
    have "(p2rel (\<approx>)) O ?Y \<subseteq> ?Y" using wbisim_trans by fastforce
    then show ?thesis 
      using assms apply -
      apply (rule wsimTransitive)
         prefer 3
         apply assumption
        apply simp_all
      apply (metis wbisim.cases wbisim_converse wsim_set_wsim)+
      done
  qed
qed

lemma sim_set_bisim_r:
  assumes "P \<leadsto>[(X O p2rel (~))] Q" 
    and p: "Q ~ Q'" 
  shows "P \<leadsto>[(X O p2rel (~))] Q'"
proof -
  let ?Y = "X O p2rel (~)"
  show ?thesis
  proof -
    have "?Y O (p2rel (~)) \<subseteq> ?Y" using bisim_trans by fastforce
    then show ?thesis 
      using assms by (smt (verit, ccfv_threshold) basic_trans_rules(24) bisim.simps bisim_refl in_p2_rel_simp relcomp.intros sim_def sim_set_def subrelI)
  qed
qed

lemma simWeakSim:
  assumes "P \<leadsto>[Rel] Q"
  shows "P \<leadsto>\<^sup>^<Rel> Q"
using assms
  apply(rule_tac weakSimI, auto)
  apply (meson sim_set_def step_wstep)
  done

lemma wsim_set_bisim_r:
  assumes "P \<leadsto>[(X O p2rel (~))] Q" 
    and p: "Q ~ Q'" 
  shows "P \<leadsto>\<^sup>^<(X O p2rel (\<approx>))> Q'"
  using assms apply -
  apply (rule simWeakSim)
  apply (drule sim_set_bisim_r)
   apply assumption
  apply (smt (verit, ccfv_threshold) bisim_wbisim in_p2_rel_simp relcomp.simps sim_set_def) 
  done


lemma wsim_set_bisim_l:
  assumes "P' \<leadsto>\<^sup>^<(p2rel (~) O X)> Q" 
    and p: "P ~ P'" 
  shows "P \<leadsto>\<^sup>^<(p2rel (~) O X)> Q"
proof -
  let ?Y = "p2rel (~) O X"
  show ?thesis
  proof -
    have "(p2rel (~)) O ?Y \<subseteq> ?Y" using bisim_trans by fastforce
    then show ?thesis 
      using assms apply -
      apply (rule wsimTransitive)
         prefer 3
         apply assumption
      apply simp_all
      apply (metis bisim.cases bisim_converse simWeakSim sim_set_sim)
      done
  qed
qed

lemma wbisim_absorb_bisim_l:
  "(X O p2rel (~)) O p2rel (\<approx>) \<subseteq> X O p2rel (\<approx>)"
  by (smt (verit) bisim_wbisim in_p2_rel_simp relcomp.simps relcompE subset_iff wbisim_trans)


lemma wbisim_absorb_bisim_r:
  "X O p2rel (\<approx>) O p2rel (~) \<subseteq> X O p2rel (\<approx>)"
  by (smt (verit) bisim_wbisim in_p2_rel_simp relcomp.simps relcompE subset_iff wbisim_trans)

lemma
  "(P', Q') \<in> p2rel (\<approx>) O X O p2rel (~) \<Longrightarrow> Q' \<leadsto>\<^sup>^<p2rel (\<approx>)> Q \<Longrightarrow> P' \<leadsto>\<^sup>^<(p2rel (\<approx>) O X O p2rel (\<approx>))> Q"
  oops

lemma wbisim_wsim_setD:
  "Q' \<approx> Q \<Longrightarrow> Q' \<leadsto>\<^sup>^<(p2rel (\<approx>))> Q \<and> Q \<leadsto>\<^sup>^<(p2rel (\<approx>))> Q'"
  by (simp add: wbisim.simps wsim_set_wsim)

lemma wsim_set_wbisim_bisim_r_l:
  assumes sim: "P' \<leadsto>\<^sup>^<(p2rel (\<approx>) O X O p2rel (~))> Q'"
    and Q: "Q' ~ Q"
    and P: "P \<approx> P'"
  shows "P \<leadsto>\<^sup>^<(p2rel (\<approx>) O X O p2rel (~))> Q"
  using assms proof -
  let ?Y = "p2rel (\<approx>) O X O p2rel (~)"
  show ?thesis
  proof -
    note Q
    then have qsim: "Q' \<leadsto>[p2rel (~)] Q" by (simp add: bisim.simps sim_set_sim)
    moreover have "?Y O p2rel (~) \<subseteq> ?Y" by (smt (z3) O_assoc bisim_trans in_p2_rel_simp relcomp.inducts relcomp_mono subrelI)
    ultimately
    have "P' \<leadsto>\<^sup>^<?Y> Q"
      apply -
      apply (rule strongAppend)
        apply (rule sim)
       apply assumption+
      done
    moreover note \<open>P \<approx> P'\<close>
    moreover have "(p2rel (\<approx>)) O ?Y \<subseteq> ?Y" using wbisim_trans by fastforce
    ultimately have "P \<leadsto>\<^sup>^<?Y> Q" 
      apply -
      apply (rule wsimTransitive)
         prefer 3
         apply assumption
        apply simp_all
      apply (metis wbisim.cases wbisim_converse wsim_set_wsim)+
      done
    then show ?thesis.
  qed
qed


lemma wsim_set_bisim_wbisim_r_l:
  assumes sim: "P' \<leadsto>\<^sup>^<(p2rel (~) O X O p2rel (\<approx>))> Q'"
    and P: "P ~ P'"
    and Q: "Q \<approx> Q'"
  shows "P \<leadsto>\<^sup>^<(p2rel (~) O X O p2rel (\<approx>))> Q"
  using assms apply -
  apply (rule wsim_set_bisim_l[rotated])
   apply assumption
  oops

lemma weakBisimWeakUpto_rSim_aux:
  assumes eq1: "P \<approx> P'" 
    and eq2: "Q' ~ Q"
    and inn: "(P', Q') \<in> X" 
    and rSim: "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<((p2rel (\<approx>)) O X O (p2rel (~)))> Q"
  shows "P \<leadsto>\<^sup>^<(p2rel (\<approx>) O X O p2rel (~))> Q"
  using assms wsim_set_wbisim_bisim_r_l by blast


lemma weakBisimWeakUpto_rSym_aux:
  assumes eq1: "P ~ P'" 
    and eq2: "Q' \<approx> Q"
    and inn: "(P', Q') \<in> X" 
    and rSym: "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> Q \<leadsto>\<^sup>^<((p2rel (\<approx>)) O X O (p2rel (~)))> P"
  shows "Q \<leadsto>\<^sup>^<(p2rel (\<approx>) O X O p2rel (~))> P"
  using assms wsim_set_wbisim_bisim_r_l bisim_sym wbisim_sym by blast

lemma weakBisimWeakUpto_rSim:
  "(P', Q') \<in> p2rel (\<approx>) O X O p2rel (~) \<Longrightarrow>
   Q' \<leadsto>\<^sup>^<p2rel (\<approx>)> Q \<Longrightarrow>
   (\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<(p2rel (\<approx>) O X O p2rel (~))> Q) \<Longrightarrow>
   P' \<leadsto>\<^sup>^<(p2rel (\<approx>) O X O p2rel (\<approx>))> Q"
  apply (subgoal_tac "(p2rel (\<approx>) O X O p2rel (~)) O p2rel (\<approx>) \<subseteq> p2rel (\<approx>) O X O p2rel (\<approx>)")
  apply (smt (verit, ccfv_threshold) in_p2_rel_simp relcomp.cases wsimTransitive wsim_set_wbisim_bisim_r_l)
  using wbisim_absorb_bisim_l apply fastforce
  done

lemma weakBisimWeakUpto_rSim:
  "(P', Q') \<in> p2rel (\<approx>) O X O p2rel (~) \<Longrightarrow>
   P' \<leadsto>\<^sup>^<p2rel (\<approx>)> P \<Longrightarrow>
   (\<And>P Q. (P, Q) \<in> X \<Longrightarrow> Q \<leadsto>\<^sup>^<((p2rel (\<approx>)) O X O (p2rel (~)))> P) \<Longrightarrow>
   Q \<leadsto>\<^sup>^<(p2rel (\<approx>) O X O p2rel (\<approx>))> P'"
  apply (subgoal_tac "(p2rel (\<approx>) O X O p2rel (~)) O p2rel (\<approx>) \<subseteq> p2rel (\<approx>) O X O p2rel (\<approx>)")
  oops
(* 
  oops
  apply (subgoal_tac "(p2rel (\<approx>) O X O p2rel (~)) O p2rel (\<approx>) \<subseteq> p2rel (\<approx>) O X O p2rel (\<approx>)")
   apply (rule wsimTransitive)
      prefer 3
      apply assumption
     apply simp_all
  subgoal for S T
    apply safe
    apply simp
    subgoal for P'' Q'' S' T'
      apply (rule weakBisimWeakUpto_rSym_aux)
      apply (subst bisim_sym)
      apply assumption+
      apply (subst wbisim_sym)
      apply assumption+
      apply simp_all *)


lemma weakBisimWeakUpto_rSym:
  assumes rSym: "(\<And>P Q. (P, Q) \<in> X \<Longrightarrow> Q \<leadsto>\<^sup>^<(p2rel (~) O X O p2rel (\<approx>))> P)"
  shows
  "(P', Q') \<in> p2rel (\<approx>) O X O p2rel (~) \<Longrightarrow>
   Q \<leadsto>\<^sup>^<p2rel (\<approx>)> Q' \<Longrightarrow>
   Q \<leadsto>\<^sup>^<(p2rel (\<approx>) O X O p2rel (\<approx>))> P'"
  apply safe
  apply simp
   apply (rule wsimTransitive[of ])
     prefer 2
  apply (rule wsim_set_bisim_r)
  oops

lemma wsim_set_def_converse_wbisim_cong:
  "P \<leadsto>\<^sup>^<converse X> Q \<Longrightarrow> P \<leadsto>\<^sup>^<p2rel (wbisim_cong (rel2p X))> Q"
  unfolding wsim_set_def
  apply safe
  apply (metis converse.cases in_p2_rel_simp rel2p_def wbisim_cong.wbc_base wbisim_cong.wbc_sym)
  done

term symclp

find_theorems symclp conversep

lemma wsim_set_def_disjI:
  "P \<leadsto>\<^sup>^<Y> Q \<or> P \<leadsto>\<^sup>^<X> Q \<Longrightarrow> P \<leadsto>\<^sup>^<(Y \<union> X)> Q"
  unfolding wsim_set_def
   apply blast
  done

lemma weakBisimWeakUpto[case_names cSim cSym, consumes 1]:
  assumes p: "(P, Q) \<in> X"
    and rSim: "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<((p2rel (\<approx>)) O X O (p2rel (~)))> Q"
    and rSym: "\<And> P Q. (P, Q) \<in> X \<Longrightarrow> Q \<leadsto>\<^sup>^<((p2rel (\<approx>)) O converse X O (p2rel (~)))> P"
  shows "P \<approx> Q"
proof -
  let ?X = "p2rel (\<approx>) O X O p2rel (\<approx>)"
  let ?Y = "p2rel (\<approx>) O X O p2rel (~)"
  from \<open>(P, Q) \<in> X\<close> have "(P, Q) \<in> (?X \<union> converse ?X)" by (metis UnI1 in_p2_rel_simp relcomp.relcompI wbisim_refl)
  thus ?thesis
  proof(coinduct rule: weakBisimWeakCoinduct)
    case(cSim P Q)
    thus ?case 
      apply safe
       apply simp_all
      subgoal for P' Q'
        apply (frule wbisim_wsim_setD[of  P])
        apply (frule wbisim_wsim_setD[of _ Q])
        apply safe
        apply (rule wsim_set_def_disjI)
        apply (rule disjI1)
        apply (rule weakBisimWeakUpto_rSim[rotated, OF _ rSim])
          apply assumption+
        apply (intro relcompI)
          apply simp_all
        apply (rule bisim_refl)
        done
      subgoal for Q' P'
        apply (frule wbisim_wsim_setD[of  P'])
        apply (frule wbisim_wsim_setD[of _ Q'])
        apply safe
        apply (rule wsim_set_def_disjI)
        apply (rule disjI2)
        apply (simp add: converse_relcomp O_assoc)
        apply (rule weakBisimWeakUpto_rSim[rotated])
          apply assumption+
         defer
         apply (intro relcompI)
           apply simp_all
        using wbisim_sym apply blast
         apply (rule bisim_refl)
        using rSym apply blast
        done
      done
  next
    case(cSym P Q)
    thus ?case 
      apply -
      apply safe
       apply simp_all
      subgoal for P' Q'
        apply (frule wbisim_wsim_setD[of  P])
        apply (frule wbisim_wsim_setD[of _ Q])
        apply safe
        apply (rule wsim_set_def_disjI)
        apply (simp add: converse_relcomp O_assoc)
        apply (rule disjI2)
        apply (rule weakBisimWeakUpto_rSim[rotated])
          apply assumption+
         defer
         apply (intro relcompI)
           apply simp_all
        using wbisim_sym apply blast
         apply (rule bisim_refl)
        using rSym apply blast
        done
      subgoal for Q' P'
        apply (frule wbisim_wsim_setD[of  P'])
        apply (frule wbisim_wsim_setD[of _ Q'])
        apply safe
        apply (rule wsim_set_def_disjI)
        apply (simp add: converse_relcomp O_assoc)
        apply (rule disjI1)
        apply (rule weakBisimWeakUpto_rSim[rotated])
          apply assumption+
         defer
         apply (intro relcompI)
           apply simp_all
         apply (rule bisim_refl)
        using rSim apply blast
        done
      done
  qed
qed

lemma weakBisimUpto[case_names cSim cSym, consumes 1]:
  assumes p: "(P, Q) \<in> X"
  and rSim: "\<And>R S. (R, S) \<in> X \<Longrightarrow> R \<leadsto>\<^sup>^<(p2rel (\<approx>) O (X \<union> p2rel (\<approx>)) O p2rel (~))> S"
  and rSym: "\<And>R S. (R, S) \<in> X \<Longrightarrow> S \<leadsto>\<^sup>^<(p2rel (\<approx>) O (converse X \<union> p2rel (\<approx>)) O p2rel (~))> R"
  shows "P \<approx> Q"
proof -
  from p have "(P, Q) \<in> X \<union> p2rel (\<approx>)" by simp
  thus ?thesis
    apply(coinduct rule: weakBisimWeakUpto)
     apply(auto dest: rSim rSym)
    unfolding wsim_set_def
      apply (metis (no_types, opaque_lifting) UnI1 bisim_refl in_p2_rel_simp inf_sup_aci(5) p2rel_relcompp relcomppI wbisim_refl wbisim_sym wbisim_wstep_alt)
    apply (metis rSym converse_add_simps(3) p2rel_converse wbisim_converse weakSimE)
    apply (smt (verit, ccfv_SIG) UnI2 bisim_refl converse_iff in_p2_rel_simp relcomp.relcompI wbisim_refl wbisim_wstep_alt)
    done
qed

thm weakBisimWeakUpto[where X="p2rel R", unfolded wsim_set_wsim p2rel_relcompp, no_vars]

lemma
  "(P, Q) \<in> p2rel R \<Longrightarrow>
(\<And>P Q. (P, Q) \<in> p2rel R \<Longrightarrow> P \<leadsto>\<^sup>^<(p2rel (\<approx>) O p2rel R O p2rel (~))> Q) \<Longrightarrow>
(\<And>P Q. (P, Q) \<in> p2rel R \<Longrightarrow> Q \<leadsto>\<^sup>^<(p2rel (\<approx>) O (p2rel R)\<inverse> O p2rel (~))> P) \<Longrightarrow> P \<approx> Q"
  apply (simp_all add: wsim_set_wsim flip: p2rel_relcompp)
  apply (simp add: converse_relcompp relcompp_assoc)
  oops

  find_theorems " (_  OO _)" name: assoc

lemma weakBisimWeakUptoBisim[case_names SIM1 SIM2, consumes 1]:
  assumes p: "R op1 op2"
  and rSim: "\<And>op1 op2. R op1 op2 \<Longrightarrow> wsim ((~) OO R\<inverse>\<inverse> OO (\<approx>)) op2 op1"
   and rSym: "\<And>op1 op2. R op1 op2 \<Longrightarrow> wsim ((~) OO R OO (\<approx>)) op1 op2"
 shows "op1 \<approx> op2"
  apply (rule weakBisimWeakUpto[where X="p2rel R"])
  using assms(1) apply fastforce
  apply (simp_all add: wsim_set_wsim flip: p2rel_relcompp)
  apply (simp_all add: converse_relcompp relcompp_assoc)
   apply (rule rSim) 
  apply assumption
   apply (rule rSym) 
  apply assumption
  done

lemma lambda_disj_conversep[simp]:
  "(\<lambda>a b. R a b \<or> a \<approx> b)\<inverse>\<inverse> = (\<lambda>a b. R b a \<or> a \<approx> b)"
  using wbisim_sym by auto

lemma weakBisimUptoBisim[case_names SIM1 SIM2, consumes 1]:
  assumes p: "R op1 op2"
  and rSim: "\<And>op1 op2. R op1 op2 \<Longrightarrow> wsim ((~) OO (\<lambda> op1 op2. R op1 op2 \<or> op1 \<approx> op2) OO (\<approx>)) op1 op2"
   and rSym: "\<And>op1 op2. R op1 op2 \<Longrightarrow> R op2 op1"
  shows "op1 \<approx> op2"
proof -
  from p have "R op1 op2 \<or> op1 \<approx> op2" by simp
  thus ?thesis
    apply(coinduct rule: weakBisimWeakUptoBisim)
     apply(auto dest: rSim rSym)
    using assms(2)
      apply (smt (z3) assms(3) predicate2D predicate2I_obj relcompp_mono wsim_mono)
  apply (smt (verit, del_insts) bisim_refl eq_OO predicate2D predicate2I_obj relcompp_mono wbisim.cases wbisim_refl wsim_mono)
    oops


lemma weakBisimUptoBisimSym[case_names SIM1, consumes 1]:
  assumes p: "R op1 op2"
  and rSim: "\<And>op1 op2. symclp R op1 op2 \<Longrightarrow> wsim ((~) OO (\<lambda> op1 op2. symclp R op1 op2 \<or> op1 \<approx> op2) OO (\<approx>)) op1 op2"
  shows "op1 \<approx> op2"
  oops

lemma weakBisimUptoBisimSym_split[case_names SIM1, consumes 1]:
  assumes p: "R op1 op2"
  and SIM1: "\<And>op1 op2. R op1 op2 \<Longrightarrow> wsim ((~) OO (\<lambda> op1 op2. symclp R op1 op2 \<or> op1 \<approx> op2) OO (\<approx>)) op1 op2"
  and SIM2: "\<And>op1 op2. R op2 op1 \<Longrightarrow> wsim ((~) OO (\<lambda> op1 op2. symclp R op1 op2 \<or> op1 \<approx> op2) OO (\<approx>)) op1 op2"
  shows "op1 \<approx> op2"
  oops

(* FIXME: move me *)
lemma steps_writes:
  "ios = map (Out p) xs \<Longrightarrow>
   steps ios (writes op p xs) op"
  apply (induct ios arbitrary: xs)
   apply (force simp add: writes_Cons_simp)+
  done

lemma cfilter_eq_forall_eq:
  "cfilter F C = cfilter F C' \<longleftrightarrow>
   (\<forall> c. F c \<longrightarrow> c |\<in>| C \<longleftrightarrow> c |\<in>| C')"
  by auto



abbreviation "is_bisim_cong f \<equiv> (\<forall> op op'. op ~ op' \<longrightarrow> f op ~ f op')"

lemma
  "is_bisim_cong f \<Longrightarrow>
   is_bisim_cong f' \<Longrightarrow>
   op ~ op' \<Longrightarrow>
   f (Write op p xs) ~ f' (Write op' p xs)"
  apply (coinduction rule: bisim_coinduct_upto'')
  subgoal for io op1'
    apply (erule bisim.cases)
    subgoal for op1 op2
      apply (auto simp add: sim_def)
      oops

(* FIXME: move me *)
lemma map_op_writes[simp]:
  "map_op f1 f2 (writes op p xs) = writes (map_op f1 f2 op) (f2 p) xs"
  apply (induct xs)
   apply (simp_all add: writes_Cons_simp)
  done

lemma bisim_step_elim:
  "op1 ~ op2 \<Longrightarrow>
   step io op1 op1' \<Longrightarrow>
   \<exists> op2'. step io op2 op2' \<and> op1' ~ op2'"
  by (meson bisim.simps sim_def)

fun extract_update where
  "extract_update (Write op (Inl nid) (Inl (Inl st))) = (Write op (Inl nid) (Inl (Inl \<lparr> cons = [], inte = [], prod = [] \<rparr>)), st)"
| "extract_update op = (op, \<lparr> cons = [], inte = [], prod = [] \<rparr>)"

abbreviation "no_Choice op \<equiv> is_Read op \<or> is_Write op \<or> is_Silent op"

corec subst_op where
  "subst_op x_op y_op op = Choice (cimage (\<lambda> op.
     if op = x_op 
     then y_op 
     else case op of 
       Write op' p x \<Rightarrow> Write (subst_op x_op y_op op') p x
     | Read p f \<Rightarrow> Read p (\<lambda> x. (subst_op x_op y_op (f x)))
     | Silent op' \<Rightarrow> Silent (subst_op x_op y_op op')) (choices op))"

lemma step_subst_op_Tau_intro[intro]:
  "step io op op' \<Longrightarrow>
   io = Tau \<Longrightarrow>
   x_op = Silent op' \<Longrightarrow>
   step io' y_op y_op' \<Longrightarrow>
   step io' (subst_op x_op y_op op) y_op'"
  apply (induct io op op' pred: step)
     apply (simp_all; hypsubst_thin; simp)
  subgoal 
    by force
  subgoal 
    apply (subst subst_op.code)
    apply force
    done
  subgoal 
    apply (subst subst_op.code)
    apply simp
    apply (smt (verit, ccfv_SIG) IO.distinct(5) IO.simps(5) cUN_I cimageI cin.rep_eq step.intros(4) step_choicesE) 
    done
  done

lemma step_subst_op_Out_intro[intro]:
  "step io op op' \<Longrightarrow>
   io = Out p x \<Longrightarrow>
   x_op = Write op' p x \<Longrightarrow>
   step io' y_op y_op' \<Longrightarrow>
   step io' (subst_op x_op y_op op) y_op'"
  apply (induct io op op' pred: step)
     apply (simp_all; hypsubst_thin; simp)
  subgoal 
    apply (subst subst_op.code)
    apply force
    done
  subgoal
    by force
  subgoal 
    apply (subst subst_op.code)
    apply simp
    apply (smt (verit, ccfv_SIG) IO.distinct(5) IO.inject(2) IO.simps(4) cUN_I cimageI cin.rep_eq step.intros(4) step_choicesE)
    done
  done

inductive sub_choice for op where
  [intro]: "sub_choice op op"
| [intro]: "sub_choice op op' \<Longrightarrow> op' |\<in>| ops \<Longrightarrow> sub_choice op (Choice ops)"

lemma no_Choice_sub_choice:
  "sub_choice nc_op op \<Longrightarrow>
   step io nc_op op' \<Longrightarrow>
   no_Choice nc_op \<Longrightarrow>
   step io op op'"
  by (induct op pred: sub_choice) auto

lemma sub_choice_trans:
  "sub_choice op1 op2 \<Longrightarrow>
   sub_choice op2 op3 \<Longrightarrow>
   sub_choice op1 op3"
  apply (induct op2 arbitrary: op3 pred: sub_choice)
   apply auto[1]
  apply (smt (verit, del_insts) cin.rep_eq sub_choice.induct sub_choice.intros(2))
  done

lemma choices_sub_choices_elim[elim]:
  assumes  "op' |\<in>| choices op"
  obtains "no_Choice op'" "sub_choice op' op"
  using assms apply atomize_elim
  unfolding choices_def
  apply (clarsimp simp del: cin.rep_eq)
  subgoal premises prems for n
    using prems(2-) apply -
    apply (induct n arbitrary: op op')
    subgoal for op op'
      by (cases op; auto)
    subgoal for n op op'
      apply (cases op; auto simp del: cin.rep_eq; hypsubst_thin)
      done
    done
  done

lemma step_Write_sub_choice_intro[intro]:
  "step io op op' \<Longrightarrow> io = Out p x \<Longrightarrow> sub_choice (Write op' p x) op"
  by (induct io op op' pred: step) auto

lemma step_Read_sub_choice_intro[intro]:
  "step io op op' \<Longrightarrow> io = Inp p x \<Longrightarrow> \<exists> f. sub_choice (Read p f) op \<and> f x = op'"
  by (induct io op op' pred: step) force+

lemma step_Silent_sub_choice_intro[intro]:
  "step io op op' \<Longrightarrow> io = Tau \<Longrightarrow> sub_choice (Silent op') op"
  by (induct io op op' pred: step) auto

lemma step_subst_op_no_subst_intro[intro]:
  "step io op op' \<Longrightarrow>
   no_Choice op \<Longrightarrow>
   op \<noteq> x_op \<Longrightarrow>
   step io (subst_op x_op y_op op) (subst_op x_op y_op op')"
  apply (induct io op op' pred: step)
  subgoal
    apply (subst subst_op.code)
    apply simp
    apply blast
    done
  subgoal
    apply (subst subst_op.code)
    apply simp
    apply blast
    done
  subgoal
    apply (subst subst_op.code)
    apply simp
    apply blast
    done
  subgoal 
    by simp
  done

lemma step_subst_op_elim[elim]:
  assumes "step io (subst_op x_op y_op op) op'"
  obtains "step io y_op op'" "sub_choice x_op op" "no_Choice x_op"
  | op'' op''' where "step io op''' op''" "op' = subst_op x_op y_op op''" "sub_choice op''' op" "no_Choice op'''" "op''' \<noteq> x_op"
  using assms apply atomize_elim
  apply (subst (asm) subst_op.code)
  apply (erule step.cases; simp del: cin.rep_eq)
  subgoal for op'' ops io' op'
    apply (clarsimp del: disjCI simp add: cDiff_iff[simplified] simp del: cin.rep_eq split: if_splits; hypsubst_thin)
    subgoal
      by (metis choices_sub_choices_elim)
    subgoal for x
       apply (erule choices_sub_choices_elim)
      apply (cases x; force)
      done
    done
  done
    
lemma aux:
  "step (Out (Inl nid) (Inl (Inl st))) op op' \<Longrightarrow>
   x_op = Write op' (Inl nid) (Inl (Inl st)) \<Longrightarrow>
   y_op = Write op' (Inl nid) (Inl (Inl \<lparr> cons = [], inte = [], prod = [] \<rparr>)) \<Longrightarrow>
   dataflow_op sg op ~
   dataflow_op (sg\<lparr> lo_pt := lo_pt sg @ extract_progress nid (edges sg) st \<rparr>) (subst_op x_op y_op op)"
proof (coinduction arbitrary: sg op op' rule: bisim_coinduct)
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
       defer
      subgoal
        apply (rule step_Inp_dataflow_op_Inp_Inr_intro)
        apply (rule no_Choice_sub_choice)
        apply (rule step_Write_sub_choice_intro)

        find_theorems sub_choice step

          apply (rule step_subst_op_no_subst_intro)
        apply assumption

      apply hypsubst_thin
           apply blast
      apply hypsubst_thin

      find_theorems no_Choice step

end
       apply force
      apply (rule b_base)
           apply (intro exI conjI)
      apply (rule refl)

end
next
  case SIM2
  then show ?case sorry
qed


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
               apply (rule aux[where nid=0 and st="\<lparr>cons = [], inte = [], prod = [(1, i, 1)]\<rparr>", of _ _ "map_op (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (case_option (Inl 0) (\<lambda>p. Inr (0, 1))) (input_top (Cap (Suc i) 1) inps1')"])
                apply simp_all
                prefer 3
              apply (rule bisim_refl)
               apply auto


              find_theorems choices map_op


end

            find_theorems choices comp_op

end
            apply (coinduction rule: bisim_coinduct_upto'')
            subgoal for io op1'
              apply (elim step_max'_top_elim step_map_op_elim step_comp_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp split: if_splits; hypsubst_thin)
                         apply (cases xs'; auto simp add: writes_Cons_simp)[1]
                        apply (cases xs'; auto simp add: writes_Cons_simp)[1]
              subgoal for op'' io' op''a p x op1'
                apply (subst (asm) writes.code)
                apply (simp split: list.splits)
                 apply force
                apply auto
                apply hypsubst_thin
                apply (intro conjI exI)
                 apply (rule step_Tau_dataflow_op_Tau_intro)
                 apply (rule step_map_op)
                  apply (rule step_Tau_comp_op_L)
                     apply (simp add: writes_Cons_simp)
                     apply (rule SW)
                defer
                    apply (rule refl)+
                  apply simp_all
                apply (intro conjI bc_base)

                find_theorems comp_op step Tau
                

lemma choices_choices_simp[simp]:
  "choices (Choice (choices op)) = choices op"
  sorry

lemma bisim_Choice_choices:
  "op ~ Choice (choices op)"
  apply (rule choices_Choice_bisim)
  apply (simp only: choices_choices_simp)
  done



end
            sorry
          done
        done
      done(* 
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
                            subgoal *)





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