theory Operators_Utils

imports
  Nondeterministic_Dataflow.Operator
  DataplaneUtils
begin 

fun steps where
  "steps [] = (=)"
| "steps (io # ios) = step io OO steps ios"

lemma steps_append[simp]:
  "steps (xs @ ys) = steps xs OO steps ys"
  by (induct xs arbitrary: ys) auto

lemma step_refl[simp]:
  "step io OO (=) = step io"
  by auto

lemma steps_map_op[intro!]:
  "op'' = map_op f g op' \<Longrightarrow> 
   map (map_IO f g id) xs = xs' \<Longrightarrow>
   steps xs op op' \<Longrightarrow>
   steps xs' (map_op f g op) op''"
  by (induct xs' arbitrary: op op' op'' xs)
    (force simp add: relcompp_apply)+

lemma step_tau_pow_map_op[intro]:
  "(step Tau ^^ n) op op' \<Longrightarrow> (step Tau ^^ n) (map_op f g op) (map_op f g op')"
  apply (induct n arbitrary: op op')
   apply simp_all
  subgoal for n op op'
    apply (elim relcomppE)
    apply (intro relcomppI)
     apply blast
    apply auto
    done
  done

lemma steps_intro[intro]:
  "step x op op' \<Longrightarrow>
   steps xs op' op'' \<Longrightarrow>
   ys = x # xs \<Longrightarrow>
   steps ys op op''"
  apply auto
  done

lemma step_tau_Out_pow_comp_op_steps_intro[intro]:
  "steps (map (\<lambda> x. Out p x) xs) op1 op1' \<Longrightarrow>
   n = length xs \<Longrightarrow>
   wire p = Some q \<Longrightarrow>
   op = comp_op wire ((\<lambda> p'. (if q = p' then xs else [])) >> buf) op1' op2 \<Longrightarrow>
   (step Tau ^^ n) (comp_op wire buf op1 op2) op"
  apply hypsubst_thin
  apply (induct xs arbitrary: op1 op1' rule: rev_induct)
   apply simp_all
  subgoal for a as op1 op1'
    apply (elim relcomppE)
    subgoal premises prems for op 
      apply (intro relcomppI)
       apply (rule prems(1))
      using prems(3) apply assumption
      using prems(2,4) apply -
      apply (rule step_Tau_comp_op_L)
         apply simp_all
      apply (rule ext)
      apply (auto simp add: BENQ_def)
      done
    done
  done

lemma step_tau_Inp_pow_comp_op_steps_intro[intro]:
  "steps (map (\<lambda> x. Inp p x) xs) op2 op2' \<Longrightarrow>
   n = length xs \<Longrightarrow>
   p \<in> ran wire \<Longrightarrow>
   length (buf p) \<ge> n \<Longrightarrow>
   xs = take n (buf p) \<Longrightarrow>
   op = comp_op wire ((\<lambda> p'. (if p = p' then drop n (buf p) else buf p'))) op1 op2' \<Longrightarrow>
   (step Tau ^^ n) (comp_op wire buf op1 op2) op"
  apply hypsubst_thin
  apply (induct xs arbitrary: op2 op2' rule: rev_induct)
   apply simp_all
  subgoal for op2
    apply (rule arg_cong4[where f=comp_op])
       apply auto
    done
  subgoal for x xs op2 op2'
    apply (elim relcomppE)
    subgoal premises prems for op 
      apply (intro relcomppI)
       apply (rule prems(1))
      using prems(5) apply assumption
      using prems(2,3,4,6-) apply -
       apply (metis Suc_to_right butlast_snoc take_minus_one_conv_butlast)
      apply (rule step_Tau_comp_op_R)
           apply assumption+
         apply (simp_all add: BTL_def BHD_def hd_drop_conv_nth take_Suc_conv_app_nth)
      apply (rule ext)+
      apply clarsimp
      apply (metis drop_Suc drop_tl)
      done
    done
  done


lemma step_taus_L_pow_comp_op_steps_intro[intro]:
  "(step Tau ^^ n) op1 op1' \<Longrightarrow>
   op = (comp_op wire buf op1' op2) \<Longrightarrow>
   (step Tau ^^ n) (comp_op wire buf op1 op2) op"
  apply hypsubst_thin
  apply (induct n arbitrary: op1 op1')
   apply simp_all
  apply force
  done

lemma step_taus_R_pow_comp_op_steps_intro[intro]:
  "(step Tau ^^ n) op2 op2' \<Longrightarrow>
   op = (comp_op wire buf op1 op2') \<Longrightarrow>
   (step Tau ^^ n) (comp_op wire buf op1 op2) op"
  apply hypsubst_thin
  apply (induct n arbitrary: op2 op2')
   apply simp_all
  apply force
  done

lemma step_taus_loop_op_steps_intro[intro]:
  "(step Tau ^^ n) op op' \<Longrightarrow>
   op'' = loop_op wire buf op' \<Longrightarrow>
   (step Tau ^^ n) (loop_op wire buf op) op''"
  apply hypsubst_thin
  apply (induct n arbitrary: op op')
   apply simp_all
  apply force
  done

lemma steps_Out_loop_op_intro[intro!]:
  "steps (map (\<lambda> x. Out p x) xs) op op' \<Longrightarrow>
   wire p = None \<Longrightarrow>
   buf = buf' \<Longrightarrow>
   ys = map (\<lambda> x. Out p x) xs \<Longrightarrow>
   steps ys (loop_op wire buf op) (loop_op wire buf' op')"
  apply hypsubst_thin
  apply (induct xs arbitrary: op op' rule: rev_induct)
   apply force+
  done

lemma steps_Inp_loop_op_intro[intro!]:
  "steps (map (\<lambda> x. Inp p x) xs) op op' \<Longrightarrow>
   p \<notin> ran wire \<Longrightarrow>
   buf = buf' \<Longrightarrow>
   ys = map (\<lambda> x. Inp p x) xs \<Longrightarrow>
   steps ys (loop_op wire buf op) (loop_op wire buf' op')"
  apply hypsubst_thin
  apply (induct xs arbitrary: op op' rule: rev_induct)
   apply force+
  done

lemma step_tau_Out_pow_loop_op_steps_intro[intro]:
  "steps (map (\<lambda> x. Out p x) xs) op op' \<Longrightarrow>
   n = length xs \<Longrightarrow>
   wire p = Some q \<Longrightarrow>
   op'' = loop_op wire ((\<lambda> p'. (if q = p' then xs else [])) >> buf) op' \<Longrightarrow>
   (step Tau ^^ n) (loop_op wire buf op) op''"
  apply hypsubst_thin
  apply (induct xs arbitrary: op op' rule: rev_induct)
   apply simp_all
  subgoal for a as op op'
    apply (elim relcomppE)
    subgoal premises prems for op0
      apply (intro relcomppI)
       apply (rule prems(1))
      using prems(3) apply assumption
      using prems(2,4) apply -
      apply (rule step_Out_Tau_loop_op)
        apply simp_all
      apply (rule ext)
      apply (auto simp add: BENQ_def)
      done
    done
  done

lemma step_tau_Inp_pow_loop_op_steps_intro[intro]:
  "steps (map (\<lambda> x. Inp p x) xs) op op' \<Longrightarrow>
   n = length xs \<Longrightarrow>
   p \<in> ran wire \<Longrightarrow>
   length (buf p) \<ge> n \<Longrightarrow>
   xs = take n (buf p) \<Longrightarrow>
   op'' = loop_op wire ((\<lambda> p'. (if p = p' then drop n (buf p) else buf p'))) op' \<Longrightarrow>
   (step Tau ^^ n) (loop_op wire buf op) op''"
  apply hypsubst_thin
  apply (induct xs arbitrary: op op' rule: rev_induct)
   apply simp_all
  subgoal for op
    apply (rule arg_cong[where f="\<lambda>b. loop_op wire b op"])
    apply (rule ext)
    apply auto
    done
  subgoal for x xs op op'
    apply (elim relcomppE)
    subgoal premises prems for op0
      apply (intro relcomppI)
       apply (rule prems(1))
      using prems(5) apply assumption
      using prems(2,3,4,6-) apply -
       apply (metis Suc_to_right butlast_snoc take_minus_one_conv_butlast)
      apply (rule step_Inp_Tau_loop_op)
          apply assumption+
        apply (simp_all add: BTL_def BHD_def hd_drop_conv_nth take_Suc_conv_app_nth)
      apply (rule ext)
      apply clarsimp
      apply (metis drop_Suc drop_tl)
      done
    done
  done

section \<open>Weak Step and Weak Trace Laws\<close>

text \<open>Generic laws for weak steps, weak traces, and finished
  computations of arbitrary operators.\<close>

lemma wsteps_step_tau[intro]:
  "wsteps vios op2 op3 \<Longrightarrow>
   step Tau op1 op2 \<Longrightarrow>
   wsteps vios op1 op3"
  by (induct vios arbitrary: op2 op3 op1 rule: wsteps.induct) auto

lemma wfinished_step_taus[intro]:
  "wfinished op \<Longrightarrow>
   (step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow>
   wfinished op'"
  unfolding wfinished_no_wstep
  apply (clarsimp del: disjCI simp flip: cin.rep_eq ; hypsubst_thin?)
  subgoal for vio opp
    unfolding not_def
    apply (drule spec[of _ vio])
    apply (drule spec[of _ opp])
    apply (drule mp)
     apply (metis (lifting) estep.elims io_of_vio_not_Tau(1) wstep_trans'(1,2))
    apply auto
    done
  done

lemma wsteps_append[simp]:
  "wsteps (xs @ ys) = (wsteps xs OO wsteps ys)"
  apply (rule ext)+
  apply (induct xs arbitrary: ys)
  subgoal for xs
    apply clarsimp    
    apply (smt (verit, ccfv_threshold) eq_OO estep.simps(1) relcomppI relcompp_assoc relcompp_distrib2 rtranclp_reflclp_absorb sup.idem sup_left_commute wstep_def wstep_steps_Tau wsteps.elims)
    done
  subgoal for a xs x xs'
    apply auto
     apply blast+
    done
  done


lemma step_taus_wtraced:
  "(step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow>
   \<not> wfinished op' \<Longrightarrow>
   wtraced op' ios \<Longrightarrow>
   wtraced op ios"
  apply (smt (verit, ccfv_threshold) append.right_neutral relcomppI relcompp_assoc wstep_def wsteps.simps(1) wsteps_append wtraced.simps)
  done

lemma wsteps_not_finished_wtraced:
  "wsteps vios op op' \<Longrightarrow>
   \<not> wfinished op' \<Longrightarrow>
   wtraced op' ios \<Longrightarrow>
   wtraced op (vios @@- ios)"
  apply (induct vios arbitrary: op op' ios rule: rev_induct)
   apply simp_all
  subgoal 
    using step_taus_wtraced by blast
  subgoal for x xs op op' ios
    apply clarsimp
    apply (metis step_taus_wtraced wfinished_no_wstep wtraced.intros(2))
    done
  done

lemma wsteps_wtraced:
  "wsteps vios op op' \<Longrightarrow>
   vios \<noteq> [] \<Longrightarrow>
   wtraced op' ios \<Longrightarrow>
   wtraced op (vios @@- ios)"
  apply (induct vios arbitrary: op op' ios rule: rev_induct)
   apply simp_all
  subgoal for x xs op op' ios
    apply clarsimp
    apply (smt (verit, ccfv_threshold) estep.cases io_of_vio_not_Tau(1) lshift_simps(1) wstep_converse_trans'(1,2) wstep_trans'(1,2) wsteps.simps(1) wtraced.intros(2)) 
    done
  done

lemma wtraced_not_LNil_not_wfinished:
  "wtraced op ios \<Longrightarrow> ios \<noteq> LNil \<Longrightarrow> \<not> wfinished op"
  apply (erule wtraced.cases)
   apply simp_all
  using wfinished_no_wstep apply blast
  done

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







lemma wbisim_absorb_bisim_l:
  "(X O p2rel (~)) O p2rel (\<approx>) \<subseteq> X O p2rel (\<approx>)"
  by (smt (verit) bisim_wbisim in_p2_rel_simp relcomp.simps relcompE subset_iff wbisim_trans)



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





lemma weakBisimWeakUpto_rSim:
  "(P', Q') \<in> p2rel (\<approx>) O X O p2rel (~) \<Longrightarrow>
   Q' \<leadsto>\<^sup>^<p2rel (\<approx>)> Q \<Longrightarrow>
   (\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<(p2rel (\<approx>) O X O p2rel (~))> Q) \<Longrightarrow>
   P' \<leadsto>\<^sup>^<(p2rel (\<approx>) O X O p2rel (\<approx>))> Q"
  apply (subgoal_tac "(p2rel (\<approx>) O X O p2rel (~)) O p2rel (\<approx>) \<subseteq> p2rel (\<approx>) O X O p2rel (\<approx>)")
  apply (smt (verit, ccfv_threshold) in_p2_rel_simp relcomp.cases wsimTransitive wsim_set_wbisim_bisim_r_l)
  using wbisim_absorb_bisim_l apply fastforce
  done


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


lemma weakBisimWeakUptoBisim[case_names SIM1 SIM2, consumes 1]:
  assumes p: "R op1 op2"
    and rSim: "\<And>op1 op2. R op1 op2 \<Longrightarrow> wsim ((~) OO R OO (\<approx>)) op1 op2"
    and rSym: "\<And>op1 op2. R op1 op2 \<Longrightarrow> wsim ((~) OO R\<inverse>\<inverse> OO (\<approx>)) op2 op1"
  shows "op1 \<approx> op2"
  apply (rule weakBisimWeakUpto[where X="p2rel R"])
  using assms(1) apply fastforce
  apply (simp_all add: wsim_set_wsim flip: p2rel_relcompp)
  apply (simp_all add: converse_relcompp relcompp_assoc)
  apply (rule rSym) 
  apply assumption
  apply (rule rSim) 
  apply assumption
  done

lemma weakBisimWeakUptoBisim_alt[case_names SIM1 SIM2, consumes 1]:
  assumes p: "R op1 op2"
    and Sim: "\<And>op1 op2. R op1 op2 \<Longrightarrow> wsim ((~) OO R OO (\<approx>)) op1 op2 \<and> wsim ((~) OO R\<inverse>\<inverse> OO (\<approx>)) op2 op1"
  shows "op1 \<approx> op2"
  using assms weakBisimWeakUptoBisim by metis

inductive wbisim_upto_bisim_cong ("\<U>") for R  where
  wb_upto_b_base[intro]:  "R op1 op2 \<Longrightarrow> \<U> R op1 op2"
| wb_upto_b_sym[intro]:  "\<U> R op2 op1 \<Longrightarrow> \<U> R op1 op2"
| wb_upto_b_Write[intro]: "\<U> R op1 op2 \<Longrightarrow> \<U> R (Write op1 p x) (Write op2 p x)"
| wb_upto_b_Sim:"sim (\<U> R) op1 op2 \<Longrightarrow> sim (\<U> R) op2 op1 \<Longrightarrow> \<U> R op1 op2"
  (* | wb_upto_b_writes[intro]: "\<U> R op1 op2 \<Longrightarrow> \<U> R (writes op1 p x) (writes op2 p x)"
| wb_upto_b_Silent[intro]: "\<U> R op1 op2 \<Longrightarrow> \<U> R (Silent op1) (Silent op2)" *)

  (* | wbc_bisim:  "wbisim x y \<Longrightarrow> wbisim_cong R x y"
| wbc_refl[intro]: "x = y \<Longrightarrow> wbisim_cong R x y"
| wbc_sym[intro]: "wbisim_cong R x y \<Longrightarrow> wbisim_cong R y x"
| wbc_Read:"x1 = y1 \<Longrightarrow> rel_fun (=) (wbisim_cong R) x2 y2 \<Longrightarrow> wbisim_cong R (Read x1 x2) (Read y1 y2)"
| wbc_Write: "wbisim_cong R x1 y1 \<Longrightarrow> wbisim_cong R (Write x1 x2 x3) (Write y1 x2 x3)"
| wbc_Silent: "wbisim_cong R x1 y1 \<Longrightarrow> wbisim_cong R (Silent x1) (Silent y1)"
lemma lambda_disj_conversep[simp]:
  "(\<lambda>a b. R a b \<or> a \<approx> b)\<inverse>\<inverse> = (\<lambda>a b. R b a \<or> a \<approx> b)" *)


lemma weakBisimWeakUptoBisimCong[case_names SIM1 SIM2, consumes 1]:
  assumes p: "R op1 op2"
    and rSim: "\<And>op1 op2. R op1 op2 \<Longrightarrow> wsim (((~) OO \<U> R OO (\<approx>))) op1 op2"
    and rSym: "\<And>op1 op2. R op1 op2 \<Longrightarrow> wsim (((~) OO \<U> R OO (\<approx>))) op2 op1"
  shows "op1 \<approx> op2"
  using assms apply -
  apply (rule weakBisimWeakUptoBisim_alt[where R="\<U> R", of op1 op2])
  subgoal
    apply (rule wb_upto_b_base)
    apply auto
    done
  subgoal premises prems for s' t'
    using prems(4-) apply -
    apply (induct s' t' pred: wbisim_upto_bisim_cong)
    subgoal for x y
      apply (intro conjI)
      using prems(2) apply blast
      using prems(3) apply (metis (no_types, opaque_lifting) conversep_iff order_antisym_conv predicate2I_obj wbisim_upto_bisim_cong.intros(2))
      done
    subgoal for x y
      apply (intro conjI)
      apply (metis conversepD conversep_le_swap order_antisym_conv predicate2I_obj wbisim_upto_bisim_cong.intros(2))+
      done
    subgoal for op1 op2 p x
      apply (intro conjI)
      apply (metis (no_types, opaque_lifting) OO_def bisim_refl step.intros(2) step_wstep wbisim_refl wsim_Write)
      apply clarsimp
      using prems(2,3)
      apply (metis (no_types, lifting) SW bisim_refl relcompp_apply step_wstep wbisim_refl)
      done
    subgoal for op1s op2s
      apply (intro conjI)
      subgoal
        unfolding wsim_def sim_def
        apply (auto simp del: cin.rep_eq)
        apply (metis bisim_refl relcompp_apply step_wstep wbisim_refl_alt)
        done
      subgoal
        unfolding wsim_def sim_def
        apply (auto simp del: cin.rep_eq)
        apply (metis bisim_refl conversep_iff relcompp_apply step_wstep wbisim_refl wbisim_upto_bisim_cong.intros(2))
        done
      done
    done
  done

lemma SR'[intro]:
  "y = (f xa) \<Longrightarrow>
   step (Inp p xa) (Read p f) y"
  by auto

lemma steps_comp_op_R_Out[intro!]:
  "steps (map (Out p) xs) op2 op2' \<Longrightarrow> buf = buf' \<Longrightarrow> op1 = op1' \<Longrightarrow> ys = map (Out (Inr p)) xs \<Longrightarrow> steps ys (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  apply hypsubst_thin
  apply (induct xs arbitrary: op2 op2'  rule: rev_induct)
   apply force+
  done

lemma steps_comp_op_L_Out:
  "steps (map (Out p) xs) op1 op1' \<Longrightarrow>
   p \<notin> dom wire \<Longrightarrow>
   buf = buf' \<Longrightarrow>
   op2 = op2' \<Longrightarrow>
   ys = map (Out (Inl p)) xs \<Longrightarrow>
   steps ys (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  apply hypsubst_thin
  apply (induct xs arbitrary: op1 op1' rule: rev_induct)
   apply force+
  done

lemma steps_comp_op_L_Inp:
  "steps (map (Inp p) xs) op1 op1' \<Longrightarrow>
   buf = buf' \<Longrightarrow>
   op2 = op2' \<Longrightarrow>
   ys = map (Inp (Inl p)) xs \<Longrightarrow>
   steps ys (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  apply hypsubst_thin
  apply (induct xs arbitrary: op1 op1' rule: rev_induct)
   apply force+
  done



section \<open>Buffer congruence for composition and loop operators\<close>

lemma comp_op_not_Silent[simp]:
  \<open>\<not> is_Silent (comp_op wire buf op1 op2)\<close>
  by (subst comp_op_code) simp

(* Note: this is basically lemma comp_op_chns_invar from dataplane_dis:dataplane/Comp_Reasoning.thy *)
lemma comp_op_buf_cong:
  assumes \<open>wire' = wire\<close> \<open>op1' = op1\<close> \<open>op2' = op2\<close> \<open>\<forall>p \<in> inputs op2 \<inter> ran wire. buf' p = buf p\<close>
  shows \<open>(comp_op wire buf op1 op2 :: ('i1 + 'i2, 'o1 + 'o2, 'd) op) = comp_op wire' buf' op1' op2'\<close>
  unfolding assms(1-3) using assms(4)
proof (coinduction arbitrary: buf buf' op1 op2 rule: op.coinduct_upto)
  case Eq_op
  define R where \<open>R = (\<lambda>op op'. \<exists>buf buf' op1 op2.
  (op :: ('i1 + 'i2, 'o1 + 'o2, 'd) op) = comp_op wire buf op1 op2 \<and> op' = comp_op wire buf' op1 op2
  \<and> (\<forall>p \<in> inputs op2 \<inter> ran wire. buf' p = buf p))\<close>
  let ?comp_op_1 = \<open>\<lambda>buf op. case op of
  Read p f \<Rightarrow> Read (Inl p) (\<lambda>x. comp_op wire buf (f x) op2)
| Write op p x \<Rightarrow> (case wire p of
    None \<Rightarrow> Write (comp_op wire buf op op2) (Inl p) x
  | Some q \<Rightarrow> Silent (comp_op wire (BENQ q x buf) op op2))
| Silent op \<Rightarrow> Silent (comp_op wire buf op op2)\<close>
  { fix p f
    assume \<open>Read p f |\<in>| choices op1\<close>
    hence \<open>rel_fun (=) (op.congclp R) (\<lambda>x. comp_op wire buf (f x) op2) (\<lambda>x. comp_op wire buf' (f x) op2)\<close>
      using Eq_op Read_choices_inputs by (fastforce simp add: rel_fun_def R_def intro: op.cong_base)
  }
  moreover {
    fix op p x
    assume \<open>Write op p x |\<in>| choices op1\<close> \<open>wire p = None\<close>
    hence \<open>op.congclp R (comp_op wire buf op op2) (comp_op wire buf' op op2)\<close>
      using Eq_op unfolding R_def by (blast intro: op.cong_base)
  }
  moreover {
    fix op p x q
    assume \<open>Write op p x |\<in>| choices op1\<close> \<open>wire p = Some q\<close>
    have \<open>op.congclp R (comp_op wire (BENQ q x buf) op op2) (comp_op wire (BENQ q x buf') op op2)\<close>
      using Eq_op unfolding R_def BENQ_def by (fastforce intro: op.cong_base)
  }
  moreover {
    fix op
    assume \<open>Silent op |\<in>| choices op1\<close>
    hence \<open>op.congclp R (comp_op wire buf op op2) (comp_op wire buf' op op2)\<close>
      using Eq_op unfolding R_def by (blast intro: op.cong_base)
  }
  ultimately have \<open>\<forall>op. op |\<in>| choices op1 \<longrightarrow> op.congclp R (?comp_op_1 buf op) (?comp_op_1 buf' op)\<close>
    by (auto split: op.splits option.splits dest: no_Choice_in_choices[simplified]
        intro!: op.cong_Read op.cong_Write op.cong_Silent)
  hence rel_fun_choices_op1: \<open>rel_fun (eq_onp (\<lambda>op. op |\<in>| choices op1)) (op.congclp R)
  (?comp_op_1 buf) (?comp_op_1 buf')\<close> unfolding rel_fun_def eq_onp_def by blast
  have rel_set_choices_op1: \<open>rel_set (eq_onp (\<lambda>op. op |\<in>| choices op1))
  (rcset (choices op1)) (rcset (choices op1))\<close> unfolding rel_set_def eq_onp_def by fastforce
  let ?comp_op_2 = \<open>\<lambda>buf op. case op of
  Read p f \<Rightarrow> if p \<in> ran wire
    then Silent (comp_op wire (BTL p buf) op1 (f (BHD p buf)))
    else Read (Inr p) (\<lambda>x. comp_op wire buf op1 (f x))
| Write op p x \<Rightarrow> Write (comp_op wire buf op1 op) (Inr p) x
| Silent op \<Rightarrow> Silent (comp_op wire buf op1 op)\<close>
  { fix p f
    assume p_f: \<open>Read p f |\<in>| choices op2\<close> \<open>p \<in> ran wire\<close> \<open>buf p \<noteq> []\<close>
    let ?x = \<open>BHD p buf\<close>
    let ?y = \<open>BHD p buf'\<close>
    have \<open>inputs (f ?x) \<subseteq> inputs op2\<close> using p_f(1) inputs_after_choices[OF p_f(1)] op.set(1) by auto
    hence \<open>\<forall>p' \<in> inputs (f ?x) \<inter> ran wire. (BTL p buf') p' = (BTL p buf) p'\<close>
      using Eq_op unfolding BTL_def by auto
    moreover have \<open>?x = ?y\<close> using Eq_op p_f Read_choices_inputs unfolding BHD_def by fastforce
    ultimately have \<open>op.congclp R (comp_op wire (BTL p buf) op1 (f ?x))
  (comp_op wire (BTL p buf') op1 (f ?y))\<close> unfolding R_def by (force intro: op.cong_base) 
  }
  moreover {
    fix p f
    assume p_f: \<open>Read p f |\<in>| choices op2\<close> \<open>p \<notin> ran wire\<close>
    have \<open>\<forall>x. inputs (f x) \<subseteq> inputs op2\<close>
      using p_f(1) inputs_after_choices[OF p_f(1)] op.set(1) by auto
    hence \<open>rel_fun (=) (op.congclp R) (\<lambda>x. comp_op wire buf op1 (f x)) (\<lambda>x. comp_op wire buf' op1 (f x))\<close>
      using Eq_op unfolding rel_fun_def R_def by (fastforce intro: op.cong_base)
  }
  moreover {
    fix op p x
    assume op_p: \<open>Write op p x |\<in>| choices op2\<close>
    have \<open>op.congclp R (comp_op wire buf op1 op) (comp_op wire buf' op1 op)\<close>
      using Eq_op inputs_after_choices[OF op_p] op.set(2) unfolding R_def
      by (force intro: op.cong_base)
  }
  moreover {
    fix op
    assume op: \<open>Silent op |\<in>| choices op2\<close>
    have \<open>op.congclp R (comp_op wire buf op1 op) (comp_op wire buf' op1 op)\<close>
      using Eq_op inputs_after_choices[OF op] op.set(4) unfolding R_def
      by (force intro: op.cong_base)
  }
  ultimately have \<open>\<forall>op. op |\<in>| sound_reads wire buf (choices op2) \<longrightarrow>
  op.congclp R (?comp_op_2 buf op) (?comp_op_2 buf' op)\<close>
    by (auto split: op.splits option.splits dest: no_Choice_in_choices[simplified]
        intro!: op.cong_Read op.cong_Write op.cong_Silent)
  hence rel_fun_choices_op2: \<open>rel_fun (eq_onp (\<lambda>op. op |\<in>| sound_reads wire buf (choices op2))) (op.congclp R)
  (?comp_op_2 buf) (?comp_op_2 buf')\<close> unfolding rel_fun_def eq_onp_def by blast
  have rel_set_choices_op2: \<open>rel_set (eq_onp (\<lambda>op. op |\<in>| sound_reads wire buf (choices op2)))
  {op. op |\<in>| choices op2 \<and> (case op of Read p f \<Rightarrow> p \<in> ran wire \<longrightarrow> buf p \<noteq> [] | _ \<Rightarrow> True)}
  {op. op |\<in>| choices op2 \<and> (case op of Read p f \<Rightarrow> p \<in> ran wire \<longrightarrow> buf' p \<noteq> [] | _ \<Rightarrow> True)}\<close>
    using Eq_op Read_choices_inputs by (fastforce simp add: rel_set_def eq_onp_def split: op.splits)
  have \<open>rel_set (op.congclp R)
  (rcset (un_Choice (comp_op wire buf op1 op2))) (rcset (un_Choice (comp_op wire buf' op1 op2)))\<close>
    using union_transfer[THEN rel_funD, THEN rel_funD,
        OF image_transfer[THEN rel_funD, THEN rel_funD, OF rel_fun_choices_op1 rel_set_choices_op1]
           image_transfer[THEN rel_funD, THEN rel_funD, OF rel_fun_choices_op2 rel_set_choices_op2]]
    by (subst (1 2) comp_op_code) simp
  thus ?case unfolding R_def by simp
qed

lemma un_Choice_loop_op_buf_cong:
  fixes wire
  defines \<open>R \<equiv> (\<lambda>op1 op2. \<exists>buf buf' op. op1 = loop_op wire buf op \<and> op2 = loop_op wire buf' op
  \<and> (\<forall>p. p \<in> inputs (op :: ('i, 'o, 'd) op) \<and> p \<in> ran wire \<longrightarrow> buf' p = buf p))\<close>
  assumes bufs_eq: \<open>\<forall>p \<in> inputs (op :: ('i, 'o, 'd) op) \<inter> ran wire. buf' p = buf p\<close>
    and op': \<open>op' |\<in>| un_Choice (loop_op wire buf op)\<close>
  obtains op'' where \<open>op'' |\<in>| un_Choice (loop_op wire buf' op)\<close> \<open>op.congclp R op' op''\<close>
proof atomize_elim
  consider (read_outside) p f where \<open>op' = Read p (\<lambda>x. loop_op wire buf (f x))\<close>
    \<open>Read p f |\<in>| choices op\<close> \<open>p \<notin> ran wire\<close>
  | (read_inside) p f where \<open>op' = Silent (loop_op wire (BTL p buf) (f (BHD p buf)))\<close>
    \<open>Read p f |\<in>| choices op\<close> \<open>p \<in> ran wire\<close> \<open>buf p \<noteq> []\<close>
  | (write_outside) op'' p x where \<open>op' = Write (loop_op wire buf op'') p x\<close>
    \<open>Write op'' p x |\<in>| choices op\<close> \<open>wire p = None\<close>
  | (write_inside) op'' p x q where \<open>op' = Silent (loop_op wire (BENQ q x buf) op'')\<close>
    \<open>Write op'' p x |\<in>| choices op\<close> \<open>wire p = Some q\<close>
  | (silent) op'' where \<open>op' = Silent (loop_op wire buf op'')\<close>
    \<open>Silent op'' |\<in>| choices op\<close>
    using op' by (subst (asm) (6) loop_op.code)
      (auto split: op.splits option.splits if_splits dest: no_Choice_in_choices[simplified])
  thus \<open>\<exists>op''. op'' |\<in>| un_Choice (loop_op wire buf' op) \<and> op.congclp R op' op''\<close>
  proof cases
    case read_outside
    let ?op'' = \<open>Read p (\<lambda>x. loop_op wire buf' (f x))\<close>
    have \<open>R (loop_op wire buf (f x)) (loop_op wire buf' (f x))\<close> for x unfolding R_def
      using bufs_eq read_outside inputs_after_choices inputs_sub_op_Read mem_simps(4)
        sub_op.intros(2) sub_op_Read_inputs by metis
    hence \<open>op.congclp R op' ?op''\<close>
      using op.cong_base op.cong_Read[OF refl] unfolding rel_fun_def read_outside(1) by metis
    moreover have \<open>?op'' |\<in>| un_Choice (loop_op wire buf' op)\<close>
      using read_outside(2-) by (subst (2) loop_op.code) force
    ultimately show ?thesis by blast
  next
    case read_inside
    let ?x = \<open>BHD p buf\<close>
    let ?y = \<open>BHD p buf'\<close>
    let ?op'' = \<open>Silent (loop_op wire (BTL p buf') (f ?y))\<close>
    have \<open>?x = ?y\<close>
      using bufs_eq read_inside(2,3) Read_choices_inputs mem_simps(4) BHD_def by metis
    moreover have \<open>\<forall>p' \<in> inputs (f ?x) \<inter> ran wire. BTL p buf' p' = BTL p buf p'\<close>
      using bufs_eq read_inside(2) inputs_after_choices inputs_sub_op_Read mem_simps(4)
        sub_op.intros(2) sub_op_Read_inputs BTL_access BTL_diff_access by metis
    ultimately have \<open>R (loop_op wire (BTL p buf) (f ?x)) (loop_op wire (BTL p buf') (f ?y))\<close>
      unfolding R_def by auto
    hence \<open>op.congclp R op' ?op''\<close> using op.cong_Silent[OF op.cong_base]
      unfolding read_inside(1) by metis
    moreover have \<open>?op'' |\<in>| un_Choice (loop_op wire buf' op)\<close>
      using read_inside(2-) bufs_eq Read_choices_inputs by (subst (2) loop_op.code) force
    ultimately show ?thesis by blast
  next
    case write_outside
    let ?op'' = \<open>Write (loop_op wire buf' op'') p x\<close>
    have \<open>R (loop_op wire buf op'') (loop_op wire buf' op'')\<close> unfolding R_def
      using bufs_eq write_outside(2) inputs_after_choices mem_simps(4) op.set(2) by metis
    hence \<open>op.congclp R op' ?op''\<close> using op.cong_Write[OF op.cong_base refl refl]
      unfolding write_outside(1) by metis
    moreover have \<open>?op'' |\<in>| un_Choice (loop_op wire buf' op)\<close>
      using write_outside(2-) by (subst (2) loop_op.code) force
    ultimately show ?thesis by blast
  next
    case write_inside
    let ?op'' = \<open>Silent (loop_op wire (BENQ q x buf') op'')\<close>
    have \<open>R (loop_op wire (BENQ q x buf) op'') (loop_op wire (BENQ q x buf') op'')\<close>
      using bufs_eq write_inside(2) inputs_after_choices mem_simps(4) op.set(2)
      unfolding R_def BENQ_def by force
    hence \<open>op.congclp R op' ?op''\<close> using op.cong_Silent[OF op.cong_base]
      unfolding write_inside(1) by metis
    moreover have \<open>?op'' |\<in>| un_Choice (loop_op wire buf' op)\<close>
      using write_inside(2-) by (subst (2) loop_op.code) force
    ultimately show ?thesis by blast
  next
    case silent
    let ?op'' = \<open>Silent (loop_op wire buf' op'')\<close>
    have \<open>R (loop_op wire buf op'') (loop_op wire buf' op'')\<close>
      using bufs_eq silent inputs_after_choices mem_simps(4) op.set(4) unfolding R_def by metis
    hence \<open>op.congclp R op' ?op''\<close> using op.cong_Silent[OF op.cong_base]
      unfolding silent(1) by metis
    moreover have \<open>?op'' |\<in>| un_Choice (loop_op wire buf' op)\<close>
      using silent(2-) by (subst (2) loop_op.code) force
    ultimately show ?thesis by blast
  qed
qed

lemma loop_op_buf_cong:
  assumes \<open>wire' = wire\<close> \<open>(op' :: ('i, 'o, 'd) op) = op\<close> \<open>\<forall>p \<in> inputs op \<inter> ran wire. buf' p = buf p\<close>
  shows \<open>loop_op wire buf op = loop_op wire' buf' op'\<close>
  unfolding assms(1,2) using assms(3)
proof (coinduction arbitrary: buf buf' op rule: op.coinduct_upto)
  case (Eq_op buf buf' op)
  define R :: \<open>('i, 'o, 'd) op \<Rightarrow> ('i, 'o, 'd) op \<Rightarrow> bool\<close> where
    \<open>R = (\<lambda>op1 op2. \<exists>buf buf' op. op1 = loop_op wire buf op \<and> op2 = loop_op wire buf' op
  \<and> (\<forall>p. p \<in> inputs op \<and> p \<in> ran wire \<longrightarrow> buf' p = buf p))\<close>
  have \<open>\<forall>op'. op' |\<in>| un_Choice (loop_op wire buf op) \<longrightarrow> (\<exists>op''.
  op'' |\<in>| un_Choice (loop_op wire buf' op) \<and> op.congclp R op' op'')\<close>
    using un_Choice_loop_op_buf_cong[where op=op] Eq_op unfolding R_def by (metis (lifting))
  moreover have \<open>\<forall>op'. op' |\<in>| un_Choice (loop_op wire buf' op) \<longrightarrow> (\<exists>op''.
  op'' |\<in>| un_Choice (loop_op wire buf op) \<and> op.congclp R op'' op')\<close>
  proof (intro allI impI)
    fix op'
    assume op': \<open>op' |\<in>| un_Choice (loop_op wire buf' op)\<close>
    obtain op'' where op'': \<open>op'' |\<in>| un_Choice (loop_op wire buf op)\<close> \<open>op.congclp R op' op''\<close>
      using un_Choice_loop_op_buf_cong[OF _ op', where buf'=buf] Eq_op unfolding R_def by auto
    moreover have \<open>op.congclp R op'' op'\<close> by (rule op.cong_sym[OF op''(2)])
    ultimately show \<open>\<exists>op''. op'' |\<in>| un_Choice (loop_op wire buf op) \<and> op.congclp R op'' op'\<close>
      by blast
  qed
  ultimately show ?case by (force simp add: rel_set_def R_def Ball_def)
qed

lemma step_Tau_pow_eqI:
  "op = op' \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* op op'"
  by auto
end
