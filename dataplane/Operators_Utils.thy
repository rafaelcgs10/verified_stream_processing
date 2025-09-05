theory Operators_Utils

imports
  Nondeterministic_Dataflow.Operator
  DataplaneUtils
begin 

corec writes where
  "writes op p xs =
    (case xs of [] \<Rightarrow> case_op Read Write Choice Silent op | x #xs \<Rightarrow> Write (writes op p xs) p x)"

lemma foo[friend_of_corec_simps]:
  "(if snd (snd x) = [] then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x)))) else ctor_op (Abs_op_pre_op (Inl (Inr (algrho (fst x, fst (snd x), btl (snd (snd x))), fst (snd x), bhd (snd (snd x))))))) =
         (if snd (snd x) = []
         then if isl (Rep_op_pre_op (dtor_op (fst x))) \<and> isl (projl (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
              else if isl (Rep_op_pre_op (dtor_op (fst x))) \<and> \<not> isl (projl (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
                   else if \<not> isl (Rep_op_pre_op (dtor_op (fst x))) \<and> isl (projr (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
                        else ctor_op
                              (Abs_op_pre_op
                                (Inr (Inr (if isl (Rep_op_pre_op (dtor_op (fst x))) then undefined
                                           else if isl (projr (Rep_op_pre_op (dtor_op (fst x)))) then undefined else projr (projr (Rep_op_pre_op (dtor_op (fst x))))))))
         else ctor_op (Abs_op_pre_op (Inl (Inr (algrho (fst x, fst (snd x), btl (snd (snd x))), fst (snd x), bhd (snd (snd x)))))))"
  by (auto split: if_splits)

friend_of_corec writes where
  "writes op p xs =
    (case xs of [] \<Rightarrow> case_op Read Write Choice Silent op | x #xs \<Rightarrow> Write (writes op p xs) p x)"
  apply (rule writes.code)
  apply transfer_prover
  done

lemma step_Out_writes:
  "step io (writes op p buf) op' \<Longrightarrow>
   buf \<noteq> [] \<Longrightarrow>
   op' = writes op p (tl buf) \<and> io = Out p (hd buf)"
  apply (subst (asm) writes.code)
  apply (auto split: op.splits list.splits)
  done

lemma step_writes_reads_buf_empty:
  "step io (writes op p buf) op' \<Longrightarrow> io = Inp p' x \<Longrightarrow> buf = []"
  apply (subst (asm) writes.code)
  apply (auto split: op.splits list.splits)
  done

lemma step_writes_silent_buf_empty:
  "step io (writes op p buf) op' \<Longrightarrow> io = Tau \<Longrightarrow> buf = []"
  apply (subst (asm) writes.code)
  apply (auto split: op.splits list.splits)
  done

lemma step_writes_elim:
  assumes "step io (writes op p xs) op'"
  obtains x xs' where "io = Out p x" "xs = x # xs'" "op' = writes op p xs'"
  | "xs = []" "step io op op'"
  using assms apply atomize_elim
  apply (subst (asm) writes.code)
  apply (auto split: op.splits list.splits)
  done


lemma step_writes_Out_intro[intro]:
  "buf = x # buf' \<Longrightarrow>
   op' = writes op p buf'\<Longrightarrow>
   step (Out p x) (writes op p buf) op'"
  apply (subst writes.code)
  apply (auto split: op.splits list.splits)
  done

lemma writes_empty_buf_simp[simp]:
  "writes op p [] = op"
  apply (coinduction arbitrary: op rule: op.coinduct_upto)
  apply (intro conjI impI)
  apply (subst writes.code, simp split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (meson cset.rel_refl rel_cset.rep_eq op.cong_refl)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  done

lemma writes_Cons_simp:
  "writes op p (x # xs) = Write (writes op p xs) p x"
  apply (coinduction arbitrary: op rule: op.coinduct_upto)
  apply (intro conjI impI)
  apply (subst writes.code, simp split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst writes.code, simp split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  done


fun steps where
  "steps [] = (=)"
| "steps (io # ios) = step io OO steps ios"

lemma steps_append[simp]:
  "steps (xs @ ys) = steps xs OO steps ys"
  by (induct xs arbitrary: ys) auto

lemma step_refl[simp]:
  "step io OO (=) = step io"
  by auto

thm step_map_op[no_vars]

lemma steps_map_op[intro!]:
  "op'' = map_op f g op' \<Longrightarrow> 
   map (map_IO f g id) xs = xs' \<Longrightarrow>
   steps xs op op' \<Longrightarrow>
   steps xs' (map_op f g op) op''"
  by (induct xs' arbitrary: op op' op'' xs)
    (force simp add: relcompp_apply)+

lemma steps_intro[intro]:
  "step x op op' \<Longrightarrow>
   steps xs op' op'' \<Longrightarrow>
   ys = x # xs \<Longrightarrow>
   steps ys op op''"
  apply auto
  done

lemma steps_intro_alt[intro]:
  "steps xs op op' \<Longrightarrow>
   step x op' op'' \<Longrightarrow>
   ys = xs @ [x] \<Longrightarrow>
   steps ys op op''"
  apply auto
  done

lemma steps_append_intro[intro]:
  "steps xs op op' \<Longrightarrow>
   steps ys op' op'' \<Longrightarrow>
   zs = xs @ ys \<Longrightarrow>
   steps zs op op''"
  apply auto
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

term bisim_cong

inductive wbisim_upto_bisim_cong ("\<U>") for R  where
  wb_upto_b_base[intro]:  "R op1 op2 \<Longrightarrow> \<U> R op1 op2"
| wb_upto_b_sym[intro]:  "\<U> R op2 op1 \<Longrightarrow> \<U> R op1 op2"
| wb_upto_b_Write[intro]: "\<U> R op1 op2 \<Longrightarrow> \<U> R (Write op1 p x) (Write op2 p x)"
| wb_upto_b_Sim:"sim (\<U> R) op1 op2 \<Longrightarrow> sim (\<U> R) op2 op1 \<Longrightarrow> \<U> R op1 op2"
(* | wb_upto_b_writes[intro]: "\<U> R op1 op2 \<Longrightarrow> \<U> R (writes op1 p x) (writes op2 p x)"
| wb_upto_b_Silent[intro]: "\<U> R op1 op2 \<Longrightarrow> \<U> R (Silent op1) (Silent op2)" *)

term bisim_cong

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

lemma map_op_writes[simp]:
  "map_op f1 f2 (writes op p xs) = writes (map_op f1 f2 op) (f2 p) xs"
  apply (induct xs)
   apply (simp_all add: writes_Cons_simp)
  done




(* find_theorems nd_writes

friend_of_corec nd_writes where
  "nd_writes op p xs =
    (case op of 
     Read p' f \<Rightarrow> Read p' (\<lambda> x'. nd_writes (f x') p xs)
   | Write op' p' x' \<Rightarrow> (if p = p' then Write (nd_writes op' p (tl (xs @ [x']))) p (hd (xs @ [x'])) else Write (nd_writes op' p xs) p' x')
   | Choice ops \<Rightarrow> Choice (cimage (\<lambda> op. nd_writes op p xs) ops)
   | Silent op' \<Rightarrow> Silent (nd_writes op' p xs))"
   apply (rule nd_writes.code)
  apply transfer_prover
  done
 *)
 


(* 
friend_of_corec nd_writes where
"nd_writes op p xs =
   Choice (cimage (\<lambda> op. case op of
   Write op' p' x' \<Rightarrow> (if p = p' then let xs' = xs @ [x'] in Write (nd_writes op' p (tl xs')) p (hd xs') else Write (nd_writes op' p xs) p' x')
 | Silent op' \<Rightarrow> Silent (nd_writes op' p xs)
 | Read p' f \<Rightarrow> Read p' (\<lambda> x'. nd_writes (f x') p xs)
 )
 (choices op))" 
*)

lemma step_nd_writes_elim:                  
  assumes "step io (nd_writes op p xs) op'"
  obtains 
    x x' xs' op'' where "io = Out p x" "xs @ [x'] = x # xs'" "op' = nd_writes op'' p xs'" "step (Out p x') op op''"
  | p' x' op'' where "io = Out p' x'" "op' = nd_writes op'' p xs" "step (Out p' x') op op''"
  | p' x' op'' where "io = Inp p' x'" "op' = nd_writes op'' p xs" "step (Inp p' x') op op''"
  | op'' where "io = Tau" "op' = nd_writes op'' p xs" "step Tau op op''"
 (*  using assms apply atomize_elim
  apply (induct "nd_writes op p xs" op' arbitrary: op pred: step)
  subgoal
    apply (subst (asm) nd_writes.code)
    apply (clarsimp simp flip: cin.rep_eq del: disjCI split: op.splits if_splits; force)
    done
  subgoal
    apply (cases xs)
    subgoal
    apply (subst (asm) nd_writes.code)
    apply (auto simp flip: cin.rep_eq del: disjCI split: op.splits if_splits)
    done
    subgoal
    apply (subst (asm) nd_writes.code)
    apply (auto simp flip: cin.rep_eq del: disjCI split: op.splits if_splits)
      apply force+
      done
    done
  subgoal
    apply (subst (asm) nd_writes.code)
    apply (clarsimp simp flip: cin.rep_eq del: disjCI split: op.splits if_splits; force)
    done
  subgoal for op' ops io op'' op'''
    apply (clarsimp simp flip: cin.rep_eq del: disjCI split: if_splits)
    apply (subst (asm) (6) nd_writes.code)
    apply (clarsimp simp flip: cin.rep_eq del: disjCI split: op.splits if_splits; hypsubst_thin)
    apply (drule meta_spec)
    apply (drule meta_mp)
     apply simp
    apply (smt (verit, ccfv_threshold) step.intros(4))
    done
  done *)
  oops

end