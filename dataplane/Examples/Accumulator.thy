theory Accumulator

imports
  Nondeterministic_Dataflow.BNA_Operators
begin

(* In-order operator: we assume the input data are in batches of increasing timestamps. *)

corec accumulator_op where
  \<open>accumulator_op f g P n ins acc = Choice (cimage (\<lambda>p. case ldropWhile (P p) (ins p) of
      LCons x lxs \<Rightarrow>
        let n' = n(p := n p + the_enat (llength (ltakeWhile (P p) (ins p))));
            acc' = acc(p := (f p) (acc p) x) in
        Write (accumulator_op f g P n' (ins(p := lxs)) acc') p ((g p) (acc' p), n' p))
    (cfilter (\<lambda>p. ldropWhile (P p) (ins p) \<noteq> LNil) c\<UU>))\<close>

lemma no_step_accumulator_op_Inp:
  assumes \<open>step io (accumulator_op f g P n ins acc) op\<close> \<open>io = Inp p x\<close>
  obtains False
  using assms
  by (subst (asm) accumulator_op.code) (auto split: llist.splits)

lemma no_step_accumulator_op_Tau:
  assumes \<open>step io (accumulator_op f g P n ins acc) op\<close> \<open>io = Tau\<close>
  obtains False
  using assms
  by (subst (asm) accumulator_op.code) (auto split: llist.splits)

lemma step_accumulator_op_Out:
  assumes \<open>step io (accumulator_op f g P n ins acc) op\<close> \<open>io = Out p x\<close>
  obtains x' lxs where \<open>op = accumulator_op f g P (n(p := n p + the_enat (llength (ltakeWhile (P p) (ins p))))) (ins(p := lxs)) (acc(p := (f p) (acc p) x'))\<close>
    \<open>ldropWhile (P p) (ins p) = LCons x' lxs\<close> \<open>x = ((g p) ((f p) (acc p) x'), n p + the_enat (llength (ltakeWhile (P p) (ins p))))\<close>
    \<open>p \<notin> defaults\<close>
  using assms
  by (subst (asm) accumulator_op.code) (auto split: llist.splits)

lemma step_accumulator_op_elim:
  assumes \<open>step io (accumulator_op f g P n ins acc) op\<close>
  obtains p x x' lxs where \<open>io = Out p x\<close> \<open>op = accumulator_op f g P (n(p := n p + the_enat (llength (ltakeWhile (P p) (ins p))))) (ins(p := lxs)) (acc(p := (f p) (acc p) x'))\<close>
    \<open>ldropWhile (P p) (ins p) = LCons x' lxs\<close> \<open>x = ((g p) ((f p) (acc p) x'), n p + the_enat (llength (ltakeWhile (P p) (ins p))))\<close>
    \<open>p \<notin> defaults\<close>
  using assms
  by (subst (asm) accumulator_op.code) (auto split: llist.splits)

lemma step_accumulator_op_Write:
  assumes \<open>ldropWhile (P p) (ins p) = LCons x' lxs\<close> \<open>x = ((g p) (acc' p), n p + the_enat (llength (ltakeWhile (P p) (ins p))))\<close>
    \<open>p \<notin> defaults\<close> \<open>n' = n(p := n p + the_enat (llength (ltakeWhile (P p) (ins p))))\<close>
    \<open>ins' = ins(p := lxs)\<close> \<open>acc' = acc(p := (f p) (acc p) x')\<close> \<open>io = Out p x\<close>
  shows \<open>step io (accumulator_op f g P n ins acc) (accumulator_op f g P n' ins' acc')\<close>
proof -
  have \<open>Write (accumulator_op f g P n' ins' acc') p x |\<in>| choices (accumulator_op f g P n ins acc)\<close>
    using assms by (subst (2) accumulator_op.code) (auto intro: bexI[of _ p])
  thus ?thesis
    using assms Write_in_choices_step by auto
qed

lemma wstep_step_accumulator_op:
  assumes \<open>io \<noteq> Tau\<close>
  shows \<open>wstep io (accumulator_op f g P n ins acc) op = step io (accumulator_op f g P n ins acc) op\<close>
proof (cases io)
  case (Inp x11 x12)
  then show ?thesis
    by (metis converse_rtranclpE estep.simps(2) no_step_accumulator_op_Inp no_step_accumulator_op_Tau pick_middlep
        wstep_def)
next
  case (Out x21 x22)
  then show ?thesis
    by (smt (verit, best) converse_rtranclpE estep.simps(3) no_step_accumulator_op_Tau pick_middlep step_accumulator_op_Out
        step_wstep wstep_def)
qed (simp add: assms)

lemma wfinished_accumulator_op_ins:
  \<open>wfinished (accumulator_op f g P n ins acc) \<longleftrightarrow> (\<forall>p \<in> \<UU>. ldropWhile (P p) (ins p) = LNil)\<close>
proof
  assume \<open>wfinished (accumulator_op f g P n ins acc)\<close>
  thus \<open>\<forall>p \<in> \<UU>. ldropWhile (P p) (ins p) = LNil\<close>
  proof (rule contrapos_pp)
    assume \<open>\<not> (\<forall>p\<in>\<UU>. ldropWhile (P p) (ins p) = LNil)\<close>
    hence \<open>\<exists>p\<in>\<UU>. ldropWhile (P p) (ins p) \<noteq> LNil\<close>
      by blast
    then obtain p where \<open>p \<in> \<UU>\<close> \<open>ldropWhile (P p) (ins p) \<noteq> LNil\<close>
      by blast
    then obtain x lxs where \<open>ldropWhile (P p) (ins p) = LCons x lxs\<close>
      using llist.exhaust_sel by blast
    hence \<open>step (io_of_vio (VOut p ((g p) ((f p) (acc p) x), n p + the_enat (llength (ltakeWhile (P p) (ins p))))))
  (accumulator_op f g P n ins acc)
  (accumulator_op f g P (n(p := n p + the_enat (llength (ltakeWhile (P p) (ins p))))) (ins(p := lxs)) (acc(p := (f p) (acc p) x)))\<close>
      using step_accumulator_op_Write \<UU>_E \<open>p \<in> \<UU>\<close> fun_upd_same io_of_vio.simps(2) by metis
    thus \<open>\<not> wfinished (accumulator_op f g P n ins acc)\<close>
      by (rule step_not_wfinished)
  qed
next
  assume \<open>\<forall>p \<in> \<UU>. ldropWhile (P p) (ins p) = LNil\<close>
  hence \<open>accumulator_op f g P n ins acc = \<oslash>\<close>
    by (subst accumulator_op.code, fastforce)
  thus \<open>wfinished (accumulator_op f g P n ins acc)\<close>
    using arg_cong[where ?f=wfinished] by fastforce
qed

coinductive accumulates for f g P where
  \<open>\<forall>p \<in> \<UU>. ldropWhile (P p) (ins p) = LNil \<Longrightarrow> accumulates f g P n ins acc LNil\<close>
| \<open>p \<notin> defaults \<Longrightarrow> ldropWhile (P p) (ins p) = LCons x lxs \<Longrightarrow>
  n' = n(p := n p + the_enat (llength (ltakeWhile (P p) (ins p)))) \<Longrightarrow> acc' = acc(p := (f p) (acc p) x) \<Longrightarrow>
  accumulates f g P n' (ins(p := lxs)) acc' vios \<Longrightarrow> 
  accumulates f g P n ins acc (LCons (VOut p ((g p) (acc' p), n' p)) vios)\<close>

lemma accumulator_op_soundness:
  assumes \<open>wtraced (accumulator_op f g P n ins acc) vios\<close>
  shows \<open>accumulates f g P n ins acc vios\<close>
  using assms
proof (coinduction arbitrary: n ins acc vios)
  case accumulates
  then show ?case
  proof (cases rule: wtraced.cases)
    case Nil
    hence \<open>\<forall>p \<in> \<UU>. ldropWhile (P p) (ins p) = LNil\<close>
      using wfinished_accumulator_op_ins by blast
    thus ?thesis
      using Nil by blast
  next
    case (Step vio op' lxs)
    hence \<open>step (io_of_vio vio) (accumulator_op f g P n ins acc) op'\<close>
      by (simp add: wstep_step_accumulator_op)
    then obtain p x x' lxs' where \<open>io_of_vio vio = Out p x\<close> \<open>op' = accumulator_op f g P (n(p := n p + the_enat (llength (ltakeWhile (P p) (ins p))))) (ins(p := lxs')) (acc(p := (f p) (acc p) x'))\<close>
    \<open>ldropWhile (P p) (ins p) = LCons x' lxs'\<close> \<open>x = ((g p) ((f p) (acc p) x'), n p + the_enat (llength (ltakeWhile (P p) (ins p))))\<close>
    \<open>p \<notin> defaults\<close>
      using step_accumulator_op_elim by (smt (verit, ccfv_threshold))
    moreover have \<open>vio = VOut p x\<close>
      using \<open>io_of_vio vio = Out p x\<close> io_of_vio.simps(2) io_of_vio_inverse by metis
    ultimately show ?thesis
      using accumulates Step by simp
  qed
qed

lemma accumulator_op_completeness:
  assumes \<open>accumulates f g P n ins acc vios\<close>
  shows \<open>wtraced (accumulator_op f g P n ins acc) vios\<close>
  using assms
proof (coinduction arbitrary: n ins acc vios)
  case wtraced
  then show ?case
  proof (cases rule: accumulates.cases)
    case 1
    hence \<open>wfinished (accumulator_op f g P n ins acc)\<close>
      using wfinished_accumulator_op_ins by blast
    then show ?thesis
      using 1 by blast
  next
    case (2 p x lxs n' acc' vios)
    hence \<open>wstep (io_of_vio (VOut p ((g p) ((f p) (acc p) x), n p + the_enat (llength (ltakeWhile (P p) (ins p))))))
  (accumulator_op f g P n ins acc)
  (accumulator_op f g P (n(p := n p + the_enat (llength (ltakeWhile (P p) (ins p))))) (ins(p := lxs)) (acc(p := (f p) (acc p) x)))\<close>
      using step_accumulator_op_Write fun_upd_same io_of_vio.simps(2) step_wstep by metis
    then show ?thesis
      using 2 by auto
  qed
qed

lemma accumulator_op_correctness:
  \<open>wtraced (accumulator_op f g P n ins acc) vios \<longleftrightarrow> accumulates f g P n ins acc vios\<close>
  using accumulator_op_soundness accumulator_op_completeness by meson

end