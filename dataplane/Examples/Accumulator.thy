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
  assumes \<open>step io (accumulator_op f g P n ins acc) op\<close>
    and \<open>io = Inp p x\<close>
  obtains False
  using assms
  by (subst (asm) accumulator_op.code) (auto split: llist.splits)

lemma no_step_accumulator_op_Tau:
  assumes \<open>step io (accumulator_op f g P n ins acc) op\<close>
    and \<open>io = Tau\<close>
  obtains False
  using assms
  by (subst (asm) accumulator_op.code) (auto split: llist.splits)

lemma step_accumulator_op_Out:
  assumes \<open>step io (accumulator_op f g P n ins acc) op\<close>
    and \<open>io = Out p x\<close>
  obtains x' lxs where \<open>op = accumulator_op f g P (n(p := n p + the_enat (llength (ltakeWhile (P p) (ins p))))) (ins(p := lxs)) (acc(p := (f p) (acc p) x'))\<close>
    \<open>ldropWhile (P p) (ins p) = LCons x' lxs\<close> \<open>x = ((g p) ((f p) (acc p) x'), n p + the_enat (llength (ltakeWhile (P p) (ins p))))\<close>
    \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  by (subst (asm) accumulator_op.code) (auto split: llist.splits)

lemma step_accumulator_op_elim:
  assumes \<open>step io (accumulator_op f g P n ins acc) op\<close>
  obtains p x x' lxs where \<open>io = Out p x\<close> \<open>op = accumulator_op f g P (n(p := n p + the_enat (llength (ltakeWhile (P p) (ins p))))) (ins(p := lxs)) (acc(p := (f p) (acc p) x'))\<close>
    \<open>ldropWhile (P p) (ins p) = LCons x' lxs\<close> \<open>x = ((g p) ((f p) (acc p) x'), n p + the_enat (llength (ltakeWhile (P p) (ins p))))\<close>
    \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  by (subst (asm) accumulator_op.code) (auto split: llist.splits)

lemma step_accumulator_op_Write:
  \<open>ldropWhile (P p) (ins p) = LCons x' lxs \<Longrightarrow> x = ((g p) (acc' p), n p + the_enat (llength (ltakeWhile (P p) (ins p)))) \<Longrightarrow>
  p \<notin> defaults \<Longrightarrow> n' = n(p := n p + the_enat (llength (ltakeWhile (P p) (ins p)))) \<Longrightarrow>
  ins' = ins(p := lxs) \<Longrightarrow> acc' = acc(p := (f p) (acc p) x') \<Longrightarrow> io = Out p x \<Longrightarrow>
  step io (accumulator_op f g P n ins acc) (accumulator_op f g P n' ins' acc')\<close>
  apply (subst accumulator_op.code)
  unfolding Let_def
  apply (rule SC)
   apply (rule cimage_eqI[rotated])
    apply force+
  done

lemma wstep_step_accumulator_op:
  \<open>io \<noteq> Tau \<Longrightarrow> wstep io (accumulator_op f g P n ins acc) op = step io (accumulator_op f g P n ins acc) op\<close>
  unfolding wstep_def
  apply (cases io; simp)
   apply (metis converse_rtranclpE no_step_accumulator_op_Inp no_step_accumulator_op_Tau relcompp.cases)
  by (smt (verit, ccfv_threshold) converse_rtranclpE no_step_accumulator_op_Tau reflclp_tranclp relcompp_apply step_accumulator_op_elim
      sup2CI)

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
      using Nil accumulates.intros(1) by blast
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

(*
(* WIP Out-of-order operator: we interpret the time in an event as the difference since the last seen watermark. *)

corec accumulator_op where
  \<open>accumulator_op f g wm ins acc = Choice (cimage (\<lambda>p. case ldropWhile (Not \<circ> is_Data) (ins p) of
    LCons (Data ts d) lxs \<Rightarrow>
      let ts' = foldl (+) 0 (list_of (lmap time (ltakeWhile (Not \<circ> is_Data) (ins p))));
          wm' = wm(p := wm p + ts');
          acc' = acc(p := (f p) (acc p) d)
      in Write (accumulator_op f g wm' (ins(p := lxs)) acc') p ((g p) (acc' p), wm' p + ts))
    (cfilter (\<lambda>p. ldropWhile (Not \<circ> is_Data) (ins p) \<noteq> LNil) c\<UU>))\<close>

lemma no_step_accumulator_op_Inp:
  assumes \<open>step io (accumulator_op f g wm ins acc) op\<close>
    and \<open>io = Inp p x\<close>
  obtains False
  using assms
  apply (subst (asm) accumulator_op.code)
  apply (auto split: llist.splits event.splits)
  using ldropWhile_LConsD by auto

lemma no_step_accumulator_op_Tau:
  assumes \<open>step io (accumulator_op f g wm ins acc) op\<close>
    and \<open>io = Tau\<close>
  obtains False
  using assms
  apply (subst (asm) accumulator_op.code)
  apply (auto split: llist.splits event.splits)
  using ldropWhile_LConsD by auto

lemma step_accumulator_op_Out:
  assumes \<open>step io (accumulator_op f g wm ins acc) op\<close>
    and \<open>io = Out p x\<close>
  obtains ts d lxs where \<open>op = accumulator_op f g (wm(p := wm p + foldl (+) 0 (list_of (lmap time (ltakeWhile (Not \<circ> is_Data) (ins p)))))) (ins(p := lxs)) (acc(p := (f p) (acc p) d))\<close>
    \<open>ldropWhile (Not \<circ> is_Data) (ins p) = LCons (Data ts d) lxs\<close>
    \<open>x = ((g p) ((f p) (acc p) d), wm p + foldl (+) 0 (list_of (lmap time (ltakeWhile (Not \<circ> is_Data) (ins p)))) + ts)\<close>
    \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) accumulator_op.code)
  apply (auto split: llist.splits event.splits)
  using ldropWhile_LConsD by fastforce

lemma step_accumulator_op_elim:
  assumes \<open>step io (accumulator_op f g wm ins acc) op\<close>
  obtains p ts d lxs where \<open>io = Out p ((g p) ((f p) (acc p) d), wm p + foldl (+) 0 (list_of (lmap time (ltakeWhile (Not \<circ> is_Data) (ins p)))) + ts)\<close>
    \<open>op = accumulator_op f g (wm(p := wm p + foldl (+) 0 (list_of (lmap time (ltakeWhile (Not \<circ> is_Data) (ins p)))))) (ins(p := lxs)) (acc(p := (f p) (acc p) d))\<close>
    \<open>ldropWhile (Not \<circ> is_Data) (ins p) = LCons (Data ts d) lxs\<close>
    \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) accumulator_op.code)
  apply (auto split: llist.splits event.splits)
  using ldropWhile_LConsD by fastforce

lemma step_accumulator_op_Write:
  \<open>wm' = wm(p := wm p + foldl (+) 0 (list_of (lmap time (ltakeWhile (Not \<circ> is_Data) (ins p))))) \<Longrightarrow>
  ins' = ins(p := lxs) \<Longrightarrow> acc' = acc(p := (f p) (acc p) d) \<Longrightarrow>
  io = Out p ((g p) (acc' p), wm' p + ts) \<Longrightarrow> ldropWhile (Not \<circ> is_Data) (ins p) = LCons (Data ts d) lxs \<Longrightarrow>
  p \<notin> defaults \<Longrightarrow>
  step io (accumulator_op f g wm ins acc) (accumulator_op f g wm' ins' acc')\<close>
  apply (subst accumulator_op.code)
  apply (rule SC)
   apply (rule cimage_eqI[rotated])
    apply force+
  done

lemma wstep_step_accumulator_op:
  \<open>io \<noteq> Tau \<Longrightarrow> wstep io (accumulator_op f g wm ins acc) op = step io (accumulator_op f g wm ins acc) op\<close>
  unfolding wstep_def
  apply (cases io; simp)
   apply (metis converse_rtranclpE no_step_accumulator_op_Inp no_step_accumulator_op_Tau relcompp.cases)
  subgoal for p x
    apply (rule iffI)
     apply (erule relcompp.cases)
     apply (erule converse_rtranclpE)
      apply (erule relcompp.cases)
      apply (erule converse_rtranclpE)
       apply blast
    using step_accumulator_op_Out no_step_accumulator_op_Tau apply metis
    using no_step_accumulator_op_Tau apply blast
    apply blast
    done
  done

lemma wfinished_accumulator_op_ins:
  \<open>wfinished (accumulator_op f g wm ins acc) \<longleftrightarrow> (\<forall>p \<in> \<UU>. ldropWhile (Not \<circ> is_Data) (ins p) = LNil)\<close>
  apply (rule iffI)
  subgoal
    apply (erule contrapos_pp)
    apply simp
    apply (erule bexE)
    subgoal for p
      apply (cases \<open>ldropWhile (Not \<circ> is_Data) (ins p)\<close>; simp)
      subgoal for x lxs
        apply (cases x; simp)
        subgoal for ts d
        apply (subgoal_tac \<open>step (io_of_vio (VOut p ((g p) ((f p) (acc p) d), wm p + foldl (+) 0 (list_of (lmap time (ltakeWhile (Not \<circ> is_Data) (ins p)))) + ts)))
  (accumulator_op f g wm ins acc)
  (accumulator_op f g (wm(p := wm p + foldl (+) 0 (list_of (lmap time (ltakeWhile (Not \<circ> is_Data) (ins p)))))) (ins(p := lxs)) (acc(p := (f p) (acc p) d)))\<close>)
         apply (erule step_not_wfinished)
        apply (rule step_accumulator_op_Write)
              apply (simp_all add: \<UU>_def)
          done
        using ldropWhile_LConsD by auto
      done
    done
  subgoal
    apply (subgoal_tac \<open>accumulator_op f g wm ins acc = \<oslash>\<close>)
     apply (drule arg_cong[of _ _ wfinished])
     apply simp
    apply (subst accumulator_op.code)
    apply fastforce
    done
  done

coinductive accumulates for f g where
  \<open>\<forall>p \<in> \<UU>. ldropWhile (Not \<circ> is_Data) (ins p) = LNil \<Longrightarrow> accumulates f g wm ins acc LNil\<close>
| \<open>p \<notin> defaults \<Longrightarrow> ldropWhile (Not \<circ> is_Data) (ins p) = LCons (Data ts d) lxs \<Longrightarrow>
  wm' = wm(p := wm p + foldl (+) 0 (list_of (lmap time (ltakeWhile (Not \<circ> is_Data) (ins p))))) \<Longrightarrow>
  acc' = acc(p := (f p) (acc p) d) \<Longrightarrow>
  accumulates f g wm' (ins(p := lxs)) acc' vios \<Longrightarrow>
  accumulates f g wm ins acc (LCons (VOut p ((g p) (acc' p), wm' p + ts)) vios)\<close>

lemma accumulator_op_soundness:
  \<open>wtraced (accumulator_op f g wm ins acc) vios \<Longrightarrow> accumulates f g wm ins acc vios\<close>
  apply (coinduction arbitrary: wm ins acc vios)
  apply (erule wtraced.cases; hypsubst_thin; simp)
  subgoal
    by (simp add: wfinished_accumulator_op_ins)
  subgoal
    apply (simp add: wstep_step_accumulator_op)
    apply (erule step_accumulator_op_elim)
    subgoal for p ts d
      apply (rule exI[of _ p])
      apply (rule exI[of _ ts])
      apply (intro exI[of _ d] conjI)
        apply (unfold comp_def)
        apply (metis io_of_vio.simps(2) io_of_vio_inverse)
       apply auto
      done
    done
  done

lemma accumulator_op_completeness:
  \<open>accumulates f g wm ins acc vios \<Longrightarrow> wtraced (accumulator_op f g wm ins acc) vios\<close>
  apply (coinduction arbitrary: wm ins acc vios)
  apply (erule accumulates.cases; hypsubst_thin; simp)
  subgoal
    using wfinished_accumulator_op_ins by fastforce
  subgoal for p ins ts d lxs wm acc
    apply (intro exI[of _ \<open>accumulator_op f g (wm(p := wm p + foldl (+) 0 (list_of (lmap time (ltakeWhile (Not \<circ> is_Data) (ins p)))))) (ins(p := lxs)) (acc(p := (f p) (acc p) d))\<close>] conjI disjI1)
     apply (simp add: wstep_step_accumulator_op)
     apply (rule step_accumulator_op_Write)
          apply auto
    done
  done

lemma accumulator_op_correctness:
  \<open>wtraced (accumulator_op f g wm ins acc) vios \<longleftrightarrow> accumulates f g wm ins acc vios\<close>
  using accumulator_op_soundness accumulator_op_completeness by meson

*)

end