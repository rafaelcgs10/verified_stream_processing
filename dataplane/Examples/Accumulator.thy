theory Accumulator

imports
  Nondeterministic_Dataflow.BNA_Operators
begin

corec accumulator_op where
  \<open>accumulator_op f g P n ins acc = Choice (cimage (\<lambda>p. case ldropWhile P (ins p) of
      LCons x lxs \<Rightarrow> let n' = n(p := n p + the_enat (llength (ltakeWhile P (ins p)))); acc' = f acc x in
        Write (accumulator_op f g P n' (ins(p := lxs)) acc') p (g acc', n' p))
    (cfilter (\<lambda>p. ldropWhile P (ins p) \<noteq> LNil) c\<UU>))\<close>

lemma no_step_accumulator_op_Inp:
  assumes \<open>step io (accumulator_op f g P n ins acc) op\<close>
    and \<open>io = Inp p x\<close>
  obtains False
  using assms
  apply (subst (asm) accumulator_op.code)
  by (auto split: llist.splits simp add: Let_def)

lemma no_step_accumulator_op_Tau:
  assumes \<open>step io (accumulator_op f g P n ins acc) op\<close>
    and \<open>io = Tau\<close>
  obtains False
  using assms
  apply (subst (asm) accumulator_op.code)
  by (auto split: llist.splits simp add: Let_def)

lemma step_accumulator_op_Out:
  assumes \<open>step io (accumulator_op f g P n ins acc) op\<close>
    and \<open>io = Out p x\<close>
  obtains x' lxs where \<open>op = accumulator_op f g P (n(p := n p + the_enat (llength (ltakeWhile P (ins p))))) (ins(p := lxs)) (f acc x')\<close>
    \<open>ldropWhile P (ins p) = LCons x' lxs\<close> \<open>x = (g (f acc x'), n p + the_enat (llength (ltakeWhile P (ins p))))\<close>
    \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) accumulator_op.code)
  by (auto split: llist.splits simp add: Let_def)

lemma step_accumulator_op_elim:
  assumes \<open>step io (accumulator_op f g P n ins acc) op\<close>
  obtains p x x' lxs where \<open>io = Out p x\<close> \<open>op = accumulator_op f g P (n(p := n p + the_enat (llength (ltakeWhile P (ins p))))) (ins(p := lxs)) (f acc x')\<close>
    \<open>ldropWhile P (ins p) = LCons x' lxs\<close> \<open>x = (g (f acc x'), n p + the_enat (llength (ltakeWhile P (ins p))))\<close>
    \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) accumulator_op.code)
  by (auto split: llist.splits simp add: Let_def)

lemma step_accumulator_op_Write:
  \<open>ldropWhile P (ins p) = LCons x' lxs \<Longrightarrow> x = (g acc', n p + the_enat (llength (ltakeWhile P (ins p)))) \<Longrightarrow>
  p \<notin> defaults \<Longrightarrow> n' = n(p := n p + the_enat (llength (ltakeWhile P (ins p)))) \<Longrightarrow>
  ins' = ins(p := lxs) \<Longrightarrow> acc' = f acc x' \<Longrightarrow> io = Out p x \<Longrightarrow>
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

lemma accumulator_op_wfinished:
  \<open>wfinished (accumulator_op f g P n ins acc) \<longleftrightarrow> (\<forall>p \<in> \<UU>. ldropWhile P (ins p) = LNil)\<close>
  apply (rule iffI)
  subgoal
    apply (erule contrapos_pp)
    apply simp
    apply (erule bexE)
    subgoal for p
      apply (cases \<open>ldropWhile P (ins p)\<close>; simp)
      subgoal for x lxs
        apply (subgoal_tac \<open>step (io_of_vio (VOut p (g (f acc x), n p + the_enat (llength (ltakeWhile P (ins p))))))
  (accumulator_op f g P n ins acc)
  (accumulator_op f g P (n(p := n p + the_enat (llength (ltakeWhile P (ins p))))) (ins(p := lxs)) (f acc x))\<close>)
         apply (erule step_not_wfinished)
        apply (rule step_accumulator_op_Write)
              apply (simp_all add: \<UU>_def)
        done
      done
    done
  subgoal
    apply (subgoal_tac \<open>accumulator_op f g P n ins acc = \<oslash>\<close>)
     apply (drule arg_cong[of _ _ wfinished])
     apply simp
    apply (subst accumulator_op.code)
    apply fastforce
    done
  done

coinductive accumulates for f g P where
  \<open>\<forall>p \<in> \<UU>. ldropWhile P (ins p) = LNil \<Longrightarrow> accumulates f g P n ins acc LNil\<close>
| \<open>p \<notin> defaults \<Longrightarrow> ldropWhile P (ins p) = LCons x lxs \<Longrightarrow>
  n' = n(p := n p + the_enat (llength (ltakeWhile P (ins p)))) \<Longrightarrow> acc' = f acc x \<Longrightarrow>
  accumulates f g P n' (ins(p := lxs)) acc' vios \<Longrightarrow> 
  accumulates f g P n ins acc (LCons (VOut p (g acc', n' p)) vios)\<close>

lemma accumulator_op_soundness:
  \<open>wtraced (accumulator_op f g P n ins acc) vios \<Longrightarrow> accumulates f g P n ins acc vios\<close>
  apply (coinduction arbitrary: n ins acc vios)
  apply (erule wtraced.cases; hypsubst_thin; simp)
  subgoal
    using accumulator_op_wfinished accumulates.intros(1) by fast
  subgoal for n ins acc vio op vios
    apply (simp add: wstep_step_accumulator_op)
    apply (erule step_accumulator_op_elim)
    subgoal for p x x' lxs
      apply (rule exI[of _ p])
      apply (intro exI[of _ x'] conjI)
        apply (metis io_of_vio.simps(2) io_of_vio_inverse)
       apply assumption
      apply (rule exI[of _ lxs])
      apply simp
      done
    done
  done

lemma accumulator_op_completeness:
  \<open>accumulates f g P n ins acc vios \<Longrightarrow> wtraced (accumulator_op f g P n ins acc) vios\<close>
  apply (coinduction arbitrary: n ins acc vios)
  apply (erule accumulates.cases; hypsubst_thin; simp)
  subgoal
    using accumulator_op_wfinished accumulates.intros(1) by fast
  subgoal for p ins x lxs n acc vios
    apply (intro exI[of _ \<open>accumulator_op f g P (n(p := n p + the_enat (llength (ltakeWhile P (ins p))))) (ins(p := lxs)) (f acc x)\<close>] conjI disjI1)
     apply (simp add: wstep_step_accumulator_op)
     apply (rule step_accumulator_op_Write)
           apply auto
    done
  done

lemma accumulator_op_correctness:
  \<open>wtraced (accumulator_op f g P n ins acc) vios \<longleftrightarrow> accumulates f g P n ins acc vios\<close>
  using accumulator_op_soundness accumulator_op_completeness by meson

end