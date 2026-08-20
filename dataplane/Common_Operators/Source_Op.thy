theory Source_Op

imports
  "../Lib/DataplaneUtils"
begin 

corec source_op where
  "source_op inps = Choice (cimage (\<lambda> p. case inps p of
     LCons x lxs \<Rightarrow> Write (source_op (inps (p := lxs))) p x)
     (cfilter (\<lambda> p. inps p \<noteq> LNil) c\<UU>))"

lemma step_source_op_elim:
  assumes "step io (source_op inps) op"
  obtains p x lxs where "io = Out p x" "inps p = LCons x lxs"
    "op = source_op (inps(p := lxs))" "p \<notin> defaults"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) source_op.code)
  apply (clarsimp split: llist.splits list.splits)
  done

lemma step_source_op_Out_intro[intro]:
  "inps p = LCons x lxs \<Longrightarrow>
   inps' = inps(p := lxs) \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   step (Out p x) (source_op inps) (source_op inps')"
  apply (subst source_op.code)
  apply force
  done

lemma step_source_op_Out_intro'[intro]:
  "inps p = LCons x lxs \<Longrightarrow>
   inps' = inps(p := lxs) \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   op = source_op inps' \<Longrightarrow>
   io = Out p x \<Longrightarrow>
   step io (source_op inps) op"
  by auto

lemma no_step_source_op_Tau[simp]:
  "\<not> step Tau (source_op inps) op'"
  apply (subst source_op.code)
  apply (auto split: llist.splits)
  done

lemma no_step_source_op_Inp[simp]:
  "\<not> step (Inp p x) (source_op inps) op'"
  apply (subst source_op.code)
  apply (auto split: llist.splits)
  done

lemma wstep_step_source_op[simp]:
  "io \<noteq> Tau \<Longrightarrow> wstep io (source_op inps) op' = step io (source_op inps) op'"
 apply (rule iffI)
  subgoal
    unfolding wstep_def
    apply (erule relcomppE)
    apply rotate_tac
    subgoal for op''
      apply (cases io)
        apply (simp_all add: OO_def)
       apply (metis converse_rtranclpE no_step_source_op_Inp no_step_source_op_Tau)
      subgoal
        apply safe
        apply hypsubst_thin
        apply (subgoal_tac "op'' = source_op inps")
        subgoal
          apply hypsubst_thin
          apply (elim step_source_op_elim)
          apply (metis converse_rtranclpE no_step_source_op_Tau step_source_op_Out_intro)
          done
        subgoal
          using converse_rtranclpE by force
        done
      done
    done
  subgoal
    by auto
  done

coinductive port_interleave where
  "port_interleave (inps(p := inpsp)) lxs \<Longrightarrow> inps p = LCons x inpsp \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow> port_interleave inps (LCons (VOut p x) lxs)"
| "(\<forall> p. p \<notin> defaults \<longrightarrow> inps p = LNil) \<Longrightarrow> port_interleave inps LNil"




end