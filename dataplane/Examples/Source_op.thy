theory Source_op

imports
  "../Timely_Infrastructure"
  "../Utils"
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

end