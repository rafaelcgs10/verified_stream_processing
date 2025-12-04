theory Sync_op

imports
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.CSet_LList_Impl
  "../Timely_Infrastructure"
begin


corec sync_op where
  "sync_op op buf vios = choice2
   (Choice (
   cimage
    (\<lambda> op. case op of
      Write op p x \<Rightarrow> Silent (sync_op op ((p, x) # buf) vios)
    | Silent op \<Rightarrow> Silent (sync_op op buf vios)
    | Read _ _ \<Rightarrow> Code.abort (STR ''Sync_op can only output'') (\<lambda> _. \<oslash>)
    )
   (choices op)))
    (case vios of 
       LNil \<Rightarrow> \<oslash>
     | LCons (p, x) lxs \<Rightarrow> 
       if (p, x) \<in> set buf then Write (sync_op op (remove1 (p, x) buf) lxs) p x else \<oslash>)"

lemma step_sync_op_elim:
  assumes "step io (sync_op op buf vios) op'"
  obtains p x lxs where "io = Out p x" "vios = LCons (p, x) lxs"
    "op' = sync_op op (remove1 (p, x) buf) lxs" "(p, x) \<in> set buf"
  | op'' where "io = Tau" "step Tau op op''" "op' = sync_op op'' buf vios"
  | p x op'' where "io = Tau" "step (Out p x) op op''" "op' = sync_op op'' ((p, x) # buf) vios" 
  using assms apply -
  apply atomize_elim
  apply (subst (asm) sync_op.code)
  apply (auto del: disjCI split: op.splits simp flip: cin.rep_eq split: if_splits llist.splits; hypsubst_thin?)
          apply fastforce+  
  done



end