theory Propagation_Idempotence

imports
  Propagation_Exec
begin

section \<open>Idempotence of propagate_all\<close>

text \<open>If propagate_all terminates, the resulting configuration has an empty worklist.\<close>

lemma propagate_all_empty_worklist:
  "propagate_all summary conf = Some conf' \<Longrightarrow> worklist_is_empty summary conf'"
  unfolding propagate_all_def
  by (drule while_option_stop) simp

text \<open>On a quiescent configuration, propagate_all is the identity.\<close>

lemma propagate_all_quiescent:
  "worklist_is_empty summary conf \<Longrightarrow> propagate_all summary conf = Some conf"
  unfolding propagate_all_def
  by (subst while_option_unfold) simp

lemma propagate_all_idem:
  "propagate_all summary conf = Some conf' \<Longrightarrow> propagate_all summary conf' = Some conf'"
  by (rule propagate_all_quiescent[OF propagate_all_empty_worklist])

end
