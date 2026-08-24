theory Propagation_Idempotence

imports
  Propagation_Exec
begin

section ‹Idempotence of propagate_all›

text ‹If propagate_all terminates, the resulting configuration has an empty worklist.›

lemma propagate_all_empty_worklist:
  "propagate_all summary conf = Some conf' ⟹ worklist_is_empty summary conf'"
  unfolding propagate_all_def
  by (drule while_option_stop) simp

text ‹On a quiescent configuration, propagate_all is the identity.›

lemma propagate_all_quiescent:
  "worklist_is_empty summary conf ⟹ propagate_all summary conf = Some conf"
  unfolding propagate_all_def
  by (subst while_option_unfold) simp

lemma propagate_all_idem:
  "propagate_all summary conf = Some conf' ⟹ propagate_all summary conf' = Some conf'"
  by (rule propagate_all_quiescent[OF propagate_all_empty_worklist])

end
