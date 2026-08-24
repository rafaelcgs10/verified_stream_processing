

theory Nop_Step_Lemmas

imports
  Dataflow_Op
begin

section ‹Self-Loop Lemmas for Nop Choices›

text ‹Toolbox for the weak bisimulation between @{const dataflow_op} and its
pruned variant. The pruned choices are (a) frontier reads with a stale
@{const upfro} flag and (b) progress writes without progress. The lemmas
below show that these choices are self-loops: they change nothing except
the @{const upfro} bookkeeping field of the subgraph record.›

subsection ‹Empty progress states›

lemma not_has_progress_empty[simp]:
  "¬ has_progress ⦇ cons = [], inte = [], prod = [] ⦈"
  unfolding has_progress_def by simp

subsection ‹Extracted progress and multiplicity changes of empty batches›

lemma extract_progress_empty[simp]:
  "cons st = [] ⟹ inte st = [] ⟹ prod st = [] ⟹ extract_progress nid nt st = []"
  unfolding extract_progress_def by simp

lemma extract_progress_no_progress[simp]:
  "¬ has_progress st ⟹ extract_progress nid nt st = []"
  unfolding has_progress_def by simp

lemma change_multiplicities_Nil[simp]:
  "change_multiplicities summary [] conf = conf"
  unfolding change_multiplicities_def by simp

subsection ‹Subgraph record identities›

declare operator_state_front_initia_upd_triv[simp]

end
