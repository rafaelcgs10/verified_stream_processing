

theory Nop_Step_Lemmas

imports
  Dataflow_Op
begin

section ‹Nop Step Simp Rules›

text ‹Simp rules showing that steps without progress are no-ops: empty
progress states have no progress to extract, empty batches cause no
multiplicity changes, and trivial record updates collapse.›

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
