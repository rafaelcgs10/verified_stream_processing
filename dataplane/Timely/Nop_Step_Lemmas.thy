

theory Nop_Step_Lemmas

imports
  Dataflow_Op
begin

section \<open>Nop Step Simp Rules\<close>

text \<open>Simp rules showing that steps without progress are no-ops: empty
progress states have no progress to extract, empty batches cause no
multiplicity changes, and trivial record updates collapse.\<close>

subsection \<open>Empty progress states\<close>

lemma not_has_progress_empty[simp]:
  "\<not> has_progress \<lparr> cons = [], inte = [], prod = [] \<rparr>"
  unfolding has_progress_def by simp

subsection \<open>Extracted progress and multiplicity changes of empty batches\<close>

lemma extract_progress_empty[simp]:
  "cons st = [] \<Longrightarrow> inte st = [] \<Longrightarrow> prod st = [] \<Longrightarrow> extract_progress nid nt st = []"
  unfolding extract_progress_def by simp

lemma extract_progress_no_progress[simp]:
  "\<not> has_progress st \<Longrightarrow> extract_progress nid nt st = []"
  unfolding has_progress_def by simp

lemma change_multiplicities_Nil[simp]:
  "change_multiplicities summary [] conf = conf"
  unfolding change_multiplicities_def by simp

subsection \<open>Subgraph record identities\<close>

declare operator_state_front_initia_upd_triv[simp]

end
