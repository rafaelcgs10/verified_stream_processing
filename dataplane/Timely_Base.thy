theory Timely_Base

imports
  Nondeterministic_Dataflow.Operator
  Nondeterministic_Dataflow.BNA_Operators
  Progress_Tracking.Propagate
  Nondeterministic_Dataflow.Eval
  "HOL-Library.While_Combinator"
  "../propagation_extras/Executable"
  "../propagation_extras/Termination"
  Zero_Cyc_Check
  Locations
  Operators_Utils
  DataplaneUtils
  CsetUtils
  ZmsetUtils
  ListUtils
  Containers.Collection_Order
  AntichainOrder
  Bots
  MyMisc
begin

declare in_filter_zmset_in_zmset[simp del]  pos_filter_zmset_pos_zmset[simp del]
  neg_filter_zmset_neg_zmset[simp del] set_antichain1[simp del] set_antichain2[simp del] mset_set.infinite[simp del]

definition "DEBUG = False"

definition "trace = (if DEBUG then Debug.tracing else (\<lambda> x y. y))"

lemma trace_simp[simp]:
  "trace x r = r"
  by (auto simp add: trace_def)

type_synonym 'a change_batch = "'a list"

record ('id, 'p, 't) subgraph =
  pt_tr :: "(('id, 'p) location, 't) configuration"
  nxt :: "'id \<times> 'p \<Rightarrow> ('id \<times> 'p) option"
  summ :: "('id, 'p) location \<Rightarrow> ('id, 'p) location \<Rightarrow> 't antichain"
  upfro :: "'id \<Rightarrow> bool"

record ('p, 't) shared_state =
  cons :: "('p \<times> 't \<times> int) change_batch"
  inte :: "('p \<times> 't \<times> int) change_batch"
  prod :: "('p \<times> 't \<times> int) change_batch"

datatype ('p, 't) capability = Cap (time: "'t :: plus") (out: 'p)

end
