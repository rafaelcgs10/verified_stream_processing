theory Example
  imports Complex_Main "HOL-Library.Linear_Temporal_Logic_on_Streams"
     "HOL-Library.Multiset"
     "HOL.List"
     Types
     Input_0_2
     "HOL-Library.While_Combinator"
begin

definition followed_by :: "sum \<Rightarrow> sum \<Rightarrow> sum" where
  "followed_by \<equiv> plus"

definition results_in :: "sum \<Rightarrow> sum \<Rightarrow> sum" where
  "results_in \<equiv> plus"

lemma frontier_empty_zmset: "frontier {#}\<^sub>z = {}\<^sub>A"
  by transfer' (auto simp: minimal_antichain_def)

lemma summary_self: "summary (op, p) (op, p) = {}\<^sub>A"
  by (cases op; cases p) (auto simp: summary_def frontier_empty_zmset)

global_interpretation sum: enum_dataflow_topology
  "summary :: (op \<times> port) \<Rightarrow> (op \<times> port) \<Rightarrow> sum antichain"
  "results_in :: sum \<Rightarrow> sum \<Rightarrow> sum"
  defines take_step' = "enum_dataflow_topology.take_step summary results_in :: _ \<Rightarrow> (op \<times> port, sum) Step \<Rightarrow> _ \<Rightarrow> _" and
      after_summary = "dataflow_topology.after_summary results_in :: sum zmultiset \<Rightarrow> sum antichain \<Rightarrow> sum zmultiset"
  sorry

definition mymin_code :: "(sum \<times> (op \<times> port)) set \<Rightarrow> (sum \<times> (op \<times> port))" where [code del]: "mymin_code = mymin (<)"

lemma mymin_code[code]: "mymin_code (set (x # xs)) = fold (\<lambda>a b. if t_loc_linord (<) a b then a else b) xs x"
  unfolding mymin_code_def
  apply (rule linorderMin)
  apply unfold_locales
      apply auto
  done

definition take_step where
  "take_step = take_step' (<)"

declare sum.take_step.simps[of "((<) :: sum \<Rightarrow> _ \<Rightarrow> _)",  folded mymin_code_def take_step_def, code]

definition initial_state where
"initial_state = (\<lparr> c_work =  (\<lambda>x. zmultiset_of_antichain (frontier (default_capabilities x))),
                    c_pts = (default_capabilities),
                    c_imp = (\<lambda>x.{#}\<^sub>z) \<rparr>
                    :: ((op \<times> port, sum) configuration))"

lift_definition zequal :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> bool" is
  "\<lambda> (M, N) (P, Q). (M-N) = (P-Q) \<and> (N-M) = (Q-P)"
  apply (auto simp: equiv_zmset_def)
    apply (metis (full_types) Multiset.diff_right_commute add_diff_cancel_right')
    apply (metis Multiset.diff_right_commute add_diff_cancel_left')
  apply (metis add_diff_cancel_right' cancel_ab_semigroup_add_class.diff_right_commute)
  by (metis Multiset.diff_right_commute add_diff_cancel_left')

definition "reachable_locations \<equiv> { loc . \<exists> loc' .
     \<not> is_empty_antichain (summary loc loc') \<or> \<not> is_empty_antichain (summary loc' loc) }"

definition worklist_is_empty :: "(op \<times> port, sum) configuration \<Rightarrow> bool" where
"worklist_is_empty c = Set.Ball reachable_locations (\<lambda> loc. zequal (c_work c loc) {#}\<^sub>z)"

definition "propagate_all c0 = while_option worklist_is_empty
                                            (take_step PR) c0"

value "the (propagate_all initial_state)"

value "((c_pts initial_state) (Op 1, Src (Pnum 0)), (c_work initial_state) (Op 1, Src (Pnum 0)))"
value "((c_pts initial_state) (Op 2, Src (Pnum 0)), (c_work initial_state) (Op 2, Src (Pnum 0)))"
value "((c_pts initial_state) (Op 5, Src (Pnum 0)), (c_work initial_state) (Op 5, Src (Pnum 0)))"

value "(\<lambda> c. (c_pts c) (Op 1, Src (Pnum 0))) initial_state"

find_consts "_ list list \<Rightarrow> _ list"

value "(\<lambda> c. concat (map (\<lambda> (op, inps, outs). map (\<lambda> out. (c_pts c) (Op op, Src (Pnum out))) outs) [(1, [], [0])])) initial_state"


(* value "(c_imp (hd configs)) (Op 1, Src (Pnum 0))" *)


(*
  Comparing Rust trace with Isabelle trace
*)





value "test"

(* some helper print-out for debugging *)
(*
value "map (\<lambda> loc. (loc, ((znorm o (c_pts (configs ! 4))) loc))) (sorted_list_of_set reachable_locations)"
value "map (\<lambda> loc. (loc, ((znorm o (c_work (configs ! 7))) loc))) (sorted_list_of_set reachable_locations)"
value "map (\<lambda> loc. (loc, ((znorm o (c_work (configs ! 8))) loc))) (sorted_list_of_set reachable_locations)"
value "map (\<lambda> loc. (loc, ((znorm o (c_imp (configs ! 8))) loc), rust_implications loc 8))
  (sorted_list_of_set reachable_locations)"
*)

end
