theory SimulationProofMethods
  imports
    Main
    "HOL-Eisbach.Eisbach"
begin

text \<open>The following method is an experiment with Eisbach.  It is designed to work for a simulation
goal as we have them in correctness proofs, i.e., goals of the form
\<open>step io op1 op1' \<Longrightarrow> \<exists>op2'. (w)step io op2 op2' \<and> R op1' op2'\<close>.\<close>

method sim_cases uses sim defs elims intros =
  (use nothing in \<open>insert sim, (unfold defs)?, repeat_new \<open>erule conjE elims; simp?; hypsubst_thin?\<close>;
  auto intro: intros method_facts simp flip: defs\<close>)

(* TODO: create more methods to be more flexible, in particular for the last method applied.
Sometimes we want to apply auto with various settings, maybe sometimes we want something else than
auto. *)

end
