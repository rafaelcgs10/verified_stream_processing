section \<open>The BNA operators operator\<close>

theory BNA_Operators

imports
  Operator
  Loop
  Composition
begin

abbreviation "write op p x \<equiv> Write op p (Observed x)"
abbreviation "eob op p \<equiv> Write op p EOB"
abbreviation "eos op p \<equiv> Write op p EOS"

definition bna_feedback :: "('m + 'l, 'n + 'l, 'd) op \<Rightarrow> ('m, 'n, 'd) op" where
  "bna_feedback op = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some o Inr)) (\<lambda>_. BEmpty) op)"

corec (friend) cp_list where "cp_list \<pi> ps op = (case ps of p # ps \<Rightarrow> Read p (case_observation (Write (cp_list \<pi> ps op) (\<pi> p)) (cp_list \<pi> ps op) End) | [] \<Rightarrow> 
  (case op of End \<Rightarrow> End | Write op p x \<Rightarrow> Write op p x | Read p f \<Rightarrow> Read p f))"

lemma cp_list_code: "cp_list \<pi> ps op = (case ps of p # ps \<Rightarrow> Read p (case_observation (Write (cp_list \<pi> ps op) (\<pi> p)) (cp_list \<pi> ps op) End) | [] \<Rightarrow> op)"
  by (subst cp_list.code) (auto split: list.splits op.splits)

corec bna_identity :: "('m :: enum, 'm, 'd) op" where
  "bna_identity = (case Enum.enum :: 'm list of (p # ps) \<Rightarrow> Read p (case_observation (Write (cp_list id ps bna_identity) p) (cp_list id ps bna_identity) End))"

corec bna_transpose :: "('m :: enum + 'n :: enum, 'n + 'm, 'd) op" where
  "bna_transpose = (case Enum.enum :: 'm list of (p # ps) \<Rightarrow>
  Read (Inl p) (case_observation (Write (cp_list (case_sum Inr Inl) (map Inl ps @ map Inr Enum.enum) bna_transpose) (Inr p)) bna_transpose End))"

abbreviation "bna_parcomp \<equiv> pcomp_op"
abbreviation "bna_seqcomp \<equiv> scomp_op"


abbreviation sum_assoc :: \<open>('a + 'b) + 'c \<Rightarrow> 'a + ('b + 'c)\<close> where
  \<open>sum_assoc \<equiv> case_sum (case_sum Inl (Inr o Inl)) (Inr o Inr)\<close>

lemma
  assumes \<open>history (bna_parcomp a (bna_parcomp b c)) lin lout\<close> \<open>history (bna_parcomp (bna_parcomp a b) c) rin rout\<close>
  shows \<open>lout (sum_assoc p) = rout p\<close>
  using assms unfolding history_def traced_pcomp_op'
  apply auto
  oops
 
end
