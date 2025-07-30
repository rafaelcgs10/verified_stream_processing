theory ConnectedComponents

imports
  Accumulator
begin

locale graph =
  fixes edges :: \<open>('a \<times> 'a) set\<close> (\<open>E\<close>)

context graph
begin

inductive reachable :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  reach_refl: \<open>reachable x x\<close>
| reach_edge: \<open>(x, y) \<in> E \<Longrightarrow> reachable y z \<Longrightarrow> reachable x z\<close>

lemma edge_reachable:
  \<open>(x, y) \<in> E \<Longrightarrow> reachable x y\<close>
  using reachable.intros by blast

lemma reachable_trans:
  \<open>reachable x y \<Longrightarrow> reachable y z \<Longrightarrow> reachable x z\<close>
proof (induct x y rule: reachable.induct)
  case (reach_refl x)
  then show ?case .
next
  case (reach_edge x y z)
  then show ?case
    using reachable.reach_edge by blast
qed

lemma reach_edge_alt:
  \<open>reachable x y \<Longrightarrow> (y, z) \<in> E \<Longrightarrow> reachable x z\<close>
  using edge_reachable reachable_trans by blast

definition is_subcc :: \<open>'a set \<Rightarrow> bool\<close>  where
  \<open>is_subcc S \<equiv> \<forall>x \<in> S. \<forall>y \<in> S. reachable x y\<close>

definition is_cc :: \<open>'a set \<Rightarrow> bool\<close>  where
  \<open>is_cc S \<equiv> S \<noteq> {} \<and> is_subcc S \<and> (\<forall>S'. S \<subseteq> S' \<and> is_subcc S' \<longrightarrow> S' = S)\<close>

abbreviation ccs :: \<open>'a set set\<close> where
  \<open>ccs \<equiv> {S. is_cc S}\<close>

definition is_ccs :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>is_ccs \<equiv> (=) ccs\<close>

end

abbreviation cc_spec where
  \<open>cc_spec \<equiv> accumulator_op (\<union>) (The \<circ> graph.is_ccs) ((=) {})\<close>

end