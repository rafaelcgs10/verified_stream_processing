theory ConnectedComponents

imports
  Nondeterministic_Dataflow.BNA_Operators
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

corec cc_spec :: \<open>(_ \<Rightarrow> nat) \<Rightarrow> (_ \<Rightarrow> ('a \<times> 'a) set llist) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> (_, _, 'a set set \<times> nat) op\<close> where
  \<open>cc_spec n ins E = Choice (cimage (\<lambda>p. case ldropWhile ((=) {}) (ins p) of
      LCons x lxs \<Rightarrow> let n' = n(p := n p + the_enat (llength (ltakeWhile ((=) {}) (ins p)))) in
        Write (cc_spec n' (ins(p := lxs)) (E \<union> x)) p (The (graph.is_ccs (E \<union> x)), n' p))
    (cfilter (\<lambda>p. ldropWhile ((=) {}) (ins p) \<noteq> LNil) c\<UU>))\<close>

lemma no_step_cc_spec_Inp:
  assumes \<open>step io (cc_spec n ins E) op\<close>
    and \<open>io = Inp p x\<close>
  obtains False
  using assms
  apply (subst (asm) cc_spec.code)
  by (auto split: llist.splits)

lemma no_step_cc_spec_Tau:
  assumes \<open>step io (cc_spec n ins E) op\<close>
    and \<open>io = Tau\<close>
  obtains False
  using assms
  apply (subst (asm) cc_spec.code)
  by (auto split: llist.splits)

lemma step_cc_spec_Out:
  assumes \<open>step io (cc_spec n ins E) op\<close>
    and \<open>io = Out p x\<close>
  obtains x' lxs where \<open>op = cc_spec (n(p := n p + the_enat (llength (ltakeWhile ((=) {}) (ins p))))) (ins(p := lxs)) (E \<union> x')\<close>
    \<open>ldropWhile ((=) {}) (ins p) = LCons x' lxs\<close> \<open>x = (The (graph.is_ccs (E \<union> x')), n p + the_enat (llength (ltakeWhile ((=) {}) (ins p))))\<close>
    \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) cc_spec.code)
  by (auto split: llist.splits)

lemma step_cc_spec_elim:
  assumes \<open>step io (cc_spec n ins E) op\<close>
  obtains p x x' lxs where \<open>io = Out p x\<close> \<open>op = cc_spec (n(p := n p + the_enat (llength (ltakeWhile ((=) {}) (ins p))))) (ins(p := lxs)) (E \<union> x')\<close>
    \<open>ldropWhile ((=) {}) (ins p) = LCons x' lxs\<close> \<open>x = (The (graph.is_ccs (E \<union> x')), n p + the_enat (llength (ltakeWhile ((=) {}) (ins p))))\<close>
    \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) cc_spec.code)
  by (auto split: llist.splits)

lemma step_cc_spec_Write:
  \<open>ldropWhile ((=) {}) (ins p) = LCons x' lxs \<Longrightarrow> x = (The (graph.is_ccs (E \<union> x')), n p + the_enat (llength (ltakeWhile ((=) {}) (ins p)))) \<Longrightarrow>
  p \<notin> defaults \<Longrightarrow> n' = n(p := n p + the_enat (llength (ltakeWhile ((=) {}) (ins p)))) \<Longrightarrow>
  ins' = ins(p := lxs) \<Longrightarrow> E' = E \<union> x' \<Longrightarrow>
  step (Out p x) (cc_spec n ins E) (cc_spec n' ins' E')\<close>
  apply (subst cc_spec.code)
  apply (rule SC)
   apply (rule cimage_eqI[rotated])
    apply force+
  done

lemma wstep_step_cc_spec:
  \<open>io \<noteq> Tau \<Longrightarrow> wstep io (cc_spec n ins E) op = step io (cc_spec n ins E) op\<close>
  unfolding wstep_def
  apply (cases io; simp)
   apply (metis (no_types, opaque_lifting) OO_def converse_rtranclpE no_step_cc_spec_Inp no_step_cc_spec_Tau)
  by (smt (verit, ccfv_threshold) converse_rtranclpE no_step_cc_spec_Tau reflclp_tranclp relcompp_apply step_cc_spec_elim
      sup2CI)

end