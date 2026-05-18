theory Traces_op

imports
  Dataplane.Timely_Infrastructure
  Source_op
  Set_op
begin

corec traces_op where
  "traces_op (S :: ('p :: {countable,defaults} \<Rightarrow> ('d :: cenum) llist) set) =
   (Choice (cimage 
   (\<lambda> p. let hds = acset ((\<lambda> f. lhd (f p)) ` 
   (Set.filter (\<lambda> f. f p \<noteq> LNil) S)) in 
   Choice (cimage (\<lambda> x. Write (traces_op ((\<lambda> f. f(p := ltl (f p))) ` {f \<in> S. lhd (f p) = x})) p x) hds))
   c\<UU>))"

lemma step_traces_op_elim:
  assumes "step io (traces_op S) op"
  obtains S' hds p x where
   "io = Out p x" "x |\<in>| hds" "p \<notin> defaults" "hds = acset ((\<lambda> f. lhd (f p)) ` (Set.filter (\<lambda> f. f p \<noteq> LNil) S))" 
   "S' = (\<lambda> f. f(p := ltl (f p))) ` {f \<in> S. lhd (f p) = x}"
   "op = traces_op S'"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) traces_op.code)
  apply auto
  done

lemma step_traces_op_intro[intro]:
 "io = Out p x \<Longrightarrow> x |\<in>| hds \<Longrightarrow>
  p \<notin> defaults \<Longrightarrow> hds = acset ((\<lambda> f. lhd (f p)) ` (Set.filter (\<lambda> f. f p \<noteq> LNil) S)) \<Longrightarrow>
  S' = (\<lambda> f. f(p := ltl (f p))) ` {f \<in> S. lhd (f p) = x} \<Longrightarrow>
  op = (traces_op S') \<Longrightarrow>
  step io (traces_op S) op"
  apply (subst traces_op.code)
  apply simp
  apply fastforce
  done

lemma traces_op_no_Tau[simp]:
  "\<not> step Tau (traces_op S) op"
  apply (subst traces_op.code)
  apply auto
  done

lemma traces_op_no_Inp[simp]:
  "\<not> step (Inp p x) (traces_op S) op"
  apply (subst traces_op.code)
  apply auto
  done

lemma wstep_step_traces_op[simp]:
  "io \<noteq> Tau \<Longrightarrow> wstep io (traces_op S) op' = step io (traces_op S) op'"
  apply (rule iffI)
  subgoal
    unfolding wstep_def
    apply (erule relcomppE)
    apply rotate_tac
    subgoal for op''
      apply (cases io)
        apply (simp_all add: OO_def)
       apply (metis converse_rtranclpE traces_op_no_Inp traces_op_no_Tau)
      subgoal
        apply safe
        apply hypsubst_thin
        apply (subgoal_tac "op'' = traces_op S")
        subgoal
          apply hypsubst_thin
          apply (elim step_traces_op_elim)
          apply (rule step_traces_op_intro)
               apply simp_all
          using converse_rtranclpE apply force
          done
        subgoal
          using converse_rtranclpE by force
        done
      done
    done
  subgoal
    by auto
  done

lemma step_sources_step_traces_op[intro]:
  "step (Out p x) (source_op inps) op \<Longrightarrow> 
   inps \<in> S \<Longrightarrow>
   op' = traces_op ((\<lambda> f. f(p := ltl (f p))) ` {f \<in> S. lhd (f p) = x}) \<Longrightarrow>
   io = Out p x \<Longrightarrow>
   step io (traces_op S) op'"
  apply (elim step_source_op_elim)
  apply simp
  apply (rule step_traces_op_intro)
       apply (rule refl)+
      defer
      apply assumption+
       apply (rule refl)+
  apply force
  done

coinductive traces_interleave where
  "traces_interleave S' lxs \<Longrightarrow> lhd (inps p) = x \<Longrightarrow>
   inps \<in> (Set.filter (\<lambda> f. f p \<noteq> LNil) S) \<Longrightarrow> S' = (\<lambda> f. f(p := ltl (f p))) ` {f \<in> S. lhd (f p) = x} \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow> traces_interleave S (LCons (VOut p x) lxs)"
| "(\<forall> inps p. inps \<in> S \<longrightarrow> p \<notin> defaults \<longrightarrow> inps p = LNil) \<Longrightarrow> traces_interleave S LNil"
         
thm set_spec_op_trace_eq_set_spec_op_trace_alt
thm set_op_bisim_set_spec_op


lemma cinfiniteD:
  "cinfinite (f |`| A) \<Longrightarrow> cinfinite A"
  unfolding cinfinite_def
  by (auto del: disjCI simp flip: cin.rep_eq; hypsubst_thin?)

end