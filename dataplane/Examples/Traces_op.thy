theory Traces_op

imports
  Dataplane.Timely_Infrastructure
  Source_op
begin

corec traces_op where
  "traces_op (S :: ('p :: {countable,defaults} \<Rightarrow> ('d :: cenum) llist) set) =
   (Choice (cimage 
   (\<lambda> p. let hds = acset ((\<lambda> f. lhd (f p)) ` (Set.filter (\<lambda> f. f p \<noteq> LNil) S)) in Choice (cimage (\<lambda> x. Write (traces_op ((\<lambda> f. f(p := ltl (f p))) ` {f \<in> S. lhd (f p) = x})) p x) hds))
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

lemma
  "lxs \<in> S \<Longrightarrow> wfinished (source_op lxs) \<Longrightarrow> wfinished (traces_op S)"
  unfolding wfinished_no_wstep
  apply auto
  subgoal for vio x
    apply (cases vio; simp)
    apply hypsubst_thin
    using step_sources_step_traces_op 
    oops

lemma 
  "inps \<in> S \<Longrightarrow> wtraced (source_op inps) trc \<Longrightarrow> wtraced (traces_op S) trc"
    apply (erule wtraced.cases)
     apply simp
     apply hypsubst_thin
  oops

lemma
  "wtraces (traces_op S) = \<Union> ((\<lambda> inps. wtraces (source_op inps)) ` S)"
  oops


coinductive traces_interleave where
  "traces_interleave S' lxs \<Longrightarrow> lhd (inps p) = x \<Longrightarrow>
   inps \<in> (Set.filter (\<lambda> f. f p \<noteq> LNil) S) \<Longrightarrow> S' = (\<lambda> f. f(p := ltl (f p))) ` {f \<in> S. lhd (f p) = x} \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow> traces_interleave S (LCons (VOut p x) lxs)"
| "(\<forall> inps p. inps \<in> S \<longrightarrow> p \<notin> defaults \<longrightarrow> inps p = LNil) \<Longrightarrow> traces_interleave S LNil"
         
lemma
  "wtraces (traces_op S) = {lxs. traces_interleave S lxs}"
  unfolding wtraces_def 
  apply safe
  subgoal for lxs
    apply (coinduction arbitrary: S lxs)
    subgoal for S lxs
      apply (erule wtraced.cases)
      subgoal for op
        apply auto
        apply hypsubst_thin
     unfolding wfinished_no_wstep
          apply simp
          apply (rule ccontr)
          subgoal for inps p
            apply (cases "inps p"; simp)
            subgoal for x lxs
              apply (drule spec[of _ "VOut p x"])
              apply (drule spec)+
              unfolding not_def
              apply (drule mp)
               back
               apply (rule step_sources_step_traces_op)
                  apply simp_all
              apply force
              done
            done
          done
        subgoal for vio op op' lxs
          apply hypsubst_thin
           apply auto
          apply (elim step_traces_op_elim)
          apply (cases vio)
           apply auto
          done
        done
      done
    subgoal for lxs
    apply (coinduction arbitrary: S lxs)
    subgoal for inps S
      apply (auto del: disjCI)
      apply (erule traces_interleave.cases)
      subgoal for S' lxs inpsa p x S
        apply hypsubst_thin
        apply (rule disjI2)
        apply (intro exI conjI)
          apply (rule refl)
        apply simp
         apply (rule step_traces_op_intro)
              apply (rule refl)+
        defer
           apply assumption+
          apply (rule refl)+
         apply auto[1]
        apply simp
        done
      subgoal for inps
        apply auto
        apply hypsubst_thin
        unfolding wfinished_no_wstep
        apply auto
        apply (elim step_traces_op_elim)
        apply auto
        done
      done
    done
  done


end