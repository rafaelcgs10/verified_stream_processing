theory Spec

imports
  Operator
  BNA_Operators
begin

corec spec_op where
  "spec_op C = Choice (cimage (\<lambda> ios. case ios of
    LNil \<Rightarrow> \<oslash> 
  | LCons io ios' \<Rightarrow> 
    (case io of
      VInp p _ \<Rightarrow> Read p (\<lambda> y. spec_op (cimage ltl (cfilter (\<lambda> ios. lhd ios = VInp p y) C))) 
    | VOut p x \<Rightarrow> Write (spec_op (cimage ltl (cfilter (\<lambda> ios. lhd ios = io) C))) p x)) C)"

lemma step_spec_op_elim:
  assumes  "step io (spec_op C) op"
  obtains p x ios where "io = Out p x" "LCons (VOut p x) ios |\<in>| C" "op = spec_op (cimage ltl (cfilter (\<lambda> ios. lhd ios = VOut p x) C))"
  | p x y ios where "io = Inp p y"  "LCons (VInp p x) ios |\<in>| C" "op = spec_op (cimage ltl (cfilter (\<lambda> ios. lhd ios = VInp p y) C))"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) spec_op.code)
  apply (force split: llist.splits VIO.splits)
  done

lemma step_spec_op_intro1[intro]:
  "C' = cimage ltl (cfilter (\<lambda> ios. lhd ios = VOut p x) C) \<Longrightarrow>
   io = Out p x \<Longrightarrow>
   (\<exists> ios. LCons (VOut p x) ios |\<in>| C) \<Longrightarrow>
   step io (spec_op C) (spec_op C')"
  apply hypsubst_thin
  apply (elim exE)
  apply (subst spec_op.code)
  apply (rule SC)
   apply (rule cimageI)
   apply simp
  apply force
  done

lemma step_spec_op_intro2[intro]:
  "C' = cimage ltl (cfilter (\<lambda> ios. lhd ios = VInp p y) C) \<Longrightarrow>
   io = Inp p y \<Longrightarrow>
   (\<exists> ios x. LCons (VInp p x) ios |\<in>| C) \<Longrightarrow>
   step io (spec_op C) (spec_op C')"
  apply hypsubst_thin
  apply (elim exE)
  apply (subst spec_op.code)
  apply (rule SC)
   apply (rule cimageI)
   apply simp
  apply force
  done

lemma step_Tau_spec_op_False[simp]:
  "\<not> (step Tau (spec_op C) op)"
  apply (subst spec_op.code)
  apply (auto split: llist.splits VIO.splits)
  done

corec repeat_op where
  "repeat_op x = choice2
   (Write (repeat_op x) (1 :: 1) x) (Silent (repeat_op x))"

lemma step_repeat_op_elim:
  assumes  "step io (repeat_op x) op"
  obtains "io = Out 1 x" "op = repeat_op x"
  | "io = Tau" "op = repeat_op x"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) repeat_op.code)
  apply auto
  done

lemma step_repeat_intro[intro!]:
  "io = Tau \<or> io = Out 1 x \<Longrightarrow>
   step io (repeat_op x) (repeat_op x)"
  apply (subst repeat_op.code)
  apply auto
  done

lemma
  "wtraced (repeat_op x) ios \<Longrightarrow>
   ios = repeat (VOut 1 x)"
  apply (coinduction arbitrary: ios)
  subgoal for ios
    apply (erule wtraced.cases)
    subgoal
      sorry
    subgoal for vio op op' lxs
      apply simp
      apply hypsubst_thin
      oops

lemma
  "wtraced (repeat_op x) (repeat (VOut 1 x))"
  apply (coinduction)
  apply simp
  apply (rule disjI2)
  apply (rule exI[of _ "VOut 1 x"])
  apply (rule exI)
  apply (rule exI[of _ "repeat (VOut 1 x)"])
  apply simp
  apply (intro conjI)
    apply (meson iterates)
   apply (rule step_wstep)
   apply auto
  done

lemma repeat_op_spec_op:
  "repeat_op x \<approx> spec_op {| repeat (VOut 1 x) |}"
proof (coinduction rule: wbisim_coinduct)
  case SIM1
  then show ?case 
    apply -
    apply (elim step_repeat_op_elim; simp; hypsubst_thin?)
    subgoal
      apply (intro exI conjI wbcr_base step_wstep)
        apply simp_all
      apply (rule step_spec_op_intro1[where p=1])
        apply simp_all
       apply fastforce
      apply (metis iterates)
      done
    subgoal
      apply (intro exI conjI wbcr_base step_wstep)
        apply simp_all
      done
    done
next
  case SIM2
  then show ?case 
    apply -
    apply (elim step_spec_op_elim; simp; hypsubst_thin?)
    subgoal
      apply (intro exI conjI wbcr_base step_wstep)
        apply simp_all
       apply (metis io_of_vio.simps(2) lhd_iterates llist.sel(1) step_repeat_intro)
      apply (smt (verit, ccfv_threshold) cimage_cempty cimage_cinsert cin_cfilter cset_eqI csingleton_iff lhd_LCons ltl_iterates)
      done
    subgoal
      apply (intro exI conjI wbcr_base step_wstep)
        apply simp_all
       apply (metis VIO.distinct(1) lhd_LCons lhd_iterates)+
      done
    done
qed

lemma wstep_spec_opD:
  "wstep (io_of_vio vio) (spec_op C) op' \<Longrightarrow>
   step (io_of_vio vio) (spec_op C) op'"
  apply (cases vio; simp)
  subgoal
    unfolding wstep_def
    apply simp
    apply (smt (verit) converse_rtranclpE relcomppE step_Tau_spec_op_False step_spec_op_elim)
    done
  subgoal
    unfolding wstep_def
    apply simp
    apply (smt (verit) converse_rtranclpE relcomppE step_Tau_spec_op_False step_spec_op_elim)
    done
  done

lemma wtraced_spec_op_soundness:
  "ios |\<in>| C \<Longrightarrow>
   wtraced (spec_op C) ios"
  apply (coinduction arbitrary: ios C)
  subgoal for ios
    apply (cases ios)
    subgoal
      sorry
    subgoal for io lxs
      apply simp
      apply (cases io; simp)
      subgoal for p x
        apply (intro conjI exI disjI1 step_wstep)
          apply fastforce
         apply (rule refl)
        using cin_cimage_cfilter apply fastforce
        done
      subgoal
        apply (intro conjI exI disjI1 step_wstep)
          apply (rule step_spec_op_intro1)
            apply simp_all
         apply fast
        apply force
        done
      done
    done
  done

lemma wtraced_spec_op_completeness:
  "wtraced (spec_op C) ios \<Longrightarrow>
   ios |\<in>| C"
  apply (erule wtraced.cases)
  subgoal               
    sorry
  subgoal
    apply hypsubst_thin

  find_theorems "_ \<Longrightarrow> _ \<in> lset _" 

lemma repeat_op_soundness:
  "wtraced (repeat_op x) (repeat (VOut 1 x))"
  by (metis cinsertCI repeat_op_spec_op wbisim_sym wbisim_wtraced wtraced_spec_op_soundness)

lemma 
  "wtraced (repeat_op x) ios \<Longrightarrow>
   ios = repeat (VOut 1 x)"
  oops



end

lemma
  "sink_op = spec_op C"

corec univ_source_op where
  "univ_source_op = choice2
   (Choice (cimage (\<lambda> n. Write univ_source_op (1 :: 1) (n :: _ :: countable)) cUNIV))
   (Silent univ_source_op)"


lemma
  "univ_source_op \<approx> spec_op (cimage (lmap (VOut 1)) cUNIV)"


end