section \<open>The composition operator\<close>

theory New_Composition

imports
  Operator
begin

corec bind_op where
  "bind_op r w op = (case op of
    Read p f \<Rightarrow> r p f
  | Write op p x \<Rightarrow> w op p x
  | Choice ops \<Rightarrow> Choice (cimage (bind_op r w) ops))"

consts comp_op :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('ip2 \<Rightarrow> 'd buf) \<Rightarrow>
  ('ip1, 'op1, 'd) op \<Rightarrow> ('ip2, 'op2, 'd) op \<Rightarrow> ('ip1 + 'ip2, 'op1 + 'op2, 'd) op" 

lemma comp_op_code:
  "comp_op wire buf op1 op2 = Choice {| bind_op 
   (\<lambda> p f. Read (Inl p) (\<lambda> x. comp_op wire buf (f x) op2))
   (\<lambda> op1' p x. case wire p of None \<Rightarrow> Write (comp_op wire buf op1' op2) (Inl p) x | Some q \<Rightarrow> comp_op wire (BENQ q x buf) op1' op2) op1,
   bind_op
   (\<lambda> p f. if p \<in> ran wire then if buf p = [] then \<oslash> else comp_op wire (BTL p buf) op1 (f (BHD p buf)) else Read (Inr p) (\<lambda> x. comp_op wire buf op1 (f x)))
   (\<lambda> op2' p x. Write (comp_op wire buf op1 op2') (Inr p) x)
   op2  
 |}"
 sorry


definition scomp_op (infixl "\<bullet>" 65) where
  "scomp_op op1 op2 = map_op projl projr (comp_op Some (\<lambda>_. []) op1 op2)"


lemma
  "Read (1::1) (\<lambda> _. end_op) \<bullet> Choice {| Choice {| Write (end_op :: ('a, 1, nat) op) (1::1) 1, Write end_op (1::1) 4|}, Choice {|Write end_op (1::1) (0::nat), Write end_op (1::1) 2|}|} ~
   Read (1::1) (\<lambda> _. end_op) \<bullet> Choice {| Choice {| Write (end_op :: ('a, 1, nat) op) (1::1) 0, Write end_op (1::1) 4|}, Choice {|Write end_op (1::1) (1::nat), Write end_op (1::1) 2|}|} \<Longrightarrow> False"
  unfolding scomp_op_def
  apply auto
  apply (erule bisim.cases)
  subgoal for s t
    unfolding sim_def
    apply (auto simp add: ranI cfilter.rep_eq)
   apply hypsubst_thin
    apply (drule spec2)
    apply (drule mp)
     apply (subst comp_op_code)
    apply simp
     apply (rule step.intros)
      apply (rule cinsertI2)
      apply simp
     apply (subst bind_op.code)
    apply simp
     apply (rule step.intros)
      apply simp
      apply (rule disjI1)
      apply (rule refl)
         apply (subst bind_op.code)
    apply simp
     apply (rule step.intros)
    apply simp
      apply (rule disjI1)
      apply (rule refl)
         apply (subst bind_op.code)
    apply simp
     apply (rule step.intros)
    apply (erule thin_rl)
    apply auto
     apply (subst (asm) comp_op_code)
    apply auto
    subgoal
     apply (subst (asm) bind_op.code)
      apply auto
      done
    subgoal
    apply (subst (asm) bind_op.code)
      apply (auto simp add: ranI)
      subgoal
        apply (subst (asm) bind_op.code)
        apply auto
        subgoal
        apply (subst (asm) bind_op.code)
          apply auto
          done
        subgoal
       apply (subst (asm) bind_op.code)
          apply auto
          done
        done
   subgoal
        apply (subst (asm) bind_op.code)
        apply auto
        subgoal
        apply (subst (asm) bind_op.code)
          apply auto
          oops


lemma scomp_op_example_1:
  "end_op \<bullet> Choice {| Choice {| Write (end_op :: ('a, 1, nat) op) (1::1) 1, Write end_op (1::1) 4|}, Choice {|Write end_op (1::1) (0::nat), Write end_op (1::1) 2|}|} ~
   end_op \<bullet> Choice {| Choice {| Write (end_op :: ('a, 1, nat) op) (1::1) 0, Write end_op (1::1) 4|}, Choice {|Write end_op (1::1) (1::nat), Write end_op (1::1) 2|}|}"
  apply (coinduction rule: bisim_coinduct_upto)
  unfolding sim_def scomp_op_def
  apply (intro conjI allI impI)
  subgoal for io op
    apply (subst (asm) comp_op_code)
    apply auto
    subgoal 
      apply (subst (asm) bind_op.code)
      apply auto
      done
    subgoal 
      apply (subst (asm) bind_op.code)
      apply auto
       apply (subst (asm) bind_op.code)
       apply auto
      subgoal
        apply (subst (asm) bind_op.code)
        apply auto
        apply hypsubst_thin
        apply (intro exI conjI)
         apply (rule step_map_op)
          apply (subst comp_op_code)
          apply simp
          apply (rule step.intros)
           apply (rule cinsertI2)
           apply (subst bind_op.code)
           apply auto
          apply (rule step.intros)
           apply simp
           apply (rule disjI2)
           apply (rule refl)
          apply (subst bind_op.code)
          apply auto
          apply (rule step.intros)
           apply auto
          apply (subst bind_op.code)
          apply simp
          apply (rule step.intros)
         apply simp
        apply (rule bc_refl)
        apply simp
        done
      subgoal
        apply (subst (asm) bind_op.code)
        apply auto
        apply hypsubst_thin
        apply (intro exI conjI)
         apply (rule step_map_op)
          apply (subst comp_op_code)
          apply simp
          apply (rule step.intros)
           apply (rule cinsertI2)
           apply (subst bind_op.code)
           apply auto
          apply (rule step.intros)
           apply simp
           apply (rule disjI1)
           apply (rule refl)
          apply (subst bind_op.code)
          apply auto
          apply (rule step.intros)
           apply simp
           apply (rule disjI2)
           apply (rule refl)
          apply (subst bind_op.code)
          apply simp
          apply (rule step.intros)
         apply simp
        apply (rule bc_refl)
        apply simp
        done
      subgoal
        apply (subst (asm) bind_op.code)
        apply auto
        subgoal
          apply (subst (asm) bind_op.code)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule step_map_op)
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI1)
             apply (rule refl)
            apply (subst bind_op.code)
            apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI1)
             apply (rule refl)
            apply (subst bind_op.code)
            apply simp
            apply (rule step.intros)
           apply simp
          apply (rule bc_refl)
          apply simp
          done
        subgoal
          apply (subst (asm) bind_op.code)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule step_map_op)
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI2)
             apply (rule refl)
            apply (subst bind_op.code)
            apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI2)
             apply (rule refl)
            apply (subst bind_op.code)
            apply simp
            apply (rule step.intros)
           apply simp
          apply (rule bc_refl)
          apply simp
          done
        done
      done
    done
  subgoal for io op
    apply (subst (asm) comp_op_code)
    apply auto
    subgoal 
      apply (subst (asm) bind_op.code)
      apply auto
      done
    subgoal 
      apply (subst (asm) bind_op.code)
      apply auto
       apply (subst (asm) bind_op.code)
       apply auto
      subgoal
        apply (subst (asm) bind_op.code)
        apply auto
        apply hypsubst_thin
        apply (intro exI conjI)
         apply (rule step_map_op)
          apply (subst comp_op_code)
          apply simp
          apply (rule step.intros)
           apply (rule cinsertI2)
           apply (subst bind_op.code)
           apply auto
          apply (rule step.intros)
           apply simp
           apply (rule disjI2)
           apply (rule refl)
          apply (subst bind_op.code)
          apply auto
          apply (rule step.intros)
           apply auto
          apply (subst bind_op.code)
          apply simp
          apply (rule step.intros)
         apply simp
        apply (rule bc_refl)
        apply simp
        done
      subgoal
        apply (subst (asm) bind_op.code)
        apply auto
        apply hypsubst_thin
        apply (intro exI conjI)
         apply (rule step_map_op)
          apply (subst comp_op_code)
          apply simp
          apply (rule step.intros)
           apply (rule cinsertI2)
           apply (subst bind_op.code)
           apply auto
          apply (rule step.intros)
           apply simp
           apply (rule disjI1)
           apply (rule refl)
          apply (subst bind_op.code)
          apply auto
          apply (rule step.intros)
           apply simp
           apply (rule disjI2)
           apply (rule refl)
          apply (subst bind_op.code)
          apply simp
          apply (rule step.intros)
         apply simp
        apply (rule bc_refl)
        apply simp
        done
      subgoal
        apply (subst (asm) bind_op.code)
        apply auto
        subgoal
          apply (subst (asm) bind_op.code)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule step_map_op)
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI1)
             apply (rule refl)
            apply (subst bind_op.code)
            apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI1)
             apply (rule refl)
            apply (subst bind_op.code)
            apply simp
            apply (rule step.intros)
           apply simp
          apply (rule bc_refl)
          apply simp
          done
        subgoal
          apply (subst (asm) bind_op.code)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule step_map_op)
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI2)
             apply (rule refl)
            apply (subst bind_op.code)
            apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI2)
             apply (rule refl)
            apply (subst bind_op.code)
            apply simp
            apply (rule step.intros)
           apply simp
          apply (rule bc_refl)
          apply simp
          done
        done
      done
    done
  done


lemma scomp_op_example_2:
  "Read (1::1) (\<lambda> _. end_op) \<bullet> Choice {| Choice {| Write (end_op :: ('a, 1, nat) op) (1::1) 1, Write end_op (1::1) 4|}, Choice {|Write end_op (1::1) (0::nat), Write end_op (1::1) 2|}|} ~
   Read (1::1) (\<lambda> _. end_op) \<bullet> Choice {| Choice {| Write (end_op :: ('a, 1, nat) op) (1::1) 0, Write end_op (1::1) 4|}, Choice {|Write end_op (1::1) (1::nat), Write end_op (1::1) 2|}|}"
  apply (coinduction rule: bisim_coinduct_upto)
  unfolding sim_def scomp_op_def
  apply (intro conjI allI impI)
  subgoal for io op
    apply (subst (asm) comp_op_code)
    apply auto
    subgoal 
      apply (subst (asm) bind_op.code)
      apply auto
      subgoal for x
        apply hypsubst_thin
        apply (intro exI conjI)
         apply (rule step_map_op)
          apply (subst comp_op_code)
          apply simp
          apply (rule step.intros)
           apply (rule cinsertI1)
          apply (subst bind_op.code)
          apply auto
          apply (rule step.intros)
         apply simp
        apply (rule bc_bisim)
        using scomp_op_example_1[unfolded scomp_op_def] apply simp
        done
      done
    subgoal 
      apply (subst (asm) bind_op.code)
      apply auto
      subgoal
        apply (subst (asm) bind_op.code)
        apply auto
        subgoal
          apply (subst (asm) bind_op.code)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule step_map_op)
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI2)
             apply (rule refl)
            apply (subst bind_op.code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI1)
            apply (subst bind_op.code)
            apply auto
            apply (rule step.intros)
           apply auto
          apply (rule bc_refl)
          apply auto
          done
        subgoal
          apply (subst (asm) bind_op.code)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule step_map_op)
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI1)
             apply (rule refl)
            apply (subst bind_op.code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
           apply auto
          apply (rule bc_refl)
          apply auto
          done
        done
      subgoal
        apply (subst (asm) bind_op.code)
        apply auto
        subgoal
          apply (subst (asm) bind_op.code)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule step_map_op)
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI1)
             apply (rule refl)
            apply (subst bind_op.code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI1)
            apply (subst bind_op.code)
            apply auto
            apply (rule step.intros)
           apply auto
          apply (rule bc_refl)
          apply auto
          done
        subgoal
          apply (subst (asm) bind_op.code)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule step_map_op)
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI2)
             apply (rule refl)
            apply (subst bind_op.code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
           apply auto
          apply (rule bc_refl)
          apply auto
          done
        done
      done
    done
subgoal for io op
    apply (subst (asm) comp_op_code)
    apply auto
    subgoal 
      apply (subst (asm) bind_op.code)
      apply auto
      subgoal for x
        apply hypsubst_thin
        apply (intro exI conjI)
         apply (rule step_map_op)
          apply (subst comp_op_code)
          apply simp
          apply (rule step.intros)
           apply (rule cinsertI1)
          apply (subst bind_op.code)
          apply auto
          apply (rule step.intros)
         apply simp
        apply (rule bc_bisim)
        using scomp_op_example_1[unfolded scomp_op_def] 
        apply (simp add: bisim_sym)
        done
      done
    subgoal 
      apply (subst (asm) bind_op.code)
      apply auto
      subgoal
        apply (subst (asm) bind_op.code)
        apply auto
        subgoal
          apply (subst (asm) bind_op.code)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule step_map_op)
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI2)
             apply (rule refl)
            apply (subst bind_op.code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI1)
            apply (subst bind_op.code)
            apply auto
            apply (rule step.intros)
           apply auto
          apply (rule bc_refl)
          apply auto
          done
        subgoal
          apply (subst (asm) bind_op.code)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule step_map_op)
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI1)
             apply (rule refl)
            apply (subst bind_op.code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
           apply auto
          apply (rule bc_refl)
          apply auto
          done
        done
      subgoal
        apply (subst (asm) bind_op.code)
        apply auto
        subgoal
          apply (subst (asm) bind_op.code)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule step_map_op)
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI1)
             apply (rule refl)
            apply (subst bind_op.code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI1)
            apply (subst bind_op.code)
            apply auto
            apply (rule step.intros)
           apply auto
          apply (rule bc_refl)
          apply auto
          done
        subgoal
          apply (subst (asm) bind_op.code)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule step_map_op)
            apply (subst comp_op_code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
             apply simp
             apply (rule disjI2)
             apply (rule refl)
            apply (subst bind_op.code)
            apply simp
            apply (rule step.intros)
             apply (rule cinsertI2)
             apply (subst bind_op.code)
             apply auto
            apply (rule step.intros)
           apply auto
          apply (rule bc_refl)
          apply auto
          done
        done
      done
    done
  done


abbreviation "read_or_write \<equiv> Choice {| Read (1::2) (\<lambda> _. end_op), Write (Read (2::2) (\<lambda> _. end_op)) (1::1) (1::nat) |}"

lemma example_1:
  "read_or_write \<bullet> ((end_op :: (1, 1, nat) op) \<bullet> (Write end_op (1::1) 1)) ~ read_or_write \<bullet> (end_op :: (1, 1, nat) op) \<bullet> (Write end_op (1::1) 1)"
  apply (coinduction rule: bisim_coinduct_upto)
  unfolding sim_def scomp_op_def
  apply (intro impI allI conjI)
  subgoal
    apply (subst (asm) comp_op_code)
    apply auto
    subgoal
      apply (subst (asm) bind_op.code)
      apply auto
      subgoal
        apply (subst (asm) bind_op.code)
        apply auto
        apply hypsubst_thin
        subgoal for x
          apply (intro conjI exI)
           apply (rule step_map_op)
            apply (subst (2) comp_op_code)
            apply simp
            apply (rule step.intros(3))
             apply (rule cinsertI1)
            apply (subst bind_op.code)
            apply (subst (5) comp_op_code)
            apply auto
            apply (rule step.intros(3))
             apply (rule cinsertI1)
            apply (subst bind_op.code)
            apply (subst bind_op.code)
            apply simp
            apply (rule step.intros(3))
             apply (rule cinsertI1)
            apply (subst (1) bind_op.code)
            apply (subst (1) bind_op.code)
            apply simp
            apply (rule step.intros(1))
           apply auto[1]
          apply (rule bc_bisim)
          sorry
        done
      subgoal
        apply (subst (asm) bind_op.code)
        apply auto
        apply (subst (asm) comp_op_code)
        apply auto
         apply (subst (asm) bind_op.code)
         apply auto
        subgoal 
          apply hypsubst_thin
          apply (intro conjI exI)
           apply (rule step_map_op)
            apply (subst (2) comp_op_code)
            apply simp
            apply (rule step.intros(3))
             apply (rule cinsertI1)
            apply (subst bind_op.code)
            apply (subst (5) comp_op_code)
            apply auto
            apply (rule step.intros(3))
             apply (rule cinsertI1)
            apply (subst bind_op.code)
            apply (subst bind_op.code)
            apply simp
            apply (rule step.intros(3))
             apply (rule cinsertI2)
             apply (subst (1) bind_op.code)
             apply (subst (1) bind_op.code)
             apply simp
            apply (subst (5) comp_op_code)
            apply simp
            apply (rule step.intros(3))
             apply simp
             apply (rule disjI1)
             apply (rule refl)
            apply (subst (1) bind_op.code)
            apply (subst (1) bind_op.code)
            apply simp
            apply (rule step.intros(1))
           apply simp
          apply (rule bc_bisim)
          sorry
        subgoal
          apply (subst (asm) bind_op.code)
          apply (subst (asm) (7) comp_op_code)
          apply auto
           apply (subst (asm) bind_op.code)
           apply (subst (asm) bind_op.code)
           apply auto
          apply (subst (asm) bind_op.code)
          apply (subst (asm) bind_op.code)
          apply auto
          apply hypsubst_thin
          apply (intro conjI exI)
           apply (rule step_map_op)
            apply (subst (2) comp_op_code)
            apply simp
            apply (rule step.intros(3))
             apply simp
             apply (rule disjI1)
             apply (rule refl)
            apply (subst (1) bind_op.code)
            apply (subst (5) comp_op_code)
            apply simp
            apply (rule step.intros(3))
             apply simp
             apply (rule disjI1)
             apply (rule refl)
            apply (subst (1) bind_op.code)
            apply (subst (1) bind_op.code)
            apply simp
            apply (rule step.intros(3))
             apply simp
             apply (rule disjI2)
             apply (rule refl)
            apply (subst (1) bind_op.code)
            apply (subst (1) bind_op.code)
            apply simp
            apply (subst (5) comp_op_code)
            apply simp
            apply (rule step.intros(3))
             apply simp
             apply (rule disjI2)
             apply (rule refl)
            apply (subst (1) bind_op.code)
            apply (subst (1) bind_op.code)
            apply simp
          oops



