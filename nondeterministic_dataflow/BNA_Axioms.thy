section \<open>The BNA Axioms\<close>
  \<comment> \<open>The basic operators - except compositions, loop and fair merge- from the BNA book "Network Algebra for Synchronous and Asynchronous Dataflow" (https://staff.fnwi.uva.nl/c.a.middelburg/papers/P9508.pdf) \<close>
  \<comment> \<open>Here we list most of the axioms from Table 1, and Table 4\<close>
theory BNA_Axioms

imports
  BNA_Operators
  Loop
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom B1: Associativity of parallel composition\<close>
\<comment> \<open>TODO\<close>

section \<open>Axiom B2: Neutral element of parallel composition\<close>
\<comment> \<open>TODO\<close>

section \<open>Axiom B3: Associativity of sequential composition\<close>
lemma step_scomp_op_1:
  "step io (map_op projl projr (comp_op Some (buf1 :: 'd \<Rightarrow> 'c buf) op1 (map_op projl projr (comp_op Some (buf2 :: 'e \<Rightarrow> 'c buf) op2 op3)))) op \<Longrightarrow>
   \<exists> op1' op2' op3' (buf1' :: 'd \<Rightarrow> 'c buf) (buf2' :: 'e \<Rightarrow> 'c buf). op = map_op projl projr (comp_op Some buf1' op1' (map_op projl projr (comp_op Some buf2' op2' op3'))) \<and>
   step io (map_op projl projr (comp_op Some buf2 (map_op projl projr (comp_op Some buf1 op1 op2)) op3)) (map_op projl projr (comp_op Some buf2' (map_op projl projr (comp_op Some buf1' op1' op2')) op3'))"
  apply (induct "map_op projl projr (comp_op Some buf1 op1 (map_op projl projr (comp_op Some buf2 op2 op3)))" op arbitrary: op1 op2 op3 buf1 buf2 pred: step)
     apply (subst (asm) comp_op_code, simp)
    apply (subst (asm) comp_op_code, simp)
   apply (subst (asm) comp_op_code, simp)
  subgoal for op ops io op' op1 op2 op3 buf1 buf2
    apply (subst (asm) (9) comp_op_code)
    apply clarsimp
    apply hypsubst_thin
    subgoal for op''
      apply (elim disjE)
      subgoal
        apply clarsimp
        subgoal for op1
          apply (cases op1)
          subgoal for p f
            apply clarsimp
            apply (erule thin_rl)
            apply hypsubst_thin
            apply (intro exI conjI)
             apply (rule refl)
            apply (subst (2) comp_op_code)
            apply (rule step_map_op)
             apply (rule SC[rotated])
              apply (rule SR)
             apply simp
             apply (rule disjI1)
             apply (rule image_eqI[rotated])
              apply (subst comp_op_code)
              apply simp
              apply (rule disjI1)
              apply (rule bexI[rotated])
               apply simp
              apply fastforce+
            done
          subgoal for op1' p x
            apply clarsimp
            apply (erule thin_rl)
            apply hypsubst_thin
            apply (intro exI conjI)
             apply (rule refl)
            apply (subst (2) comp_op_code)
            apply (rule step_map_op)
             apply (rule SC[rotated])
              apply (rule ST)
             apply simp
             apply (rule disjI1)
             apply (rule image_eqI[rotated])
              apply (subst comp_op_code)
              apply simp
              apply (rule disjI1)
              apply (rule bexI[rotated])
               apply simp
              apply fastforce+
            done
          subgoal for ops
            by clarsimp
          subgoal
            apply clarsimp
            apply (erule thin_rl)
            apply hypsubst_thin
            apply (intro exI conjI)
             apply (rule refl)
            apply (subst (2) comp_op_code)
            apply (rule step_map_op)
             apply (rule SC)
              apply simp
              apply (rule disjI1)
              apply (rule image_eqI[rotated])
               apply (subst comp_op_code)
               apply simp
               apply (rule disjI1)
               apply (rule bexI[rotated])
                apply simp
               apply force+
            done
          done
        done
      subgoal
        apply clarsimp
        subgoal for op23
          apply (cases op23)
          subgoal for p f
            apply clarsimp
            apply (erule thin_rl)
            apply hypsubst_thin
            apply (subst (asm) comp_op_code)
            apply auto
            subgoal for op2
              apply (cases op2)
              subgoal
                apply (intro exI conjI)
                 apply auto
                apply hypsubst_thin
                apply (subst (2) comp_op_code)
                apply (rule step_map_op)
                 apply (rule SC[rotated])
                  apply (rule ST)
                 apply simp
                 apply (rule disjI1)
                 apply (rule image_eqI[rotated])
                  apply (subst comp_op_code)
                  apply simp
                  apply (rule disjI2)
                  apply (rule bexI[rotated])
                   apply simp
                   apply fastforce+
                done
              subgoal by auto
              subgoal by auto
              subgoal by auto
              done
            subgoal for op3
              apply (cases op3)
                 apply auto
              done
            done
          subgoal for op23' p x
            apply clarsimp
            apply (erule thin_rl)
            apply hypsubst_thin
            apply (subst (asm) comp_op_code)
            apply auto
            subgoal for op2
              apply (cases op2)
                 apply auto
              done
            subgoal for op3
              apply (cases op3)
                 apply auto
              apply hypsubst_thin
              apply (intro exI conjI)
               apply (rule refl)
              apply (subst (2) comp_op_code)
              apply (rule step_map_op)
               apply (rule SC)
                apply simp
                apply (rule disjI2)
                apply (rule image_eqI[rotated])
                 apply simp
                 apply force
                apply simp_all
               apply (rule SW)
              apply auto
              done
            done
          subgoal
            by clarsimp
          subgoal for op'
            apply clarsimp
            apply (erule thin_rl)
            apply hypsubst_thin
            apply (subst (asm) comp_op_code)
            apply auto
            subgoal for op2'
              apply (cases op2')
                 apply auto
              subgoal
                apply hypsubst_thin
                apply (intro exI conjI)
                 apply (rule refl)
                apply (subst (2) comp_op_code)
                apply (rule step_map_op[of Tau])
                 apply (rule SC)
                  apply simp
                  apply (rule disjI1)
                  apply (rule image_eqI[rotated])
                   apply (subst comp_op_code)
                   apply simp_all
                 apply (rule disjI2)
                 apply (intro bexI)
                  apply (auto intro: ST)
                done
              subgoal for op2'
                apply hypsubst_thin
                apply (intro exI conjI)
                 apply (rule refl)
                apply (subst (2) comp_op_code)
                apply (rule step_map_op[of Tau])
                 apply (rule SC)
                  apply simp
                  apply (rule disjI1)
                  apply (rule image_eqI[rotated])
                   apply (subst comp_op_code)
                   apply simp_all
                 apply (rule disjI2)
                 apply (intro bexI)
                  apply (auto intro: ST)
                done
              done
            subgoal for op3'
              apply (cases op3')
                 apply auto
              subgoal for p f
                apply hypsubst_thin
                apply (intro exI conjI)
                 apply (rule refl)
                apply (subst (2) comp_op_code)
                apply (rule step_map_op[of Tau])
                 apply (rule SC)
                  apply simp
                  apply (rule disjI2)
                  apply (rule image_eqI[rotated])
                   apply force
                  apply simp_all
                apply (auto intro: ST)
                done
              subgoal
                apply hypsubst_thin
                apply (intro exI conjI)
                 apply (rule refl)
                apply (subst (2) comp_op_code)
                apply (rule step_map_op[of Tau])
                 apply (rule SC)
                  apply simp
                  apply (rule disjI2)
                  apply (rule image_eqI[rotated])
                   apply force
                  apply simp_all
                apply (auto intro: ST)
                done
              done
            done
          done
        done
      done
    done
  done

lemma step_scomp_op_2:
  "step io (map_op projl projr (comp_op Some (buf2 :: 'e \<Rightarrow> 'c buf) (map_op projl projr (comp_op Some (buf1 :: 'd \<Rightarrow> 'c buf) op1 op2)) op3)) op \<Longrightarrow>
   \<exists> op1' op2' op3' (buf1' :: 'd \<Rightarrow> 'c buf) (buf2' :: 'e \<Rightarrow> 'c buf). op = map_op projl projr (comp_op Some buf2' (map_op projl projr (comp_op Some buf1' op1' op2')) op3') \<and>
   step io (map_op projl projr (comp_op Some buf1 op1 (map_op projl projr (comp_op Some buf2 op2 op3)))) (map_op projl projr (comp_op Some buf1' op1' (map_op projl projr (comp_op Some buf2' op2' op3'))))"
  apply (induct "map_op projl projr (comp_op Some buf2 (map_op projl projr (comp_op Some buf1 op1 op2)) op3)" op arbitrary: op1 op2 op3 buf1 buf2 pred: step)
     apply (subst (asm) (2) comp_op_code, simp)
    apply (subst (asm) (2) comp_op_code, simp)
   apply (subst (asm) (2) comp_op_code, simp)
  subgoal for op ops io op' op1 op2 op3 buf1 buf2
    apply (subst (asm) (10) comp_op_code)
    apply clarsimp
    apply hypsubst_thin
    subgoal for op''
      apply (elim disjE)
      subgoal
        apply clarsimp
        subgoal for op12
          apply (cases op12)
          subgoal for p f
            apply clarsimp
            apply (erule thin_rl)
            apply hypsubst_thin
            apply (subst (asm) comp_op_code)
            apply auto
            subgoal for op1 op1'
              apply (cases op1')
              subgoal
                apply (intro exI conjI)
                 apply auto
                apply hypsubst_thin
                apply (subst (1) comp_op_code)
                apply (rule step_map_op)
                 apply (rule SC[rotated])
                  apply (rule SR)
                 apply simp
                 apply (rule disjI1)
                 apply (rule image_eqI[rotated])
                  apply simp
                 apply auto
                done
                apply auto
              done
            subgoal for op2 op2'
              apply (cases op2')
                 apply auto
              done
            done
          subgoal for op12' p x
            apply auto
            apply (erule thin_rl)
            apply hypsubst_thin
            apply (subst (asm) comp_op_code)
            apply auto
            subgoal for op1'
              apply (cases op1')
                 apply auto
              done
            subgoal for op1'
              apply (cases op1')
                 apply auto
              apply hypsubst_thin
              apply (intro exI conjI)
               apply auto
              apply (subst (1) comp_op_code)
              apply (rule step_map_op)
               apply (rule SC[rotated])
                apply (rule ST)
               apply simp_all
              apply simp
              apply (rule disjI2)
              apply (rule image_eqI[rotated])
               apply simp_all
               apply (subst (1) comp_op_code)
               apply simp
               apply (intro exI conjI)
                apply (rule disjI1)
                apply force
               apply simp_all
              apply (metis fun_upd_apply)
              done
            done
          subgoal
            by auto
          subgoal
            apply clarsimp
            apply (erule thin_rl)
            apply hypsubst_thin
            apply (subst (asm) comp_op_code)
            apply auto
            subgoal for op1'
              apply (cases op1')
              subgoal
                by auto
              subgoal for op1'' p x
                apply (intro exI conjI)
                 apply simp_all
                apply (subst (1) comp_op_code)
                apply simp
                apply (rule SC)
                 apply simp_all
                 apply force
                apply simp
                apply (rule ST)
                done
              subgoal
                by auto
              subgoal for op1'''
                apply simp
                apply hypsubst_thin
                apply (intro exI conjI)
                 apply simp_all
                apply (subst (1) comp_op_code)
                apply simp
                apply (rule SC)
                 apply simp_all
                 apply force
                apply simp
                apply (rule ST)
                done
              done
            subgoal for op2'
              apply (cases op2')
              subgoal for p f
                apply clarsimp
                apply hypsubst_thin
                apply (intro exI conjI)
                 apply simp_all
                apply (subst (1) comp_op_code)
                apply simp
                apply (rule SC)
                 apply simp_all
                 apply (rule image_eqI[rotated])
                  apply simp
                  apply (rule disjI2)
                  apply (rule image_eqI[rotated])
                   apply (subst (1) comp_op_code)
                   apply simp
                   apply (intro conjI)
                    apply (rule disjI1)
                    apply force
                   apply simp_all
                apply simp
                apply (rule ST)
                done
              subgoal
                by auto
              subgoal
                by auto
              subgoal
                apply clarsimp
                apply hypsubst_thin
                apply (intro exI conjI)
                 apply simp_all
                apply (subst (1) comp_op_code)
                apply simp
                apply (rule SC)
                 apply simp_all
                 apply (rule image_eqI[rotated])
                  apply simp
                  apply (rule disjI2)
                  apply simp_all
                 apply (rule image_eqI[rotated])
                  apply (subst (1) comp_op_code)
                  apply simp
                  apply (intro conjI)
                   apply (rule disjI1)
                   apply force
                  apply simp_all
                apply simp
                apply (rule ST)
                done
              done
            done
          done
        done
      subgoal
        apply auto
        subgoal for op3'
          apply (cases op3')
             apply auto
          subgoal
            apply (erule thin_rl)
            apply hypsubst_thin
            apply (intro exI conjI)
             apply simp_all
            apply (subst (1) comp_op_code)
            apply simp
            apply (rule SC)
             apply simp_all
             apply (rule image_eqI[rotated])
              apply simp
              apply (rule disjI2)
              apply (rule image_eqI[rotated])
               apply (subst (1) comp_op_code)
               apply simp
               apply (intro conjI)
                apply (rule disjI2)
                apply force
               apply simp_all
            apply simp
            apply (rule ST)
            done
          subgoal
            apply (erule thin_rl)
            apply hypsubst_thin
            apply (intro exI conjI)
             apply simp_all
            apply (subst (1) comp_op_code)
            apply simp
            apply (rule SC)
             apply simp_all
             apply (rule image_eqI[rotated])
              apply simp
              apply (rule disjI2)
              apply (rule image_eqI[rotated])
               apply (subst (1) comp_op_code)
               apply simp
               apply (intro conjI)
                apply (rule disjI2)
                apply force
               apply auto
            done
          subgoal
            apply (erule thin_rl)
            apply hypsubst_thin
            apply (intro exI conjI)
             apply simp_all
            apply (subst (1) comp_op_code)
            apply simp
            apply (rule SC)
             apply simp_all
             apply (rule image_eqI[rotated])
              apply simp
              apply (rule disjI2)
              apply (rule image_eqI[rotated])
               apply (subst (1) comp_op_code)
               apply simp
               apply (intro conjI)
                apply (rule disjI2)
                apply force
               apply simp_all
            apply simp
            apply (rule ST)
            done
          done
        done
      done
    done
  done

lemma scomp_op_assoc_gen:
  "map_op projl projr (comp_op Some buf1 op1 (map_op projl projr (comp_op Some buf2 op2 op3))) ~
   map_op projl projr (comp_op Some buf2 (map_op projl projr (comp_op Some buf1 op1 op2)) op3)"
  apply (coinduction arbitrary: op1 op2 op3 buf1 buf2 rule: bisim_coinduct_upto)
  subgoal for op1 op2 op3 buf1 buf2
    apply (intro conjI)
    subgoal
      unfolding sim_def
      apply safe
      subgoal for io op
        apply (drule step_scomp_op_1)
        apply auto
        apply hypsubst_thin
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
         apply auto
        apply fast
        done
      done
    subgoal
      unfolding sim_def
      apply safe
      subgoal for io op
        apply (drule step_scomp_op_2)
        apply auto
        apply hypsubst_thin
        apply (intro conjI[rotated] exI)
         apply (rule bc_sym)
         apply (rule bc_base)
         apply auto
        apply blast
        done
      done
    done
  done

lemma scomp_op_assoc:
  "op1 \<bullet> op2 \<bullet> op3 ~ op1 \<bullet> (op2 \<bullet> op3)"
  unfolding scomp_op_def using scomp_op_assoc_gen
  using bisim_sym by blast

section \<open>Axiom B4: Neutral element of sequential composition\<close>
lemma id_id_gen:
  "map_op projl projr (comp_op Some buf2 (id_op buf1) (id_op buf3)) \<approx> id_op (buf1 >> buf2 >> buf3)"
  apply (coinduction arbitrary: buf1 buf2 buf3 rule: wbisim_coinduct_upto)
  subgoal for buf1 buf2 buf3
    unfolding wsim_def
    apply auto
    subgoal for io op
      apply (drule step_map_op_inv)
      apply safe
      apply hypsubst_thin
      subgoal for io' op'
        apply (drule step_comp_op_Some_id_op_id_op)
          apply (rule refl)+
        apply simp
        apply (elim disjE exE conjE)
        subgoal for p x buf1' buf2' buf3'
          apply hypsubst_thin
          apply (intro conjI exI)
           apply (subst id_op_code)
           apply (rule step_wstep)
           apply (rule SC[rotated])
            apply simp
            apply (rule SR)
           apply simp
           apply (rule disjI1)
           apply (rule image_eqI)
            apply (rule refl)
           apply simp
          apply (rule wbc_base)
          apply (intro conjI exI)
           apply (rule refl)
          apply (rule arg_cong[where f=id_op])
          apply (rule ext)
          apply simp
          apply metis
          done
        subgoal for p x buf1' buf2' buf3'
          apply hypsubst_thin
          apply simp
          apply (intro conjI exI)
           apply (subst id_op_code)
           apply (rule step_wstep)
           apply (rule SC[rotated])
            apply (rule SW)
           apply simp
           apply (rule disjI2)
           apply (rule image_eqI)
            apply force
           apply (simp add: cUNIV.rep_eq)
          apply (rule wbc_base)
          apply (intro conjI exI)
           apply (rule refl)
          apply (rule arg_cong[where f=id_op])
          apply (rule ext)
          apply simp
          done
        subgoal for p buf1' buf2' buf3'
          apply hypsubst_thin
          apply (intro conjI exI)
          unfolding wstep_def
           apply simp
           apply (rule disjI2)
           apply (rule relcomppI[rotated])
            apply (rule relcomppI[rotated])
             apply (rule rtranclp.intros(1))
            apply (rule refl)
           apply (rule rtranclp.intros(1))
          apply (rule wbc_base)
          apply (intro conjI exI)
           apply (rule refl)
          apply (rule arg_cong[where f=id_op])
          apply auto
          done
        subgoal for p buf1' buf2' buf3'
          apply hypsubst_thin
          apply (intro conjI exI)
          unfolding wstep_def
           apply simp
           apply (rule disjI2)
           apply (rule relcomppI[rotated])
            apply (rule relcomppI[rotated])
             apply (rule rtranclp.intros(1))
            apply (rule refl)
           apply (rule rtranclp.intros(1))
          apply (rule wbc_base)
          apply (intro conjI exI)
           apply (rule refl)
          apply (rule arg_cong[where f=id_op])
          apply auto
          done
        done
      done
    subgoal for io op1'
      apply (cases io)
      subgoal for p x
        apply hypsubst_thin
        apply (drule step_id_op_Inp)
         apply simp
        apply hypsubst_thin
        apply (rule exI[of _ "map_op projl projr (comp_op Some buf2 (id_op (BENQ p x buf1)) (id_op buf3))"])
        apply (intro conjI)
        subgoal
          apply (rule wstep_map_op)
           apply (rule step_wstep)
           apply (subst comp_op_code)
           apply (rule SC)
            apply (rule cUnI1)
            apply (rule cimage_eqI)
             apply simp
            apply simp
            apply (rule disjI1)
            apply (rule exI)
            apply (rule refl)
           apply simp
           apply (rule SR)
          apply auto
          done
        subgoal
          apply (rule wbc_sym)
          apply (rule wbc_base)
          apply (intro conjI exI)
           apply (rule refl)
          apply (rule arg_cong[where f=id_op])
          apply auto
          done
        done
      subgoal for p x
        apply hypsubst_thin
        apply (drule step_id_op_Out)
         apply simp
        apply (elim conjE)
        apply (drule BHD_BAPPEND_2_cases)
         apply simp
        apply hypsubst_thin
        apply (elim exE disjE conjE)
        subgoal
          apply (rule exI[of _ "map_op projl projr (comp_op Some buf2 (id_op buf1) (id_op (BTL p buf3)))"])
          apply (intro conjI)
          subgoal
            apply (rule wstep_map_op[where f=projl and g=projr and io="Out (Inr p) x", simplified])
             apply (subst comp_op_code)
             apply simp
             apply (rule step_wstep)
             apply (rule SC)
              apply (simp add: Set.filter_def)
              apply (rule disjI2)
              apply simp
              apply (rule image_eqI)
               apply (rule refl)
              apply (simp add: cUNIV.rep_eq)
              apply (intro conjI)
               apply (rule disjI2)
               apply (intro conjI exI)
                apply assumption
               apply (rule refl)
              apply (auto simp add: step.intros(2))
            done
          subgoal
            apply (rule wbc_sym)
            apply (rule wbc_base)
            apply (intro exI conjI) 
             apply (rule refl)
            apply (rule arg_cong[where f=id_op])
            apply (rule ext)
            apply (auto simp only: split: if_splits)
              apply (smt (verit, best) fun_upd_apply tl_append2)+
            done
          done
        subgoal
          apply (rule exI[of _ "map_op projl projr (comp_op Some (BTL p buf2) (id_op buf1) (id_op buf3))"])
          apply (intro conjI)
          subgoal
            apply (rule wstep_map_op[where f=projl and g=projr and io="Out (Inr p) x", simplified])
             apply simp_all
            apply (rule step_tau_step_io_wstep[of _ "comp_op Some (BTL p buf2) (id_op buf1) (id_op (BENQ p x buf3))"])
             apply (subst comp_op_code)
             apply simp
             apply (rule SC[rotated])
              apply (rule ST)
             apply simp
             apply (rule disjI2)
             apply simp
             apply (rule image_eqI[rotated])
              apply (simp add: Set.filter_def)
              apply (intro conjI)
               apply (rule disjI1)
               apply (intro exI conjI)
               apply (rule refl)
              apply simp_all
             apply simp
            apply (subst comp_op_code)
            apply (rule SC[rotated])
             apply (rule SW)
            apply simp
            apply (rule disjI2)
            apply (rule image_eqI[rotated])
             apply (simp add: Set.filter_def)
             apply (intro conjI)
              apply (rule disjI2)
              apply (intro exI conjI)
               apply blast+
             apply simp_all
            apply (metis fun_upd_idem_iff)
            done
          subgoal
            apply (rule wbc_sym)
            apply (rule wbc_base)
            apply (intro conjI exI)
             apply (rule refl)
            apply (rule arg_cong[where f=id_op])
            apply auto
            done
          done
        subgoal
          apply (rule exI[of _ "map_op projl projr (comp_op Some buf2 (id_op (BTL p buf1)) (id_op buf3))"])
          apply (intro conjI)
          subgoal
            apply (rule wstep_map_op[where f=projl and g=projr and io="Out (Inr p) x", simplified])
             apply simp_all
            apply (rule step_tau_step_tau_step_io_wstep[of _ "comp_op Some (BENQ p x buf2) (id_op (BTL p buf1)) (id_op buf3)" "comp_op Some (BTL p (BENQ p x buf2)) (id_op (BTL p buf1)) (id_op (BENQ p x buf3))"])
              apply (subst comp_op_code)
              apply simp
              apply (rule SC[rotated])
               apply (rule ST)
              apply simp
              apply (rule disjI1)
              apply simp
              apply (rule image_eqI[rotated])
               apply (simp add: Set.filter_def)
               apply (rule disjI2)
               apply (intro exI conjI)
                apply simp_all
              apply simp
             apply (subst comp_op_code)
             apply (rule SC[rotated])
              apply (rule ST)
             apply simp
             apply (rule disjI2)
             apply (rule image_eqI[rotated])
              apply (simp add: Set.filter_def)
              apply (intro conjI)
               apply (rule disjI1)
               apply (intro conjI exI)
               apply (rule refl)
              apply simp
              apply blast
             apply simp
            apply (subst comp_op_code)
            apply simp
            apply (rule SC[rotated])
             apply (rule SW)
            apply simp
            apply (simp add: Set.filter_def)          
            apply (rule disjI2)
            apply (rule image_eqI[rotated])
             apply (simp add: Set.filter_def)
             apply (intro exI conjI)
              apply (rule disjI2)
              apply (intro exI conjI)
               apply blast
              apply simp_all
             apply blast
            apply (simp add: fun_upd_idem)
            done
          subgoal
            apply (rule wbc_sym)
            apply (rule wbc_base)
            apply (intro conjI exI)
             apply (rule refl)
            apply (rule arg_cong[where f=id_op])
            apply auto
            done
          done
        done
      subgoal
        apply (subst (asm) id_op_code)
        apply auto
        done
      done
    done
  done

subsubsection \<open>Axiom: B4\<close>
lemma scomp_op_id_id:
  "\<I> \<bullet> \<I> \<approx> \<I>"
  unfolding scomp_op_def
  using id_id_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] apply simp
  done

lemma scomp_op_id_op_right_neutral:
  "\<stileturn>op\<turnstile> \<bullet> \<I> \<approx> \<stileturn>op\<turnstile>"
  using bisim_wbisim scomp_op_assoc scomp_op_id_id wbisim_refl wbisim_scomp_op_cong wbisim_trans by blast

lemma scomp_op_id_op_right_neutral_gen:
  "op \<bullet> \<I> \<approx> op"
  oops

lemma scomp_op_id_op_left_neutral:
  "\<I> \<bullet> \<stileturn>op\<turnstile> \<approx> \<stileturn>op\<turnstile>"
  by (smt (verit, best) bisim_wbisim scomp_op_assoc scomp_op_id_id wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans)


section \<open>Axiom B5: Parallel and sequential distributes\<close>
  \<comment> \<open>TODO\<close>

section \<open>Axiom B6: Parallel composition of identities\<close>
lemma pcomp_op_id_id:
  "\<I> \<parallel> \<I> ~ \<I>"
  oops

section \<open>Axiom B7: Transpose of transpose is identity\<close>
lemma scomp_op_transp_transp:
  "\<X> \<bullet> \<X> \<approx> \<X>"
  oops

section \<open>Axiom B9: Transpose decomposes in parallel and sequential composition\<close>
lemma trans_op_decomposes_scomp_op_pcomp_op:
  assumes "\<X>klm = (\<X> :: ('k :: countable + 'l :: countable + 'm :: countable, ('l + 'm) + 'k, 'c) op)"
  and "\<X>kl = (\<X> :: ('k + 'l, 'l + 'k, 'c) op)"
  and "\<X>km = (\<X> :: ('k + 'm, 'm + 'k, 'c) op)"
  and "\<I>m = (\<I> :: ('m, 'm, 'c) op)"
  and "\<I>l = (\<I> :: ('l, 'l, 'c) op)"
shows "\<X>klm \<approx> map_op reassoc reassoc (\<X>kl \<parallel> \<I>m) \<bullet> map_op id assoc (\<I>l \<parallel> \<X>km)"
  oops

section \<open>Axiom B10: Transpose commutes with sequential composition of parallel operators\<close>
lemma transp_op_commutes_scomp_op_pcomp_op:
 "(op1 \<parallel> op2) \<bullet> \<X> = \<X> \<bullet> (op2 \<parallel> op1)"
  oops

section \<open>Axiom: R1: Loop absorb\<close>
lemma loop_op_absorb:
  "op2 \<bullet> (op1\<up>) ~ ((op2 \<parallel> \<I>) \<bullet> op1)\<up>"
  oops

section \<open>Axiom: R2: Loop distribute scomp_op\<close>
lemma loop_op_distribute_scomp_op:
  "(op1\<up>) \<bullet> op2 ~ (op1 \<bullet> (op2 \<parallel> \<I>))\<up>"
  oops

section \<open>Axiom: R3: Parallel loop\<close>
lemma loop_op_parallel:
  "op1 \<parallel> (op2\<up>) ~ (map_op assoc assoc (op1 \<parallel> op2))\<up>"
  oops

section \<open>Axiom: R4: Loop commutes sequential composition\<close>
lemma loop_op_commutes_scomp_op:
  "(op1 \<bullet> (\<I> \<parallel> op2))\<up> ~ ((\<I> \<parallel> op2) \<bullet> op1)\<up>"
  oops

section \<open>Axiom: R5: Loop with no loop\<close>
lemma loop_op_no_loop:
  "loop_op (\<lambda> _. None) buf op = op"
  oops

section \<open>Axiom: R6: Loop absorb\<close>
lemma loop_op_absorb:
  "(op\<up>)\<up> = (map_op reassoc reassoc op)\<up>"
  oops

end