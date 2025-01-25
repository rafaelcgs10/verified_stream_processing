\<comment> \<open>Axioms from Table 1 for BNA operators\<close>
theory BNA_Axioms

imports
  BNA_Operators
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom B1: Associativity of parallel composition\<close>
lemma pcomp_op_assoc:
 "bisim (pcomp_op op1 (pcomp_op op2 op3)) (map_op reassoc reassoc (pcomp_op (pcomp_op op1 op2) op3))"
  oops

  section \<open>Axiom B2: Neutral element of parallel composition\<close>
lemma pcomp_op_end_op_right_neutral:
  "map_op projl projl (op \<parallel> \<oslash>) ~ op"
  oops
lemma pcomp_op_end_op_left_neutral:
  "map_op projr projr (\<oslash> \<parallel> op) ~ op"
  oops

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
lemma step_comp_op_Some_id_op_id_op:
  "step io (comp_op Some buf2 op1 op2) op \<Longrightarrow>
   op1 = id_op buf1 \<Longrightarrow>
   op2 = id_op buf3 \<Longrightarrow>
   (\<exists> p x. io = Inp (Inl p) x \<and>
     (\<exists> buf1' buf2' buf3'. op = comp_op Some buf2' (id_op (BENQ p x buf1')) (id_op buf3') \<and>
      buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3')) \<or>

   (\<exists> p x. io = Out (Inr p) x \<and>
     (\<exists> buf1' buf2' buf3'. op = comp_op Some buf2' (id_op buf1') (id_op (BTL p buf3')) \<and> BHD p buf3' = x \<and> buf3' p \<noteq> [] \<and>
     buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3')) \<or>

   (\<exists> p x. io = Tau \<and>
     (\<exists> buf1' buf2' buf3'. op = comp_op Some (BTL p buf2') (id_op buf1') (id_op (BENQ p x buf3')) \<and> BHD p buf2' = x \<and> buf2' p \<noteq> [] \<and>
     buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3')) \<or>

   (\<exists> p x. io = Tau \<and>
     (\<exists> buf1' buf2' buf3'. op = comp_op Some (BENQ p x buf2') (id_op (BTL p buf1')) (id_op buf3') \<and> BHD p buf1' = x \<and> buf1' p \<noteq> [] \<and>
     buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3'))"
  apply (induction io "comp_op Some buf2 op1 op2" op arbitrary: op1 op2 buf1 buf2 buf3 rule: step.induct)
  subgoal
    apply hypsubst_thin
    apply (subst (asm) comp_op_code)
    apply auto
    done
  subgoal
    apply hypsubst_thin
    apply (subst (asm) comp_op_code)
    apply auto
    done
  subgoal
    apply hypsubst_thin
    apply (subst (asm) comp_op_code)
    apply auto
    done
  subgoal for op ops io op' op1 op2 buf2 buf1 buf3
    apply hypsubst_thin
    apply (subst (asm) (6) comp_op_code)
    apply (auto 0 0)
             apply blast+
    done
  done

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
lemma pcomp_op_scomp_distributes:
 "(op1 \<parallel> op2) \<bullet> (op3 \<parallel> op4) ~ (op1 \<bullet> op3) \<parallel> (op2 \<bullet> op4)"
  oops

section \<open>Axiom B6: Parallel composition of identities\<close>

lemma case_sum_updateL:
  \<open>(case_sum x y)(Inl a := b) = case_sum (x(a := b)) y\<close>
  by (auto split: sum.splits)

lemma case_sum_updateR:
  \<open>(case_sum x y)(Inr a := b) = case_sum x (y(a := b))\<close>
  by (auto split: sum.splits)

lemma pcomp_op_id_id_bufs:
  \<open>id_op buf1 \<parallel> id_op buf2 ~ id_op (case_sum buf1 buf2)\<close>
  apply (coinduction arbitrary: buf1 buf2 rule: bisim_coinduct_upto)
  apply (rule conjI)
  subgoal for buf1 buf2
    unfolding pcomp_op_def sim_def
    apply auto
    apply (subst (asm) comp_op_code)
    apply auto
    subgoal for p x
      apply (rule exI[of _ \<open>id_op (case_sum (BENQ p x buf1) buf2)\<close>])
      apply (rule conjI)
      subgoal
        apply (rule Read_in_choices_step)
        apply (subst (2) id_op_code)
        apply (simp add: case_sum_updateL)
        done
      subgoal
        apply (rule bc_base)
        apply (rule exI[of _ \<open>BENQ p x buf1\<close>])
        apply (rule exI[of _ buf2])
        apply simp
        done
      done
    subgoal for p
      apply (rule exI[of _ \<open>id_op (case_sum (BTL p buf1) buf2)\<close>])
      apply (rule conjI)
      subgoal
        apply (rule Write_in_choices_step)
        apply (subst (2) id_op_code)
        apply (simp add: case_sum_updateL)
        done
      subgoal
        apply (rule bc_base)
        apply (rule exI[of _ \<open>BTL p buf1\<close>])
        apply (rule exI[of _ buf2])
        apply simp
        done
      done
    subgoal for p x
      apply (rule exI[of _ \<open>id_op (case_sum buf1 (BENQ p x buf2))\<close>])
      apply (rule conjI)
      subgoal
        apply (rule Read_in_choices_step)
        apply (subst (2) id_op_code)
        apply (simp add: case_sum_updateR)
        done
      subgoal
        apply (rule bc_base)
        apply (rule exI[of _ buf1])
        apply (rule exI[of _ \<open>BENQ p x buf2\<close>])
        apply simp
        done
      done
    subgoal for p
      apply (rule exI[of _ \<open>id_op (case_sum buf1 (BTL p buf2))\<close>])
      apply (rule conjI)
      subgoal
        apply (rule Write_in_choices_step)
        apply (subst (2) id_op_code)
        apply (simp add: case_sum_updateR)
        done
      subgoal
        apply (rule bc_base)
        apply (rule exI[of _ buf1])
        apply (rule exI[of _ \<open>BTL p buf2\<close>])
        apply simp
        done
      done
    done
  subgoal for buf1 buf2
    unfolding pcomp_op_def sim_def
    apply auto
    apply (subst (asm) id_op_code)
    apply (auto split: sum.splits)
    subgoal for x p
      apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ p x buf1)) (id_op buf2)\<close>])
      apply (rule conjI)
      subgoal
        apply (rule Read_in_choices_step)
        apply (subst (2) comp_op_code)
        apply simp
        done
      subgoal
        apply (rule bc_sym)
        apply (rule bc_base)
        apply (rule exI[of _ \<open>BENQ p x buf1\<close>])
        apply (rule exI[of _ buf2])
        apply (simp add: case_sum_updateL)
        done
      done
    subgoal for x p
      apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (id_op (BENQ p x buf2))\<close>])
      apply (rule conjI)
      subgoal
        apply (rule Read_in_choices_step)
        apply (subst (2) comp_op_code)
        apply force
        done
      subgoal
        apply (rule bc_sym)
        apply (rule bc_base)
        apply (rule exI[of _ buf1])
        apply (rule exI[of _ \<open>BENQ p x buf2\<close>])
        apply (simp add: case_sum_updateR)
        done
      done
    subgoal for p
      apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL p buf1)) (id_op buf2)\<close>])
      apply (rule conjI)
      subgoal
        apply (rule Write_in_choices_step)
        apply (subst (2) comp_op_code)
        apply simp
        done
      subgoal
        apply (rule bc_sym)
        apply (rule bc_base)
        apply (rule exI[of _ \<open>BTL p buf1\<close>])
        apply (rule exI[of _ buf2])
        apply (simp add: case_sum_updateL)
        done
      done
    subgoal for p
      apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (id_op (BTL p buf2))\<close>])
      apply (rule conjI)
      subgoal
        apply (rule Write_in_choices_step)
        apply (subst (2) comp_op_code)
        apply force
        done
      subgoal
        apply (rule bc_sym)
        apply (rule bc_base)
        apply (rule exI[of _ buf1])
        apply (rule exI[of _ \<open>BTL p buf2\<close>])
        apply (simp add: case_sum_updateR)
        done
      done
    done
  done

lemma pcomp_op_id_id:
  \<open>\<I> \<parallel> \<I> ~ \<I>\<close>
  using pcomp_op_id_id_bufs[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by auto

section \<open>Axiom B7: Transpose of transpose is identity\<close>
lemma scomp_op_transp_transp_id:
  "\<X> \<bullet> \<X> \<approx> \<I>"
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


lemma case_sum_BENQ_R[simp]:
  "case_sum A (BENQ p x buf) = BENQ (Inr p) x (case_sum A buf)"
  by (auto split: sum.splits)
lemma case_sum_BTL_R[simp]:
  "case_sum A (BTL p buf) = BTL (Inr p) (case_sum A buf)"
  by (auto split: sum.splits)
lemma case_sum_BENQ_L[simp]:
  "case_sum (BENQ p x buf) A = BENQ (Inl p) x (case_sum buf A)"
  by (auto split: sum.splits)
lemma case_sum_BTL_L[simp]:
  "case_sum (BTL p buf) A = BTL (Inl p) (case_sum buf A)"
  by (auto split: sum.splits)

lemma step_id_op_Read:
  "step (Inp p x) (id_op buf) (id_op (BENQ p x buf))"
  apply (subst id_op_code)
  apply (rule SC)
   apply simp
   apply (rule disjI1)
   apply force+
  done

lemma step_id_op_Write:
  "BHD p buf = x \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow> step (Out p x) (id_op buf) (id_op (BTL p buf))"
  apply (subst id_op_code)
  apply (rule SC)
   apply simp
   apply (rule disjI2)
   apply force+
  done

(* FIXME: move me *)
lemma rtranclp_intros_1':
  "a = b \<Longrightarrow> r\<^sup>*\<^sup>* a b"
  by auto


section \<open>Axiom: R1: Loop commute sequential composition\<close>
lemma loop_op_scomp_commute_gen:
  "map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1))) \<approx>
   map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))"
  apply (coinduction arbitrary: op1 op2 buf2 lbuf1 lbuf2 lbuf3 rule: wbisim_coinduct_upto)
  subgoal for op1 op2 buf2 lbuf1 lbuf2 lbuf3
    unfolding wsim_def
    apply auto
    subgoal for io op'
      apply (drule step_map_op_inv)
      apply safe
      apply hypsubst_thin
      apply (drule step_comp_op_cases)
      subgoal for io op''
        apply auto
        subgoal for p x op2'
          apply hypsubst_thin
          apply (intro exI conjI)
           apply (rule step_wstep)
           apply (rule step_map_op[of "Inp (Inl p) x"])
            apply (rule step_Inp_Inl_loop_op)
            apply (rule step_map_op[of "Inp (Inl (Inl p)) x"])
             apply (rule step_comp_op_L_Inp)
             apply (rule step_comp_op_L_Inp)
             apply assumption
            apply simp_all
          apply (rule wbc_base)
          apply fast
          done
        subgoal for p x op2'
          apply hypsubst_thin
          apply (drule step_map_op_inv)
          apply auto
          subgoal for io' op''
            apply hypsubst_thin
            apply (cases io')
              apply auto
            subgoal for lp
              apply hypsubst_thin
              apply (drule step_loop_op)
              apply auto
              subgoal for p op''
                apply hypsubst_thin
                apply (intro exI conjI)
                 apply (rule step_wstep)
                 apply (rule step_map_op[of "Out (Inl p) x"])
                  apply (rule step_Out_Inl_loop_op)
                  apply (rule step_map_op[of "Out (Inr (Inl p)) x"])
                   apply (rule step_comp_op_R_Out)
                   apply assumption
                  apply simp_all
                apply (rule wbc_base)
                apply fast
                done
              done
            done
          done
        subgoal for p x op2'
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule wbc_base)
           apply fast
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op[of Tau])
           apply simp_all
          apply (rule step_Tau_loop_op)
          apply (rule step_map_op[of Tau])
           apply simp_all
          apply (drule step_comp_op_L_Out[where wire="\<lambda>_. None" and buf="\<lambda>_. []", of _ _ _ _ "id_op lbuf2"])
           apply simp
          apply (drule step_Tau_comp_op_L[where wire=Some and buf="case_sum buf2 lbuf3", of _ _ _ _ _ op1])
           apply (auto split: sum.splits)
          done
        subgoal for p op'
          apply hypsubst_thin
          apply (drule step_map_op_inv)
          apply auto
          apply hypsubst_thin
          apply (drule step_loop_op)
          apply auto
          subgoal for op''
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply fast
            apply (rule rtranclp.intros(2))
             apply (rule rtranclp.intros(1))
            apply (rule step_map_op[of Tau])
             apply simp_all
            apply (rule step_Tau_loop_op)
            apply (rule step_map_op[of Tau])
             apply simp_all
            apply (metis ranI step_Tau_comp_op_R sum.case(1))
            done
          done
        subgoal for op'
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule wbc_base)
           apply fast
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op[of Tau])
           apply simp_all
          apply (rule step_Tau_loop_op)
          apply (rule step_map_op[of Tau])
           apply auto
          done
        subgoal for op'
          apply hypsubst_thin
          apply (drule step_map_op_inv)
          apply auto
          apply hypsubst_thin
          apply (drule step_loop_op)
          apply auto
          subgoal for op'''
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply fast
            apply (rule rtranclp.intros(2))
             apply (rule rtranclp.intros(1))
            apply (rule step_map_op[of Tau])
             apply simp_all
            apply (rule step_Tau_loop_op)
            apply (rule step_map_op[of Tau])
             apply auto
            done
          subgoal for op''' p
            apply (cases "lbuf3 p")
            subgoal
              apply (intro exI conjI[rotated])
               apply (rule wbc_base)
               apply (rule exI[of _ op'''])
               apply (rule exI[of _ op2])
               apply (rule exI[of _ buf2])
               apply (rule exI[of _ "lbuf1"])
               apply (rule exI[of _ "BTL p lbuf2"])
               apply (rule exI[of _ "lbuf3"])
               apply (intro exI conjI)
                apply simp_all
               apply (rule arg_cong[where f="map_op projl projr"])
               apply (rule arg_cong[where f="comp_op Some buf2 op2"])
               apply (rule arg_cong[where f="map_op projl projl"])
               apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
                apply simp_all
               apply (rule ext)
               apply (auto split: sum.splits)[1]
              apply (rule transitive_closurep_trans'(6))
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_loop_op)
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_comp_op_L)
                apply simp_all
               apply (rule step_comp_op_R_Out)
               apply (rule step_id_op_Write)
                apply simp_all
              apply (rule transitive_closurep_trans'(6))
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_loop_op)
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_comp_op_R)
                  apply assumption
                 apply simp_all
              apply (simp add: fun_upd_idem) 
              done
            subgoal for x lbuf3'
              apply (intro exI conjI[rotated])
               apply (rule wbc_base)
               apply (rule exI[of _ op'''])
               apply (rule exI[of _ op2])
               apply (rule exI[of _ buf2])
               apply (rule exI[of _ "lbuf1"])
               apply (rule exI[of _ "lbuf2"])
               apply (rule exI[of _ "BTL p lbuf3"])
               apply (intro exI conjI)
                apply simp_all
               apply (rule arg_cong[where f="map_op projl projr"])
               apply (rule arg_cong[where f="comp_op Some buf2 op2"])
               apply (rule arg_cong[where f="map_op projl projl"])
               apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
                apply simp_all
               apply (rule ext)
               apply (auto split: sum.splits)[1]
              apply (rule transitive_closurep_trans'(6))
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_loop_op)
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_comp_op_R)
                  apply assumption
                 apply simp_all
              apply (simp add: case_sum_updateR)
              done
            done
          subgoal for op''' p
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply (rule exI[of _ op'''])
             apply (rule exI[of _ op2])
             apply (rule exI[of _ buf2])
             apply (rule exI[of _ "lbuf1"])
             apply (rule exI[of _ "lbuf2"])
             apply (rule exI[of _ "BTL p lbuf3"])
             apply (intro exI conjI)
              apply simp_all
             apply (rule arg_cong[where f="map_op projl projr"])
             apply (rule arg_cong[where f="comp_op Some buf2 op2"])
             apply (rule arg_cong[where f="map_op projl projl"])
             apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
              apply simp_all
             apply (rule ext)
             apply (auto split: sum.splits)[1]
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_loop_op)
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_comp_op_R)
                apply assumption
               apply simp_all
            done
          subgoal for op''' p
            apply (cases "lbuf3 p")
            subgoal
              apply (cases "lbuf2 p")
              subgoal
                apply (intro exI conjI[rotated])
                 apply (rule wbc_base)
                 apply (rule exI[of _ op'''])
                 apply (rule exI[of _ op2])
                 apply (rule exI[of _ buf2])
                 apply (rule exI[of _ "BTL p lbuf1"])
                 apply (rule exI[of _ " lbuf2"])
                 apply (rule exI[of _ "lbuf3"])
                 apply (intro exI conjI)
                  apply simp_all
                 apply (rule arg_cong[where f="map_op projl projr"])
                 apply (rule arg_cong[where f="comp_op Some buf2 op2"])
                 apply (rule arg_cong[where f="map_op projl projl"])
                 apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
                  apply simp_all
                 apply (rule ext)
                 apply (auto split: sum.splits)[1]
                apply (rule transitive_closurep_trans'(6))
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Inp_Inr_loop_op[where buf="case_sum undefined lbuf1" and p=p])
                  apply simp_all
                 apply (rule step_map_op[of "Inp (Inl (Inr p)) _"])
                  apply simp_all
                 apply (rule step_comp_op_L_Inp)
                 apply (rule step_comp_op_R_Inp)
                  apply (rule step_id_op_Read)
                 apply simp_all
                apply (rule transitive_closurep_trans'(6))
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Tau_loop_op)
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Tau_comp_op_L)
                  apply simp_all
                 apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write)
                  apply simp_all
                 apply blast
                apply simp
                apply (rule transitive_closurep_trans'(6))
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Tau_loop_op)
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Tau_comp_op_R)
                    apply assumption
                   apply simp_all
                apply (simp add: fun_upd_idem) 
                done
              subgoal 
                apply (intro exI conjI[rotated])
                 apply (rule wbc_base)
                 apply (rule exI[of _ op'''])
                 apply (rule exI[of _ op2])
                 apply (rule exI[of _ buf2])
                 apply (rule exI[of _ "lbuf1"])
                 apply (rule exI[of _ "BTL p lbuf2"])
                 apply (rule exI[of _ "lbuf3"])
                 apply (intro exI conjI)
                  apply simp_all
                 apply (rule arg_cong[where f="map_op projl projr"])
                 apply (rule arg_cong[where f="comp_op Some buf2 op2"])
                 apply (rule arg_cong[where f="map_op projl projl"])
                 apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
                  apply simp_all
                 apply (rule ext)
                 apply (auto split: sum.splits)[1]
                apply (rule transitive_closurep_trans'(6))
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Tau_loop_op)
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Tau_comp_op_L)
                  apply simp_all
                 apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write[where p=p])
                  apply simp_all          
                apply (rule transitive_closurep_trans'(6))
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Tau_loop_op)
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Tau_comp_op_R)
                    apply assumption
                   apply simp_all
                apply (simp add: fun_upd_idem)
                done
              done
            subgoal for x lbuf3'
              apply (intro exI conjI[rotated])
               apply (rule wbc_base)
               apply (rule exI[of _ op'''])
               apply (rule exI[of _ op2])
               apply (rule exI[of _ buf2])
               apply (rule exI[of _ "lbuf1"])
               apply (rule exI[of _ "lbuf2"])
               apply (rule exI[of _ "BTL p lbuf3"])
               apply (intro exI conjI)
                apply simp_all
               apply (rule arg_cong[where f="map_op projl projr"])
               apply (rule arg_cong[where f="comp_op Some buf2 op2"])
               apply (rule arg_cong[where f="map_op projl projl"])
               apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
                apply simp_all
               apply (rule ext)
               apply (auto split: sum.splits)[1]
              apply (rule transitive_closurep_trans'(6))
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_loop_op)
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_comp_op_R)
                  apply assumption
                 apply simp_all
              apply (simp add: case_sum_updateR)
              done
            done
          subgoal for op''' p x
            apply (intro conjI[rotated] exI)
             apply (rule wbc_base)
             apply (rule exI[of _ op'''])
             apply (rule exI[of _ op2])
             apply (rule exI[of _ buf2])
             apply (rule exI[of _ "BENQ p x lbuf1"])
             apply (rule exI[of _ "lbuf2"])
             apply (rule exI[of _ "lbuf3"])
             apply (intro exI conjI)
              apply (simp add: fun_upd_idem) 
              apply (rule arg_cong[where f="map_op projl projr"])
              apply (rule arg_cong[where f="comp_op Some buf2 op2"])
              apply (rule arg_cong[where f="map_op projl projl"])
              apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
               apply simp_all
             apply (rule ext)
             apply (auto split: sum.splits)[1]
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Out_Inr_loop_op)
             apply (rule step_map_op[of "Out (Inr _) _"])
              apply simp_all
             apply (rule step_comp_op_R_Out)
             apply assumption
            apply blast 
            done
          done
        done
      done
    subgoal for io op1'
      apply (drule step_map_op_inv)
      apply auto
      apply hypsubst_thin
      apply (drule step_loop_op)
      apply auto
      subgoal for p op'' x
        apply (drule step_map_op_inv)
        apply auto
        subgoal for io' op'''
          apply (cases io')
            apply auto
          subgoal for iop
            apply hypsubst_thin
            apply (cases iop)
             apply auto
            subgoal
              apply hypsubst_thin
              apply (drule step_comp_op_cases)
              apply auto
              subgoal for op1'
                apply hypsubst_thin
                apply (drule step_comp_op_cases)
                apply auto
                subgoal for op1'
                  apply hypsubst_thin
                  apply (intro conjI[rotated] exI)
                   apply (rule wbc_sym)
                   apply (rule wbc_base)
                   apply force
                  apply (rule step_wstep)
                  apply (rule step_map_op[of "Inp (Inl _) _"])
                   apply simp_all
                  apply auto
                  done
                done
              done
            subgoal for r
              apply hypsubst_thin
              apply (drule step_comp_op_cases)
              apply auto
              done
            done
          done
        done
      subgoal for p op'' x
        apply (drule step_map_op_inv)
        apply auto
        subgoal for io' op'''
          apply (cases io')
            apply auto
          subgoal for iop
            apply hypsubst_thin
            apply (cases iop)
             apply auto
            subgoal
              apply hypsubst_thin
              apply (drule step_comp_op_cases)
              apply auto
              done
            subgoal     
              apply hypsubst_thin
              apply (drule step_comp_op_cases)
              apply auto
              subgoal for op1'
                apply hypsubst_thin
                apply (intro conjI[rotated] exI)
                 apply (rule wbc_sym)
                 apply (rule wbc_base)
                 apply force
                subgoal
                  unfolding wstep_def
                  apply (rule relcomppI[rotated])
                   apply (rule relcomppI)
                    apply simp
                    apply (rule step_map_op[where f=projl and g=projr])
                     apply (rule step_comp_op_R_Out)
                     apply (rule step_map_op[where f=projl and g=projl])
                      apply (rule step_Out_Inl_loop_op)
                      apply assumption
                     apply simp_all
                   apply force+
                  done
                done
              done
            done
          done
        done
      subgoal for op''
        apply (drule step_map_op_inv)
        apply auto
        subgoal for io' op'''
          apply hypsubst_thin
          apply (cases io')
            apply auto
          apply hypsubst_thin
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for p x op1'
            apply (cases p)
             apply auto
            subgoal for lp
              apply hypsubst_thin
              apply (drule step_comp_op_cases)
              apply auto
              apply hypsubst_thin
              subgoal for op2'
                apply (intro conjI[rotated] exI)
                 apply (rule wbc_sym)
                 apply (rule wbc_base)
                 apply (rule exI[of _ op1])
                 apply (rule exI[of _ op2'])
                 apply (rule exI[of _ "BENQ lp x buf2"])
                 apply (rule exI[of _ "lbuf1"])
                 apply (rule exI[of _ "lbuf2"])
                 apply (rule exI[of _ "lbuf3"])
                 apply (intro conjI)
                  apply (rule refl)
                 apply simp_all
                apply (rule transitive_closurep_trans'(6))
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Tau_comp_op_L)
                  apply assumption
                 apply auto
                done
              done
            subgoal for lr
              apply hypsubst_thin
              apply (drule step_comp_op_cases)
              apply auto
              subgoal for op2'
                apply hypsubst_thin
                apply (drule step_id_op_Out)
                 apply simp_all
                apply auto
                apply hypsubst_thin
                apply (intro conjI[rotated] exI)
                 apply (rule wbc_sym)
                 apply (rule wbc_base)
                 apply (rule exI[of _ op1])
                 apply (rule exI[of _ ])
                 apply (rule exI[of _ "buf2"])
                 apply (rule exI[of _ "lbuf1"])
                 apply (rule exI[of _ "BTL lr lbuf2"])
                 apply (rule exI[of _ "BENQ lr (BHD lr lbuf2) lbuf3"])
                 apply (intro conjI)
                  apply (rule refl)
                 apply simp
                apply (rule rtranclp_intros_1')
                apply (rule arg_cong[where f="map_op projl projr"])
                apply (rule arg_cong[where f="comp_op Some buf2 op2"])
                apply (rule arg_cong[where f="map_op projl projl"])
                apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
                 apply (auto split: sum.splits if_splits simp add: fun_upd_def)
                done
              done
            done
          subgoal for p op1'
            apply (cases p)
            subgoal for lp
              apply auto
              apply hypsubst_thin
              apply (intro conjI[rotated] exI)
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply (rule exI[of _ op1'])
               apply (rule exI[of _ op2])
               apply (rule exI[of _ "BTL lp buf2"])
               apply (rule exI[of _ "lbuf1"])
               apply (rule exI[of _ "lbuf2"])
               apply (rule exI[of _ "lbuf3"])
               apply (intro conjI)
                apply (rule refl)
               apply simp
              apply (rule transitive_closurep_trans'(6))
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_comp_op_R)
                  apply (rule step_map_op[of "Inp (Inl _) _"])
                   apply simp_all
               apply (rule step_Inp_Inl_loop_op)
               apply assumption
              apply auto
              done
            subgoal for lr
              apply auto
              apply hypsubst_thin
              apply (intro conjI[rotated] exI)
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply (rule exI[of _ op1'])
               apply (rule exI[of _ op2])
               apply (rule exI[of _ "buf2"])
               apply (rule exI[of _ "lbuf1"])
               apply (rule exI[of _ "lbuf2"])
               apply (rule exI[of _ "BTL lr lbuf3"])
               apply force
              apply (rule transitive_closurep_trans'(6))
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_comp_op_R_Tau)
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Inp_Inr_loop_op[where p=lr, of _ _ op1'])
                apply simp_all
              apply (rule rtranclp_intros_1')
              apply (rule arg_cong[where f="map_op projl projr"])
              apply (rule arg_cong[where f="comp_op Some buf2 op2"])
              apply (rule arg_cong[where f="map_op projl projl"])
              apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
               apply (auto split: sum.splits if_splits simp add: fun_upd_def)
              done
            done
          subgoal for op2'
            apply hypsubst_thin
            apply (drule step_comp_op_cases)
            apply auto
            subgoal for op2''
              apply hypsubst_thin
              apply (intro conjI[rotated] exI)
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply (rule exI[of _ op1])
               apply (rule exI[of _ op2''])
               apply (rule exI[of _ "buf2"])
               apply (rule exI[of _ "lbuf1"])
               apply (rule exI[of _ "lbuf2"])
               apply (rule exI[of _ "lbuf3"])
               apply (intro conjI)
                apply (rule refl)
               apply simp
              apply (rule transitive_closurep_trans'(6))
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_comp_op_L_Tau)
               apply assumption
              apply simp_all
              done
            subgoal for op2''
              apply hypsubst_thin
              apply (rule FalseE)
              apply (subst (asm) id_op_code)
              apply auto
              done
            done
          subgoal for op1'' 
            apply hypsubst_thin      
            apply (intro conjI[rotated] exI)
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply (rule exI[of _ op1''])
             apply (rule exI[of _ op2])
             apply (rule exI[of _ "buf2"])
             apply (rule exI[of _ "lbuf1"])
             apply (rule exI[of _ "lbuf2"])
             apply (rule exI[of _ "lbuf3"])
             apply (intro conjI)
              apply (rule refl)
             apply simp
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_comp_op_R_Tau)
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_loop_op)
             apply assumption
            apply auto
            done
          done
        done
      subgoal for op2'' p
        apply (drule step_map_op_inv)
        apply auto
        subgoal for io' op'''
          apply hypsubst_thin
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for op2''
            apply hypsubst_thin
            apply (drule step_comp_op_cases)
            apply auto
            subgoal for op2''
              apply hypsubst_thin
              apply (drule step_id_op_Inp)
               apply auto
              apply hypsubst_thin
              apply (intro conjI[rotated] exI)
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply (rule exI[of _ op1])
               apply (rule exI[of _ op2])
               apply (rule exI[of _ "buf2"])
               apply (rule exI[of _ "BTL p   lbuf1"])
               apply (rule exI[of _ "BENQ p (BHD p lbuf1) lbuf2"])
               apply (rule exI[of _ "lbuf3"])
               apply (intro conjI)
                apply (rule refl)
               apply auto
              apply (rule rtranclp_intros_1')
              apply (rule arg_cong[where f="map_op projl projr"])
              apply (rule arg_cong[where f="comp_op Some buf2 op2"])
              apply (rule arg_cong[where f="map_op projl projl"])
              apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
               apply (auto split: sum.splits if_splits simp add: fun_upd_def)
              done
            done
          done
        done
      subgoal for op''' p x
        apply (drule step_map_op_inv)
        apply auto
        subgoal for io' op'''
          apply hypsubst_thin
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for op1'
            apply hypsubst_thin
            apply (intro conjI[rotated] exI)
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply (rule exI[of _ op1'])
             apply (rule exI[of _ op2])
             apply (rule exI[of _ "buf2"])
             apply (rule exI[of _ "BENQ p x lbuf1"])
             apply (rule exI[of _ " lbuf2"])
             apply (rule exI[of _ "lbuf3"])
             apply auto
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_comp_op_R_Tau)
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Out_Inr_loop_op)
             apply simp
            apply (rule rtranclp_intros_1')
            apply (rule arg_cong[where f="map_op projl projr"])
            apply (rule arg_cong[where f="comp_op Some buf2 op2"])
            apply (rule arg_cong[where f="map_op projl projl"])
            apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
             apply (auto split: sum.splits if_splits simp add: fun_upd_def)
            done
          done
        done
      done
    done
  done

lemma loop_op_scomp_commute:
  "op2 \<bullet> (op1\<up>) \<approx> ((op2 \<parallel> \<I>) \<bullet> op1)\<up>"
  unfolding feedback_op_def scomp_op_def pcomp_op_def comp_def
  using loop_op_scomp_commute_gen[of "\<lambda>_. []" op2 "\<lambda>_. []" "\<lambda>_. []" "\<lambda>_. []" op1, unfolded comp_def, simplified] by auto

section \<open>Axiom: R2: Loop distribute scomp_op\<close>
lemma loop_op_distribute_scomp_op_gen:
  "map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)) op2) \<approx>
   map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))"
  apply (coinduction arbitrary: op1 op2 buf2 lbuf1 lbuf2 lbuf3 rule: wbisim_coinduct_upto)
  subgoal for op1 op2 buf2 lbuf1 lbuf2 lbuf3
    unfolding wsim_def
    apply auto
    subgoal for io op1'
      apply (drule step_map_op_inv)
      apply safe
      apply hypsubst_thin
      apply (drule step_comp_op_cases)
      subgoal for io op''
        apply auto
        subgoal for p x op1'
          apply hypsubst_thin
          apply (drule step_map_op_inv)
          apply auto
          subgoal for io op
            apply hypsubst_thin
            apply (drule step_loop_op)
            apply auto
            subgoal for op1'
              apply hypsubst_thin
              apply (intro exI conjI)
               apply (rule step_wstep)
               apply (rule step_map_op[of "Inp (Inl p) x"])
                apply (rule step_Inp_Inl_loop_op)
                apply (rule step_map_op[of "Inp (Inl (Inl p)) x"])
                 apply (rule step_comp_op_L_Inp)
                 apply assumption
                apply simp_all
              apply (rule wbc_base)
              apply fast
              done
            done
          done
        subgoal for p x op2'
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule wbc_base)
           apply fast
          apply (rule step_wstep)
          apply (rule step_map_op[of "Out (Inl p) x"])
           apply (rule step_Out_Inl_loop_op)
           apply simp_all
          apply (rule step_map_op[of "Out (Inr (Inl p)) x"])
           apply simp_all
          apply (rule step_comp_op_R_Out)
          apply (rule step_comp_op_L_Out)
           apply auto
          done
        subgoal for p x op1'
          apply hypsubst_thin
          apply (drule step_map_op_inv)
          apply auto
          apply hypsubst_thin
          apply (drule step_loop_op)
          apply auto
          subgoal for op1'
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply fast
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_loop_op)
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_comp_op_L)
              apply assumption
             apply simp_all
            apply (rule rtranclp_intros_1')
            apply (rule arg_cong[where f="map_op projl projl"])
            apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
             apply (auto split: sum.splits if_splits simp add: fun_upd_def)
            done
          done
        subgoal for p op2'
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule wbc_base)
           apply fast
          apply (rule transitive_closurep_trans'(6))
           apply (rule step_map_op[of Tau])
            apply simp_all
           apply (rule step_Tau_loop_op)
           apply (rule step_map_op[of Tau])
            apply simp_all
           apply (rule step_Tau_comp_op_R)
              apply (rule step_comp_op_L_Inp)
              apply assumption
             apply simp_all
          done
        subgoal for op1'
          apply hypsubst_thin
          apply (drule step_map_op_inv)
          apply auto
          apply hypsubst_thin
          apply (drule step_loop_op)
          apply auto
          subgoal for op1'
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply fast
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_loop_op)
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_comp_op_L_Tau)
             apply assumption
            apply auto
            done
          subgoal for op1' p
            apply (cases "lbuf3 p")
            subgoal
              apply (intro exI conjI[rotated])
               apply (rule wbc_base)
               apply (rule exI[of _ op1'])
               apply (rule exI[of _ op2])
               apply (rule exI[of _ "buf2"])
               apply (rule exI[of _ "lbuf1"])
               apply (rule exI[of _ "BTL p lbuf2"])
               apply (rule exI[of _ "lbuf3"])
               apply (intro exI conjI)
                apply (rule arg_cong[where f="map_op projl projr"])
                apply (rule arg_cong2[where f="comp_op Some buf2"])
                 apply simp_all
               apply (rule arg_cong[where f="map_op projl projl"])
               apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
                apply (auto split: sum.splits if_splits simp add: fun_upd_def)[2]
              apply (rule transitive_closurep_trans'(6))
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Out_Inr_loop_op)
               apply (rule step_map_op[of "Out (Inr (Inr p)) _"])
                apply simp_all
               apply (rule step_comp_op_R_Out)
               apply (rule step_comp_op_R_Out)
               apply (rule step_id_op_Write)
                apply simp_all
              apply (rule transitive_closurep_trans'(6))
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Inp_Inr_loop_op[where p=p])
                apply (rule step_map_op[of "Inp (Inl (Inr p)) (BHD p lbuf2)"])
                 apply simp_all
               apply (rule step_comp_op_L_Inp)
               apply simp
              apply (metis (no_types, lifting) Nitpick.rtranclp_unfold case_sum_updateR fun_upd_triv)
              done
            subgoal for x lbuf3'
              apply (intro exI conjI[rotated])
               apply (rule wbc_base)
               apply (rule exI[of _ op1'])
               apply (rule exI[of _ op2])
               apply (rule exI[of _ "buf2"])
               apply (rule exI[of _ "lbuf1"])
               apply (rule exI[of _ "lbuf2"])
               apply (rule exI[of _ "BTL p lbuf3"])
               apply (intro exI conjI)
                apply (rule arg_cong[where f="map_op projl projr"])
                apply (rule arg_cong2[where f="comp_op Some buf2"])
                 apply simp_all
               apply (rule arg_cong[where f="map_op projl projl"])
               apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
                apply (auto split: sum.splits if_splits simp add: fun_upd_def)[2]
              apply (rule transitive_closurep_trans'(6))
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Inp_Inr_loop_op[where p=p])
                apply (rule step_map_op[of "Inp (Inl (Inr p)) (BHD p lbuf3)"])
                 apply simp_all
               apply (rule step_comp_op_L_Inp)
               apply simp
              apply (metis (no_types, lifting) Nitpick.rtranclp_unfold case_sum_updateR)
              done
            done
          subgoal for op1' p
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply (rule exI[of _ op1'])
             apply (rule exI[of _ op2])
             apply (rule exI[of _ "buf2"])
             apply (rule exI[of _ "lbuf1"])
             apply (rule exI[of _ "lbuf2"])
             apply (rule exI[of _ "BTL p lbuf3"])
             apply (intro exI conjI)
              apply (rule arg_cong[where f="map_op projl projr"])
              apply (rule arg_cong2[where f="comp_op Some buf2"])
               apply simp_all
             apply (rule arg_cong[where f="map_op projl projl"])
             apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
              apply (auto split: sum.splits if_splits simp add: fun_upd_def)[2]
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Inp_Inr_loop_op[where p=p])
              apply (rule step_map_op[of "Inp (Inl (Inr p)) (BHD p lbuf3)"])
               apply simp_all
             apply (rule step_comp_op_L_Inp)
             apply simp
            apply (metis (no_types, lifting) Nitpick.rtranclp_unfold case_sum_updateR)
            done
          subgoal for op1' p
            apply (cases "lbuf3 p")
            subgoal 
              apply (cases "lbuf2 p")
              subgoal
                apply (intro exI conjI[rotated])
                 apply (rule wbc_base)
                 apply (rule exI[of _ op1'])
                 apply (rule exI[of _ op2])
                 apply (rule exI[of _ "buf2"])
                 apply (rule exI[of _ "BTL p lbuf1"])
                 apply (rule exI[of _ "lbuf2"])
                 apply (rule exI[of _ "lbuf3"])
                 apply (intro exI conjI)
                  apply (rule arg_cong[where f="map_op projl projr"])
                  apply (rule arg_cong2[where f="comp_op Some buf2"])
                   apply simp_all
                 apply (rule arg_cong[where f="map_op projl projl"])
                 apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
                  apply (auto split: sum.splits if_splits simp add: fun_upd_def)[2]
                apply (rule transitive_closurep_trans'(6))
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Tau_loop_op)
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Tau_comp_op_R)
                    apply (rule step_comp_op_R_Inp)
                     apply (rule step_id_op_Read)
                    apply simp_all
                apply (rule transitive_closurep_trans'(6))
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Out_Inr_loop_op)
                 apply (rule step_map_op[of "Out (Inr (Inr p)) _"])
                  apply simp_all
                 apply (rule step_comp_op_R_Out)
                 apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write)
                  apply simp_all
                apply (rule transitive_closurep_trans'(6))
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Inp_Inr_loop_op[where p=p])
                  apply (rule step_map_op[of "Inp (Inl (Inr p)) (BHD p lbuf1)"])
                   apply simp_all
                 apply (rule step_comp_op_L_Inp)
                 apply simp
                apply (metis (no_types, lifting) Nitpick.rtranclp_unfold case_sum_updateR fun_upd_triv)
                done
              subgoal for x lbuf2'
                apply (intro exI conjI[rotated])
                 apply (rule wbc_base)
                 apply (rule exI[of _ op1'])
                 apply (rule exI[of _ op2])
                 apply (rule exI[of _ "buf2"])
                 apply (rule exI[of _ "lbuf1"])
                 apply (rule exI[of _ "BTL p lbuf2"])
                 apply (rule exI[of _ "lbuf3"])
                 apply (intro exI conjI)
                  apply (rule arg_cong[where f="map_op projl projr"])
                  apply (rule arg_cong2[where f="comp_op Some buf2"])
                   apply simp_all
                 apply (rule arg_cong[where f="map_op projl projl"])
                 apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
                  apply (auto split: sum.splits if_splits simp add: fun_upd_def)[2]
                apply (rule transitive_closurep_trans'(6))
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Out_Inr_loop_op)
                 apply (rule step_map_op[of "Out (Inr (Inr p)) _"])
                  apply simp_all
                 apply (rule step_comp_op_R_Out)
                 apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write)
                  apply simp_all
                apply (rule transitive_closurep_trans'(6))
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Inp_Inr_loop_op[where p=p])
                  apply (rule step_map_op[of "Inp (Inl (Inr p)) (BHD p lbuf2)"])
                   apply simp_all
                 apply (rule step_comp_op_L_Inp)
                 apply simp
                apply (metis (no_types, lifting) Nitpick.rtranclp_unfold case_sum_updateR fun_upd_triv)
                done
              done
            subgoal for x lbuf3'
              apply (intro exI conjI[rotated])
               apply (rule wbc_base)
               apply (rule exI[of _ op1'])
               apply (rule exI[of _ op2])
               apply (rule exI[of _ "buf2"])
               apply (rule exI[of _ "lbuf1"])
               apply (rule exI[of _ "lbuf2"])
               apply (rule exI[of _ "BTL p lbuf3"])
               apply (intro exI conjI)
                apply (rule arg_cong[where f="map_op projl projr"])
                apply (rule arg_cong2[where f="comp_op Some buf2"])
                 apply simp_all
               apply (rule arg_cong[where f="map_op projl projl"])
               apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
                apply (auto split: sum.splits if_splits simp add: fun_upd_def)[2]
              apply (rule transitive_closurep_trans'(6))
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Inp_Inr_loop_op[where p=p])
                apply (rule step_map_op[of "Inp (Inl (Inr p)) (BHD p lbuf3)"])
                 apply simp_all
               apply (rule step_comp_op_L_Inp)
               apply simp
              apply (metis (no_types, lifting) Nitpick.rtranclp_unfold case_sum_updateR)
              done
            done
          subgoal for op1' p x
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply (rule exI[of _ op1'])
             apply (rule exI[of _ op2])
             apply (rule exI[of _ "buf2"])
             apply (rule exI[of _ "BENQ p x lbuf1"])
             apply (rule exI[of _ "lbuf2"])
             apply (rule exI[of _ "lbuf3"])
             apply (intro exI conjI)
              apply (rule arg_cong[where f="map_op projl projr"])
              apply (rule arg_cong2[where f="comp_op Some buf2"])
               apply simp_all
             apply (rule arg_cong[where f="map_op projl projl"])
             apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
              apply (auto split: sum.splits if_splits simp add: fun_upd_def)[2]
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_loop_op)
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_comp_op_L)
              apply simp_all
            apply simp
            done
          done
        subgoal for op2'
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule wbc_base)
           apply force
          apply (rule transitive_closurep_trans'(6))
           apply (rule step_map_op[of Tau])
            apply simp_all
           apply (rule step_Tau_loop_op)
           apply (rule step_map_op[of Tau])
            apply simp_all
           apply (rule step_comp_op_R_Tau)
           apply (rule step_comp_op_L_Tau)
           apply auto
          done
        done
      done
    subgoal for io op1'


                find_theorems Tau comp_op  


end


              apply (rule step_Tau_loop_op)
             apply (rule step_map_op[of Tau])
                apply simp_all

              apply (rule step_comp_op_L_Inp)

              find_theorems comp_op Inp 

                apply (rule step_Tau_loop_op)
             apply (rule step_map_op[of Tau])
                 apply simp_all


                apply (rule step_Inp_Inr_loop_op)


            apply (rule step_map_op[of "Inp (Inl (Inr p)) _ "])
              apply simp_all


            apply (rule step_Tau_loop_op)
            apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_comp_op_L_Tau)



            find_theorems loop_op Tau 


            find_theorems step Tau loop_op


           apply (rule step_wstep)


            apply (rule step_map_op[of "Inp (Inl (Inl p)) x"])
             apply (rule step_comp_op_R_Inp)
             apply assumption



lemma loop_op_distribute_scomp_op:
  "(op1\<up>) \<bullet> op2 \<approx> (op1 \<bullet> (op2 \<parallel> \<I>))\<up>"
  unfolding feedback_op_def scomp_op_def pcomp_op_def


  oops

section \<open>Axiom: R3: Loop parallel composition\<close>
lemma loop_op_pcomp_commue:
  "op1 \<parallel> (op2\<up>) ~ (map_op assoc assoc (op1 \<parallel> op2))\<up>"
  oops

section \<open>Axiom: R4: Loop commutes inner sequential composition\<close>
lemma loop_op_commutes_inner_scomp_op:
  "(op1 \<bullet> (\<I> \<parallel> op2))\<up> ~ ((\<I> \<parallel> op2) \<bullet> op1)\<up>"
  oops

section \<open>Axiom: R5: Loop with no loop\<close>
lemma loop_op_no_loop:
  "loop_op (\<lambda> _. None) buf op = op"
  oops

section \<open>Axiom: R6: Loop absorb\<close>
lemma loop_op_absorb_gen:
  "map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf1) op))) ~
   map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))"
  apply (coinduction arbitrary: op buf1 buf2 rule: bisim_coinduct_upto)
  subgoal for op buf1 buf2
    unfolding sim_def
    apply auto
    subgoal for io op'
      apply (drule step_double_loop_1)
      apply auto
      apply (intro exI conjI)
       apply auto
      apply (rule bc_base)
      apply (intro exI conjI)
       apply auto
      done
    subgoal for io op'
      apply (drule step_double_loop_2)
      apply auto
      apply (intro exI conjI)
       apply auto
      apply (rule bc_sym)
      apply (rule bc_base)
      apply (intro exI conjI)
       apply auto
      done
    done
  done

lemma loop_op_absorb:
  "(op\<up>)\<up> ~ (map_op reassoc reassoc op)\<up>"
  unfolding feedback_op_def
  using loop_op_absorb_gen[of "\<lambda> _.[]" "\<lambda> _.[]" op] by auto

section \<open>Axiom F1: Identity looped is end_op\<close>

lemma id_op_loop_spin: \<open>\<I>\<up> = \<oslash>\<close>
  oops

section \<open>Axiom F2: Transpose looped is identity\<close>

lemma transp_op_loop_id: \<open>\<X>\<up> \<approx> \<I>\<close>
  oops

end