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

section \<open>Axiom: R1: Loop commute sequential composition\<close>
lemma loop_op_scomp_commute:
  "op2 \<bullet> (op1\<up>) ~ ((op2 \<parallel> \<I>) \<bullet> op1)\<up>"
  oops

section \<open>Axiom: R2: Loop distribute scomp_op\<close>
lemma loop_op_distribute_scomp_op:
  "(op1\<up>) \<bullet> op2 ~ (op1 \<bullet> (op2 \<parallel> \<I>))\<up>"
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
lemma step_loop_op:
  "step io (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op) op' \<Longrightarrow>
   (\<exists>p x. io = Inp (Inl p) x \<and> (\<exists> op''. op' = loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op'' \<and> step io op op'')) \<or>
   (\<exists>p x. io = Out (Inl p) x \<and> (\<exists> op''. op' = loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op'' \<and> step io op op'')) \<or>
   (io = Tau \<and> (\<exists> op''. op' = loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op'' \<and> step io op op'')) \<or>
   (io = Tau \<and> (\<exists> op'' p x. op' = loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (BTL (Inr p) buf) op'' \<and> step (Inp (Inr p) x) op op'' \<and> buf (Inr p) \<noteq> [] \<and> BHD (Inr p) buf = x)) \<or>
   (io = Tau \<and> (\<exists> op'' p x. op' = loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (BENQ (Inr p) x buf) op'' \<and> step (Out (Inr p) x) op op''))"
  apply (induct io "loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op" op' arbitrary: buf op pred: step)
     apply (simp add: loop_op.code)
    apply (simp add: loop_op.code)
   apply (simp add: loop_op.code)
  subgoal for op ops io op' buf op''
    apply (subst (asm) (7) loop_op.code)
    apply (clarsimp del: disjCI split: if_splits option.splits)
    subgoal for op
      apply (cases op)
      subgoal for p f
        apply (simp del: disjCI split: if_splits option.splits)
        subgoal
          apply hypsubst_thin
          apply (erule thin_rl)
          apply (cases p)
          subgoal for lp
            apply (clarsimp del: disjCI)
            apply hypsubst_thin
            apply (smt (verit, best) Inl_Inr_False comp_apply mem_Collect_eq option.discI option.sel ran_def sum.case_eq_if)
            done
          subgoal for rp
            apply (clarsimp del: disjCI)
            apply hypsubst_thin
            apply (rule disjI2)
            apply (rule disjI1)
            apply (metis Read_in_choices_step cin.rep_eq)
            done
          done
        subgoal
          apply hypsubst_thin
          apply (erule thin_rl)
          apply (cases p)
          subgoal for lp
            apply (clarsimp del: disjCI)
            apply hypsubst_thin
            apply (metis Read_in_choices_step cin.rep_eq)
            done
          subgoal
            apply (clarsimp del: disjCI)
            apply hypsubst_thin
            apply (metis (full_types) comp_apply old.sum.simps(6) ranI)
            done
          done
        done
      subgoal for op' p x
        apply (simp split: if_splits option.splits)
        subgoal
          apply hypsubst_thin
          apply (erule thin_rl)
          apply (cases p)
          subgoal for lp
            apply (clarsimp del: disjCI)
            apply hypsubst_thin
            using Write_in_choices_step apply fastforce
            done
          subgoal
            by (clarsimp del: disjCI)
          done
        subgoal
          apply hypsubst_thin
          apply (erule thin_rl)
          apply (cases p)
          subgoal
            by (clarsimp del: disjCI)
          subgoal
            apply (clarsimp del: disjCI)
            apply hypsubst_thin
            using Write_in_choices_step apply fastforce
            done
          done
        done
      subgoal for op'
        apply (simp split: if_splits option.splits)
        apply blast
        done
      subgoal for op'
        apply (clarsimp split: if_splits option.splits)
        apply hypsubst_thin
        apply (erule thin_rl)
        apply (metis Silent_in_choices_step cin.rep_eq)
        done
      done
    done
  done

lemma step_Inp_Inl_loop_op:
  "step (Inp (Inl p) x) op op' \<Longrightarrow>
   step (Inp (Inl p) x) (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op) (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op')"
  apply (subst loop_op.code)
  apply simp
  apply (erule step_choicesE)
    apply simp_all
  subgoal for p' f
    apply clarsimp
    apply hypsubst_thin
    apply (rule SC)
     apply (rule cimage_eqI[of _  _ "Read _ _"])
      apply simp_all
     apply (intro conjI)
      apply assumption
     apply auto
     apply (smt (verit) mem_Collect_eq o_apply option.sel option.simps(3) ran_def sum.case_eq_if sum.simps(4))
    apply (smt (verit) mem_Collect_eq o_apply option.sel option.simps(3) ran_def sum.case_eq_if sum.simps(4))
    done
  done

lemma step_Out_Inl_loop_op:
  "step (Out (Inl p) x) op op' \<Longrightarrow>
   step (Out (Inl p) x) (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op) (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op')"
  apply (subst loop_op.code)
  apply simp
  apply (erule step_choicesE)
    apply simp_all
  subgoal
    apply (rule SC)
     apply (rule cimage_eqI[of _  _ "Write _ _ _"])
      apply simp_all
    apply auto
    done
  done

lemma step_Tau_loop_op:
  "step Tau op op' \<Longrightarrow>
   step Tau (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op) (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op')"
  apply (subst loop_op.code)
  apply simp
  apply (erule step_choicesE)
    apply simp_all
  subgoal
    apply (rule SC)
     apply (rule cimage_eqI[of _  _ "Silent _"])
      apply auto
    done
  done

lemma step_Out_Inr_loop_op:
  "step (Out (Inr p) x) op op' \<Longrightarrow>
   step Tau (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op) (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (BENQ (Inr p) x buf) op')"
  apply (subst loop_op.code)
  apply simp
  apply (erule step_choicesE)
    apply simp_all
  apply (rule SC[rotated])
   apply (rule ST)
  apply (rule cimage_eqI[of _ _ "Write _ (Inr p) _"])
   apply simp_all
  done

lemma step_Inp_Inr_loop_op:
  "step (Inp (Inr p) (BHD (Inr p) buf)) op op' \<Longrightarrow>
   buf (Inr p) \<noteq> [] \<Longrightarrow>
   step Tau (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op) (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (BTL (Inr p) buf) op')"
  apply (subst loop_op.code)
  apply simp
  apply (erule step_choicesE)
    apply simp_all
  apply (rule SC[rotated])
   apply (rule ST)
  apply (rule cimage_eqI[of _ _ ])
   apply auto
  apply (metis comp_apply sum.simps(6) ranI)
  done


lemma step_loop_op_map_op:
  "step (map_IO assoc assoc id io) (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf op) (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) buf' op') \<Longrightarrow>
   step io (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (buf \<circ> assoc) (map_op reassoc reassoc op))
   (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (buf' \<circ> assoc) (map_op reassoc reassoc op'))"
  apply (drule step_map_op[where f=reassoc and g=reassoc])
   apply (auto simp add: IO.map_comp IO.map_id)
  apply (drule step_map_op_inv)
  apply auto
  apply (drule map_op_inj_inv[rotated 2])
    apply (metis BNA_Operators.assoc_reassoc comp_def eq_id_iff inj_on_inverseI)
   apply (metis BNA_Operators.assoc_reassoc comp_def eq_id_iff inj_on_inverseI)
  apply hypsubst_thin
  apply (auto simp add: )
  oops


lemma ST':
  "op = op' \<Longrightarrow> step Tau (Silent op) op'"
  by auto

lemma step_double_loop_1:
  "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf1) (op :: (('a + 'd) + 'e, ('b + 'd) + 'e, 'c) op))))) op' \<Longrightarrow>
   \<exists> (op'' :: (('a + 'd) + 'e, ('b + 'd) + 'e, 'c) op) buf1' buf2'.
   op' = (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf2') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf1') op''))))  \<and>
   step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)))
   (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined (case_sum buf2' buf1')) (map_op reassoc reassoc op'')))"
  unfolding feedback_op_def
  apply (drule step_map_op_inv)
  apply auto
  apply (drule step_loop_op)
  apply auto
  subgoal for p op'' x
    apply hypsubst_thin
    apply (drule step_map_op_inv)
    apply auto
    subgoal for io'
      apply (cases io')
        apply auto
      apply (drule step_loop_op)
      apply auto
      apply hypsubst_thin
      apply (intro exI conjI[rotated])
       apply (rule step_map_op)
        apply (rule step_Inp_Inl_loop_op)
        apply (rule step_map_op)
         apply auto
      done
    done
  subgoal for p op'' x
    apply hypsubst_thin
    apply (drule step_map_op_inv)
    apply auto
    subgoal for io'
      apply (cases io')
        apply auto
      apply hypsubst_thin
      apply (drule step_loop_op)
      apply auto
      apply (intro exI conjI[rotated])
       apply (rule step_map_op)
        apply (rule step_Out_Inl_loop_op)
        apply (rule step_map_op)
         apply auto
      done
    done
  subgoal for op'
    apply hypsubst_thin
    apply (drule step_map_op_inv)
    apply auto
    subgoal for io' op'
      apply hypsubst_thin
      apply (drule step_loop_op)
      apply auto
      subgoal
        apply hypsubst_thin
        apply (intro exI conjI[rotated])
         apply (rule step_map_op)
          apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply auto
        done
      subgoal for op'' p
        apply hypsubst_thin
        apply (rule exI[of _op''])
        apply (rule exI[of _ "BTL p buf1"])
        apply (rule exI[of _ "buf2"])
        apply (intro conjI)
        subgoal
          apply (rule arg_cong[where f="map_op projl projl"])
          apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
           apply force
          apply (rule arg_cong[where f="map_op projl projl"])
          apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
           apply auto
          apply (rule ext)
          apply (auto split: sum.splits)
          done
        subgoal
          apply (erule step_choicesE)
            apply auto
          subgoal for f
            apply hypsubst_thin
            apply (subst loop_op.code)
            apply simp
            apply (rule SC)
             apply (rule cimage_eqI)
              apply (rule refl)
             apply (rule cimage_eqI[of _ _ "Read (Inr (Inr p)) (\<lambda> x. map_op reassoc reassoc (f x))"])
              apply simp_all
             defer
             apply (rule step_map_op)
              apply simp
              apply (intro conjI impI)
               apply (rule ST')
               apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
            subgoal
              unfolding fun_upd_def
              apply (rule ext)
              apply (auto split: sum.splits)
              done
               apply auto
             apply (smt (verit, ccfv_SIG) comp_apply old.sum.simps(6) ranI)
            apply (auto simp flip: choices_map_op)
            apply (rule image_eqI[rotated])
             apply assumption
            apply auto
            done
          done
        done
      subgoal for op'' p x
        apply hypsubst_thin
        apply (rule exI[of _op''])
        apply (rule exI[of _ "BENQ p x buf1"])
        apply (rule exI[of _ "buf2"])
        apply (intro conjI)
        subgoal
          apply (rule arg_cong[where f="map_op projl projl"])
          apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
           apply force
          apply (rule arg_cong[where f="map_op projl projl"])
          apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
           apply auto
          apply (rule ext)
          apply (auto split: sum.splits)
          done
        subgoal
          apply (erule step_choicesE)
            apply auto
          apply (subst loop_op.code)
          apply simp
          apply (rule SC)
           apply (rule cimage_eqI)
            apply (rule refl)
           apply (rule cimage_eqI[of _ _ "Write (map_op reassoc reassoc op'') (Inr (Inr p)) x"])
            apply simp_all
           defer
           apply (rule step_map_op[rotated, of _ _ _ Tau])
            apply simp
           apply (rule ST')
           apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
          subgoal
            unfolding fun_upd_def
            apply (rule ext)
            apply (auto split: sum.splits)
            done
           apply auto
          apply (auto simp flip: choices_map_op)
          apply (rule image_eqI[rotated])
           apply assumption
          apply auto
          done
        done
      done
    done
  subgoal for op'' p
    apply hypsubst_thin
    apply (drule step_map_op_inv)
    apply auto
    subgoal for io op'''
      apply hypsubst_thin
      apply (drule step_loop_op)
      apply auto
      subgoal for op'''
        apply hypsubst_thin
        apply (rule exI[of _ "op'''"])
        apply (rule exI[of _ buf1])
        apply (rule exI[of _ "BTL p buf2"])
        apply auto
        subgoal
          apply (rule arg_cong[where f="map_op projl projl"])
          apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
           apply auto
          apply (rule ext)
          apply (auto split: sum.splits)
          done
        subgoal
          apply (rule step_map_op[of Tau, rotated])
           apply simp_all
          apply (erule step_choicesE)
            apply auto
          subgoal for f
            apply (subst loop_op.code)
            apply simp
            apply (rule SC)
             apply (rule cimage_eqI[of _ _ "Read (Inr (Inl p)) (\<lambda> x. map_op reassoc reassoc (f x))"])
              apply (rule refl)
             apply (auto simp flip: choices_map_op)
              apply (rule image_eqI[rotated])
               apply assumption
              apply auto
             apply (rule ST')
            subgoal
              apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
               apply auto
              apply (rule ext)
              apply (auto split: sum.splits)
              done
            subgoal
              by (metis (no_types, lifting) comp_apply old.sum.simps(6) ranI)
            done
          done
        done
      done
    done
  subgoal for op'' p x
    apply hypsubst_thin
    apply (drule step_map_op_inv)
    apply auto
    subgoal for io op'''
      apply hypsubst_thin
      apply (drule step_loop_op)
      apply auto
      subgoal for op'''
        apply hypsubst_thin
        apply (rule exI[of _ "op'''"])
        apply (rule exI[of _ buf1])
        apply (rule exI[of _ "BENQ p x buf2"])
        apply auto
        subgoal
          apply (rule arg_cong[where f="map_op projl projl"])
          apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
           apply auto
          apply (rule ext)
          apply (auto split: sum.splits)
          done
        subgoal
          apply (rule step_map_op[of Tau, rotated])
           apply simp_all
          apply (erule step_choicesE)
            apply auto
          apply (subst loop_op.code)
          apply simp
          apply (rule SC)
           apply (rule cimage_eqI[of _ _ "Write _  (Inr (Inl p)) x"])
            apply (rule refl)
           apply (auto simp flip: choices_map_op)
           apply (rule image_eqI[rotated])
            apply assumption
           apply auto
          apply (rule ST')
          subgoal
            apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
             apply auto
            apply (rule ext)
            apply (auto split: sum.splits)
            done
          done
        done
      done
    done
  done


lemma step_double_loop_2:
  "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc (op :: (('a + 'd) + 'e, ('b + 'd) + 'e, 'c) op)))) op' \<Longrightarrow>
   \<exists> (op'' :: (('a + 'd) + 'e, ('b + 'd) + 'e, 'c) op) buf1' buf2'.
   op' = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined (case_sum buf2' buf1')) (map_op reassoc reassoc op''))  \<and>
   step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf1) op))))
   (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf2') (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf1') op''))))"
  unfolding feedback_op_def
  apply (drule step_map_op_inv)
  apply auto
  apply (drule step_loop_op)
  apply auto
  subgoal for p op'' x
    apply hypsubst_thin
    apply (rule exI[of _ "map_op assoc assoc op''"])
    apply (rule exI[of _ buf1])
    apply (rule exI[of _ buf2])
    apply auto
    subgoal
      apply (rule arg_cong[where f="map_op projl projl"])
      apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
       apply (auto simp add: op.map_comp op.map_id)
      done
    subgoal
      apply (rule step_map_op[of "Inp (Inl p) x"])
       apply auto
      apply (erule step_choicesE)
        apply simp_all
      apply (subst loop_op.code)
      apply simp
      subgoal for p' f
        apply clarsimp
        apply hypsubst_thin
        apply (rule SC)
         apply (rule cimage_eqI)
          apply simp_all
         apply (simp flip: choices_map_op)
         apply (intro conjI)
          apply (subst loop_op.code)
          apply (simp flip: choices_map_op add: Set.filter_def)
          apply (rule image_eqI)
           apply (rule refl)
          apply simp
          apply (intro exI[of _  "Read (Inl (Inl p)) (\<lambda> x. map_op assoc assoc (f x))"] conjI)
            apply (subst inj_image_mem_iff[where f="map_op reassoc reassoc", where a="Read (Inl (Inl p)) (\<lambda> x. map_op assoc assoc (f x))", symmetric, simplified])
        using map_op_reassoc_inj apply force
            apply simp
        subgoal
          unfolding comp_def
          apply auto
          apply (rule image_eqI[rotated])
           apply assumption
          subgoal for x
            apply (cases x)
               apply auto
            apply (rule ext)
            apply auto
            apply (simp add: op.map_comp)
            done
          done
           apply (auto simp add: ran_def sum.case_eq_if)
        done
      done
    done
  subgoal for p op'' x
    apply hypsubst_thin
    apply (rule exI[of _ "map_op assoc assoc op''"])
    apply (rule exI[of _ buf1])
    apply (rule exI[of _ buf2])
    apply auto
    subgoal
      apply (rule arg_cong[where f="map_op projl projl"])
      apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
       apply (auto simp add: op.map_comp op.map_id)
      done
    subgoal
      apply (rule step_map_op[of "Out (Inl p) x"])
       apply auto
      apply (erule step_choicesE)
        apply simp_all
      apply (subst loop_op.code)
      apply (rule SC)
       apply (rule cimage_eqI)
        apply simp_all
       apply (simp flip: choices_map_op)
       apply (intro conjI)
        apply (subst loop_op.code)
        apply (simp flip: choices_map_op add: Set.filter_def)
        apply (rule image_eqI)
         apply (rule refl)
        apply simp
        apply (intro exI[of _  "Write (map_op assoc assoc op'') (Inl (Inl p)) x"] conjI)
          apply (subst inj_image_mem_iff[where f="map_op reassoc reassoc", where a="Write (map_op assoc assoc op'') (Inl (Inl p)) x", symmetric, simplified])
      using map_op_reassoc_inj apply force
          apply simp
      subgoal
        unfolding comp_def
        apply auto
        apply (rule image_eqI[rotated])
         apply assumption
        subgoal for x
          apply (cases x)
             apply (auto simp add: op.map_comp)
          done
        done
         apply (auto simp add: ran_def sum.case_eq_if)
      done
    done
  subgoal for op''
    apply hypsubst_thin
    apply (rule exI[of _ "map_op assoc assoc op''"])
    apply (rule exI[of _ buf1])
    apply (rule exI[of _ buf2])
    apply auto
    subgoal
      apply (rule arg_cong[where f="map_op projl projl"])
      apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
       apply (auto simp add: op.map_comp op.map_id)
      done
    subgoal
      apply (rule step_map_op[of "Tau"])
       apply auto
      apply (erule step_choicesE)
        apply simp_all
      apply (subst loop_op.code)
      apply (rule SC)
       apply (rule cimage_eqI)
        apply simp_all
       apply (simp flip: choices_map_op)
       apply (intro conjI)
        apply (subst loop_op.code)
        apply (simp flip: choices_map_op add: Set.filter_def)
        apply (rule image_eqI)
         apply (rule refl)
        apply simp
        apply (intro exI[of _  "Silent (map_op assoc assoc op'')"] conjI)
          apply (subst inj_image_mem_iff[where f="map_op reassoc reassoc", where a="Silent (map_op assoc assoc op'')", symmetric, simplified])
      using map_op_reassoc_inj apply force
          apply simp
      subgoal
        unfolding comp_def
        apply auto
        apply (rule image_eqI[rotated])
         apply assumption
        subgoal for x
          apply (cases x)
             apply (auto simp add: op.map_comp)
          done
        done
         apply (auto simp add: ran_def sum.case_eq_if)
      done
    done
  subgoal for op'' p
    apply hypsubst_thin
    apply (cases p; simp; hypsubst_thin)
    subgoal for lp
      apply (rule exI[of _ "map_op assoc assoc op''"])
      apply (rule exI[of _ buf1])
      apply (rule exI[of _ "BTL lp buf2"])
      apply auto
      subgoal
        apply (rule arg_cong[where f="map_op projl projl"])
        apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
         apply (auto simp add: op.map_comp op.map_id)
        apply (rule ext)
        subgoal for x
          apply (cases x)
           apply (auto split: sum.splits)
          done
        done
      subgoal
        apply (rule step_map_op[of "Tau"])
         apply auto
        apply (erule step_choicesE)
          apply simp_all
        subgoal for p f
          apply (subst loop_op.code)
          apply (rule SC)
           apply (rule cimage_eqI)
            apply (simp_all flip: choices_map_op)
           apply (intro conjI)
            apply (subst loop_op.code)
            apply (simp flip: choices_map_op add: Set.filter_def)
            apply (rule image_eqI)
             apply (rule refl)
            apply simp
            apply (intro exI[of _ "Read (Inl (Inr lp)) _"] conjI)
              apply (subst inj_image_mem_iff[where f="map_op reassoc reassoc" and a="Read _ (\<lambda> x. map_op assoc assoc (f x))", symmetric, simplified])
          using map_op_reassoc_inj apply force
              apply simp_all
          subgoal
            unfolding comp_def
            apply auto
            apply (rule image_eqI[rotated])
             apply assumption
            subgoal for x
              apply (cases x)
                 apply auto
              apply (rule ext)
              apply auto
              apply (simp add: op.map_comp)
              done
            done
             apply (auto simp add: ran_def sum.case_eq_if)
          subgoal for p'
            apply (cases p')
               apply auto
            apply hypsubst_thin
            apply (rule ST')
            apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
             apply (auto simp add: op.map_comp op.map_id)
            apply (rule ext)
            subgoal for x
              apply (cases x)
               apply (auto split: sum.splits)
              done
            done
          subgoal
            by (meson sum.disc(2) sum.sel(2))
          done
        done
      done
    subgoal for rp
      apply (rule exI[of _ "map_op assoc assoc op''"])
      apply (rule exI[of _ "BTL rp buf1"])
      apply (rule exI[of _ "buf2"])
      apply auto
      subgoal
        apply (rule arg_cong[where f="map_op projl projl"])
        apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
         apply (auto simp add: op.map_comp op.map_id)
        apply (rule ext)
        subgoal for x
          apply (cases x)
           apply (auto split: sum.splits)
          done
        done
      subgoal
        apply (rule step_map_op[of "Tau"])
         apply auto
        apply (erule step_choicesE)
          apply simp_all
        subgoal for p f
          apply (rule step_Tau_loop_op)
          apply (subst loop_op.code)
          apply (rule step_map_op)
           apply (rule SC)
            apply (simp_all flip: Set.filter_def choices_map_op)
            apply (rule image_eqI)
             apply (rule refl)
            apply simp
            apply (intro conjI)
             apply (subst inj_image_mem_iff[where f="map_op reassoc reassoc" and a="Read (Inr rp) (\<lambda> x. map_op assoc assoc (f x))", symmetric, simplified])
          using map_op_reassoc_inj apply force

          subgoal
            unfolding comp_def
            apply auto
            apply (rule image_eqI[rotated])
             apply assumption
            subgoal for x
              apply (cases x)
                 apply auto
              apply (rule ext)
              apply auto
              apply (simp add: op.map_comp)
              done
            done
            apply (auto simp add: ran_def sum.case_eq_if)
            apply (rule ST')
            apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
             apply (auto simp add: op.map_comp op.map_id)
           apply (rule ext)
          subgoal for x
            apply (cases x)
               apply (auto split: sum.splits)
            done
          apply (meson sum.disc(2) sum.sel(2))
          done
        done
      done
    done
  subgoal for op'' p x
    apply hypsubst_thin
    apply (cases p; simp; hypsubst_thin)
    subgoal for lp
      apply (rule exI[of _ "map_op assoc assoc op''"])
      apply (rule exI[of _ buf1])
      apply (rule exI[of _ "BENQ lp x buf2"])
      apply auto
      subgoal
        apply (rule arg_cong[where f="map_op projl projl"])
        apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
         apply (auto simp add: op.map_comp op.map_id)
        apply (rule ext)
        subgoal for x
          apply (cases x)
           apply (auto split: sum.splits)
          done
        done
      subgoal
        apply (rule step_map_op[of "Tau"])
         apply auto
        apply (erule step_choicesE)
          apply simp_all
        apply (subst loop_op.code)
        apply (rule SC)
         apply (rule cimage_eqI)
          apply (simp_all flip: choices_map_op)
         apply (intro conjI)
          apply (subst loop_op.code)
          apply (simp flip: choices_map_op add: Set.filter_def)
          apply (rule image_eqI)
           apply (rule refl)
          apply simp
          apply (intro exI[of _ "Write _ (Inl (Inr lp)) x"] conjI)
            apply (subst inj_image_mem_iff[where f="map_op reassoc reassoc" and a="Write (map_op assoc assoc op'') (Inl (Inr lp))  x", symmetric, simplified])
        using map_op_reassoc_inj apply force
            apply simp_all
        subgoal
          unfolding comp_def
          apply auto
          apply (rule image_eqI[rotated])
           apply assumption
          subgoal for x
            apply (cases x)
               apply (auto simp add: op.map_comp)
            done
          done
         apply (auto simp add: ran_def sum.case_eq_if)
        subgoal for p'
          apply (cases p')
             apply auto
          apply hypsubst_thin
          apply (rule ST')
          apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
           apply (auto simp add: op.map_comp op.map_id)
          apply (rule ext)
          subgoal for x
            apply (cases x)
               apply (auto split: sum.splits)
            done
          done
        done
      done
    subgoal for rp
      apply (rule exI[of _ "map_op assoc assoc op''"])
      apply (rule exI[of _ "BENQ rp x buf1"])
      apply (rule exI[of _ "buf2"])
      apply auto
      subgoal
        apply (rule arg_cong[where f="map_op projl projl"])
        apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
         apply (auto simp add: op.map_comp op.map_id)
        apply (rule ext)
        subgoal for x
          apply (cases x)
           apply (auto split: sum.splits)
          done
        done
      subgoal
        apply (rule step_map_op[of "Tau"])
         apply auto
        apply (erule step_choicesE)
          apply simp_all
        apply (rule step_Tau_loop_op)
        apply (subst loop_op.code)
        apply (rule step_map_op)
         apply (rule SC)
          apply (simp_all flip: Set.filter_def choices_map_op)
          apply (rule image_eqI)
           apply (rule refl)
          apply simp
          apply (intro conjI)
           apply (subst inj_image_mem_iff[where f="map_op reassoc reassoc" and a="Write (map_op assoc assoc op'') (Inr rp) x", symmetric, simplified])
        using map_op_reassoc_inj apply force
        subgoal
          unfolding comp_def
          apply auto
          apply (rule image_eqI[rotated])
           apply assumption
          subgoal for x
            apply (cases x)
               apply (auto simp add: op.map_comp)
            done
          done
          apply (auto simp add: ran_def sum.case_eq_if)
         apply (rule ST')
         apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
          apply (auto simp add: op.map_comp op.map_id)
        apply (rule ext)
        subgoal for x
          apply (cases x)
             apply (auto split: sum.splits)
          done
        done
      done
    done
  done

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