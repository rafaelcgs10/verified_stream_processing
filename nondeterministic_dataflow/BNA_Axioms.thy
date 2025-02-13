\<comment> \<open>Axioms from Table 1 for BNA operators\<close>
theory BNA_Axioms

imports
  BNA_Operators
  "HOL-ex.Sketch_and_Explore"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom B1: Associativity of parallel composition\<close>

(* FIXME: make intro! at the proof*)
declare step_map_op[intro!,simp]

lemma pcomp_op_assoc:
  \<open>op1 \<parallel> (op2 \<parallel> op3) ~ map_op reassoc reassoc ((op1 \<parallel> op2) \<parallel> op3)\<close>
  apply (coinduction arbitrary: op1 op2 op3 rule: bisim_coinduct_upto)
  unfolding pcomp_op_def sim_def
  subgoal for op1 op2 op3
    apply auto
    subgoal for io
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x op1'
        apply (rule exI)
        apply (rule conjI[rotated])
         apply (rule bc_base)
         apply auto
        done
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for pr op3'
          apply (rule exI)
          apply (rule conjI[rotated])
           apply (rule bc_base)
           apply auto
          done
        subgoal
          apply (rule exI)
          apply (rule conjI[rotated])
           apply (rule bc_base)
           apply auto
          done
        done
      subgoal 
        apply (rule exI)
        apply (rule conjI[rotated])
         apply (rule bc_base)
         apply auto
        done
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply hypsubst_thin
          apply (rule exI)
          apply (rule conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
           apply (rule step_comp_op_L_Inp)
             apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (rule exI)
          apply (rule conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        done
      subgoal
        apply hypsubst_thin
        apply (rule exI)
        apply (rule conjI[rotated])
         apply (rule bc_base)
         apply blast
        apply auto
        done
      subgoal
        apply hypsubst_thin
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply (rule exI)
          apply (rule conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply (rule exI)
          apply (rule conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        done
      done
    subgoal for io
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for pl op1'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op3)\<close>])
          apply auto
          apply (rule bc_sym)
          apply (rule bc_base)
          apply auto
          done
        subgoal for pr op2'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2' op3)\<close>])
          apply auto
          apply (rule bc_sym)
          apply (rule bc_base)
          apply auto
          done
        done
      subgoal for p x op3'
        apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op3')\<close>])
        apply auto
        apply (rule bc_sym)
        apply (rule bc_base)
        apply auto
        done
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for pr op2'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2' op3)\<close>])
          apply auto
          apply (rule bc_sym)
          apply (rule bc_base)
          apply auto
          done
        subgoal for pl op1'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op3)\<close>])
          apply auto
          apply (rule bc_sym)
          apply (rule bc_base)
          apply auto
          done
        done
      subgoal for p x op3'
        apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op3')\<close>])
        apply (rule conjI)
         apply fastforce
        apply (rule bc_sym)
        apply (rule bc_base)
        apply auto
        done
      subgoal
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for op1'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op3)\<close>])
          apply auto
          apply (rule bc_sym)
          apply (rule bc_base)
          apply auto
          done
        subgoal for op2'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2' op3)\<close>])
          apply auto
          apply (rule bc_sym)
          apply (rule bc_base)
          apply auto
          done
        done
      subgoal for op3'
        apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op3')\<close>])
        apply (rule conjI)
         apply auto
        apply (rule bc_sym)
        apply (rule bc_base)
        apply auto
        done
      done
    done
  done

section \<open>Axiom B2: Neutral element of parallel composition\<close>

lemma pcomp_op_end_op_right_neutral:
  \<open>map_op projl projl (op \<parallel> \<oslash>) ~ op\<close>
  apply (coinduction arbitrary: op rule: bisim_coinduct_upto)
  subgoal for op
    unfolding pcomp_op_def sim_def
    apply auto
    subgoal for io op'
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply (auto simp: bc_base)
      done
    subgoal for io op'
      apply (rule exI[of _ \<open>map_op projl projl (comp_op (\<lambda>_. None) (\<lambda>_. []) op' \<oslash>)\<close>])
      apply (cases io)
        apply auto
      subgoal for p x
        apply (drule step_comp_op_L_Inp)
          apply (simp_all add: bc_base bc_sym)
        done
      subgoal for p x
        apply (drule step_comp_op_L_Out[of _ _ _ _ \<open>\<lambda>_. None\<close>])
           apply (simp_all add: bc_base bc_sym)
        done
      subgoal
        apply (drule step_comp_op_L_Tau)
          apply (simp_all add: bc_base bc_sym)
        done
      done
    done
  done

lemma pcomp_op_end_op_left_neutral:
  \<open>map_op projr projr (\<oslash> \<parallel> op) ~ op\<close>
  apply (coinduction arbitrary: op rule: bisim_coinduct_upto)
  subgoal for op
    unfolding pcomp_op_def sim_def
    apply auto
    subgoal for io op'
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply (auto simp: bc_base)
      done
    subgoal for io op'   
      apply (cases io)
      subgoal
        apply (rule exI)
        apply (rule conjI[rotated])
         apply (rule bc_sym)
         apply (rule bc_base)
         apply blast
        apply auto
        done
      subgoal
        apply (rule exI)
        apply (rule conjI[rotated])
         apply (rule bc_sym)
         apply (rule bc_base)
         apply blast
        apply auto
        done
      subgoal
        apply (rule exI)
        apply (rule conjI[rotated])
         apply (rule bc_sym)
         apply (rule bc_base)
         apply blast
        apply auto
        done
      done
    done
  done

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
   (\<exists> p x. io = Inp (Inl p) x \<and> p \<notin> defaults \<and>
     (\<exists> buf1' buf2' buf3'. op = comp_op Some buf2' (id_op (BENQ p x buf1')) (id_op buf3') \<and>
      buf1 >> buf2 >> buf3 = buf1' >> buf2' >> buf3')) \<or>

   (\<exists> p x. io = Out (Inr p) x \<and> p \<notin> defaults \<and>
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
             apply (metis (no_types, opaque_lifting) BENQ_def)
            apply (metis (no_types, opaque_lifting) BENQ_def)
           apply (metis (no_types, opaque_lifting) BENQ_def)
          apply (metis (no_types, opaque_lifting) BENQ_def)
         apply (metis (no_types, lifting) BTL_def)
        apply (metis (no_types, lifting) BTL_def)
       apply (metis (no_types, lifting) BTL_def)
      apply (metis (no_types, lifting) BTL_def)
     apply (metis (no_types, opaque_lifting) BENQ_def)
    apply (metis (no_types, lifting) BTL_def)
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
          done
        subgoal for p x buf1' buf2' buf3'
          apply hypsubst_thin
          apply simp
          apply (intro conjI[rotated] exI)
           apply (rule wbc_base)
           apply blast
          apply (rule step_wstep)
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
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)
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
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)
          done
        done
      done
    subgoal for io op1'
      apply (cases io)
      subgoal for p x
        apply hypsubst_thin
        apply (drule step_id_op_Inp)
         apply auto
        apply (rule exI[of _ "map_op projl projr (comp_op Some buf2 (id_op (BENQ p x buf1)) (id_op buf3))"])
        apply (intro conjI)
        subgoal
          apply (rule wstep_map_op[where io="Inp (Inl p) _"])
           apply simp_all
          apply (rule step_wstep)
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
        apply hypsubst_thin
        apply (drule BHD_BAPPEND_2_cases)
         apply simp
        apply (elim exE disjE conjE)
        subgoal
          apply (rule exI[of _ "map_op projl projr (comp_op Some buf2 (id_op buf1) (id_op (BTL p buf3)))"])
          apply (intro conjI)
          subgoal
            apply (rule wstep_map_op[where f=projl and g=projr and io="Out (Inr p) (BHD p buf3)", simplified])
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
                apply (auto simp add: step.intros(2))
            done
          subgoal
            apply (rule wbc_sym)
            apply (rule wbc_base)
            apply (intro exI conjI) 
             apply (rule refl)
            apply (rule arg_cong[where f=id_op])
            apply simp
            done
          done
        subgoal
          apply (rule exI[of _ "map_op projl projr (comp_op Some (BTL p buf2) (id_op buf1) (id_op buf3))"])
          apply (intro conjI)
          subgoal
            apply (rule wstep_map_op[where f=projl and g=projr and io="Out (Inr p) (BHD p buf2)", simplified])
             apply simp_all
            apply (rule step_tau_step_io_wstep[of _ "comp_op Some (BTL p buf2) (id_op buf1) (id_op (BENQ p (BHD p buf2) buf3))"])
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
               apply blast+
              apply simp_all
             apply (simp add: BENQ_def)
            apply (subst comp_op_code)
            apply (rule SC[rotated])
             apply (rule SW)
            apply simp
            apply (rule disjI2)
            apply (rule image_eqI[rotated])
             apply (simp add: Set.filter_def)
             apply (intro conjI)
              apply (rule disjI2)
              apply (intro exI[of _ p] conjI)
                apply (auto simp add: fun_upd_idem)
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
            apply (rule wstep_map_op[where f=projl and g=projr and io="Out (Inr p) (BHD p buf1)", simplified])
             apply simp_all
            apply (rule step_tau_step_tau_step_io_wstep[of _ "comp_op Some (BENQ p (BHD p buf1) buf2) (id_op (BTL p buf1)) (id_op buf3)" "comp_op Some (BTL p (BENQ p (BHD p buf1) buf2)) (id_op (BTL p buf1)) (id_op (BENQ p (BHD p buf1) buf3))"])
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
                 apply (auto simp add: )
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
  using id_id_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] by auto

lemma scomp_op_id_op_right_neutral:
  "op\<turnstile> \<bullet> \<I> \<approx> op\<turnstile>"
  using bisim_wbisim scomp_op_assoc scomp_op_id_id wbisim_refl wbisim_scomp_op_cong wbisim_trans by blast

lemma scomp_op_id_op_left_neutral:
  "\<I> \<bullet> \<stileturn>op \<approx> \<stileturn>op"
  by (smt (verit, best) bisim_wbisim scomp_op_assoc scomp_op_id_id wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans)


section \<open>Axiom B5: Parallel and sequential distributes\<close>

lemma pcomp_op_scomp_distributes_bufs:
  \<open>map_op projl projr (comp_op Some (case_sum buf1 buf2) (op1 \<parallel> op2) (op3 \<parallel> op4))
  ~ (map_op projl projr (comp_op Some buf1 op1 op3)) \<parallel> (map_op projl projr (comp_op Some buf2 op2 op4))\<close>
  apply (coinduction arbitrary: buf1 buf2 op1 op2 op3 op4 rule: bisim_coinduct_upto)
  subgoal for buf1 buf2 op1 op2 op3 op4
    unfolding sim_def pcomp_op_def
    apply auto
    subgoal for io
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal 
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal 
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        done
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p' op4'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf1 op1 op3))
             (map_op projl projr (comp_op Some buf2 op2 op4'))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_base)
          apply fast
          done
        subgoal for p' op3'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf1 op1 op3'))
             (map_op projl projr (comp_op Some buf2 op2 op4))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_base)
          apply fast
          done
        done
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done     
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done     
        done
      subgoal for p op2'
        apply hypsubst_thin
        apply (cases p)
         apply simp_all
        subgoal
          apply (drule step_comp_op_cases)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply (rule step_comp_op_L_Tau)
            apply auto
          done
        subgoal
          apply (drule step_comp_op_cases)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply (rule step_comp_op_R_Tau)
            apply auto
          done
        done
      subgoal
        apply hypsubst_thin
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        done
      subgoal
        apply hypsubst_thin
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_base)
           apply blast
          apply auto
          done
        done
      done
    subgoal for io
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for op1'
          apply (rule exI[of _ \<open>map_op projl projr
                (comp_op Some (case_sum buf1 buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' op2)
                  (comp_op (\<lambda>_. None) (\<lambda>_. []) op3 op4))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        done
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for op4'
          apply (rule exI[of _ \<open>map_op projl projr
                (comp_op Some (case_sum buf1 buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2)
                  (comp_op (\<lambda>_. None) (\<lambda>_. []) op3 op4'))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        done
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for op3'
          apply (rule exI[of _ \<open>map_op projl projr
                (comp_op Some (case_sum buf1 buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2)
                  (comp_op (\<lambda>_. None) (\<lambda>_. []) op3' op4))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        done
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for op2'
          apply (rule exI[of _ \<open>map_op projl projr
                (comp_op Some (case_sum buf1 buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2')
                  (comp_op (\<lambda>_. None) (\<lambda>_. []) op3 op4))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        done
      subgoal
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply auto
          done
        done
      subgoal
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
           apply hypsubst_thin
        subgoal
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_comp_op_R_Inp)
                   apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply auto
          done
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply auto
          done
        done
      done
    done
  done

lemma pcomp_op_scomp_distributes:
  \<open>(op1 \<parallel> op2) \<bullet> (op3 \<parallel> op4) ~ (op1 \<bullet> op3) \<parallel> (op2 \<bullet> op4)\<close>
  unfolding scomp_op_def
  using pcomp_op_scomp_distributes_bufs[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by auto

section \<open>Axiom B6: Parallel composition of identities\<close>



lemma pcomp_op_id_id_bufs:
  \<open>id_op buf1 \<parallel> id_op buf2 ~ id_op (case_sum buf1 buf2)\<close>
  apply (coinduction arbitrary: buf1 buf2 rule: bisim_coinduct_upto)
  subgoal for buf1 buf2
    unfolding pcomp_op_def sim_def
    apply auto
    subgoal for io op
      apply (drule step_comp_op_cases)
      apply auto
      subgoal
        apply (drule step_id_op_Inp)
         apply auto
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
         apply blast
        apply (metis Inr_Inl_False PlusE Plus_def case_sum_BENQ_L defaults_sum_def step_id_op_Read sum.sel(1))
        done
      subgoal 
        apply (drule step_id_op_Out)
         apply auto
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
         apply blast
        apply auto
        done
      subgoal 
        apply (drule step_id_op_Out)
         apply auto
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
         apply blast
        apply auto
        done
      subgoal
        apply (drule step_id_op_Inp)
         apply auto
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
         apply blast
        apply (metis Inr_Inl_False Inr_inject PlusE Plus_def case_sum_BENQ_R defaults_sum_def step_id_op_Read)
        done
      done
    subgoal for io op
      apply (cases io)
      subgoal for p x
        apply (cases p)
        subgoal for lp
          apply (drule step_id_op_Inp)
           apply auto
          apply hypsubst_thin
          apply (intro conjI[rotated] exI)
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply (auto simp add: defaults_sum_def step_comp_op_L_Inp step_id_op_Read)
          done
        subgoal for p
          apply (drule step_id_op_Inp)
           apply auto
          apply hypsubst_thin
          apply (intro conjI[rotated] exI)
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply (rule step_comp_op_R_Inp)
             apply auto
          done
        done
      subgoal for p x
        apply (cases p)
        subgoal
          apply (drule step_id_op_Out)
           apply auto
          apply hypsubst_thin
          apply (intro conjI[rotated] exI)
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply (simp add: defaults_sum_def image_iff step_comp_op_L_Out step_id_op_Write)
          done
        subgoal
          apply (drule step_id_op_Out)
           apply auto
          apply hypsubst_thin
          apply (intro conjI[rotated] exI)
           apply (rule bc_sym)
           apply (rule bc_base)
           apply blast
          apply (simp add: defaults_sum_def image_iff step_comp_op_R_Out step_id_op_Write)
          done
        done
      subgoal
        by force
      done
    done
  done


lemma pcomp_op_id_id:
  \<open>\<I> \<parallel> \<I> ~ \<I>\<close>
  using pcomp_op_id_id_bufs[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

section \<open>Axiom B7: Transpose of transpose is identity\<close>

lemma comp_op_transp_transp_id_bufs:
  \<open>map_op projl projr (comp_op Some buf2 (transp_op buf1) (transp_op buf3))
  \<approx> id_op (buf1 >> (buf2 >> buf3 \<circ> case_sum Inr Inl))\<close>
  apply (coinduction arbitrary: buf1 buf2 buf3 rule: wbisim_coinduct_upto)
  subgoal for buf1 buf2 buf3
    unfolding wsim_def
    apply auto
    subgoal for io
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (erule step_transp_op_Inp)
         apply simp
        apply (rule exI[of _ \<open>id_op ((BENQ p x buf1) >> (buf2 >> buf3 \<circ> case_sum Inr Inl))\<close>])
        apply auto
        done
      subgoal for p x
        apply (erule step_transp_op_Out)
          apply simp_all
        apply (intro exI conjI[rotated])
         apply (rule wbc_base)
         apply fast
        apply (cases p)
        subgoal for lp
          apply (rule step_wstep)
          apply auto
           apply (metis BHD_BULK_BENQ_cases BULK_BENQ_empty case_sum_BHD_L case_sum_BHD_R case_sum_Inl_Inr_L o_case_sum)
          apply (simp add: BULK_BENQ_BTL_right_not_empty_case_sum)
          done
        subgoal for rp
          apply (rule step_wstep)
          apply auto
           apply (metis BHD_BULK_BENQ_cases BULK_BENQ_empty case_sum_BHD_L case_sum_BHD_R case_sum_expand_Inr_pointfree o_case_sum)
          apply (simp add: BULK_BENQ_BTL_right_not_empty_case_sum)
          done
        done
      subgoal for p x
        apply (erule step_transp_op_Out)
          apply simp_all
        apply (rule exI[of _ \<open>id_op (buf1 >> (buf2 >> buf3 \<circ> case_sum Inr Inl))\<close>])
        apply simp
        apply (rule wbc_base)
        apply (rule exI[of _ \<open>BTL (case_sum Inr Inl p) buf1\<close>])
        apply (rule exI[of _ \<open>BENQ p x buf2\<close>])
        apply (rule exI[of _ buf3])
        apply auto
        using BAPPEND_BENQ_BHD[of _ \<open>case_sum Inr Inl p\<close> \<open>buf2 >> buf3 \<circ> case_sum Inr Inl\<close>]
        apply (simp add: BENQ_case_sum_compose)
        done
      subgoal for p
        apply (erule step_transp_op_Inp)
         apply simp
        apply (rule exI[of _ \<open>id_op (buf1 >> (buf2 >> buf3 \<circ> case_sum Inr Inl))\<close>])
        apply simp
        apply (rule wbc_base)
        apply fastforce
        done
       apply (rule no_step_transp_op_Tau, simp_all)+
      done
    subgoal for io
      apply (erule step_id_op_cases)
      subgoal for p x
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some buf2 (transp_op (BENQ p x buf1)) (transp_op buf3))\<close>])
        apply auto
        apply blast
        done
      subgoal for p x
        apply hypsubst_thin
        apply (drule BHD_BULK_BENQ_cases)
         apply (auto simp del: BULK_BENQ_empty)
        subgoal
          apply (drule BHD_BULK_BENQ_cases)
           apply auto
          subgoal
            apply (rule exI[of _ \<open>map_op projl projr (comp_op Some buf2 (transp_op buf1) (transp_op (BTL (case_sum Inr Inl p) buf3)))\<close>])
            apply (rule conjI[rotated])
            subgoal
              apply (rule wbc_sym)
              apply (rule wbc_base)
              apply (rule exI)
              apply (rule exI)
              apply (rule exI[of _ \<open>BTL (case_sum Inr Inl p) buf3\<close>])
              apply (auto simp: BULK_BENQ_BTL_right_not_empty_case_sum)
              done
            subgoal
              apply (simp split: sum.splits)
              subgoal
                apply (rule step_wstep)
                apply auto
                apply (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty comp_eq_dest_lhs old.sum.simps(5))
                done
              subgoal
                apply (rule step_wstep)
                apply auto
                apply (metis BHD_BULK_BENQ_right_not_empty BHD_def comp_apply old.sum.simps(6))
                done
              done
            done
          subgoal
            apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (BTL (case_sum Inr Inl p) buf2) (transp_op buf1) (transp_op buf3))\<close>])
            apply (rule conjI[rotated])
            subgoal
              apply (rule wbc_sym)
              apply (rule wbc_base)
              apply (rule exI)
              apply (rule exI[of _ \<open>BTL (case_sum Inr Inl p) buf2\<close>])
              apply (rule exI)
              using BTL_case_sum_compose[of \<open>case_sum Inr Inl p\<close> \<open>buf2 >> buf3\<close>]
              apply (simp split: sum.splits)
              done
            subgoal
              apply (cases p)
              subgoal for lp
                apply simp
                apply (rule step_tau_step_io_wstep)
                 apply (rule step_map_op[of Tau])
                  apply (rule step_Tau_comp_op_R[where p="Inr lp"])
                       apply (rule step_transp_op_Read)
                        apply simp_all
                apply (rule step_map_op[of "Out (Inr (Inl lp)) _"])
                 apply (rule step_comp_op_R_Out)
                   apply (rule step_transp_op_Write[where p="Inr lp"])
                       apply simp_all
                apply (simp add: BHD_def)
                done
              subgoal for rp
                apply simp
                apply (rule step_tau_step_io_wstep)
                 apply (rule step_map_op[of Tau])
                  apply (rule step_Tau_comp_op_R[where p="Inl rp"])
                       apply (rule step_transp_op_Read)
                        apply simp_all
                apply (rule step_map_op[of "Out (Inr (Inr rp)) _"])
                 apply (rule step_comp_op_R_Out)
                   apply simp_all
                apply (rule step_transp_op_Write[where p="Inl rp"])
                    apply simp_all
                apply (simp add: BHD_def)
                done
              done
            done
          done
        subgoal
          apply (cases p)
          subgoal for lp
            apply simp
            apply (intro conjI[rotated] exI)
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply (rule exI)
             apply blast
            apply (rule step_tau_step_tau_step_io_wstep)
              apply (rule step_map_op[of Tau])
               apply simp_all
              apply (rule step_Tau_comp_op_L[where p="Inr lp"])
                 apply simp_all
              apply (rule step_transp_op_Write)
                  apply simp_all
              apply simp_all
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_comp_op_R[where p="Inr lp"])
                  apply simp_all
             apply (rule step_transp_op_Read)
              apply simp_all
            apply (rule step_map_op[of "Out (Inr (Inl lp)) _"])
             apply simp_all
            apply (rule step_comp_op_R_Out)
              apply simp_all
            apply auto
            done
          subgoal for rp
            apply simp
            apply (intro conjI[rotated] exI)
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply (rule exI)
             apply blast
            apply (rule step_tau_step_tau_step_io_wstep)
              apply (rule step_map_op[of Tau])
               apply simp_all
              apply (rule step_Tau_comp_op_L)
                 apply force
                apply simp_all
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_comp_op_R[where p="Inl rp"])
                  apply auto
                apply simp_all
            apply auto
            done
          done
        done
      done
    done
  done

lemma scomp_op_transp_transp_id:
  \<open>\<X> \<bullet> \<X> \<approx> \<I>\<close>
  using comp_op_transp_transp_id_bufs[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  unfolding scomp_op_def
  by (auto simp: o_def)

(* lemma map_IO_eq_Out[intro!]:
  "\<exists> p'. g p' = p \<and> IO = Out p' x \<Longrightarrow>
   map_IO f g id IO = Out p x"
  by auto *)

section \<open>Axiom B9: Transpose decomposes in parallel and sequential composition\<close>
lemma trans_op_decomposes_scomp_op_pcomp_op_gen:
  "transp_op (case_sum (buf1 >> buf1' >> buf1'') (case_sum (buf2 >> buf2' >> buf2'') (buf3 >> buf3' >> buf3''))) \<approx>
   map_op projl projr (comp_op Some (case_sum buf2' (case_sum buf1' buf3'))
   (map_op BNA_Operators.reassoc BNA_Operators.reassoc (transp_op (case_sum buf1 buf2) \<parallel> id_op buf3))
   (map_op id BNA_Operators.assoc (id_op buf2'' \<parallel> transp_op (case_sum buf1'' buf3''))))"
  apply (coinduction arbitrary: buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf3'' rule: wbisim_coinduct_upto)
  subgoal for buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf3''
    unfolding wsim_def
    apply auto
    subgoal for io op'
      apply (erule step_transp_op_cases)
      subgoal for p x
        apply (auto; hypsubst_thin?)
        apply (cases p)
        subgoal for lp
          apply hypsubst_thin
          apply (intro exI conjI[rotated])        
           apply (rule wbc_base)
           apply force
          unfolding pcomp_op_def
          using step_wstep[OF step_map_op[OF step_comp_op_L_Inp[OF step_map_op[OF step_comp_op_L_Inp]]], simplified]
          apply (metis BNA_Operators.reassoc.simps(1) Inl_in_defaults case_sum_BENQ_L step_transp_op_Read sum.sel(1))
          done
        subgoal for rp
          apply hypsubst_thin
          apply (cases rp)
          subgoal for lp
            apply hypsubst_thin
            apply (intro exI conjI[rotated])        
             apply (rule wbc_base)
             apply force
            apply (rule step_wstep)
            apply (rule step_map_op)
             apply (rule step_comp_op_L_Inp)
               apply (rule step_map_op)
            unfolding pcomp_op_def
                apply (rule step_comp_op_L_Inp)
                  apply (rule step_transp_op_Read)
                   apply auto
            done
          subgoal for rp
            apply hypsubst_thin
            apply (intro exI conjI[rotated])        
             apply (rule wbc_base)
             apply force
            apply (rule step_wstep)
            apply (rule step_map_op)
             apply simp_all
             apply (rule step_comp_op_L_Inp)
               apply (rule step_map_op)
            unfolding pcomp_op_def
                apply (rule step_comp_op_R_Inp)
                   apply (rule step_id_op_Read)
                    apply auto
            done
          done
        done
      subgoal for p x p'
        apply (cases p)
        subgoal for lp
          apply (cases lp)
          subgoal for lp
            apply (auto; hypsubst_thin?)
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_tau_step_io_wstep)
               apply (rule step_map_op)
                apply simp_all
               apply (rule step_Tau_comp_op_R)
                    apply (rule step_map_op)
                     apply (rule step_comp_op_L_Inp)
                       apply blast
                      apply simp_all
               apply simp
              apply (rule step_map_op)
               apply simp_all
               apply (rule step_comp_op_R_Out)
                 apply auto
              done
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply force+
              done
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply blast
              unfolding pcomp_op_def
              apply (rule step_tau_step_tau_step_io_wstep)
                apply (rule step_map_op)
                 apply (rule step_Tau_comp_op_L)
                    apply (rule step_map_op)
                     apply (rule step_comp_op_L_Out)
                        apply (rule step_transp_op_Write)
                            apply simp_all
                 prefer 3
                 apply (rule step_map_op)
                  apply (rule step_Tau_comp_op_R)
                       apply (rule step_map_op)
                        apply (rule step_comp_op_L_Inp)
                          apply (rule step_id_op_Read)
                           apply (auto simp add: BHD_def split: sum.splits)
              done
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply blast
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply auto
              done
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply blast
              unfolding pcomp_op_def
              apply (rule step_tau_step_io_wstep)
               apply (rule step_map_op)
                apply (rule step_Tau_comp_op_R)
                     apply (rule step_map_op)
                      apply (rule step_comp_op_L_Inp)
                        apply (rule step_id_op_Read)
                         apply (auto split: sum.splits)
              done
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply blast
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply auto
              done
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply blast
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply auto
              done
            subgoal
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply blast
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply auto
              done
            done
          subgoal for rp
            apply auto
            subgoal
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_tau_step_io_wstep)
               apply (rule step_map_op)
                apply (rule step_Tau_comp_op_R)
                     apply (rule step_map_op)
                      apply (rule step_comp_op_R_Inp)
                         apply (rule step_transp_op_Read)
                          apply (simp_all split: sum.splits)
                apply auto
               apply auto
              done
            subgoal 
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply (rule step_map_op[of "Out (Inr (Inl (Inr rp))) _"])
               apply simp_all
              apply (rule step_comp_op_R_Out)
                apply (rule step_map_op[of "Out (Inr (Inl _)) _"])
                 apply simp_all
              apply auto  
              done
            subgoal 
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_tau_step_tau_step_io_wstep)
                apply (rule step_map_op[of Tau])
                 apply force
                apply simp
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_comp_op_R)
                    apply (rule step_map_op)
                     apply (rule step_comp_op_R_Inp)
                        apply (rule step_transp_op_Read)
                         apply (auto split: sum.splits)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_transp_op_Write)
                     apply auto
              done
            subgoal 
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply (auto 2 2)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_transp_op_Write)
                     apply auto
              done
            subgoal 
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_tau_step_io_wstep)
               apply (rule step_map_op)
                apply (rule step_Tau_comp_op_R)
                     apply (rule step_map_op)
                      apply (rule step_comp_op_R_Inp)
                         apply (rule step_transp_op_Read)
                          apply (auto split: sum.splits)
               apply auto
              done
            subgoal 
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply force
              done
            subgoal
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply force
              done
            subgoal
              apply hypsubst_thin
              apply (intro exI conjI[rotated])        
               apply (rule wbc_base)
               apply force
              unfolding pcomp_op_def
              apply (rule step_wstep)
              apply force
              done
            done
          done
        subgoal for lp
          apply simp
          apply (simp split: if_splits; hypsubst_thin?)
          subgoal 
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force
            unfolding pcomp_op_def
            apply auto
            apply (rule wstep_trans_tau_1)
             apply (rule step_Tau_comp_op_L)
                apply (rule step_map_op)
                 apply simp_all
              apply (rule step_comp_op_L_Out)
                 apply (rule step_transp_op_Write)
                     apply (rule refl)+
                    apply auto
            apply (rule wstep_trans_tau_1)
             apply (rule step_Tau_comp_op_R)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Inp)
                      apply (rule step_transp_op_Read)
                       apply auto
            apply (rule step_wstep)
            apply auto+
            done
          subgoal 
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force
            unfolding pcomp_op_def
            apply auto
            apply (rule wstep_trans_tau_1)
             apply (rule step_Tau_comp_op_R)
                  apply (rule step_map_op)
                   apply (rule step_comp_op_R_Inp)
                      apply (rule step_transp_op_Read)
                       apply auto
            apply (rule step_wstep)
            apply auto+
            done
          apply (intro exI conjI[rotated])  
           apply (rule wbc_base)
           apply force
          unfolding pcomp_op_def
          apply auto
          apply force
          done
        done
      done
    subgoal for io op'
      unfolding pcomp_op_def
      apply (drule step_map_op_inv)
      apply (auto; hypsubst_thin?)
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x op''
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        subgoal for io op''
          apply (drule step_comp_op_cases)
          apply (auto; hypsubst_thin?)
          subgoal for p op''
            apply (erule step_transp_op_cases)
             apply (auto; hypsubst_thin?)
            subgoal
              apply (cases p)
              subgoal for lp
                apply (auto; hypsubst_thin?)
                apply (intro exI conjI[rotated])  
                 apply (rule wbc_sym)
                 apply (rule wbc_base)
                 apply force+
                done
              subgoal for rp
                apply (auto; hypsubst_thin?)
                apply (intro exI conjI[rotated])  
                 apply (rule wbc_sym)
                 apply (rule wbc_base)
                 apply force+
                done
              done
            subgoal
              by simp
            done
          subgoal for p op''
            apply (erule step_id_op_cases)
             apply (auto; hypsubst_thin?)
            subgoal
              apply (intro exI conjI[rotated])  
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force+
              done
            subgoal
              by simp
            done
          done
        done
      subgoal for p x op'
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        apply (drule step_comp_op_cases)
        apply (auto; hypsubst_thin?)
        subgoal for p op'
          apply (erule step_transp_op_cases)
           apply (auto; hypsubst_thin?)
          subgoal for p x p'
            apply (cases p)
             apply (auto; hypsubst_thin?)
            subgoal for lp
              apply (intro exI conjI[rotated])  
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force
              apply (rule step_wstep)
              apply auto
              done
            subgoal for rp
              apply (auto; hypsubst_thin?)
              apply (intro exI conjI[rotated])  
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force
              apply (rule step_wstep)
              apply (rule step_transp_op_Write)
                  apply auto
              done
            done
          done
        subgoal for p op
          apply (drule step_id_op_Out)
           apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force
          apply (rule step_wstep)
          apply (rule step_transp_op_Write)
              apply auto
          done
        done
      subgoal for p x op'
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        apply (drule step_comp_op_cases)
        apply (auto; hypsubst_thin?)
        subgoal for p op2
          apply (drule step_id_op_Out)
           apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force+
          done
        subgoal for p op2
          apply (cases p)
          subgoal for lp
            apply (erule step_transp_op_Out)
              apply auto
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply force+
            done
          subgoal for rp
            apply (erule step_transp_op_Out)
              apply auto
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply force+
            done
          done
        done
      subgoal for p op
        apply (cases p)
        subgoal for lp
          apply (drule step_map_op_inv)
          apply (auto; hypsubst_thin?)
          apply (drule step_comp_op_cases)
          apply (auto; hypsubst_thin?)
          apply (drule step_id_op_Inp)
           apply (auto; hypsubst_thin?)
          apply (intro exI conjI[rotated])  
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
          done
        subgoal for rp
          apply (cases rp; auto)
          subgoal for lp
            apply (drule step_map_op_inv)
            apply (auto; hypsubst_thin?)
            apply (drule step_comp_op_cases)
            apply (auto; hypsubst_thin?)
            apply (erule step_transp_op_Inp)
             apply auto
            apply (intro exI conjI[rotated])  
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply force
            apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
            done
          subgoal for rp
            apply (drule step_map_op_inv)
            apply (auto; hypsubst_thin?)
            apply (drule step_comp_op_cases)
            apply (auto; hypsubst_thin?)
            apply (erule step_transp_op_Inp)
             apply auto
            apply (intro exI conjI[rotated])  
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply force
            apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
            done
          done
        done
      subgoal for op1
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        apply (drule step_comp_op_cases)
        apply (auto elim: no_step_transp_op_Tau no_step_id_op_Tau)
        done
      subgoal for op2'
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        apply (drule step_comp_op_cases)
        apply (auto elim: no_step_transp_op_Tau no_step_id_op_Tau)
        done
      done
    done
  done

lemma trans_op_decomposes_scomp_op_pcomp_op:
  assumes "\<X>klm = (\<X> :: ('k :: {countable,defaults} + 'l :: {countable,defaults} + 'm :: {countable,defaults}, ('l + 'm) + 'k, 'c) op)"
    and "\<X>kl = (\<X> :: ('k + 'l, 'l + 'k, 'c) op)"
    and "\<X>km = (\<X> :: ('k + 'm, 'm + 'k, 'c) op)"
    and "\<I>m = (\<I> :: ('m, 'm, 'c) op)"
    and "\<I>l = (\<I> :: ('l, 'l, 'c) op)"
  shows "\<X>klm \<approx> map_op reassoc reassoc (\<X>kl \<parallel> \<I>m) \<bullet> map_op id assoc (\<I>l \<parallel> \<X>km)"
  using assms unfolding scomp_op_def
  apply hypsubst_thin
  using trans_op_decomposes_scomp_op_pcomp_op_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] by auto

section \<open>Axiom B10: Transpose commutes with sequential composition of parallel operators\<close>

lemma transp_op_commutes_scomp_op_pcomp_op_bufs:
  \<open>map_op projl projr (comp_op Some (case_sum buf1''' buf2''')
    (map_op projl projr (comp_op Some buf1' (id_op buf1) op1) \<parallel> map_op projl projr (comp_op Some buf2' (id_op buf2) op2))
    (transp_op (case_sum buf1'' buf2'')))
  \<approx> map_op projl projr (comp_op Some (case_sum buf2' buf1')
    (transp_op (case_sum buf1 buf2))
    (map_op projl projr (comp_op Some buf2''' op2 (id_op buf2'')) \<parallel> map_op projl projr (comp_op Some buf1''' op1 (id_op buf1''))))\<close>
  apply (coinduction arbitrary: op1 op2 buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2''' rule: wbisim_coinduct_upto)
  subgoal for op1 op2 buf1 buf1' buf1'' buf1''' buf2 buf2' buf2'' buf2'''
    unfolding wsim_def pcomp_op_def
    apply auto
    subgoal for io
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          apply (drule step_id_op_Inp)
           apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_base)
           apply force
          apply auto
          done
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          apply (drule step_id_op_Inp)
           apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_base)
           apply force
          apply auto
          done
        done
      subgoal for p x
        apply (erule step_transp_op_Out)
          apply (auto split: sum.splits)
        subgoal for p'
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_base)
           apply force
          apply auto
          done
        subgoal for p'
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_base)
           apply force
          apply auto
          done
        done
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for op2'
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force
            apply auto
            done
          done
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for op1'
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force+
            done
          done
        done
      subgoal for p
        apply (erule step_transp_op_Inp)
         apply (auto split: sum.splits)
        subgoal for p'
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_base)
           apply force+
          done
        subgoal for p'
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_base)
           apply force+
          done
        done
      subgoal
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for p x
            apply (drule step_id_op_Out)
             apply auto
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force+
            done
          subgoal for p op1'
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force+
            done
          subgoal
            using no_step_id_op_Tau
            apply blast
            done
          done
        subgoal
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for p x
            apply (drule step_id_op_Out)
             apply auto
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force+
            done
          subgoal for p op2'
            apply hypsubst_thin
            apply (intro exI conjI[rotated])  
             apply (rule wbc_base)
             apply force+
            done
          subgoal for op2'
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply blast
            apply blast
            done
          done
        done
      subgoal
        using no_step_transp_op_Tau
        apply blast
        done
      done
    subgoal for io
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (erule step_transp_op_Inp)
         apply auto
        apply (cases p)
        subgoal for p'
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply fastforce+
          done
        subgoal for p'
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply fastforce+
          done
        done
      subgoal for p x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          apply (drule step_id_op_Out)
           apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force+
          done
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          apply (drule step_id_op_Out)
           apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])  
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force+
          done
        done
      subgoal for p x
        apply (drule step_transp_op_Out)
           apply (auto split: sum.splits)
        subgoal for p'
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply fast+
          done
        subgoal for p'
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply fast+
          done
        done
      subgoal for p
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for op2'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          done
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for op1'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          done
        done
      subgoal
        using no_step_transp_op_Tau
        apply blast
        done
      subgoal
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for p x op2'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          subgoal for p
            apply (drule step_id_op_Inp)
             apply simp
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          subgoal for op2'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          done
        subgoal
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for p x op1'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          subgoal for p
            apply (drule step_id_op_Inp)
             apply simp
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          subgoal for op1'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply fast
            apply fastforce
            done
          done
        done
      done
    done
  done

thm transp_op_commutes_scomp_op_pcomp_op_bufs[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> _ \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> _  \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
lemma transp_op_commutes_scomp_op_pcomp_op:
  \<open>(\<stileturn>op1 \<parallel> \<stileturn>op2) \<bullet> \<X> \<approx> \<X> \<bullet> (op2\<turnstile> \<parallel> op1\<turnstile>)\<close>
  using transp_op_commutes_scomp_op_pcomp_op_bufs[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> _ \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> _  \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  unfolding scomp_op_def
  by auto

(* FIXME: move me *)
lemma rtranclp_intros_1':
  "a = b \<Longrightarrow> r\<^sup>*\<^sup>* a b"
  by auto

(* FIXME: move me *)
lemma Inl_notin_ran_feedback_wire[simp]:
  "Inl p \<notin> ran (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
  by (auto simp add: ran_def  split: sum.splits if_splits)
term scomp_op

(* FIXME: move me *)
lemma step_inputs_outputs:
  "step io op op' \<Longrightarrow>
   inputs op' \<subseteq> inputs op \<and> outputs op' \<subseteq> outputs op"
  by (induct io op op' pred: step) auto

lemma wbisim_coinduct_upto_alt[consumes 1, case_names BISIM]:
  "R op1 op2 \<Longrightarrow> (\<And>s t. R s t \<Longrightarrow> wsim (wbisim_cong R) s t \<and> wsim (wbisim_cong R) t s) \<Longrightarrow> op1 \<approx> op2"
  using wbisim_coinduct_upto by blast

lemma step_map_op_elim[]:
  assumes  "step io (map_op f g op) op'"
  obtains io' op'' where "step io' op op'' \<and> map_IO f g id io' = io \<and> map_op f g op'' = op'"
  apply atomize
  apply (simp add: assms step_map_op_inv)
  done

lemma step_comp_op_elim[]:
  assumes "step io (comp_op wire buf op1 op2) op"
  obtains p x op1' where "io = Inp (Inl p) x" "op = comp_op wire buf op1' op2" "step (Inp p x) op1 op1'" |
    p x op2' where "io = Out (Inr p) x" "op = comp_op wire buf op1 op2'" "step (Out p x) op2 op2'" |
    p x op1' where "io = Out (Inl p) x" "op = comp_op wire buf op1' op2" "wire p = None" "step (Out p x) op1 op1'" |
    p x op2' where "io = Inp (Inr p) x" "op = comp_op wire buf op1 op2'" "p \<notin> ran wire" "step (Inp p x) op2 op2'" |
    p x op1' q where "io = Tau" "op = comp_op wire (BENQ q x buf) op1' op2" "wire p = Some q" "step (Out p x) op1 op1'" |
    p x op2' where "io = Tau" "op = comp_op wire (BTL p buf) op1 op2'" "p \<in> ran wire" "step (Inp p x) op2 op2'" "buf p \<noteq> []" "BHD p buf = x" |
    p x op1' where "io = Tau" "op = comp_op wire buf op1' op2" "step Tau op1 op1'" |
    p x op2' where "io = Tau" "op = comp_op wire buf op1 op2'" "step Tau op2 op2'"
  using assms apply -
  apply (drule step_comp_op_cases[where io=io and wire=wire and buf=buf, of op1 op2 op])
  apply auto
  done


lemma step_loop_op_elim:
  assumes "step io (loop_op wire buf op) op'"
  obtains
    p x op'' where "p \<notin> ran wire" "io = Inp p x" "op' = loop_op wire buf op''" "step io op op''" |
    p x op'' where "wire p = None" "io = Out p x" "op' = loop_op wire buf op''" "step io op op''" |
    op'' where "io = Tau" "op' = loop_op wire buf op''" "step io op op''" |
    op'' p x where "io = Tau" "p \<in> ran wire" "op' = loop_op wire (BTL p buf) op''" "step (Inp p x) op op''" "buf p \<noteq> []" "BHD p buf = x" |
    op'' p q x where "io = Tau" "wire p = Some q" "op' = loop_op wire (BENQ q x buf) op''" "step (Out p x) op op''"
  using assms apply -
  apply (drule step_loop_op_gen)
  apply auto
  done

lemma step_id_op_Inp_elim:
  assumes  "step (Inp p x) (id_op buf) op'"
  obtains "op' = id_op (BENQ p x buf)" "p \<notin> defaults"
  apply atomize
  apply (meson assms step_id_op_Inp)
  done

lemma step_id_op_Out:
  assumes  "step (Out p x) (id_op buf) op'"
  obtains "op' = id_op (BTL p buf)" "BHD p buf = x" "buf p \<noteq> []" "p \<notin> defaults"
  apply atomize
  apply (meson assms step_id_op_Out)
  done

lemma loop_op_scomp_commute_gen:
  fixes op1 :: "('a + 'm :: {countable, defaults}, 'b + 'm, 'd) op"
    and op2 :: "('c, 'a, 'd) op"
  assumes "Inr -` inputs op1 \<inter> defaults = {}"
    and "Inr -` outputs op1 \<inter> defaults = {}"
  shows "map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda> _. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1))) \<approx>
   map_op projl projl (loop_op (case_sum (\<lambda> _. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))"
  using assms
proof (coinduction arbitrary: op1 op2 buf2 lbuf1 lbuf2 lbuf3 rule: wbisim_coinduct_upto_alt)
  case BISIM
  then show ?case 
    unfolding wsim_def
  proof (intro conjI allI impI)
    fix io :: "('c, 'b, 'd) IO"
      and op1' :: "('c, 'b, 'd) op"
    assume "Inr -` inputs op1 \<inter> defaults = {}"
      and "Inr -` outputs op1 \<inter> defaults = {}"
      and H: "step io (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)))) op1'"
    then show "\<exists>op2'. wstep io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op1' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Inp p x) op2 op1'"
        for p :: 'c
          and x :: 'd
          and op1' :: "('c, 'a, 'd) op"
        using that by (fastforce del: wbc_base intro!: wbc_base)
      moreover have "\<exists>op2'. wstep (Out p x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)))) op2'"
        if  "Inr -` inputs op1 \<inter> defaults = {}"
          and  "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Out (Inl p) x) op1 op''b"
        for p :: 'b
          and x :: 'd
          and op''b :: "('a + 'm, 'b + 'm, 'd) op"
      proof -
        from that have "wstep (Out p x) (map_op projl projl
       (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
         (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))))
     (map_op projl projl
       (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
         (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op''b))))"
          using step_inputs_outputs by force
        then show ?thesis
          using step_inputs_outputs that by (smt (z3) disjoint_iff subsetD vimage_mono wbisim_cong.intros(1))
      qed
      moreover have "\<exists>op2'. wstep (Out (projl (Inr pa)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "pa \<in> defaults"
          and "step (Out (Inr pa) x) op1 op''b"
        for x :: 'd
          and pa :: 'm
          and op''b :: "('a + 'm, 'b + 'm, 'd) op"
        using that 
        by (metis (no_types, lifting) IO.distinct(1) IO.sel(4) IO.simps(8) disjoint_iff_not_equal op.set_intros(8) outputs_after_choices step_choicesE vimageI)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some (BENQ q x buf2) op1' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Out q x) op2 op1'"
        for x :: 'd
          and op1' :: "('c, 'a, 'd) op"
          and q :: 'a
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum (BENQ q x buf2) lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (id_op lbuf2)) op1)))"
          by (rule step_Tau_loop_op, auto intro!: that(3))
        from this that show ?thesis
          by (auto del: exI intro!: exI conjI[rotated, OF wbc_base])
      qed
      moreover have  H1: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some (BTL p buf2) op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "buf2 p \<noteq> []"
          and "step (Inp (Inl p) (BHD p buf2)) op1 op''b"
        for p :: 'a
          and op''b :: "('a + 'm, 'b + 'm, 'd) op"
        using that 
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum (BTL p buf2) lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op''b)))"
          apply (rule step_Tau_loop_op)
          using that apply auto
          done
        from this that show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
          using step_inputs_outputs apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some (BTL (projl (Inr pa)) buf2) op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "buf2 (projl (Inr pa)) \<noteq> []"
          and "pa \<in> defaults"
          and "step (Inp (Inr pa) (BHD (projl (Inr pa)) buf2)) op1 op''b"
        for pa :: 'm
          and op''b :: "('a + 'm, 'b + 'm, 'd) op"
        using that 
        apply -
        apply (rule FalseE)
        apply (metis IO.inject(1) IO.simps(4) IO.simps(6) Read_choices_inputs disjoint_iff step_choicesE vimageI)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op1' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op2 op1'"
        for op1' :: "('c, 'a, 'd) op"
        using that
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (id_op lbuf2)) op1)))"
          using that by (auto del: step_Tau_loop_op intro!: step_Tau_loop_op)
        from this that show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
          using step_inputs_outputs apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op1 op''b"
        for op''b :: "('a + 'm, 'b + 'm, 'd) op"
        using that
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have H2: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> BTL pa lbuf2) >> lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "pa \<notin> defaults"
          and "step (Inp (Inr pa) (BHD pa lbuf2)) op1 op''b"
          and "lbuf2 pa \<noteq> []"
          and "lbuf3 pa = []"
        for op''b :: "('a + 'm, 'b + 'm, 'd) op"
          and pa :: 'm
        using that
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa lbuf2)lbuf3)) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL pa lbuf2))) op1)))"
          apply (rule step_Tau_loop_op)
          using that apply auto
          done
        moreover have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa lbuf2)lbuf3)) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL pa lbuf2))) op1)))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL pa lbuf2))) op''b)))"
          apply (rule step_Tau_loop_op)
          using that apply auto
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
          using step_inputs_outputs that apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> BTL pa lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "pa \<notin> defaults"
          and "step (Inp (Inr pa) (BHD pa lbuf3)) op1 op''b"
          and "lbuf3 pa \<noteq> []"
        for op''b :: "('a + 'm, 'b + 'm, 'd) op"
          and pa :: 'm
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((BTL pa lbuf1 >> lbuf2) >> lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "pa \<notin> defaults"
          and "step (Inp (Inr pa) (BHD pa lbuf1)) op1 op''b"
          and "lbuf1 pa \<noteq> []"
          and "lbuf2 pa = []"
          and "lbuf3 pa = []"
        for op''b :: "('a + 'm, 'b + 'm, 'd) op"
          and pa :: 'm
        using that 
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1)
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL pa lbuf1))
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BENQ pa (BHD pa lbuf1) lbuf2))) op1)))"
          apply (rule step_Inp_Tau_loop_op)
          using that apply (auto simp add: ran_def split: sum.splits)
          done
        moreover have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL pa lbuf1))
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BENQ pa (BHD pa lbuf1) lbuf2))) op1)))
          (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL pa lbuf1))
       (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa lbuf1) lbuf3)) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))"
          using that by (auto del: step_Tau_loop_op step_Tau_comp_op_L intro!: step_Tau_loop_op step_Tau_comp_op_L)
        moreover have "step Tau
          (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL pa lbuf1))
       (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa lbuf1) lbuf3)) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL pa lbuf1))
       (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op''b)))"
          using that by (auto del: step_Tau_loop_op intro!: step_Tau_loop_op)
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
          using step_inputs_outputs that apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((BENQ pa xa lbuf1 >> lbuf2) >> lbuf3)) op''b)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "pa \<notin> defaults"
          and "step (Out (Inr pa) xa) op1 op''b"
        for op''b :: "('a + 'm, 'b + 'm, 'd) op"
          and pa :: 'm
          and xa :: 'd
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Out_Tau_loop_op)
           apply auto
        done
      ultimately show ?thesis
        using H BISIM by (auto 0 0 dest!: step_loop_op elim !:  step_map_op_elim step_comp_op_elim)
    qed
  next
    fix io :: "('c, 'b, 'd) IO"
      and op1' :: "('c, 'b, 'd) op"
    assume "Inr -` inputs op1 \<inter> defaults = {}"
      and "Inr -` outputs op1 \<inter> defaults = {}"
      and H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1)))) op1'"
    then show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p x) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1'a (id_op lbuf2)) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Inp p x) op2 op1'a"
        for p :: 'c
          and x :: 'd
          and op1'a :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply force
        done
      moreover have "\<exists>op2'a. wstep (Out p x) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op2')))) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Out (Inl p) x) op1 op2'"
        for p :: 'b
          and x :: 'd
          and op2' :: "('a + 'm, 'b + 'm, 'd) op"
        using that         
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply force
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 (BENQ pa (BHD pa lbuf2) lbuf3)) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL pa lbuf2))) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "lbuf2 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'm
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp_intros_1')
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum (BENQ pa xa buf2) lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1'a (id_op lbuf2)) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Out pa xa) op2 op1'a"
        for pa :: 'a
          and xa :: 'd
          and op1'a :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum (BTL x1 buf2) lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op2')))) op2'a"
        if "step (Inp (Inl x1) (BHD x1 buf2)) op1 op2'"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "buf2 x1 \<noteq> []"
        for op2' :: "('a + 'm, 'b + 'm, 'd) op"
          and x1 :: 'a
        using that 
      proof -
        have "step Tau (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))
     (comp_op Some (BTL x1 buf2) op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op2')))"
          apply (rule step_Tau_comp_op_R)
          using that apply auto
          done
        from this that show ?thesis
          apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
          using step_inputs_outputs that apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 lbuf3)) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op2')))) op2'a"
        if "step (Inp (Inr x2) (BHD x2 lbuf3)) op1 op2'"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "lbuf3 x2 \<noteq> []"
        for op2' :: "('a + 'm, 'b + 'm, 'd) op"
          and x2 :: 'm
        using that 
      proof -
        have "step Tau (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))
     (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> BTL x2 lbuf3)) op2')))"
          using that apply -
          apply (rule step_comp_op_R_Tau)
            apply (rule step_map_op)
             apply simp_all
          apply (rule step_Inp_Tau_loop_op[where p="Inr x2"])
              apply simp_all
          using that apply (smt (verit, del_insts) IO.inject(1) IO.simps(4) IO.simps(6) Int_iff Read_choices_inputs case_sum_if empty_iff ranI step_choicesE vimageI)
          done
        from this that show ?thesis
          apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
          using step_inputs_outputs that apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1'a (id_op lbuf2)) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op2 op1'a"
        for op1'a :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force+
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op2') op1)))) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau (id_op lbuf2) op2'"
        for op2' :: "('m, 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force+
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op2')))) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op1 op2'"
        for op2' :: "('a + 'm, 'b + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force+
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL p lbuf1)) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BENQ p (BHD p lbuf1) lbuf2))) op1)))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "p \<notin> defaults"
          and "lbuf1 p \<noteq> []"
        for p :: 'm
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force+
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ p x lbuf1)) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op2')))) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "p \<notin> defaults"
          and "step (Out (Inr p) x) op1 op2'"
        for p :: 'm
          and x :: 'd
          and op2' :: "('a + 'm, 'b + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force+
        done
      moreover have "\<exists>op2'a. wstep (Out (projl (Inr p)) x) (map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op Some buf2 op2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p::'a + 'm))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op1))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf1) (map_op projl projr (comp_op Some (case_sum buf2 lbuf3) (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)) op2')))) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "p \<in> defaults"
          and "step (Out (Inr p) x) op1 op2'"
        for p :: 'm
          and x :: 'd
          and op2' :: "('a + 'm, 'b + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply force
        done
      ultimately show ?thesis
        using BISIM H by (auto 0 0 dest!: step_loop_op elim !: step_id_op_Out step_id_op_Inp_elim step_map_op_elim step_comp_op_elim split: sum.splits)
    qed
  qed
qed

lemma loop_op_scomp_commute:
  fixes op1 :: "('a + 'm :: {countable, defaults}, 'b + 'm, 'd) op"
    and op2 :: "('c, 'a, 'd) op"
  assumes "Inr -` inputs op1 \<inter> defaults = {}"
    and "Inr -` outputs op1 \<inter> defaults = {}"
  shows "op2 \<bullet> (op1\<up>) \<approx> ((op2 \<parallel> \<I>) \<bullet> op1)\<up>"
  unfolding feedback_op_def scomp_op_def pcomp_op_def comp_def
  using assms loop_op_scomp_commute_gen[of  op1  "\<lambda>_. []" op2 "\<lambda>_. []" "\<lambda>_. []" "\<lambda>_. []", unfolded comp_def, simplified] by auto 



section \<open>Axiom: R2: Loop distribute scomp_op\<close>
lemma loop_op_distribute_scomp_op_gen:
  fixes op1 :: "('b + 'm :: {defaults, countable}, 'c + 'm, 'd) op"
    and op2 :: "('c, 'a, 'd) op"
  assumes "Inr -` inputs op1 \<inter> defaults = {}"
    and "Inr -` outputs op1 \<inter> defaults = {}"
  shows "map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)) op2) \<approx>
   map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))"
  using assms proof (coinduction arbitrary: op1 op2 buf2 lbuf1 lbuf2 lbuf3 rule: wbisim_coinduct_upto_alt)
  case BISIM
  then show ?case 
    unfolding wsim_def
  proof (intro allI conjI impI)
    fix io :: "('b, 'a, 'd) IO"
      and op1' :: "('b, 'a, 'd) op"
    assume "Inr -` inputs op1 \<inter> defaults = {}"
      and "Inr -` outputs op1 \<inter> defaults = {}"
      and H: "step io (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)) op2)) op1'"
    show "\<exists>op2'. wstep io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp (projl pa) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)) op2)) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "pa \<notin> ran (case_sum ((\<lambda>_. None)::'c \<Rightarrow> ('b + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp pa x) op1 op''b"
        for x :: 'd
          and pa :: "'b + 'm"
          and op''b :: "('b + 'm, 'c + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_Inp_loop_op)
          apply (auto simp add: ran_def split: sum.splits if_splits)
        done
      moreover have "\<exists>op2'a. wstep (Out p x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2')) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Out p x) op2 op2'"
        for p :: 'a
          and x :: 'd
          and op2' :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_Out_loop_op)
           apply (auto simp add: ran_def split: sum.splits if_splits)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some (BENQ q x buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)) op2)) op2'"
        if "step (Out (Inl q) x) op1 op''b"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
        for x :: 'd
          and q :: 'c
          and op''b :: "('b + 'm, 'c + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some (BENQ (projl (Inr x2)) x buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)) op2)) op2'"
        if "step (Out (Inr x2) x) op1 op''b"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "x2 \<in> defaults"
        for x :: 'd
          and op''b :: "('b + 'm, 'c + 'm, 'd) op"
          and x2 :: 'm
        using that 
        apply -
        apply (rule FalseE)
        apply (metis IO.distinct(1) IO.sel(4) IO.simps(8) disjoint_iff_not_equal op.set_intros(8) outputs_after_choices step_choicesE vimageI)
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some (BTL p buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2')) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Inp p (BHD p buf2)) op2 op2'"
          and "buf2 p \<noteq> []"
        for p :: 'c
          and op2' :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply simp_all
        apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op''b)) op2)) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op1 op''b"
        for op''b :: "('b + 'm, 'c + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply simp_all
        apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((BTL x2 lbuf1 >> lbuf2) >> lbuf3)) op''b)) op2)) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'c \<Rightarrow> ('b + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) (BHD x2 lbuf1)) op1 op''b"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "lbuf1 x2 \<noteq> []"
          and "lbuf3 x2 = []"
          and "lbuf2 x2 = []"
        for op''b :: "('b + 'm, 'c + 'm, 'd) op"
          and x2 :: 'm
        using that 
        using that 
      proof -
        have "step Tau (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 lbuf1)) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BENQ x2 (BHD x2 lbuf1) lbuf2))))))"
          using that apply -
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_R)
                 apply (rule step_comp_op_R_Inp)
                    apply (auto split: sum.splits dest: Read_choices_inputs elim: step_choicesE)
          done
        moreover have "step Tau 
     (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 lbuf1)) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BENQ x2 (BHD x2 lbuf1) lbuf2))))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (BENQ x2 (BHD x2 lbuf1) lbuf3)) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 lbuf1)) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))"
          using that apply -
          apply (rule step_Out_Tau_loop_op)
            apply (rule step_map_op)
             apply (rule step_comp_op_R_Out[where p="Inr x2"])
               apply (auto split: sum.splits dest: Read_choices_inputs elim: step_choicesE)
          done
        moreover have "step Tau 
     (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (BENQ x2 (BHD x2 lbuf1) lbuf3)) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 lbuf1)) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 (BTL x2 lbuf1)) op''b (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))"
          using that apply -
          apply (simp add: ran_def split: if_splits sum.splits)
          subgoal for p
            apply (cases p; simp)
            apply (rule step_Inp_Tau_loop_op)
                apply (rule step_map_op)
                 apply (auto simp add: ran_def split: sum.splits if_splits  dest: Write_choices_outputs elim: step_choicesE)
            done
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
          using step_inputs_outputs that apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> BTL x2 lbuf2) >> lbuf3)) op''b)) op2)) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'c \<Rightarrow> ('b + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) (BHD x2 lbuf2)) op1 op''b"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "lbuf3 x2 = []"
          and "lbuf2 x2 \<noteq> []"
        for op''b :: "('b + 'm, 'c + 'm, 'd) op"
          and x2 :: 'm
        using that 
      proof -
        have 
          "step Tau (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))
            (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (BENQ x2 (BHD x2 lbuf2) lbuf3)) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL x2 lbuf2))))))"
          using that apply -
          apply (rule step_Out_Tau_loop_op)
            apply (rule step_map_op)
             apply (rule step_comp_op_R_Out[where p="Inr x2"])
               apply (auto split: sum.splits dest: Read_choices_inputs elim: step_choicesE)
          done
        moreover have  "step Tau (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (BENQ x2 (BHD x2 lbuf2) lbuf3)) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL x2 lbuf2))))))
             (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op''b (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL x2 lbuf2))))))"
          using that apply -
          apply (simp add: ran_def split: sum.splits if_splits)
          subgoal for a
            apply (cases a; simp)
            apply (rule step_Inp_Tau_loop_op)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Inp[where p="Inr x2"])
                   apply (auto simp add: ran_def split: sum.splits dest: Write_choices_outputs elim: step_choicesE)
            done
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated, OF wbc_base])
          using step_inputs_outputs that apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> BTL x2 lbuf3)) op''b)) op2)) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'c \<Rightarrow> ('b + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) (BHD x2 lbuf3)) op1 op''b"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "lbuf3 x2 \<noteq> []"
        for op''b :: "('b + 'm, 'c + 'm, 'd) op"
          and x2 :: 'm
        using that apply -
        apply (simp add: ran_def split: sum.splits if_splits)
        subgoal for p
          apply (cases p; simp)
          apply (intro exI conjI[rotated, OF wbc_base])
          using step_inputs_outputs that apply force
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_Inp_Tau_loop_op)
               apply (rule step_map_op)
                apply (auto simp add: ran_def split: sum.splits)
          done
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((BENQ x2 xa lbuf1 >> lbuf2) >> lbuf3)) op''b)) op2)) op2'"
        if "step (Out (Inr x2) xa) op1 op''b"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "x2 \<notin> defaults"
        for op''b :: "('b + 'm, 'c + 'm, 'd) op"
          and xa :: 'd
          and x2 :: 'm
        using that 
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2')) op2'a"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op2 op2'"
        for op2' :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_base])
        using step_inputs_outputs that apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      ultimately show ?thesis
        using BISIM H by (auto 0 0 elim !: step_loop_op_elim step_id_op_Out step_id_op_Inp_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
    qed
  next
    fix io :: "('b, 'a, 'd) IO"
      and op1' :: "('b, 'a, 'd) op"
    assume "Inr -` inputs op1 \<inter> defaults = {}"
      and "Inr -` outputs op1 \<inter> defaults = {}"
      and H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined (lbuf1 >> lbuf2 >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp (projl (p::'b + 'm)) x) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1' (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "p \<notin> ran (case_sum ((\<lambda>_. None)::'a \<Rightarrow> ('b + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp p x) op1 op1'"
        for p :: "'b + 'm"
          and x :: 'd
          and op1' :: "('b + 'm, 'c + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply (simp add: ran_def split: sum.splits if_splits)
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_map_op)
            apply (rule step_Inp_loop_op)
             apply (auto simp add: ran_def  split: sum.splits if_splits)
        done
      moreover have "\<exists>op2'. wstep (Out x1 x) (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (id_op lbuf2)))))) op2'"
        if "step (Out x1 x) op2 op1'"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
        for x :: 'd
          and op1' :: "('c, 'a, 'd) op"
          and x1 :: 'a
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force+
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (BENQ q x (case_sum buf2 lbuf1)) op1' (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step (Out q x) op1 op1'"
        for x :: 'd
          and op1' :: "('b + 'm, 'c + 'm, 'd) op"
          and q :: "'c + 'm"
        using that 
      proof (cases q)
        case (Inl a)
        from this that show ?thesis 
          apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
          using step_inputs_outputs that apply force
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_L)
              apply auto
          done
      next
        case (Inr b)
        from this that show ?thesis 
          apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
          using step_inputs_outputs that apply force
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_Out_Tau_loop_op)
                apply assumption
               apply (auto 3 3 dest: outputs_after_choices split: sum.splits elim!: step_choicesE)
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum (BTL pa buf2) lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (id_op lbuf2)))))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "buf2 pa \<noteq> []"
          and "step (Inp pa (BHD pa buf2)) op2 op1'"
        for pa :: 'c
          and op1' :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 (BTL pa lbuf1)) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BENQ pa (BHD pa lbuf1) lbuf2))))))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "lbuf1 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'm
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1' (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op1 op1'"
        for op1' :: "('b + 'm, 'c + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (id_op lbuf2)))))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau op2 op1'"
        for op1' :: "('c, 'a, 'd) op"
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 op2'a))))) op2'"
        if "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "step Tau (id_op lbuf2) op2'a"
        for op2'a :: "('m, 'm, 'd) op"
        using that apply -
        apply (rule FalseE)
        apply (meson no_step_id_op_Tau)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 lbuf3)) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1' (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2)))))) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'a \<Rightarrow> ('b + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) (BHD x2 lbuf3)) op1 op1'"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
          and "lbuf3 x2 \<noteq> []"
        for op1' :: "('b + 'm, 'c + 'm, 'd) op"
          and x2 :: 'm
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply (simp add: ran_def split: if_splits sum.splits)
        subgoal for p
          apply (cases p; simp)
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_Inp_Tau_loop_op[where p="Inr x2"])
                  apply (auto simp add: ran_def split: sum.splits)
          done
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2)) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf2 lbuf1 lbuf2 lbuf3. op1axx = map_op projl projr (comp_op (Some::'c \<Rightarrow> _ option) buf2 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined ((lbuf1 >> lbuf2) >> lbuf3)) op1)) op2) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined lbuf3) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op lbuf2))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 (BHD x2 lbuf2) lbuf3)) (map_op projl projr (comp_op Some (case_sum buf2 lbuf1) op1 (comp_op (\<lambda>_. None) (\<lambda>_. []) op2 (id_op (BTL x2 lbuf2))))))) op2'"
        if "lbuf2 x2 \<noteq> []"
          and "x2 \<notin> defaults"
          and "Inr -` inputs op1 \<inter> defaults = {}"
          and "Inr -` outputs op1 \<inter> defaults = {}"
        for x2 :: 'm
        using that 
        apply (intro exI conjI[rotated, OF wbc_sym[OF wbc_base]])
        using step_inputs_outputs that apply force
        apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.simps)
        done
      ultimately show ?thesis
        using H BISIM by (auto 0 0 elim !: step_loop_op_elim step_id_op_Out step_id_op_Inp_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
    qed
  qed
qed

lemma loop_op_distribute_scomp_op:
  fixes op1 :: "('b + 'm :: {defaults, countable}, 'c + 'm, 'd) op"
    and op2 :: "('c, 'a, 'd) op"
  assumes "Inr -` inputs op1 \<inter> defaults = {}"
    and "Inr -` outputs op1 \<inter> defaults = {}"
  shows  "(op1\<up>) \<bullet> op2 \<approx> (op1 \<bullet> (op2 \<parallel> \<I>))\<up>"
  unfolding feedback_op_def scomp_op_def pcomp_op_def
  using loop_op_distribute_scomp_op_gen[of op1 "\<lambda>_. []" "\<lambda>_. []" "\<lambda>_. []" "\<lambda>_. []" op2, simplified, OF assms] by blast  

section \<open>Axiom: R3: Loop parallel composition\<close>


lemma bisim_coinduct_upto_alt[consumes 1, case_names BISIM]:
  "R s t \<Longrightarrow>
   (\<And>op1 op2. R op1 op2 \<Longrightarrow> sim (bisim_cong R) op1 op2 \<and> sim (bisim_cong R) op2 op1) \<Longrightarrow>
   s ~ t"
  using bisim_coinduct_upto by blast

lemma loop_op_pcomp_commue_gen:
  fixes op1 :: "('b + 'a, 'c + 'd, 'e) op"
    and op2 :: "('f + 'm :: defaults, 'g + 'm, 'e) op"
  assumes "Inr -` inputs op2 \<inter> defaults = {}"
    and "Inr -` outputs op2 \<inter> defaults = {}"
  shows  "comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined buf1) op2)) ~
   map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined buf1) (map_op BNA_Operators.assoc BNA_Operators.assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2)))"
  using assms proof (coinduction arbitrary: op1 op2 buf1 rule: bisim_coinduct_upto_alt)
  case BISIM
  then show ?case 
    apply -
    unfolding sim_def
    sketch (intro allI conjI impI)
  proof (intro allI conjI impI)
    fix io :: "(('b + 'a) + 'f, ('c + 'd) + 'g, 'e) IO"
      and op1' :: "(('b + 'a) + 'f, ('c + 'd) + 'g, 'e) op"
    assume "Inr -` inputs op2a \<inter> defaults = {}"
      and "Inr -` outputs op2a \<inter> defaults = {}"
      and H: "step io (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op1'"
    show "\<exists>op2'. step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. step (Inp (Inl p) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "step (Inp p x) op1a op1'"
        for p :: "'b + 'a"
          and x :: 'e
          and op1' :: "('b + 'a, 'c + 'd, 'e) op"
        using that by (intro conjI[rotated, OF bc_base] exI; force dest: step_inputs_outputs)
      moreover have "\<exists>op2'. step (Out (Inr p) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''a))) op2'"
        if "step (Out (Inl p) x) op2a op''a"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
        for p :: 'g
          and x :: 'e
          and op''a :: "('f + 'm, 'g + 'm, 'e) op"
        using that 
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
        using step_inputs_outputs apply fast
        apply auto
        done
      moreover have "\<exists>op2'. step (Out (Inr (projl (Inr x2))) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''a))) op2'"
        if "step (Out (Inr x2) x) op2a op''a"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "x2 \<in> defaults"
        for x :: 'e
          and op''a :: "('f + 'm, 'g + 'm, 'e) op"
          and x2 :: 'm
        using that 
        apply -
        apply (rule FalseE)
        apply (metis (no_types, lifting) IO.distinct(1) IO.sel(4) IO.simps(8) disjoint_iff_not_equal op.set_intros(8) outputs_after_choices step_choicesE vimageI)
        done
      moreover have "\<exists>op2'. step (Out (Inl p) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "step (Out p x) op1a op1'"
        for p :: "'c + 'd"
          and x :: 'e
          and op1' :: "('b + 'a, 'c + 'd, 'e) op"
        using that 
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
        using step_inputs_outputs apply fast
        apply auto
        done
      moreover have "\<exists>op2'. step (Inp (Inr (projl pa)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''a))) op2'"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "pa \<notin> ran (case_sum ((\<lambda>_. None)::'g \<Rightarrow> ('f + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp pa x) op2a op''a"
        for x :: 'e
          and pa :: "'f + 'm"
          and op''a :: "('f + 'm, 'g + 'm, 'e) op"
        using that 
      proof (cases pa)
        case (Inl a)
        from this that show ?thesis 
          apply (intro conjI[rotated] exI)
           apply (rule bc_base)
          using step_inputs_outputs apply fast
          apply auto
          done
      next
        case (Inr b)
        from this that show ?thesis 
          apply (intro conjI[rotated] exI)
           apply (rule bc_base)
          using step_inputs_outputs apply fast
          apply (simp add: ran_def split: if_splits sum.splits)
          apply (metis (no_types, lifting) IO.distinct(3) IO.inject(1) IO.simps(4) Read_choices_inputs disjoint_iff_not_equal step_choicesE vimageI2)
          done
      qed
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "step Tau op1a op1'"
        for op1' :: "('b + 'a, 'c + 'd, 'e) op"
        using that 
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
        using step_inputs_outputs apply fast
        apply auto
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''a))) op2'"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "step Tau op2a op''a"
        for op''a :: "('f + 'm, 'g + 'm, 'e) op"
        using that 
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
        using step_inputs_outputs apply fast
        apply auto
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1)) op''a))) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'g \<Rightarrow> ('f + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) (BHD x2 buf1)) op2a op''a"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "buf1 x2 \<noteq> []"
        for op''a :: "('f + 'm, 'g + 'm, 'e) op"
          and x2 :: 'm
        using that 
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
        using step_inputs_outputs apply fast
        apply (simp add: ran_def split: sum.splits if_splits)
        subgoal for p
          apply (cases p; simp)
          apply (rule step_map_op)
           apply (rule step_Inp_Tau_loop_op)
               apply (auto simp add: ran_def split: if_splits sum.splits)
          done
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 xa buf1)) op''a))) op2'"
        if "step (Out (Inr x2) xa) op2a op''a"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "x2 \<notin> defaults"
        for op''a :: "('f + 'm, 'g + 'm, 'e) op"
          and xa :: 'e
          and x2 :: 'm
        using that 
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
        using step_inputs_outputs apply fast
        apply auto
        done
      ultimately show ?thesis
        using H BISIM by (auto 0 0 elim !: step_loop_op_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
    qed
  next
    fix io :: "(('b + 'a) + 'f, ('c + 'd) + 'g, 'e) IO"
      and op1' :: "(('b + 'a) + 'f, ('c + 'd) + 'g, 'e) op"
    assume "Inr -` inputs op2a \<inter> defaults = {}"
      and "Inr -` outputs op2a \<inter> defaults = {}"
      and H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2a)))) op1'"
    show "\<exists>op2'. step io (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. step (Inp (Inl pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' op2a)))) op2'"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "step (Inp pa x) op1a op1'"
        for x :: 'e
          and pa :: "'b + 'a"
          and op1' :: "('b + 'a, 'c + 'd, 'e) op"
        using that by (intro exI conjI[rotated, OF bc_sym[OF bc_base]]; fast)
      moreover have "\<exists>op2'a. step (Inp (Inr x1) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'a \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2')))) op2'a"
        if "step (Inp (Inl x1) x) op2a op2'"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
        for x :: 'e
          and op2' :: "('f + 'm, 'g + 'm, 'e) op"
          and x1 :: 'f
        using that by (intro exI conjI[rotated, OF bc_sym[OF bc_base]]; force dest: step_inputs_outputs)
      moreover have "\<exists>op2'a. step (Inp (projl (Inr x2)) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'a \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2')))) op2'a"
        if "Inr x2 \<notin> ran (case_sum ((\<lambda>_. None)::('c + 'd) + 'g \<Rightarrow> ((('b + 'a) + 'f) + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) x) op2a op2'"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
        for x :: 'e
          and op2' :: "('f + 'm, 'g + 'm, 'e) op"
          and x2 :: 'm
        using that 
        apply -
        apply (rule FalseE)
        apply (simp add: ran_def split: sum.splits if_splits)
        apply (metis IO.distinct(1) IO.inject(1) IO.simps(6) Read_choices_inputs disjoint_iff_not_equal step_choicesE vimageI)
        done
      moreover have "\<exists>op2'a. step (Out (Inr x1a) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'a \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2')))) op2'a"
        if "step (Out (Inl x1a) x) op2a op2'"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
        for x :: 'e
          and op2' :: "('f + 'm, 'g + 'm, 'e) op"
          and x1a :: 'g
        using that by (intro exI conjI[rotated, OF bc_sym[OF bc_base]]; force dest: step_inputs_outputs)
      moreover have "\<exists>op2'a. step (Out (projl (Inr x2)) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'a \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2')))) op2'a"
        if "step (Out (Inr x2) x) op2a op2'"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "x2 \<in> defaults"
        for x :: 'e
          and op2' :: "('f + 'm, 'g + 'm, 'e) op"
          and x2 :: 'm
        using that 
        apply -
        apply (rule FalseE)
        apply (metis IO.distinct(1) IO.sel(4) IO.simps(8) disjoint_iff_not_equal op.set_intros(8) outputs_after_choices step_choicesE vimageI)
        done
      moreover have "\<exists>op2'. step (Out (Inl pa) x) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' op2a)))) op2'"
        if "step (Out pa x) op1a op1'"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
        for x :: 'e
          and pa :: "'c + 'd"
          and op1' :: "('b + 'a, 'c + 'd, 'e) op"
        using that by (intro exI conjI[rotated, OF bc_sym[OF bc_base]]; force dest: step_inputs_outputs)
      moreover have "\<exists>op2'. step Tau (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' op2a)))) op2'"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "step Tau op1a op1'"
        for op1' :: "('b + 'a, 'c + 'd, 'e) op"
        using that by (intro exI conjI[rotated, OF bc_sym[OF bc_base]]; force dest: step_inputs_outputs)
      moreover have "\<exists>op2'a. step Tau (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'a \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2')))) op2'a"
        if "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "step Tau op2a op2'"
        for op2' :: "('f + 'm, 'g + 'm, 'e) op"
        using that 
        apply (intro exI conjI[rotated, OF bc_sym[OF bc_base]])
        using step_inputs_outputs apply fast
        apply auto
        done
      moreover have "\<exists>op2'a. step Tau (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'a \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1)) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2')))) op2'a"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::('c + 'd) + 'g \<Rightarrow> ((('b + 'a) + 'f) + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) (BHD x2 buf1)) op2a op2'"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "buf1 x2 \<noteq> []"
        for op2' :: "('f + 'm, 'g + 'm, 'e) op"
          and x2 :: 'm
        using that 
        apply (intro exI conjI[rotated, OF bc_sym[OF bc_base]])
        using step_inputs_outputs apply fast
        apply (rule step_comp_op_R_Tau)
          apply (rule step_map_op)
           apply (rule step_Inp_Tau_loop_op[where p="Inr x2"])
               apply assumption
              apply (auto simp add: ran_def split: sum.splits if_splits dest!: Read_choices_inputs elim!: step_choicesE)
        done
      moreover have "\<exists>op2'a. step Tau (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2a))) op2'a \<and> bisim_cong (\<lambda>sxx txx. \<exists>op1 op2 buf1. sxx = comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op2)) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2))) \<and> Inr -` inputs op2 \<inter> defaults = {} \<and> Inr -` outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x buf1)) (map_op assoc assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1a op2')))) op2'a"
        if "step (Out (Inr x2) x) op2a op2'"
          and "Inr -` inputs op2a \<inter> defaults = {}"
          and "Inr -` outputs op2a \<inter> defaults = {}"
          and "x2 \<notin> defaults"
        for x :: 'e
          and op2' :: "('f + 'm, 'g + 'm, 'e) op"
          and x2 :: 'm
        using that 
        apply (intro exI conjI[rotated, OF bc_sym[OF bc_base]])
        using step_inputs_outputs apply fast
        apply (rule step_comp_op_R_Tau)
          apply (rule step_map_op)
           apply auto
        done
      ultimately show ?thesis
        using BISIM H by (auto 0 0 elim !: step_loop_op_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
    qed
  qed
qed

lemma loop_op_pcomp_commue:
  fixes op1 :: "('b + 'a, 'c + 'd, 'e) op"
    and op2 :: "('f + 'm :: defaults, 'g + 'm, 'e) op"
  assumes "Inr -` inputs op2 \<inter> defaults = {}"
    and "Inr -` outputs op2 \<inter> defaults = {}"
  shows  "op1 \<parallel> (op2\<up>) ~ (map_op assoc assoc (op1 \<parallel> op2))\<up>"
  unfolding feedback_op_def scomp_op_def pcomp_op_def
  using assms loop_op_pcomp_commue_gen[OF assms, of op1 "\<lambda> _. []"] by auto 

(* FIXME: move me *)
lemma step_tau_star_tau[intro]:
  "step Tau op0 opf \<Longrightarrow>
  (step Tau)\<^sup>*\<^sup>* (map_op f g op0) (map_op f g opf)"
  by (simp add: r_into_rtranclp step_star_map_op)
lemma step_tau_tau_star_tau[intro]:
  "step Tau op0 op1 \<Longrightarrow>
   step Tau op1 opf \<Longrightarrow>
  (step Tau)\<^sup>*\<^sup>* (map_op f g op0) (map_op f g opf)"
  by (metis step_star_map_op step_tau_step_io_wstep wstep_steps_Tau)
lemma step_tau_tau_tau_star_tau[intro]:
  "step Tau op0 op1 \<Longrightarrow>
   step Tau op1 op2 \<Longrightarrow>
   step Tau op2 opf \<Longrightarrow>
  (step Tau)\<^sup>*\<^sup>* (map_op f g op0) (map_op f g opf)"
  by (meson rtranclp_trans step_tau_star_tau)

(* FIXME: move me *)
lemma not_in_feedback_wire:
  assumes  "p \<notin> ran (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
    and "p \<notin> defaults"
  obtains p' where "p = Inl p'"
  using assms by (cases p; auto simp add: ran_def split: sum.splits if_splits)
lemma in_feedback_wire[simp]:
  "p \<in> ran (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) \<longleftrightarrow> (\<exists> p'. p = Inr p' \<and> p' \<notin> defaults)"
  apply (cases p; simp add:  ran_def split: sum.splits if_splits)
  apply (metis Inl_Inr_False Inr_inject sumE)
  done

section \<open>Axiom: R4: Loop commutes inner sequential composition\<close>
lemma loop_op_commutes_inner_scomp_op_gen:
  fixes op1 :: "('k :: {countable,defaults} + 'm :: {countable,defaults}, 'l :: {countable,defaults} + 'n :: {countable,defaults}, 'd) op"
    and op2 :: "('n, 'm, 'd) op"
  assumes "Inr -` inputs op1 \<inter> defaults = {}"
    and "Inr -` outputs op1 \<inter> defaults = {}"
    and "inputs op2 \<inter> defaults = {}"
    and "outputs op2 \<inter> defaults = {}"
  shows "map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined buf1)
   (map_op projl projr (comp_op Some (case_sum buf3 (buf2 >> buf2' >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<approx>
   map_op projl projl
  (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined buf2'')
   (map_op projl projr (comp_op Some (case_sum buf4' (buf1 >> buf1' >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))"
  using assms proof (coinduction arbitrary: op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4' rule: wbisim_coinduct_upto_alt)
  case BISIM
  then show ?case 
    unfolding wsim_def
  proof (intro conjI impI allI)
    fix io :: "('k, 'l, 'd) IO"
      and op1' :: "('k, 'l, 'd) op"
    assume "Inr -` inputs op1 \<inter> defaults = {}"
      and "Inr -` outputs op1 \<inter> defaults = {}"
      and "inputs op2 \<inter> defaults = {}"
      and "outputs op2 \<inter> defaults = {}"
      and H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 (buf2 >> buf2' >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' (buf1 >> buf1' >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 (buf2 >> buf2' >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' (buf1 >> buf1' >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p' x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum (BENQ p' x buf4) buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'"
        if "p' \<notin> defaults"
        for x :: 'd
          and p' :: 'k
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM apply force
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply auto
        done
      moreover have "\<exists>op2'. wstep (Out (projl (Inr x2)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2'a))))) op2'"
        if "step (Out x2 x) op2 op2'a"
          and "x2 \<in> defaults"
        for x :: 'd
          and op2'a :: "('n, 'm, 'd) op"
          and x2 :: 'm
        using that 
        apply-
        apply (rule FalseE)
        using BISIM 
        apply (metis IO.distinct(1) IO.inject(2) IO.simps(8) disjoint_iff op.set_intros(8) outputs_after_choices step_choicesE)
        done
      moreover have "\<exists>op2'. wstep (Out x1 (BHD x1 buf3')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL x1 buf3')) op2))))) op2'"
        if "buf3' x1 \<noteq> []"
          and "x1 \<notin> defaults"
        for x1 :: 'l
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM apply force
        apply (rule step_wstep)
        apply (rule step_map_op[where io= "Out (Inl x1) (BHD x1 buf3')"])
         apply simp_all
        apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (BENQ q x (case_sum buf3 ((buf2 >> buf2') >> buf2''))) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op2')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'a"
        if "step (Out q x) op1 op2'"
        for x :: 'd
          and q :: "'l + 'n"
          and op2' :: "('k + 'm, 'l + 'n, 'd) op"
        using that 
      proof (cases q)
        case (Inl p)
        from this that show ?thesis 
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM step_inputs_outputs apply force
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)     
            apply (rule step_map_op)
             apply (rule step_comp_op_R_Tau)
               apply auto
          done
      next
        case (Inr r)
        from this that show ?thesis 
          apply (intro exI conjI[rotated,OF wbc_base])
          using BISIM step_inputs_outputs apply force
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)     
            apply (rule step_map_op)
             apply (rule step_comp_op_R_Tau)
               apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum (BTL pa buf3) ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ pa (BHD pa buf3) buf3')) op2))))) op2'"
        if "buf3 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'l
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)     
          apply (rule step_map_op)
           apply (rule step_comp_op_R_Tau)
             apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((BTL pa buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2'a))))) op2'"
        if "buf2 pa \<noteq> []"
          and "step (Inp pa (BHD pa buf2)) op2 op2'a"
          and "buf2'' pa = []"
          and "buf2' pa = []"
        for pa :: 'n
          and op2'a :: "('n, 'm, 'd) op"
        using that
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'')
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'')
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 (BTL pa buf2)) op1 (id_op (case_sum buf3' (BENQ pa (BHD pa buf2) buf2'))))))))"
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply simp_all
          apply (rule step_comp_op_R_Tau)
            apply (rule step_map_op)
             apply simp_all
          apply (rule step_Tau_comp_op_R[where p="Inr pa"])
          using BISIM that apply (auto split: sum.splits dest: Read_choices_inputs elim!: step_choicesE)
          done
        moreover have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'')
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 (BTL pa buf2)) op1 (id_op (case_sum buf3' (BENQ pa (BHD pa buf2) buf2'))))))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ pa (BHD pa buf2) buf2''))
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 (BTL pa buf2)) op1 (id_op (case_sum buf3' buf2')))))))"
          apply (rule step_Out_Tau_loop_op[where q="Inr pa"])
            apply (rule step_map_op[of "Out (Inr (Inr pa)) (BHD pa buf2)"])
             apply simp_all
          using BISIM that apply (auto split: sum.splits dest!: Read_choices_inputs elim: not_in_feedback_wire step_choicesE)
          done
        moreover have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ pa (BHD pa buf2) buf2''))
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 (BTL pa buf2)) op1 (id_op (case_sum buf3' buf2')))))))
     ((loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'')
         (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2'a) (map_op projl projr (comp_op Some (case_sum buf3 (BTL pa buf2)) op1 (id_op (case_sum buf3' buf2'))))))))"
          apply (rule step_Inp_Tau_loop_op[where p="Inr pa"])
          using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim: step_choicesE)
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using that BISIM step_inputs_outputs apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> BTL pa buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2'a))))) op2'"
        if "step (Inp pa (BHD pa buf2')) op2 op2'a"
          and "buf2'' pa = []"
          and "buf2' pa \<noteq> []"
        for pa :: 'n
          and op2'a :: "('n, 'm, 'd) op"
        using that 
      proof -
        have "step Tau  (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'')
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ pa (BHD pa buf2') buf2''))
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' (BTL pa buf2'))))))))"
          apply (rule step_Out_Tau_loop_op[where q="Inr pa"])
            apply (rule step_map_op[of "Out (Inr (Inr pa)) (BHD pa buf2')"])
             apply simp_all
          using BISIM that apply (auto split: sum.splits dest!: Read_choices_inputs elim: not_in_feedback_wire step_choicesE)
          done
        moreover have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ pa (BHD pa buf2') buf2''))
       (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' (BTL pa buf2'))))))))
     ((loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'')
         (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2'a) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' (BTL pa buf2')))))))))"
          apply (rule step_Inp_Tau_loop_op[where p="Inr pa"])
          using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim: step_choicesE)
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_base])
          using that BISIM step_inputs_outputs apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> BTL pa buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2'a))))) op2'"
        if "step (Inp pa (BHD pa buf2'')) op2 op2'a"
          and "buf2'' pa \<noteq> []"
        for pa :: 'n
          and op2'a :: "('n, 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using that BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Inp_Tau_loop_op[where p="Inr pa"])
        using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim: step_choicesE)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum (BENQ x1 (BHD x1 buf4) buf4') buf1'') (id_op (case_sum (BTL x1 buf4) buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'"
        if "x1 \<notin> defaults"
          and "buf4 x1 \<noteq> []"
        for x1 :: 'k
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using that BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' (BENQ x2 (BHD x2 buf1') buf1'')) (id_op (case_sum buf4 (BTL x2 buf1'))) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'"
        if "x2 \<notin> defaults"
          and "buf1' x2 \<noteq> []"
        for x2 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using that BISIM step_inputs_outputs apply force
        apply (smt (verit, best) BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp_intros_1')
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum (BTL x1 buf4') buf1'') (id_op (case_sum buf4 buf1')) op2')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'a"
        if "step (Inp (Inl x1) (BHD x1 buf4')) op1 op2'"
          and "buf4' x1 \<noteq> []"
        for op2' :: "('k + 'm, 'l + 'n, 'd) op"
          and x1 :: 'k
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using that BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' (BTL x2 buf1'')) (id_op (case_sum buf4 buf1')) op2')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'a"
        if "step (Inp (Inr x2) (BHD x2 buf1'')) op1 op2'"
          and "buf1'' x2 \<noteq> []"
        for op2' :: "('k + 'm, 'l + 'n, 'd) op"
          and x2 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using that BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') op1'a op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'"
        if "step Tau (id_op (case_sum buf4 buf1')) op1'a"
        for op1'a :: "('k + 'm, 'k + 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using that BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op2')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'a"
        if "step Tau op1 op2'"
        for op2' :: "('k + 'm, 'l + 'n, 'd) op"
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)     
          apply (rule step_map_op)
           apply (rule step_comp_op_R_Tau)
             apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1' op2))))) op2'"
        if "step Tau (id_op buf3') op1'"
        for op1' :: "('l, 'l, 'd) op"
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)     
          apply (rule step_map_op)
           apply (rule step_comp_op_R_Tau)
             apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2'a))))) op2'"
        if "step Tau op2 op2'a"
        for op2'a :: "('n, 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)     
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1)) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 (BENQ x2 (BHD x2 buf1) buf1'))) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'l \<Rightarrow> ('k + 'm) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "x2 \<notin> defaults"
          and "buf1 x2 \<noteq> []"
        for x2 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply auto 
        done
      moreover have  H2: "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x buf1)) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2'a))))) op2'"
        if "step (Out x2 x) op2 op2'a"
          and "x2 \<notin> defaults"
        for x :: 'd
          and op2'a :: "('n, 'm, 'd) op"
          and x2 :: 'm
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply simp_all
        apply (rule step_Tau_loop_op)     
         apply (rule step_map_op)
          apply auto
        done
      ultimately show ?thesis
        apply -
        subgoal premises prems
          using H apply -
          by (elim not_in_feedback_wire step_loop_op_elim step_id_op_Out step_id_op_Inp_elim step_map_op_elim step_comp_op_elim exE conjE; simp split: if_splits sum.splits; force intro: prems)
        done
    qed
  next
    fix io :: "('k, 'l, 'd) IO"
      and op1' :: "('k, 'l, 'd) op"
    assume "Inr -` inputs op1 \<inter> defaults = {}"
      and "Inr -` outputs op1 \<inter> defaults = {}"
      and "inputs op2 \<inter> defaults = {}"
      and "outputs op2 \<inter> defaults = {}"
      and H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' (buf1 >> buf1' >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op1'"
    show "\<exists>op2'. wstep io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 (buf2 >> buf2' >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 (buf2 >> buf2' >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' (buf1 >> buf1' >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) op1' op2'"
    proof -
      have False
        if "step (Inp pb x) op2 op2'"
          and "pb \<in> defaults"
        for x :: 'd
          and pb :: 'n
          and op2' :: "('n, 'm, 'd) op"
        using that BISIM by (metis IO.distinct(1) IO.distinct(3) IO.inject(1) IntI Read_choices_inputs emptyE step_choicesE)
      moreover have "\<exists>op2'. wstep (Inp p' x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ p' x buf4)) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'"
        if "p' \<notin> defaults"
        for x :: 'd
          and p' :: 'k
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using BISIM apply blast
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_Inp_loop_op)     
          apply (rule step_map_op)
           apply auto
        done
      moreover have "\<exists>op2'. wstep (Out x1 (BHD x1 buf3')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum (BTL x1 buf3') buf2')))))))) op2'"
        if "buf3' x1 \<noteq> []"
          and "x1 \<notin> defaults"
        for x1 :: 'l
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using BISIM apply blast
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_Out_loop_op)     
           apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((BENQ pa x buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2') (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'a"
        if "step (Out pa x) op2 op2'"
        for x :: 'd
          and pa :: 'm
          and op2' :: "('n, 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using BISIM step_inputs_outputs apply fast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Out_Tau_loop_op[where p="Inr pa"])
        using BISIM(4) apply (auto dest: outputs_after_choices elim!: step_choicesE)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum (BENQ pa (BHD pa buf4) buf4') ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL pa buf4)) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'"
        if "buf4 pa \<noteq> []"
          and "pa \<notin> defaults"
        for pa :: 'k
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using BISIM step_inputs_outputs apply blast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_Tau_comp_op_L)
                 apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum (BTL x1 buf4') ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1' (id_op (case_sum buf3' buf2')))))))) op2'"
        if "step (Inp (Inl x1) (BHD x1 buf4')) op1 op1'"
          and "buf4' x1 \<noteq> []"
        for op1' :: "('k + 'm, 'l + 'n, 'd) op"
          and x1 :: 'k
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
         apply (intro exI conjI)
              apply (rule refl)+
        using BISIM step_inputs_outputs apply force
        using BISIM step_inputs_outputs apply force
        using BISIM step_inputs_outputs apply force
        using BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((BTL x2 buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1' (id_op (case_sum buf3' buf2')))))))) op2'"
        if "step (Inp (Inr x2) (BHD x2 buf1)) op1 op1'"
          and "buf1 x2 \<noteq> []"
          and "buf1'' x2 = []"
          and "buf1' x2 = []"
        for op1' :: "('k + 'm, 'l + 'n, 'd) op"
          and x2 :: 'm
        using that 
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1)
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1))
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 (BENQ x2 (BHD x2 buf1) buf1'))) op1))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))"
          apply (rule step_Inp_Tau_loop_op[where p="Inr x2" and x="BHD x2 buf1"])
              apply (rule step_map_op)
               apply (rule step_comp_op_L_Inp[where p="Inr x2" ])
                 apply (rule step_map_op)
                  apply (rule step_comp_op_L_Inp)
                    apply auto[1]
          using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
          done
        moreover have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1))
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 (BENQ x2 (BHD x2 buf1) buf1'))) op1))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))
      (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1))
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' (BENQ x2 (BHD x2 buf1) buf1'')) (id_op (case_sum buf4 buf1')) op1))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))"
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_L)
          using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
          done
        moreover have "step Tau
      (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1))
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' (BENQ x2 (BHD x2 buf1) buf1'')) (id_op (case_sum buf4 buf1')) op1))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))
      (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1))
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4'  buf1'') (id_op (case_sum buf4 buf1')) op1'))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))"
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_R)
          using BISIM that apply blast
          using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply (intro exI conjI)
                apply (rule refl)+
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> BTL x2 buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1' (id_op (case_sum buf3' buf2')))))))) op2'"
        if "step (Inp (Inr x2) (BHD x2 buf1')) op1 op1'"
          and "buf1'' x2 = []"
          and "buf1' x2 \<noteq> []"
        for op1' :: "('k + 'm, 'l + 'n, 'd) op"
          and x2 :: 'm
        using that 
      proof -
        have "step Tau
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1)
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1)
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' (BENQ x2 (BHD x2 buf1') buf1'')) (id_op (case_sum buf4 (BTL x2 buf1'))) op1))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))"
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_L)
          using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
          done
        moreover have "step Tau
(loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1)
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' (BENQ x2 (BHD x2 buf1') buf1'')) (id_op (case_sum buf4 (BTL x2 buf1'))) op1))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1)
       (map_op projl projr
         (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 (BTL x2 buf1'))) op1'))
           (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))"
          apply (rule step_Tau_loop_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op)
               apply (rule step_Tau_comp_op_R)
          using BISIM that apply blast
          using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply (intro exI conjI)
                apply (rule refl)+
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> BTL x2 buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1' (id_op (case_sum buf3' buf2')))))))) op2'"
        if "step (Inp (Inr x2) (BHD x2 buf1'')) op1 op1'"
          and "buf1'' x2 \<noteq> []"
        for op1' :: "('k + 'm, 'l + 'n, 'd) op"
          and x2 :: 'm
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
         apply (intro exI conjI)
              apply (rule refl)+
        using that BISIM step_inputs_outputs apply force
        using that BISIM step_inputs_outputs apply force
        using that BISIM step_inputs_outputs apply force
        using that BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op)
              apply (rule step_Tau_comp_op_R)
        using BISIM that apply blast
        using BISIM that apply (auto simp add: ran_def split: sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) op1'a op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'"
        if "step Tau (id_op buf4) op1'a"
        for op1'a :: "('k, 'k, 'd) op"
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using that BISIM step_inputs_outputs apply force
        apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2') (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'a"
        if "step Tau op2 op2'"
        for op2' :: "('n, 'm, 'd) op"
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using that BISIM step_inputs_outputs apply fast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (BENQ q xa (case_sum buf3 buf2)) op1' (id_op (case_sum buf3' buf2')))))))) op2'"
        if "step (Out q xa) op1 op1'"
        for xa :: 'd
          and op1' :: "('k + 'm, 'l + 'n, 'd) op"
          and q :: "'l + 'n"
        using that 
      proof (cases q)
        case (Inl a)
        from this that show ?thesis 
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply (intro exI conjI)
                apply (rule refl)+
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply blast
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)
            apply auto
          done
      next
        case (Inr b)
        from this that  show ?thesis 
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply (intro exI conjI)
                apply (rule refl)+
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply force
          using that BISIM step_inputs_outputs apply blast
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)
            apply (rule step_map_op)
             apply (rule step_Tau_comp_op_L)
                apply auto
          done
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum (BTL x1 buf3) buf2) op1 (id_op (case_sum (BENQ x1 (BHD x1 buf3) buf3') buf2')))))))) op2'"
        if "x1 \<notin> defaults"
          and "buf3 x1 \<noteq> []"
        for x1 :: 'l
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using that BISIM step_inputs_outputs apply blast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 (BTL x2 buf2)) op1 (id_op (case_sum buf3' (BENQ x2 (BHD x2 buf2) buf2'))))))))) op2'"
        if "x2 \<notin> defaults"
          and "buf2 x2 \<noteq> []"
        for x2 :: 'n
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using that BISIM step_inputs_outputs apply blast
        apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1' (id_op (case_sum buf3' buf2')))))))) op2'"
        if "step Tau op1 op1'"
        for op1' :: "('k + 'm, 'l + 'n, 'd) op"
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
         apply (intro exI conjI)
              apply (rule refl)+
        using that BISIM step_inputs_outputs apply force
        using that BISIM step_inputs_outputs apply force
        using that BISIM step_inputs_outputs apply force
        using that BISIM step_inputs_outputs apply force
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 op2'a)))))) op2'"
        if "step Tau (id_op (case_sum buf3' buf2')) op2'a"
        for op2'a :: "('l + 'n, 'l + 'n, 'd) op"
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using that BISIM step_inputs_outputs apply blast
        apply auto
        done
      moreover have "\<exists>op2'a. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2'a \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2') (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))) op2'a"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'l \<Rightarrow> ('k + 'n) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp x2 (BHD x2 buf2'')) op2 op2'"
          and "buf2'' x2 \<noteq> []"
        for op2' :: "('n, 'm, 'd) op"
          and x2 :: 'n
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using that BISIM step_inputs_outputs apply fast
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(1))
        apply (rule step_map_op)
         apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R[where p="Inr x2"])
                apply simp_all
        apply (rule step_comp_op_R_Inp)
           apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2))))) op2' \<and> wbisim_cong (\<lambda>op1axx op2axx. \<exists>op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'. op1axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'m) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) (map_op projl projr (comp_op Some (case_sum buf3 ((buf2 >> buf2') >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<and> op2axx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'n) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2'') (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2'))))))) \<and> Inr -` inputs op1 \<inter> defaults = {} \<and> Inr -` outputs op1 \<inter> defaults = {} \<and> inputs op2 \<inter> defaults = {} \<and> outputs op2 \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 (BHD x2 buf2') buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' ((buf1 >> buf1') >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' (BTL x2 buf2'))))))))) op2'"
        if "buf2' x2 \<noteq> []"
          and "x2 \<notin> defaults"
        for x2 :: 'n
        using that 
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
        using that BISIM step_inputs_outputs apply blast
        apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
        done
      ultimately show ?thesis
        apply -
        subgoal premises prems
          using H apply (elim not_in_feedback_wire step_loop_op_elim step_id_op_Out step_id_op_Inp_elim step_map_op_elim step_comp_op_elim exE conjE disjE; clarsimp split: if_splits sum.splits; hypsubst_thin?)
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by meson
          subgoal using prems by fastforce
          subgoal using prems by meson
          done
        done
    qed
  qed
qed

lemma loop_op_commutes_inner_scomp_op:
  fixes op1 :: "('k :: {countable,defaults} + 'm :: {countable,defaults}, 'l :: {countable,defaults} + 'n :: {countable,defaults}, 'd) op"
    and op2 :: "('n, 'm, 'd) op"
  assumes "Inr -` inputs op1 \<inter> defaults = {}"
    and "Inr -` outputs op1 \<inter> defaults = {}"
    and "inputs op2 \<inter> defaults = {}"
    and "outputs op2 \<inter> defaults = {}"
  shows  "(\<stileturn>op1 \<bullet> (\<I> \<parallel> op2))\<up> \<approx> ((\<I> \<parallel> op2) \<bullet> op1\<turnstile>)\<up>"
  unfolding feedback_op_def scomp_op_def pcomp_op_def
  using loop_op_commutes_inner_scomp_op_gen[OF assms, of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" ] by force 

(* FIXME: move me *)
lemma step_inputs_not_in_defaults[elim!]:
  "inputs op \<inter> defaults = {} \<Longrightarrow>
   p \<in> defaults \<Longrightarrow> step (Inp p x) op op' \<Longrightarrow> False"
  by (auto simp add: Read_choices_inputs disjoint_iff elim: step_choicesE)
lemma step_outputs_not_in_defaults[elim!]:
  "outputs op \<inter> defaults = {} \<Longrightarrow>
   p \<in> defaults \<Longrightarrow> step (Out p x) op op' \<Longrightarrow> False"
  by (auto simp add: outputs_after_choices Write_choices_outputs disjoint_iff elim: step_choicesE)


section \<open>Axiom: R6: Loop absorb\<close>
lemma loop_op_absorb_gen:
  fixes op :: "(('a + 'l) + 'k, ('b + 'l :: defaults) + 'k :: defaults, 'c) op"
  assumes "Inr -` inputs op \<inter> defaults = {}"
    and "Inr -` outputs op \<inter> defaults = {}"
    and "Inr -` Inl -`  inputs op \<inter> defaults = {}"
    and "Inr -` Inl -`  outputs op \<inter> defaults = {}"
  shows "map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined buf1) op))) ~
   map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))"
  using assms proof (coinduction arbitrary: op buf1 buf2 rule: bisim_coinduct_upto_alt)
  case BISIM
  then show ?case 
    apply -
    unfolding sim_def
  proof (intro allI impI conjI)
    fix io :: "('a, 'b, 'c) IO"
      and op1' :: "('a, 'b, 'c) op"
    assume "Inr -` inputs op \<inter> defaults = {}"
      and "Inr -` outputs op \<inter> defaults = {}"
      and "Inr -` Inl -` inputs op \<inter> defaults = {}"
      and "Inr -` Inl -` outputs op \<inter> defaults = {}"
      and H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op1'"
    show "\<exists>op2'. step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. step (Inp (projl (projl pa)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "projl pa \<notin> ran (case_sum ((\<lambda>_. None)::'b \<Rightarrow> ('a + 'l) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "pa \<notin> ran (case_sum ((\<lambda>_. None)::'b + 'l \<Rightarrow> (('a + 'l) + 'k) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp pa x) op op''c"
        for x :: 'c
          and pa :: "('a + 'l) + 'k"
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
        using that 
      proof (cases pa)
        case (Inl a)
        from this that show ?thesis 
          apply simp
          apply (intro exI conjI[rotated,OF bc_base])
          using BISIM step_inputs_outputs apply force
          apply (rule step_map_op)
           apply (rule step_Inp_loop_op)
            apply (rule step_map_op)
             apply assumption
          using BISIM apply (auto 4 4 simp add: ran_def split:  if_splits sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
          done
      next
        case (Inr b)
        from this that show ?thesis 
          using BISIM by (auto simp add: ran_def split: if_splits sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
      qed
      moreover have "\<exists>op2'. step (Out x1 x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "step (Out (Inl (Inl x1)) x) op op''c"
        for x :: 'c
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x1 :: 'b
        using that 
        apply (intro exI conjI[rotated,OF bc_base])
        using BISIM step_inputs_outputs apply force
        apply auto
        done
      moreover have "\<exists>op2'. step (Out x1 x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "projl (Inr x2) = (Inl x1::'b + 'l)"
          and "step (Out (Inr x2) x) op op''c"
          and "x2 \<in> defaults"
        for x :: 'c
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x1 :: 'b
          and x2 :: 'k
        using that BISIM
        apply -
        apply (rule FalseE)
        apply (subgoal_tac "Inr x2 \<in> outputs op")
         apply auto[1]
        apply (metis IO.distinct(1) IO.distinct(5) IO.inject(2) op.set_intros(8) outputs_after_choices step_choicesE)
        done
      moreover have "\<exists>op2'. step (Out (projl (Inr x2)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "step (Out (Inl (Inr x2)) x) op op''c"
          and "x2 \<in> defaults"
        for x :: 'c
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: 'l
        using that BISIM
        apply -
        apply (rule FalseE)
        apply (subgoal_tac "Inl (Inr x2) \<in> outputs op")
         apply auto[1]
        apply (metis IO.distinct(1) IO.distinct(5) IO.inject(2) op.set_intros(8) outputs_after_choices step_choicesE)
        done
      moreover have "\<exists>op2'. step (Out (projl (Inr x2)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "projl (Inr x2a) = (Inr x2::'b + 'l)"
          and "step (Out (Inr x2a) x) op op''c"
          and "x2 \<in> defaults"
          and "x2a \<in> defaults"
        for x :: 'c
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: 'l
          and x2a :: 'k
        using that BISIM
        apply -
        apply (rule FalseE)
        apply (subgoal_tac "Inl (Inr x2) \<in> outputs op")
         apply auto[1]
        apply (metis IO.sel(4) IO.simps(4) IO.simps(8) disjoint_iff op.set_intros(8) outputs_after_choices step_choicesE vimageI)
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "step Tau op op''c"
        for op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
        using that 
        apply (intro exI conjI[rotated,OF bc_base])
        using BISIM step_inputs_outputs apply force
        apply auto
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf1)) op''c)))) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'b + 'l \<Rightarrow> (('a + 'l) + 'k) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp (Inr x2) (BHD x2 buf1)) op op''c"
          and "buf1 x2 \<noteq> []"
        for op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: 'k
        using that 
        apply (intro exI conjI[rotated,OF bc_base])
        using BISIM step_inputs_outputs apply force
        apply (rule step_map_op)
         apply (rule step_Inp_Tau_loop_op)
             apply (rule step_map_op)
              apply assumption
        using BISIM apply (auto 4 4 simp add: ran_def split:  if_splits sum.splits dest!: Read_choices_inputs elim!: step_choicesE)
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x buf1)) op''c)))) op2'"
        if "step (Out (Inr x2) x) op op''c"
          and "x2 \<notin> defaults"
        for op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x :: 'c
          and x2 :: 'k
        using that 
        apply (intro exI conjI[rotated,OF bc_base])
        using BISIM step_inputs_outputs apply force
        apply (rule step_map_op)
         apply (rule step_Out_Tau_loop_op)
           apply (rule step_map_op)
            apply auto
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf2)) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "Inr x2 \<in> ran (case_sum ((\<lambda>_. None)::'b \<Rightarrow> ('a + 'l) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "projl pa = Inr x2"
          and "pa \<notin> ran (case_sum ((\<lambda>_. None)::'b + 'l \<Rightarrow> (('a + 'l) + 'k) option) (\<lambda>p. if p \<in> defaults then None else Some (Inr p)))"
          and "step (Inp pa (BHD x2 buf2)) op op''c"
          and "buf2 x2 \<noteq> []"
        for pa :: "('a + 'l) + 'k"
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: 'l
        using that 
        apply (intro exI conjI[rotated,OF bc_base])
        using BISIM step_inputs_outputs apply force
        apply (cases pa)
         apply simp_all
        subgoal for lp
          apply (cases lp)
           apply simp_all
          apply hypsubst_thin
          apply (rule step_map_op)
           apply (rule step_Inp_Tau_loop_op[where p="Inr (Inl x2)"])
               apply (rule step_map_op)
                apply assumption
               apply simp_all
          done
        subgoal for rp
          apply (rule FalseE)
          using  BISIM apply (smt (verit, best) IO.distinct(1) IO.inject(1) IO.simps(6) Read_choices_inputs disjoint_iff mem_Collect_eq step_choicesE vimage_def)
          done
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x buf2)) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "step (Out (Inl (Inr x2)) x) op op''c"
          and "x2 \<notin> defaults"
        for x :: 'c
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: 'l
        using that 
        apply (intro exI conjI[rotated,OF bc_base])
        using BISIM step_inputs_outputs apply force
        apply auto
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x buf2)) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op''c)))) op2'"
        if "projl (Inr x2a) = (Inr x2::'b + 'l)"
          and "step (Out (Inr x2a) x) op op''c"
          and "x2 \<notin> defaults"
          and "x2a \<in> defaults"
        for x :: 'c
          and op''c :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: 'l
          and x2a :: 'k
        using that 
        apply (intro exI conjI[rotated,OF bc_base])
        using BISIM step_inputs_outputs apply force
        apply (rule step_map_op)
         apply (rule step_Out_Tau_loop_op[where p="Inr (Inr x2a)" and x=x and q="Inr (Inr x2a)"])
           apply simp_all
        using BISIM apply (metis IO.sel(4) IO.simps(4) IO.simps(8) disjoint_iff op.set_intros(8) outputs_after_choices step_choicesE vimageI)+
        done      
      ultimately show ?thesis
        using H by (auto 0 0 elim !: not_in_feedback_wire step_loop_op_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
    qed
  next
    fix io :: "('a, 'b, 'c) IO"
      and op1' :: "('a, 'b, 'c) op"
    assume "Inr -` inputs op \<inter> defaults = {}"
      and "Inr -` outputs op \<inter> defaults = {}"
      and "Inr -` Inl -` inputs op \<inter> defaults = {}"
      and "Inr -` Inl -` outputs op \<inter> defaults = {}"
      and H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op))) op1'"
    show "\<exists>op2'. step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) op1' op2'"
    proof -
      have "\<exists>op2'. step (Inp (projl p) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op''b))) op2'"
        if "\<forall>p'. p = Inr p' \<longrightarrow> p' \<in> defaults"
          and "step io'a op op''b"
          and "map_IO reassoc reassoc id io'a = Inp p x"
        for p :: "'a + 'l + 'k"
          and x :: 'c
          and io'a :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) IO"
          and op''b :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
        using that 
      proof (cases p)
        case (Inl a)
        from this that show ?thesis 
          apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
          using BISIM step_inputs_outputs apply force
          apply (cases io'a; simp)
          apply hypsubst_thin
          subgoal for p
            apply (cases p; simp)
            apply (rule step_map_op[of "Inp _ x"])
             apply simp_all
             apply (rule step_Inp_loop_op)
              apply simp_all
              apply (rule step_map_op[of "Inp _ x"])
               apply (rule step_Inp_loop_op)
                apply assumption
               apply (auto split: sum.splits)
            done
          done
      next
        case (Inr b)
        from this that show ?thesis 
          using BISIM by (smt (verit, ccfv_threshold) IO.inject(1) IO.simps(15) IO.simps(16) IO.simps(17) IO.simps(4) IO.simps(6) Inl_in_defaults Inr_in_defaults Read_choices_inputs disjoint_iff reassoc.elims step_choicesE sum.simps(4) vimageI)
      qed
      moreover have "\<exists>op2'. step (Out x1 x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op''b))) op2'"
        if "step io'a op op''b"
          and "map_IO reassoc reassoc id io'a = Out (Inl x1) x"
        for x :: 'c
          and io'a :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) IO"
          and op''b :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x1 :: 'b
        using that 
        apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
        using BISIM step_inputs_outputs apply force
        apply (cases io'a; simp)
        subgoal for p
          apply (cases p; simp split: sum.splits)
          apply (rule step_map_op)
           apply (rule step_Out_loop_op)
             apply auto
          done
        done
      moreover have "\<exists>op2'. step (Out (projl (Inr x2)) x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op''b))) op2'"
        if "step io'a op op''b"
          and "map_IO reassoc reassoc id io'a = Out (Inr x2) x"
          and "x2 \<in> defaults"
        for x :: 'c
          and io'a :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) IO"
          and op''b :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: "'l + 'k"
        using that 
        apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
        using BISIM step_inputs_outputs apply force
        apply (cases io'a; simp)
        apply hypsubst_thin
        subgoal for p
          apply (cases p; simp split: sum.splits)
          subgoal for _ p
            apply (rule FalseE)
            apply hypsubst_thin
            using BISIM apply -
            apply (subgoal_tac "Inl (Inr p) \<in> outputs op")
             apply auto[1]
            apply (metis IO.distinct(1) IO.distinct(5) IO.inject(2) op.set_intros(8) outputs_after_choices step_choicesE)
            done
          subgoal for p
            apply (rule FalseE)
            apply hypsubst_thin
            using BISIM apply -
            apply (subgoal_tac "Inr p \<in> outputs op")
             apply auto[1]
            apply (metis IO.distinct(1) IO.distinct(5) IO.inject(2) op.set_intros(8) outputs_after_choices step_choicesE)
            done
          done
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op''b))) op2'"
        if "step Tau op op''b"
        for op''b :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
        using that 
        apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
        using BISIM step_inputs_outputs apply force
        apply auto
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum (BTL x1 buf2) buf1)) (map_op reassoc reassoc op''b))) op2'"
        if "step io'a op op''b"
          and "map_IO reassoc reassoc id io'a = Inp (Inr (Inl x1)) (BHD x1 buf2)"
          and "x1 \<notin> defaults"
          and "buf2 x1 \<noteq> []"
        for io'a :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) IO"
          and op''b :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x1 :: 'l
        using that 
        apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
        using BISIM step_inputs_outputs apply force
        apply (cases io'a; simp)
        subgoal for p
          apply (cases p; simp split: sum.splits)
          apply (rule step_map_op)
           apply (rule step_Inp_Tau_loop_op)
               apply auto
          done
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 (BTL x2a buf1))) (map_op reassoc reassoc op''b))) op2'"
        if "step io'a op op''b"
          and "map_IO reassoc reassoc id io'a = Inp (Inr (Inr x2a)) (BHD x2a buf1)"
          and "x2a \<notin> defaults"
          and "buf1 x2a \<noteq> []"
        for io'a :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) IO"
          and op''b :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2a :: 'k
        using that 
        apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
        using BISIM step_inputs_outputs apply force
        apply (cases io'a; simp)
        subgoal for p
          apply (cases p; simp split: sum.splits)
          apply (rule step_map_op)
           apply (rule step_Tau_loop_op)
            apply auto
          done
        done
      moreover have "\<exists>op2'. step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op)))) op2' \<and> bisim_cong (\<lambda>sxx txx. \<exists>op buf1 buf2. sxx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'l) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf2) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if (p::'k) \<in> defaults then None else Some (Inr p))) (case_sum undefined buf1) op))) \<and> txx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (case_sum buf2 buf1)) (map_op reassoc reassoc op)) \<and> Inr -` inputs op \<inter> defaults = {} \<and> Inr -` outputs op \<inter> defaults = {} \<and> Inr -` Inl -` inputs op \<inter> defaults = {} \<and> Inr -` Inl -` outputs op \<inter> defaults = {}) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2 x (case_sum buf2 buf1))) (map_op reassoc reassoc op''b))) op2'"
        if "step io'a op op''b"
          and "map_IO reassoc reassoc id io'a = Out (Inr x2) x"
          and "x2 \<notin> defaults"
        for x :: 'c
          and io'a :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) IO"
          and op''b :: "(('a + 'l) + 'k, ('b + 'l) + 'k, 'c) op"
          and x2 :: "'l + 'k"
        using that 
      proof (cases x2)
        case (Inl a)
        from this that show ?thesis 
          apply -
          apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
          using BISIM step_inputs_outputs apply force
          apply (cases io'a; simp)
          subgoal for p
            apply (cases p; simp split: sum.splits)
            apply (rule step_map_op)
             apply (rule step_Out_Tau_loop_op)
               apply auto
            done
          done
      next
        case (Inr b)
        from this that show ?thesis 
          apply -
          apply (intro exI conjI[rotated,OF bc_sym[OF bc_base]])
          using BISIM step_inputs_outputs apply force
          apply (cases io'a; simp)
          apply (cases io'a; simp)
          subgoal for p
            apply (cases p; simp split: sum.splits; hypsubst_thin?)
            apply (rule step_map_op)
             apply (rule step_Tau_loop_op)
              apply auto
            done
          done
      qed
      ultimately show ?thesis
        using H by (auto 0 0 elim !: not_in_feedback_wire step_loop_op_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
    qed
  qed
qed


lemma loop_op_absorb:
  fixes op :: "(('a + 'l) + 'k, ('b + 'l :: defaults) + 'k :: defaults, 'c) op"
  assumes "Inr -` inputs op \<inter> defaults = {}"
    and "Inr -` outputs op \<inter> defaults = {}"
    and "Inr -` Inl -`  inputs op \<inter> defaults = {}"
    and "Inr -` Inl -`  outputs op \<inter> defaults = {}"
  shows  "(op\<up>)\<up> ~ (map_op reassoc reassoc op)\<up>"
  unfolding feedback_op_def
  using loop_op_absorb_gen[OF assms, of "\<lambda> _. []" "\<lambda> _. []"] by auto

find_theorems step transp_op

section \<open>Axiom F2: Transpose looped is identity\<close>
lemma transp_op_loop_id_gen:
  "map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda> p. if p \<in> defaults then None else (Some (Inr p)))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<approx> id_op (buf >> buf' >> buf'')"
proof (coinduction arbitrary: buf buf' buf'' rule: wbisim_coinduct_upto_alt)
  case BISIM
  then show ?case 
    unfolding wsim_def
    sketch (intro allI conjI impI)
  proof (intro allI conjI impI)
    fix io :: "('a, 'a, 'b) IO"
      and op1' :: "('a, 'a, 'b) op"
    assume H: "step io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf'')))) op1'"
    show "\<exists>op2'. wstep io (id_op (buf >> buf' >> buf'')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op (buf >> buf' >> buf'')) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p' xa) (id_op ((buf >> buf') >> buf'')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum (BENQ p' xa buf) buf'')))) op2'"
        if "p' \<notin> defaults"
        for p' :: 'a
          and xa :: 'b
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply auto
        done
      moreover have "\<exists>op2'. wstep (Out x1 (BHD x1 buf'')) (id_op ((buf >> buf') >> buf'')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf (BTL x1 buf''))))) op2'"
        if "x1 \<notin> defaults"
          and "buf'' x1 \<noteq> []"
        for x1 :: 'a
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply auto
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf >> buf') >> buf'')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL x2 buf')) (transp_op (case_sum buf (BENQ x2 (BHD x2 buf') buf''))))) op2'"
        if "x2 \<notin> defaults"
          and "buf' x2 \<noteq> []"
        for x2 :: 'a
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
        done
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (id_op ((buf >> buf') >> buf'')) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ x2a (BHD x2a buf) buf')) (transp_op (case_sum (BTL x2a buf) buf'')))) op2'"
        if "x2a \<notin> defaults"
          and "buf x2a \<noteq> []"
        for x2a :: 'a
        using that 
        apply (intro exI conjI[rotated,OF wbc_base])
        using BISIM step_inputs_outputs apply force
        apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp.rtrancl_refl)
        done       
      ultimately show ?thesis
        using H by (auto 0 0 elim !: step_transp_op_cases not_in_feedback_wire step_loop_op_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
    qed
  next
    fix io :: "('a, 'a, 'b) IO"
      and op1' :: "('a, 'a, 'b) op"
    assume H: "step io (id_op (buf >> buf' >> buf'')) op1'"
    show "\<exists>op2'. wstep io (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op (buf >> buf' >> buf'')) op1' op2'"
    proof -
      have "\<exists>op2'. wstep (Inp p x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (id_op ((BENQ p x buf >> buf') >> buf'')) op2'"
        if "p \<notin> defaults"
        for p :: 'a
          and x :: 'b
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM step_inputs_outputs apply force
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply auto
        done
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf)) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (id_op ((BTL p buf >> buf') >> buf'')) op2'"
        if "buf p \<noteq> []"
          and "p \<notin> defaults"
          and "buf'' p = []"
          and "buf' p = []"
        for p :: 'a
        using that 
      proof -
        have "step Tau (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))))
     (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ p (BHD p buf) buf')) (transp_op (case_sum (BTL p buf) buf''))))"
          apply (rule step_map_op)
           apply (rule step_Out_Tau_loop_op)
          using that  apply (auto split: sum.splits)
          done
        moreover have "step Tau 
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BENQ p (BHD p buf) buf')) (transp_op (case_sum (BTL p buf) buf''))))
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum (BTL p buf) (BENQ p (BHD p buf)  buf'')))))"
          apply (rule step_map_op)
           apply (rule step_Inp_Tau_loop_op)
          using that  apply (auto split: sum.splits)
          done
        moreover have "step (Out p (BHD p buf)) 
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum (BTL p buf) (BENQ p (BHD p buf) buf'')))))
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum (BTL p buf)  buf''))))"
          apply (rule step_map_op)
           apply (rule step_Out_loop_op)
          using that  apply (auto split: sum.splits)
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
          using BISIM step_inputs_outputs apply force
          using wstep_trans_tau_1 step_wstep apply meson
          done
      qed
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (id_op ((buf >> BTL p buf') >> buf'')) op2'"
        if "p \<notin> defaults"
          and "buf'' p = []"
          and "buf' p \<noteq> []"
        for p :: 'a
        using that 
      proof -
        have "step Tau 
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))))
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL p buf')) (transp_op (case_sum buf (BENQ p (BHD p buf') buf'')))))"
          apply (rule step_map_op)
           apply (rule step_Inp_Tau_loop_op)
          using that  apply (auto split: sum.splits)
          done
        moreover have "step (Out p (BHD p buf')) 
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL p buf')) (transp_op (case_sum buf (BENQ p (BHD p buf') buf'')))))
               (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (BTL p buf')) (transp_op (case_sum buf  buf''))))"
          apply (rule step_map_op)
           apply (rule step_Out_loop_op)
          using that  apply (auto split: sum.splits)
          done
        ultimately show ?thesis
          apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
          using BISIM step_inputs_outputs apply force
          using wstep_trans_tau_1 step_wstep apply meson
          done
      qed
      moreover have "\<exists>op2'. wstep (Out p (BHD p buf'')) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf'')))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf buf' buf''. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<and> op2xx = id_op ((buf >> buf') >> buf'')) (id_op ((buf >> buf') >> BTL p buf'')) op2'"
        if "p \<notin> defaults"
          and "buf'' p \<noteq> []"
        for p :: 'a
        using that 
        apply (intro exI conjI[rotated,OF wbc_sym[OF wbc_base]])
        using BISIM step_inputs_outputs apply force
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_Out_loop_op)
        using that  apply (auto split: sum.splits)
        done
      ultimately show ?thesis
        using H by (auto 0 0 elim !: step_id_op_cases step_transp_op_cases not_in_feedback_wire step_loop_op_elim step_map_op_elim step_comp_op_elim split: if_splits sum.splits)
    qed
  qed
qed

lemma transp_op_loop_id: \<open>\<X>\<up> \<approx> \<I>\<close>
  unfolding feedback_op_def 
  using transp_op_loop_id_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] by auto


end
section "Tests"

lemma comp_op_assoc:
  fixes op1 :: "('i1,'o1, 'd) op"
    and op2 :: "('i2, 'o2, 'd) op"
    and op3 :: "('i3, 'o3, 'd) op"
    and buf12 :: "'i2 \<Rightarrow> 'd list"
    and buf23 :: "'i3 \<Rightarrow> 'd list"
    and wire12 :: "'o1 \<rightharpoonup> 'i2"
    and wire23 :: "'o2 \<rightharpoonup> 'i3"
  shows  "(comp_op (map_option Inl o wire12) (buf12 o projl) op1 (comp_op wire23 buf23 op2 op3)) ~
   map_op reassoc reassoc (comp_op (case_sum (\<lambda> _ . None) wire23) buf23 (comp_op wire12 buf12 op1 op2) op3)"
  oops


(* FIXME: move me to utils file *)
lemma ran_comp[simp]:
  "range g = dom f \<Longrightarrow>
   x \<in> ran f \<Longrightarrow> x \<in> ran (f \<circ> g)"
  by (smt (verit, best) comp_def domI image_def mem_Collect_eq ran_def)
lemma projr_surj[simp]:
  "surj projr"
  by (metis sum.sel(2) surj_def)
lemma projl_surj[simp]:
  "surj projl"
  by (metis sum.sel(1) surj_def)

lemma map_op_first_comp_op:
  fixes op1 :: "('i1,'o1, 'd) op"
    and op2 :: "('i2, 'o2, 'd) op"
  assumes "range g = dom wire"
  shows "comp_op wire buf (map_op f g op1) op2 = map_op (case_sum (Inl o f) Inr) (case_sum (Inl o g) Inr) (comp_op (wire o g) buf op1 op2)"
  using assms
  apply (coinduction arbitrary: op1 op2 buf rule: op.coinduct_upto)
  subgoal for op1 op2 buf
    apply auto
    apply (rule rel_setI)
    subgoal for op
      apply (subst (asm) comp_op_code)
      apply auto
      subgoal for op'
        apply (cases op')
        apply auto
        subgoal for p f
          apply hypsubst_thin
          apply (simp flip: choices_map_op)
          apply (simp add: image_iff)
          apply (elim bexE)
          subgoal for op'
            apply (cases op')
            apply auto
            subgoal for p' f'
              apply hypsubst_thin
              apply (intro bexI)
              apply (rule id_op.corec.cong_Read)
              apply (rule refl)
              defer
              apply (subst (1) comp_op_code)
              apply simp
              apply (rule image_eqI)
              defer
              apply simp
              apply (rule disjI1)
              apply (rule image_eqI[of _ _ "Read _ _"])
              apply (simp flip: choices_map_op)
              apply assumption
              apply auto
              apply (smt (verit, ccfv_threshold) comp_eq_dest_lhs rel_fun_def transp_op.cong_base)
              done
            done
          done
        subgoal for op1' p x
          apply (auto simp flip: choices_map_op simp add: image_iff split: option.splits)
          subgoal for op
            apply (cases op; auto; hypsubst?)
            subgoal for op1'' p'
              apply (intro bexI)
              apply (rule id_op.corec.cong_Write)
              apply (rule id_op.corec.cong_base)
              apply force+
              done
            done
          subgoal for q op
            apply (cases op; auto; hypsubst?)
            subgoal for op p'
              apply (intro bexI)
              apply (rule id_op.corec.cong_Silent)
              apply (rule id_op.corec.cong_base)
              apply force
              apply (subst (2) comp_op_code)
              apply simp
              apply (rule image_eqI)
              defer
              apply simp
              apply (rule disjI1)
              apply (rule image_eqI)
              apply (rule refl)
              apply assumption
              apply auto
              done
            done
          done
        subgoal for op
          apply (auto simp flip: choices_map_op simp add: image_iff split: option.splits)
          subgoal for op
            apply (cases op; auto; hypsubst?)
            apply (intro bexI)
            apply (rule id_op.corec.cong_Silent)
            apply (rule id_op.corec.cong_base)
            apply force+
            apply (subst (2) comp_op_code)
            apply simp
            apply (rule image_eqI)
            defer
            apply simp
            apply (rule disjI1)
            apply (rule image_eqI)
            apply (rule refl)
            apply assumption
            apply auto
            done
          done
        done
      subgoal for op'
        apply (cases op')
        apply auto
        subgoal for f p
          apply hypsubst_thin
          apply (intro bexI)
          apply (rule id_op.corec.cong_Read)
          apply (rule refl)
          defer
          apply (subst (1) comp_op_code)
          apply simp
          apply (rule image_eqI)
          defer
          apply simp
          apply (rule disjI2)
          apply (rule image_eqI[of _ _ "Read _ _"])
          apply (auto simp add: ran_def Set.filter_def simp flip: choices_map_op)
          apply (smt (verit, ccfv_threshold) comp_eq_dest_lhs rel_fun_def transp_op.cong_base)
          done    
        subgoal for f p
          apply hypsubst_thin
          apply (intro bexI)
          apply (rule id_op.corec.cong_Silent)
          apply (rule id_op.corec.cong_base)
          apply blast
          apply (subst (2) comp_op_code)
          apply simp
          apply (rule image_eqI)
          defer
          apply simp
          apply (rule disjI2)
          apply (rule image_eqI)
          apply (rule refl)
          apply (auto simp add:  Set.filter_def simp flip: choices_map_op)
          done
        subgoal for p f
          apply hypsubst_thin
          apply (intro bexI)
          apply (rule id_op.corec.cong_Read)
          apply (rule refl)
          defer
          apply (subst (1) comp_op_code)
          apply simp
          apply (rule image_eqI)
          defer
          apply simp
          apply (rule disjI2)
          apply (rule image_eqI[of _ _ "Read _ _"])
          apply (simp flip: choices_map_op)
          apply auto
          apply (smt (verit, del_insts) comp_apply fun_upd_apply rel_funI transp_op.cong_base)
          apply (simp add: ran_def)
          done
        subgoal for op2' p x
          apply hypsubst_thin
          apply (intro bexI)
          apply (rule id_op.corec.cong_Write)
          apply (rule id_op.corec.cong_base)
          apply blast
          apply (rule refl)+
          apply (subst (2) comp_op_code)
          apply simp
          apply (rule image_eqI)
          defer
          apply simp
          apply (rule disjI2)
          apply (rule image_eqI)
          apply (rule refl)
          apply force+
          done
        subgoal for op'
          apply hypsubst_thin
          apply (intro bexI)
          apply (rule id_op.corec.cong_Silent)
          apply (rule id_op.corec.cong_base)
          apply blast
          apply (subst (2) comp_op_code)
          apply simp
          apply (rule image_eqI)
          defer
          apply simp
          apply (rule disjI2)
          apply (rule image_eqI)
          apply (rule refl)
          apply force+
          done
        done
      done
    subgoal for op
      apply (subst (asm) comp_op_code)
      apply (auto split: option.splits)
      subgoal for op'
        apply (cases op')
        apply auto
        subgoal for p f
          apply hypsubst_thin
          apply (intro bexI)
          apply (rule id_op.corec.cong_Read)
          apply (rule refl)
          defer
          apply (subst (1) comp_op_code)
          apply simp
          apply (rule disjI1)
          apply (rule image_eqI)
          defer
          apply (simp flip: image_iff choices_map_op)
          apply auto
          apply (smt (verit, ccfv_threshold) comp_eq_dest_lhs rel_fun_def transp_op.cong_base)
          done
        subgoal for op p x
          apply hypsubst_thin
          apply (auto split: option.splits)
          subgoal
            apply (intro bexI)
            apply (rule id_op.corec.cong_Write)
            apply (rule id_op.corec.cong_base)
            apply blast
            apply (rule refl)+
            apply (subst (2) comp_op_code)
            apply simp
            apply (rule disjI1)
            apply (rule image_eqI)
            apply auto
            done
          subgoal for op
            apply (intro bexI)
            apply (rule id_op.corec.cong_Silent)
            apply (rule id_op.corec.cong_base)
            apply blast
            apply (subst (2) comp_op_code)
            apply simp
            apply (rule disjI1)
            apply (rule image_eqI)
            apply (auto simp flip: image_iff choices_map_op)
            done
          done
        subgoal for op
          apply hypsubst_thin
          apply (intro bexI)
          apply (rule id_op.corec.cong_Silent)
          apply (rule id_op.corec.cong_base)
          apply blast
          apply (subst (2) comp_op_code)
          apply simp
          apply (rule disjI1)
          apply (rule image_eqI)
          apply (auto simp flip: image_iff choices_map_op)
          done
        done
      subgoal for op'
        apply (cases op')
        apply auto
        subgoal for p f
          apply hypsubst_thin
          apply (intro bexI)
          apply (rule id_op.corec.cong_Read)
          apply (rule refl)
          defer
          apply (subst (1) comp_op_code)
          apply simp
          apply (rule disjI2)
          apply (rule image_eqI)
          apply (auto simp flip: image_iff choices_map_op)
          apply (smt (verit, ccfv_threshold) comp_eq_dest_lhs fun_upd_idem_iff rel_fun_def transp_op.cong_base)
          done
        subgoal for p f
          apply hypsubst_thin
          apply (intro bexI)
          apply (rule id_op.corec.cong_Silent)
          apply (rule id_op.corec.cong_base)
          apply force
          apply (subst (2) comp_op_code)
          apply simp
          apply (rule disjI2)
          apply (rule image_eqI)
          apply (auto simp flip: image_iff choices_map_op simp add: ran_def)
          done
        subgoal for p f
          apply (intro bexI)
          apply (rule id_op.corec.cong_Read)
          apply (rule refl)
          defer
          apply (subst (1) comp_op_code)
          apply simp
          apply (rule disjI2)
          apply (rule image_eqI)
          apply (auto simp flip: image_iff choices_map_op)
          apply (smt (verit, ccfv_threshold) comp_apply fun_upd_apply rel_funI transp_op.cong_base)
          done
        subgoal for op p x
          apply hypsubst_thin
          apply (intro bexI)
          apply (rule id_op.corec.cong_Write)
          apply (rule id_op.corec.cong_base)
          apply blast
          apply (rule refl)+
          apply (subst (2) comp_op_code)
          apply simp
          apply (rule disjI2)
          apply (rule image_eqI)
          apply (auto simp flip: image_iff choices_map_op)
          done
        subgoal for op
          apply hypsubst_thin
          apply (intro bexI)
          apply (rule id_op.corec.cong_Silent)
          apply (rule id_op.corec.cong_base)
          apply blast
          apply (subst (2) comp_op_code)
          apply simp
          apply (rule disjI2)
          apply (rule image_eqI)
          apply (auto simp flip: image_iff choices_map_op)
          done
        done
      done
    done
  done


lemma **:
  fixes op1 :: "('i1,'o1, 'd) op"
    and op2 :: "('i2, 'o2, 'd) op"
  assumes "\<And>x. f (f' x) = x"
  shows "comp_op wire buf op1 (map_op f g op2) = map_op (map_sum id f) (map_sum id g) (comp_op (map_option f' o wire) (buf o f) op1 op2)"
  oops

lemma bisim_reflI:
  "op1 = op2 \<Longrightarrow> op1 ~ op2"
  using bisim_refl by auto

lemma scomp_op_assoc_gen:
  "map_op projl projr (comp_op Some buf1 op1 (map_op projl projr (comp_op Some buf2 op2 op3))) ~
   map_op projl projr (comp_op Some buf2 (map_op projl projr (comp_op Some buf1 op1 op2)) op3)"
  unfolding map_op_first_comp_op[where  g=projr and wire=Some and f=projl,unfolded inj_on_def,simplified] **[where f=projl and f'=Inl,simplified]
  apply (rule bisim_trans)
  apply (rule bisim_map_op)
  apply (rule bisim_map_op)
  apply (rule comp_op_assoc)
  apply (rule bisim_reflI)
  apply (unfold op.map_comp)
  apply (rule arg_cong2[where f=map_op])

  apply (simp split: sum.splits)

  apply (rule arg_cong[where f=map_op])



  apply (rule arg_cong[where f="map_op projl projr"])


  apply (auto simp: fun_eq_iff split: sum.splits)
  apply (smt (verit) BNA_Operators.reassoc.simps(1) BNA_Operators.reassoc.simps(2) id_apply map_sum.simps(1) map_sum.simps(2) sum.exhaust_sel sum.sel(1))
  oops 

end