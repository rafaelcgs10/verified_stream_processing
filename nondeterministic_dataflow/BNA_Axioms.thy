\<comment> \<open>Axioms from Table 1 for BNA operators\<close>
theory BNA_Axioms

imports
  BNA_Operators
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
              apply (rule step_transp_op_Read[where buf="case_sum buf1 buf2" and p="Inr lp", simplified])
             apply auto
            done
          subgoal for rp
            apply hypsubst_thin
            apply (intro exI conjI[rotated])        
             apply (rule wbc_base)
             apply force
            apply (rule step_wstep)
            apply (rule step_map_op[of "Inp (Inl (Inr (Inr rp))) _"])
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
                         apply (rule step_id_op_Read[where p=lp])
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
              apply (rule step_transp_op_Write[where p="Inl _"])
                 apply simp_all
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
          apply (rule step_transp_op_Write[where p="Inr _"])
             apply simp_all
          apply simp
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
          apply (drule step_id_op_Inp[of \<open>Inp p' x\<close> buf1 _ p' x])
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
          apply (drule step_id_op_Inp[of \<open>Inp p' x\<close> buf2 _ p' x])
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
            apply (rule exI[of _ \<open>map_op projl projr
          (comp_op Some (case_sum buf2' buf1') (transp_op (case_sum buf1 buf2))
            (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf2''' op2 (id_op buf2'')))
              (map_op projl projr (comp_op Some (BENQ p' x buf1''') op1' (id_op buf1'')))))\<close>])
            apply (rule conjI)
              apply fastforce
            apply (rule wbc_base)
            apply fast
            done
          done
        done
      subgoal for p
        apply (erule step_transp_op_Inp)
         apply (auto split: sum.splits)
        subgoal for p'
          apply (rule exI[of _ \<open>map_op projl projr
                (comp_op Some (case_sum buf2' buf1') (transp_op (case_sum buf1 buf2))
                  (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf2''' op2 (id_op buf2'')))
                    (map_op projl projr (comp_op Some (BTL p' buf1''') op1 (id_op (BENQ p' (BHD p' buf1''') buf1''))))))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule wbc_base)
          apply fast
          done
        subgoal for p'
          apply (rule exI[of _ \<open>map_op projl projr
                (comp_op Some (case_sum buf2' buf1') (transp_op (case_sum buf1 buf2))
                  (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (BTL p' buf2''') op2 (id_op (BENQ p' (BHD p' buf2''') buf2''))))
                    (map_op projl projr (comp_op Some buf1''' op1 (id_op buf1'')))))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule wbc_base)
          apply fast
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
            apply (rule exI[of _ \<open>map_op projl projr
          (comp_op Some (case_sum buf2' (BTL p buf1')) (transp_op (case_sum buf1 buf2))
            (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf2''' op2 (id_op buf2'')))
              (map_op projl projr (comp_op Some buf1''' op1' (id_op buf1'')))))\<close>])
            apply (rule conjI)
             apply fastforce
            apply (rule wbc_base)
            apply fast
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
            apply (rule exI[of _ \<open>map_op projl projr
       (comp_op Some (case_sum buf2' buf1') (transp_op (case_sum buf1 buf2))
         (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf2''' op2' (id_op buf2'')))
           (map_op projl projr (comp_op Some buf1''' op1 (id_op buf1'')))))\<close>])
            apply (rule conjI)
             apply fastforce
            apply (rule wbc_base)
            apply fast
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
        apply (rule exI[of _ \<open>map_op projl projr
          (comp_op Some (case_sum buf1''' buf2''')
            (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf1' (id_op (BENQ p' x buf1)) op1))
              (map_op projl projr (comp_op Some buf2' (id_op buf2) op2)))
            (transp_op (case_sum buf1'' buf2'')))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule wbc_sym)
          apply (rule wbc_base)
          apply fastforce
          done
        subgoal for p'
        apply (rule exI[of _ \<open>map_op projl projr
          (comp_op Some (case_sum buf1''' buf2''')
            (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf1' (id_op buf1) op1))
              (map_op projl projr (comp_op Some buf2' (id_op (BENQ p' x buf2)) op2)))
            (transp_op (case_sum buf1'' buf2'')))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule wbc_sym)
          apply (rule wbc_base)
          apply fastforce
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
          apply (rule exI[of _ \<open>map_op projl projr
          (comp_op Some (case_sum buf1''' buf2''')
            (comp_op (\<lambda>_. None) (\<lambda>_. [])
              (map_op projl projr (comp_op Some (BENQ p' x buf1') (id_op (BTL p' buf1)) op1))
              (map_op projl projr (comp_op Some buf2' (id_op buf2) op2)))
            (transp_op (case_sum buf1'' buf2'')))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule wbc_sym)
          apply (rule wbc_base)
          apply fast
          done
        subgoal for p'
          apply (rule exI[of _ \<open>map_op projl projr
          (comp_op Some (case_sum buf1''' buf2''')
            (comp_op (\<lambda>_. None) (\<lambda>_. [])
              (map_op projl projr (comp_op Some buf1' (id_op buf1) op1))
              (map_op projl projr (comp_op Some (BENQ p' x buf2') (id_op (BTL p' buf2)) op2)))
            (transp_op (case_sum buf1'' buf2'')))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule wbc_sym)
          apply (rule wbc_base)
          apply fast
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
            apply (rule exI[of _ \<open>map_op projl projr
       (comp_op Some (case_sum buf1''' buf2''')
         (comp_op (\<lambda>_. None) (\<lambda>_. [])
           (map_op projl projr (comp_op Some buf1' (id_op buf1) op1))
           (map_op projl projr (comp_op Some (BTL p' buf2') (id_op buf2) op2')))
         (transp_op (case_sum buf1'' buf2'')))\<close>])
            apply (rule conjI)
             apply fastforce
            apply (rule wbc_sym)
            apply (rule wbc_base)
            apply fast
            done
          done
        subgoal for p'
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for op1'
            apply (rule exI[of _ \<open>map_op projl projr
       (comp_op Some (case_sum buf1''' buf2''')
         (comp_op (\<lambda>_. None) (\<lambda>_. [])
           (map_op projl projr (comp_op Some (BTL p' buf1') (id_op buf1) op1'))
           (map_op projl projr (comp_op Some buf2' (id_op buf2) op2)))
         (transp_op (case_sum buf1'' buf2'')))\<close>])
            apply (rule conjI)
             apply fastforce
            apply (rule wbc_sym)
            apply (rule wbc_base)
            apply fast
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
            apply (rule exI[of _ \<open>map_op projl projr
       (comp_op Some (case_sum buf1''' (BENQ p x buf2'''))
         (comp_op (\<lambda>_. None) (\<lambda>_. [])
           (map_op projl projr (comp_op Some buf1' (id_op buf1) op1))
           (map_op projl projr (comp_op Some buf2' (id_op buf2) op2')))
         (transp_op (case_sum buf1'' buf2'')))\<close>])
            apply (rule conjI)
             apply fastforce
            apply (rule wbc_sym)
            apply (rule wbc_base)
            apply fast
            done
          subgoal for p
            apply (drule step_id_op_Inp)
             apply simp
            apply (rule exI[of _ \<open>map_op projl projr
       (comp_op Some (case_sum buf1''' (BTL p buf2'''))
         (comp_op (\<lambda>_. None) (\<lambda>_. [])
           (map_op projl projr (comp_op Some buf1' (id_op buf1) op1))
           (map_op projl projr (comp_op Some buf2' (id_op buf2) op2)))
         (transp_op (case_sum buf1'' (BENQ p (BHD p buf2''') buf2''))))\<close>])
            apply (rule conjI)
            subgoal
              apply (rule step_star_map_op)
              apply (rule rtranclp.intros(2))
               apply (rule rtranclp.intros(1))
              apply (rule step_Tau_comp_op_R)
                  apply simp_all
              apply auto
              done
            subgoal
              apply (rule wbc_sym)
              apply (rule wbc_base)
              apply fast
              done
            done
          subgoal for op2'
            apply (rule exI[of _ \<open>map_op projl projr
          (comp_op Some (case_sum buf1''' buf2''')
            (comp_op (\<lambda>_. None) (\<lambda>_. [])
              (map_op projl projr (comp_op Some buf1' (id_op buf1) op1))
              (map_op projl projr (comp_op Some buf2' (id_op buf2) op2')))
            (transp_op (case_sum buf1'' buf2'')))\<close>])
            apply (rule conjI)
             apply fastforce
            apply (rule wbc_sym)
            apply (rule wbc_base)
            apply fast
            done
          done
        subgoal
          apply (drule step_map_op_inv)
          apply auto
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for p x op1'
            apply (rule exI[of _ \<open>map_op projl projr
       (comp_op Some (case_sum (BENQ p x buf1''') buf2''')
         (comp_op (\<lambda>_. None) (\<lambda>_. [])
           (map_op projl projr (comp_op Some buf1' (id_op buf1) op1'))
           (map_op projl projr (comp_op Some buf2' (id_op buf2) op2)))
         (transp_op (case_sum buf1'' buf2'')))\<close>])
            apply (rule conjI)
             apply fastforce
            apply (rule wbc_sym)
            apply (rule wbc_base)
            apply fast
            done
          subgoal for p
            apply (drule step_id_op_Inp)
             apply simp
            apply (rule exI[of _ \<open>map_op projl projr
       (comp_op Some (case_sum (BTL p buf1''') buf2''')
         (comp_op (\<lambda>_. None) (\<lambda>_. [])
           (map_op projl projr (comp_op Some buf1' (id_op buf1) op1))
           (map_op projl projr (comp_op Some buf2' (id_op buf2) op2)))
         (transp_op (case_sum (BENQ p (BHD p buf1''') buf1'') buf2'')))\<close>])
            apply (rule conjI)
            subgoal
              apply (rule step_star_map_op)
              apply (rule rtranclp.intros(2))
               apply (rule rtranclp.intros(1))
              apply (rule step_Tau_comp_op_R)
                apply auto
              done
            subgoal
              apply (rule wbc_sym)
              apply (rule wbc_base)
              apply fast
              done
            done
          subgoal for op1'
            apply (rule exI[of _ \<open>map_op projl projr
       (comp_op Some (case_sum buf1''' buf2''')
         (comp_op (\<lambda>_. None) (\<lambda>_. [])
           (map_op projl projr (comp_op Some buf1' (id_op buf1) op1'))
           (map_op projl projr (comp_op Some buf2' (id_op buf2) op2)))
         (transp_op (case_sum buf1'' buf2'')))\<close>])
            apply (rule conjI)
             apply fastforce
            apply (rule wbc_sym)
            apply (rule wbc_base)
            apply fast
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
          apply (intro exI conjI[rotated])
           apply (rule wbc_base)
           apply fast
          apply force
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
                apply (intro exI conjI[rotated])
                 apply (rule wbc_base)
                 apply fast
                apply force
                done
              done
            done
          done
        subgoal for p x op2'
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule wbc_base)
           apply fast
          apply auto
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_Tau_loop_op)
          apply (rule step_map_op)
           apply simp_all
           apply auto
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
             apply auto
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
              apply (cases "lbuf2 p")
              subgoal
                apply (intro exI conjI[rotated])
                 apply (rule wbc_base)
                 apply (rule exI[of _ op'''])
                 apply (rule exI[of _ op2])
                 apply (rule exI[of _ buf2])
                 apply (rule exI[of _ "BTL p lbuf1"])
                 apply (rule exI[of _ "lbuf2"])
                 apply (rule exI[of _ "lbuf3"])
                 apply (intro exI conjI)
                  apply simp_all
                done
              subgoal for x lbuf2'
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
                    apply auto
                  try0

end
                  done
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
              done
            done
          subgoal for op p
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply force+
            done
          subgoal for op p
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply force+
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_loop_op)
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_comp_op_L)
              apply (rule step_comp_op_R_Out)
              apply (rule step_id_op_Write[where p=p])
               apply force+
            apply simp
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Tau_loop_op)
             apply (rule step_map_op[of Tau])
              apply (rule step_Tau_comp_op_R)
                 apply assumption
                apply simp_all
            done
          subgoal for op p
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply force+
            done
          subgoal for op''' p x
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply (rule exI[of _ op'''])
             apply (rule exI[of _ op2])
             apply (rule exI[of _ buf2])
             apply (rule exI[of _ "BENQ p x  lbuf1"])
             apply (rule exI[of _ "lbuf2"])
             apply (rule exI[of _ "lbuf3"])
             apply (intro exI conjI)
              apply simp_all
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
                 apply (auto split: sum.splits if_splits simp add: )
                apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)
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
              apply (simp add: BULK_BENQ_bulk_benq)+
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
             apply (auto split: sum.splits if_splits simp add: case_sum_updateR)
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
             apply (auto split: sum.splits if_splits)
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
                apply (rule transitive_closurep_trans'(6))
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Tau_loop_op)
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Tau_comp_op_R)
                    apply (rule step_comp_op_R_Inp)
                     apply (rule step_id_op_Read[where p=p])
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
                apply (simp add: BENQ_def)
                apply (rule transitive_closurep_trans'(6))
                 apply (rule step_map_op[of Tau])
                  apply simp_all
                 apply (rule step_Inp_Inr_loop_op[where p=p])
                  apply (rule step_map_op[of "Inp (Inl (Inr p)) (BHD p lbuf1)"])
                   apply simp_all
                 apply (rule step_comp_op_L_Inp[of _ _ _ op1'])
                 apply (metis BHD_BAPPEND_2_cases)
                apply (simp_all add: BTL_def BENQ_def) 
                apply (metis (no_types, lifting) Nitpick.rtranclp_unfold fun_upd_triv)
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
                done
              done
            subgoal for x lbuf3'
              apply auto
              done
            done
          subgoal for op p
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply fast
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Inp_Inr_loop_op)
              apply (rule step_map_op[of "Inp (Inl (Inr p)) _"])
               apply simp_all
             apply (rule step_comp_op_L_Inp[of _ _ _ op])
             apply (metis BHD_BAPPEND_2_cases)
            apply auto
            done
          subgoal for op p
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply fast
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Out_Inr_loop_op)
             apply (rule step_map_op[of "Out (Inr _) _"])
              apply simp_all
             apply (rule step_comp_op_R_Out)
             apply (rule step_comp_op_R_Out)
             apply (rule step_id_op_Write)
              apply simp_all
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Inp_Inr_loop_op)
              apply (rule step_map_op[of "Inp (Inl (Inr p)) _"])
               apply simp_all
              apply (rule step_comp_op_L_Inp[of _ _ _ op])
              apply (simp add: BULK_BENQ_def)
             apply (auto simp add: BENQ_def BTL_def)
            apply (metis fun_upd_triv rtranclp_intros_1')
            done
          subgoal for op p
            apply (intro exI conjI[rotated])
             apply (rule wbc_base)
             apply fast
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Inp_Inr_loop_op)
              apply (rule step_map_op[of "Inp (Inl (Inr p)) _"])
               apply simp_all
             apply (rule step_comp_op_L_Inp[of _ _ _ op])
             apply (metis BHD_BAPPEND_2_cases)
            apply auto
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
        subgoal
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule wbc_base)
           apply force+
          done
        done
      done
    subgoal for io op2'
      apply (drule step_map_op_inv)
      apply auto
      apply hypsubst_thin
      apply (drule step_loop_op)
      apply auto
      subgoal
        apply (drule step_map_op_inv)
        apply auto
        apply hypsubst_thin
        apply (drule step_comp_op_cases)
        apply auto
        subgoal
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force+
          done
        done
      subgoal for p op2'' x
        apply (drule step_map_op_inv)
        apply auto
        subgoal for io op2''
          apply hypsubst_thin
          apply (drule step_comp_op_cases)
          apply auto
          apply hypsubst_thin
          subgoal for op2''
            apply (drule step_comp_op_cases)
            apply auto
            subgoal for op2''
              apply hypsubst_thin
              apply (intro exI conjI[rotated])
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force+
              done
            done
          done
        done
      subgoal for op2'
        apply (drule step_map_op_inv)
        apply auto
        subgoal for io op2''
          apply hypsubst_thin
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for p x op1'
            apply hypsubst_thin
            apply (cases p)
            subgoal for lp
              apply auto
              apply hypsubst_thin
              apply (intro exI conjI[rotated])
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply (rule exI[of _ op1'])
               apply (rule exI[of _ op2])
               apply (rule exI[of _ "BENQ lp x buf2"])
               apply (rule exI[of _ "lbuf1"])
               apply (rule exI[of _ "lbuf2"])
               apply (rule exI[of _ "lbuf3"])
               apply (intro exI conjI)
                apply force+
              done
            subgoal for rp
              apply auto
              apply hypsubst_thin
              apply (intro exI conjI[rotated])
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply (rule exI[of _ op1'])
               apply (rule exI[of _ op2])
               apply (rule exI[of _ "buf2"])
               apply (rule exI[of _ "BENQ rp x lbuf1"])
               apply (rule exI[of _ "lbuf2"])
               apply (rule exI[of _ "lbuf3"])
               apply (intro exI conjI)
                apply force+
              apply (rule transitive_closurep_trans'(6))
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_comp_op_L_Tau)
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Out_Inr_loop_op)
               apply assumption
              apply simp
              done
            done
          subgoal for p op2'
            apply (cases p)
            subgoal for lp
              apply auto
              apply hypsubst_thin
              apply (drule step_comp_op_cases)
              apply auto
              subgoal for op2'
                apply hypsubst_thin
                apply (intro exI conjI[rotated])
                 apply (rule wbc_sym)
                 apply (rule wbc_base)
                 apply (rule exI[of _ op1])
                 apply (rule exI[of _ op2'])
                 apply (rule exI[of _ "BTL lp buf2"])
                 apply (rule exI[of _ "lbuf1"])
                 apply (rule exI[of _ "lbuf2"])
                 apply (rule exI[of _ "lbuf3"])
                 apply force+
                done
              done
            subgoal for rp
              apply auto
              apply hypsubst_thin
              apply (drule step_comp_op_cases)
              apply auto
              subgoal for op2'
                apply hypsubst_thin
                apply (intro exI conjI[rotated])
                 apply (rule wbc_sym)
                 apply (rule wbc_base)
                 apply (rule exI[of _ op1])
                 apply (drule step_id_op_Inp)
                  apply auto
                apply hypsubst_thin
                apply (rule exI[of _ op2])
                apply (rule exI[of _ "buf2"])
                apply (rule exI[of _ "BTL rp lbuf1"])
                apply (rule exI[of _ "BENQ rp (BHD rp lbuf1) lbuf2"])
                apply (rule exI[of _ "lbuf3"])
                apply (intro exI conjI[rotated])
                 apply (rule arg_cong[where f="map_op projl projl"])
                 apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
                  apply auto
                done
              done
            done
          subgoal for op1'
            apply hypsubst_thin
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply force+
            done
          subgoal for op1'
            apply hypsubst_thin
            apply (drule step_comp_op_cases)
            apply auto
            subgoal for op2'
              apply hypsubst_thin
              apply (intro exI conjI[rotated])
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force+
              done
            subgoal for op2'
              apply hypsubst_thin
              apply (subst (asm) id_op_code)
              apply auto
              done
            done
          done
        done
      subgoal for op1' p
        apply (drule step_map_op_inv)
        apply auto
        subgoal for io op2''
          apply hypsubst_thin
          apply (drule step_comp_op_cases)
          apply auto
          apply hypsubst_thin
          subgoal for op1'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply (rule exI[of _ op1'])
             apply (rule exI[of _ op2])
             apply (rule exI[of _ "buf2"])
             apply (rule exI[of _ "lbuf1"])
             apply (rule exI[of _ "lbuf2"])
             apply (rule exI[of _ "BTL p lbuf3"])
             apply force+
            apply (rule transitive_closurep_trans'(6))
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_comp_op_L_Tau)
             apply (rule step_map_op[of Tau])
              apply simp_all
             apply (rule step_Inp_Inr_loop_op[where p=p])
              apply simp_all
             apply (auto split: sum.splits if_splits simp add: case_sum_updateR)
            apply (simp add: BULK_BENQ_def)+
            done
          done
        done
      subgoal for op1' p x
        apply (drule step_map_op_inv)
        apply auto
        subgoal for io op2''
          apply hypsubst_thin
          apply (drule step_comp_op_cases)
          apply auto
          apply hypsubst_thin
          apply (drule step_comp_op_cases)
          apply auto
          apply (drule step_id_op_Out)
           apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply (rule exI[of _ op1])
           apply (rule exI[of _ op2])
           apply (rule exI[of _ "buf2"])
           apply (rule exI[of _ "lbuf1"])
           apply (rule exI[of _ "BTL p lbuf2"])
           apply (rule exI[of _ "BENQ p (BHD p lbuf2) lbuf3"])
           apply force
          apply (rule rtranclp_intros_1')
          apply (rule arg_cong[where f="map_op projl projr"])
          apply (rule arg_cong2[where f="comp_op Some buf2"])
           apply (rule arg_cong[where f="map_op projl projl"])
           apply (rule arg_cong2[where f="loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr))"])
            apply (auto split: sum.splits if_splits simp add: )
          apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)
          done
        done
      done
    done
  done

lemma loop_op_distribute_scomp_op:
  "(op1\<up>) \<bullet> op2 \<approx> (op1 \<bullet> (op2 \<parallel> \<I>))\<up>"
  unfolding feedback_op_def scomp_op_def pcomp_op_def
  using loop_op_distribute_scomp_op_gen[of "\<lambda>_. []" "\<lambda>_. []" "\<lambda>_. []" "\<lambda>_. []" op1 op2] by simp

section \<open>Axiom: R3: Loop parallel composition\<close>

lemma loop_op_pcomp_commue_gen:
  "comp_op (\<lambda>_. None) (\<lambda>_. []) op1 (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf1) op2)) ~
   map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf1) (map_op BNA_Operators.assoc BNA_Operators.assoc (comp_op (\<lambda>_. None) (\<lambda>_. []) op1 op2)))"
  apply (coinduction arbitrary: op1 op2 buf1 rule: bisim_coinduct_upto)
  subgoal for op1 op2 buf1
    unfolding sim_def
    apply auto
    subgoal for io op'
      apply (drule step_comp_op_cases)
      apply (auto; hypsubst_thin)
      subgoal
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
         apply force+
        done
      subgoal for p x op2'
        apply (drule step_map_op_inv)
        apply auto
        subgoal for io op2''
          apply hypsubst_thin
          apply (drule step_loop_op)
          apply (auto; hypsubst_thin)
          subgoal for op2'
            apply (intro conjI[rotated] exI)
             apply (rule bc_base)
             apply force+
            done
          done
        done
      subgoal
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
         apply force+
        done
      subgoal for p x op2'
        apply (drule step_map_op_inv)
        apply auto
        subgoal for io op2''
          apply hypsubst_thin
          apply (drule step_loop_op)
          apply (auto; hypsubst_thin)
          subgoal for op2'
            apply (intro conjI[rotated] exI)
             apply (rule bc_base)
             apply force+
            done
          done
        done
      subgoal
        apply (intro conjI[rotated] exI)
         apply (rule bc_base)
         apply force+
        done
      subgoal
        apply (drule step_map_op_inv)
        apply auto
        subgoal for io op2''
          apply (drule step_loop_op)
          apply (auto; hypsubst_thin)
          subgoal 
            apply (intro conjI[rotated] exI)
             apply (rule bc_base)
             apply force+
            done
          subgoal for op2' p
            apply (intro conjI[rotated] exI)
             apply (rule bc_base)
             apply (rule exI[of _ op1])
             apply (rule exI[of _ op2'])
             apply (rule exI[of _ "BTL p buf1"])
             apply force+
            done
          subgoal for op2' p x
            apply (intro conjI[rotated] exI)
             apply (rule bc_base)
             apply (rule exI[of _ op1])
             apply (rule exI[of _ op2'])
             apply (rule exI[of _ "BENQ p x buf1"])
             apply force+
            done
          done
        done
      done
    subgoal for io op'
      apply (drule step_map_op_inv)
      apply auto
      apply hypsubst_thin
      subgoal for io' op'
        apply (drule step_loop_op)
        apply (auto; hypsubst_thin)
        subgoal for p op x
          apply (drule step_map_op_inv)
          apply auto
          apply hypsubst_thin
          apply (drule step_comp_op_cases)
          apply auto
           apply hypsubst_thin
          subgoal for p op1'
            apply (intro conjI[rotated] exI)
             apply (rule bc_sym)
             apply (rule bc_base)
             apply force+
            done
          subgoal for p' op2'
            apply (cases p; cases p')
               apply auto
            apply hypsubst_thin
            apply (intro conjI[rotated] exI)
             apply (rule bc_sym)
             apply (rule bc_base)
             apply force+
            done
          done
        subgoal for p op x
          apply (drule step_map_op_inv)
          apply (auto; hypsubst_thin)
          apply (drule step_comp_op_cases)
          apply (auto; hypsubst_thin?)
          subgoal for p' op2'
            apply (cases p; cases p')
               apply auto
            apply hypsubst_thin
            apply (intro conjI[rotated] exI)
             apply (rule bc_sym)
             apply (rule bc_base)
             apply force+
            done
          subgoal for p' op2'
            apply (intro conjI[rotated] exI)
             apply (rule bc_sym)
             apply (rule bc_base)
             apply force+
            done
          done
        subgoal for op'
          apply (drule step_map_op_inv)
          apply (auto; hypsubst_thin)
          apply (drule step_comp_op_cases)
          apply (auto; hypsubst_thin?)
          subgoal for op1'
            apply (intro conjI[rotated] exI)
             apply (rule bc_sym)
             apply (rule bc_base)
             apply force+
            done
          subgoal for op2'
            apply (intro conjI[rotated] exI)
             apply (rule bc_sym)
             apply (rule bc_base)
             apply force+
            done
          done
        subgoal for op'' p
          apply (drule step_map_op_inv)
          apply (auto; hypsubst_thin)
          apply (drule step_comp_op_cases)
          apply (auto; hypsubst_thin?)
          subgoal for p' op2'
            apply (cases p')
             apply auto
            apply hypsubst_thin
            apply (intro conjI[rotated] exI)
             apply (rule bc_sym)
             apply (rule bc_base)
             apply (rule exI[of _ op1])
             apply (rule exI[of _ op2'])
             apply (rule exI[of _ "BTL p buf1"])
             apply force+
            done
          done
        subgoal for op'' p x
          apply (drule step_map_op_inv)
          apply (auto; hypsubst_thin)
          apply (drule step_comp_op_cases)
          apply (auto; hypsubst_thin?)
          subgoal for p' op2'
            apply (cases p')
             apply (auto; hypsubst_thin)
            apply (intro conjI[rotated] exI)
             apply (rule bc_sym)
             apply (rule bc_base)
             apply (rule exI[of _ op1])
             apply (rule exI[of _ op2'])
             apply (rule exI[of _ "BENQ p x buf1"])
             apply force
            apply (rule step_comp_op_R_Tau)
            apply (rule step_map_op[of Tau])
             apply simp_all
            apply (drule step_Out_Inr_loop_op[where buf="case_sum undefined buf1", simplified])
            apply (auto simp flip: fun_upd_apply)
            done
          done
        done
      done
    done
  done

lemma loop_op_pcomp_commue:
  "op1 \<parallel> (op2\<up>) ~ (map_op assoc assoc (op1 \<parallel> op2))\<up>"
  unfolding feedback_op_def scomp_op_def pcomp_op_def
  using loop_op_pcomp_commue_gen[of op1 "\<lambda>_. []" op2] by auto

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

section \<open>Axiom: R4: Loop commutes inner sequential composition\<close>
lemma loop_op_commutes_inner_scomp_op_gen:
  "map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf1)
   (map_op projl projr (comp_op Some (case_sum buf3 (buf2 >> buf2' >> buf2'')) (map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2)))) \<approx>
   map_op projl projl
  (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf2'')
   (map_op projl projr (comp_op Some (case_sum buf4' (buf1 >> buf1' >> buf1'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf4) op2) (map_op projl projr (comp_op Some (case_sum buf3 buf2) op1 (id_op (case_sum buf3' buf2')))))))"
  apply (coinduction arbitrary: op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4' rule: wbisim_coinduct_upto)
  subgoal for op1 op2 buf1 buf1' buf1'' buf2 buf2' buf2'' buf3 buf3' buf4 buf4'
    unfolding wsim_def
    apply auto
    subgoal for io op'
      apply (drule step_map_op_inv)
      apply (auto; hypsubst_thin)
      subgoal for io' op''
        apply (drule step_loop_op)
        apply (auto; hypsubst_thin)
        subgoal for p op'' x
          apply (drule step_map_op_inv)
          apply (auto; hypsubst_thin)
          apply (drule step_comp_op_cases)
          apply (auto; hypsubst_thin?)
          apply (drule step_map_op_inv)
          apply (auto; hypsubst_thin?)
          apply (drule step_comp_op_cases)
          apply (auto; hypsubst_thin?)
          apply (drule step_id_op_Inp)
           apply (auto; hypsubst_thin?)
          subgoal for op1'
            apply hypsubst_thin
            apply (rule exI)
            apply (rule conjI[rotated])
             apply (rule wbc_base)
             apply force
            apply (rule step_wstep)
            apply (rule step_map_op[of "Inp (Inl p) _"])
             apply simp_all
            apply (rule step_Inp_Inl_loop_op)
            apply (rule step_map_op[of "Inp (Inl (Inl p)) _"])
             apply simp_all
            apply (rule step_comp_op_L_Inp)
            apply (rule step_comp_op_L_Inp)
            using step_id_op_Read apply (metis BAPPEND_BENQ)
            done
          done
        subgoal for p op'' x
          apply (drule step_map_op_inv)
          apply (auto; hypsubst_thin)
          apply (drule step_comp_op_cases)
          apply (auto; hypsubst_thin?)
          apply (drule step_comp_op_cases)
          apply (auto; hypsubst_thin?)
          apply (drule step_id_op_Out)
           apply (auto; hypsubst_thin?)
          subgoal for op1'
            apply auto
            apply hypsubst_thin
            apply (rule exI)
            apply (rule conjI[rotated])
             apply (rule wbc_base)
             apply (rule exI[of _ op1])
             apply (rule exI[of _ op2])
             apply (rule exI[of _ buf1])
             apply (rule exI[of _ buf1'])
             apply (rule exI[of _ buf1''])
             apply (rule exI[of _ buf2])
             apply (rule exI[of _ buf2'])
             apply (rule exI[of _ buf2''])
             apply (rule exI[of _ "buf3"])
             apply (rule exI[of _ "BTL p buf3'"])   
             apply (intro exI conjI)
              apply simp
             apply (rule refl)
            apply (rule step_wstep)
            apply (rule step_map_op[of "Out (Inl p) _", rotated])
             apply simp
            apply (rule step_Out_Inl_loop_op)
            apply (rule step_map_op[of "Out (Inr (Inl p)) _", rotated])
             apply simp
            apply (rule step_comp_op_R_Out)
            apply (rule step_map_op[of "Out (Inr (Inl p)) _", rotated])
             apply simp
            apply (rule step_comp_op_R_Out)
            apply (smt (verit, del_insts) BAPPEND_BTL BULK_BENQ_def append_is_Nil_conv case_sum_BTL_L hd_append2 old.sum.simps(5) step_id_op_Write)      
            done
          done
        subgoal for op''
          apply (drule step_map_op_inv)
          apply (auto; hypsubst_thin)
          apply (drule step_comp_op_cases)
          apply (auto; hypsubst_thin?)
             apply (drule step_map_op_inv)
             apply (auto; hypsubst_thin?)
             apply (drule step_comp_op_cases)
             apply auto
          subgoal for x p op1'
            apply (cases p)
            subgoal for lp
              apply auto
              apply hypsubst_thin
              apply (intro exI conjI[rotated])
               apply (rule wbc_base)
               apply (rule exI[of _ "op1'"])
               apply (rule exI[of _ op2])
               apply (rule exI[of _ buf1])
               apply (rule exI[of _ buf1'])
               apply (rule exI[of _ buf1''])
               apply (rule exI[of _ buf2])
               apply (rule exI[of _ buf2'])
               apply (rule exI[of _ buf2''])
               apply (rule exI[of _ "BENQ lp x buf3"])
               apply (rule exI[of _ buf3'])
               apply (rule exI[of _ buf4])
               apply (rule exI[of _ buf4'])
               apply (intro conjI)
                apply force
               apply simp
              apply (rule transitive_closurep_trans'(6))
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_loop_op)
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_comp_op_R_Tau)
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_comp_op_L)
                apply simp_all
              apply simp
              done
            subgoal for lr
              apply hypsubst_thin
              apply (intro exI conjI[rotated])
               apply (rule wbc_base)
               apply (rule exI[of _ "op1'"])
               apply (rule exI[of _ op2])
               apply (rule exI[of _ buf1])
               apply (rule exI[of _ buf1'])
               apply (rule exI[of _ buf1''])
               apply (rule exI[of _ "BENQ lr x buf2"])
               apply (rule exI[of _ buf2'])
               apply (rule exI[of _ buf2''])
               apply (rule exI[of _ "buf3"])
               apply (rule exI[of _ buf3'])
               apply (rule exI[of _ buf4])
               apply (rule exI[of _ buf4'])
               apply (intro conjI)
                apply simp_all
              apply (rule step_tau_star_tau) 
              apply (auto 10 10 simp flip: case_sum_BENQ_R)
              done
            done
          subgoal for p op2'
            apply (cases p)
            subgoal for lp
              apply (auto dest!: step_id_op_Inp step_comp_op_cases; hypsubst_thin?)
              apply (intro exI conjI[rotated])
               apply (rule wbc_base)
               apply force
              apply (rule step_tau_star_tau) 
              apply (rule step_Tau_loop_op)
              apply (rule step_map_op[of Tau])
               apply simp_all
              apply (rule step_comp_op_R_Tau)
              apply (rule step_map_op[of Tau])
               apply simp_all
   (* Come back here! *)
              apply (rule step_Tau_comp_op_R[where buf="case_sum buf3 buf2" and p="Inl lp", simplified])
                 apply auto
              apply (metis case_sum_BENQ_L step_id_op_Read)
              done
            subgoal for rp
              apply (auto dest!: step_id_op_Inp step_comp_op_cases; hypsubst_thin?)
              subgoal for op2'
                apply (intro exI conjI[rotated])
                 apply (rule wbc_base)
                 apply force
                apply (rule step_tau_tau_tau_star_tau) 
                  apply (rule step_Tau_loop_op)
                  apply (rule step_map_op[of Tau])
                   apply simp_all
                  apply (rule step_comp_op_R_Tau)
                  apply (rule step_map_op[of Tau])
                   apply simp_all
                  apply (rule step_Tau_comp_op_R[where p="Inr rp"])
                     apply auto[4]
                 apply (rule step_Out_Inr_loop_op)
                 apply (rule step_map_op[of "Out (Inr (Inr rp)) _"])
                  apply simp_all
                 apply (rule step_comp_op_R_Out)
                 apply (rule step_map_op[of "Out (Inr (Inr rp)) _"])
                  apply simp_all
                 apply (rule step_comp_op_R_Out)
                 apply auto
                apply (rule subst[rotated])
                 apply (rule step_Inp_Inr_loop_op[where buf="case_sum undefined (BENQ rp (BHD rp buf2) buf2'')" and p=rp, simplified])
                 defer
                 apply simp_all
                apply (rule step_map_op[of "Inp (Inl (Inr rp)) _"])
                 apply simp_all
                apply (rule step_comp_op_L_Inp)
                apply (rule step_comp_op_R_Inp)
                 apply auto
                done
              subgoal for op2'
                apply (intro exI conjI[rotated])
                 apply (rule wbc_base)
                 apply force
                apply (rule step_tau_star_tau) 
                apply (rule step_Inp_Inr_loop_op[where buf="case_sum undefined buf2''" and p=rp, simplified])
                 apply simp_all
                apply (rule step_map_op[of "Inp (Inl (Inr rp)) _"])
                 apply simp_all
                apply (rule step_comp_op_L_Inp)
                apply (rule step_comp_op_R_Inp)
                 apply auto
                done
              subgoal for op2'
                apply (intro exI conjI[rotated])
                 apply (rule wbc_base)
                 apply force
                apply (rule step_tau_tau_star_tau) 
                 apply (rule step_Out_Inr_loop_op)
                 apply (rule step_map_op[of "Out (Inr (Inr rp)) _"])
                  apply simp_all
                 apply (rule step_comp_op_R_Out)
                 apply (rule step_map_op[of "Out (Inr (Inr rp)) _"])
                  apply simp_all
                 apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write)
                  apply blast
                 apply simp
                apply simp
                apply (rule subst[rotated])
                 apply (rule step_Inp_Inr_loop_op[where buf="case_sum undefined (BENQ rp (BHD rp buf2') buf2'')" and p=rp, simplified])
                 apply auto
                apply (rule step_map_op[of "Inp (Inl (Inr rp)) _"])
                 apply simp_all
                apply (rule step_comp_op_L_Inp)
                apply (rule step_comp_op_R_Inp)
                 apply auto
                done
              subgoal for op2'
                apply (intro exI conjI[rotated])
                 apply (rule wbc_base)
                 apply force
                apply (rule step_tau_star_tau) 
                apply (rule step_Inp_Inr_loop_op[where buf="case_sum undefined buf2''" and p=rp, simplified])
                 apply simp_all
                apply (rule step_map_op[of "Inp (Inl (Inr rp)) _"])
                 apply simp_all
                apply (rule step_comp_op_L_Inp)
                apply (rule step_comp_op_R_Inp)
                 apply auto
                done
              done
            done
          subgoal for op1'
            apply (drule step_map_op_inv)
            apply (auto; hypsubst_thin)
            apply (drule step_comp_op_cases)
            apply (auto; hypsubst_thin?)
            subgoal for p x op1'
              apply (drule step_id_op_Out)
               apply auto
              apply (cases p; auto; hypsubst_thin?)
              subgoal for lp
                apply (intro exI conjI[rotated])
                 apply (rule wbc_base)
                 apply fast
                apply (rule step_tau_star_tau)
                apply (rule step_Tau_loop_op)
                apply (rule step_map_op[of Tau])
                 apply simp_all
                apply (rule step_Tau_comp_op_L[where buf="case_sum buf4' ((buf1 >> buf1') >> buf1'')" and wire="Some" and x="BHD lp buf4" and q="Inl lp" and p="Inl lp", simplified])
                apply blast
                done
              subgoal for rp
                apply (intro exI conjI[rotated])
                 apply (rule wbc_base)
                 apply fast
                apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
                done
              done
            subgoal for p op1'
              apply (cases p; auto; hypsubst_thin?)
              subgoal for lp
                apply (intro exI conjI[rotated])
                 apply (rule wbc_base)
                 apply fast
                apply (rule step_tau_star_tau)
                apply (rule step_Tau_loop_op)
                apply (rule step_map_op[of Tau])
                 apply simp_all
                apply (rule step_Tau_comp_op_R[where buf="case_sum buf4' ((buf1 >> buf1') >> buf1'')" and wire="Some" and p="Inl lp", simplified])
                  apply simp_all
                apply (rule step_map_op[of "Inp (Inl (Inl lp)) _"])
                 apply simp_all
                apply auto
                done
              subgoal for rp
                apply (intro exI conjI[rotated])
                 apply (rule wbc_base)
                 apply fast
                apply (rule step_tau_star_tau)
                apply (rule step_Tau_loop_op)
                apply (rule step_map_op[of Tau])
                 apply simp_all
                using step_Tau_comp_op_R[where buf="case_sum buf4' ((buf1 >> buf1') >> buf1'')" and wire="Some" and x="BHD rp buf1''" and p="Inr rp", simplified]
                apply simp
                apply (drule meta_spec)+
                apply (drule meta_mp)
                 defer
                 apply (drule meta_mp)
                  apply (simp add: BULK_BENQ_def)
                 apply assumption
                apply (rule step_map_op[of "Inp (Inl (Inr rp)) _"])
                 apply simp_all
                apply auto
                done
              done
            subgoal for op1'
              apply (subst (asm) id_op_code)
              apply auto
              done
            subgoal 
              apply (intro exI conjI[rotated])
               apply (rule wbc_base)
               apply force+
              done
            done
          subgoal
            apply (drule step_comp_op_cases)
            apply (auto; hypsubst_thin?)
            subgoal for op1'
              apply (subst (asm) id_op_code)
              apply auto
              done
            subgoal for op2'
              apply (intro exI conjI[rotated])
               apply (rule wbc_base)
               apply force+
              done
            done
          done
        subgoal for op'' p
          apply (auto dest!: step_comp_op_cases step_map_op_inv step_id_op_Inp; hypsubst_thin?)
          apply (intro exI conjI[rotated])
           apply (rule wbc_base)
           apply force+
          done
        subgoal for op2'' p x
          apply (auto dest!: step_comp_op_cases step_map_op_inv step_loop_op split: sum.splits; hypsubst_thin?)
          apply (intro exI conjI[rotated])
           apply (rule wbc_base)
           apply force
          apply (rule step_tau_star_tau) 
          apply (rule step_Tau_loop_op)
          apply (rule step_map_op[of Tau])
           apply simp_all
          apply (metis BAPPEND_BENQ case_sum_BENQ_R step_Tau_comp_op_L step_comp_op_R_Out)
          done
        done
      done
    subgoal for io op1'
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_loop_op)
      apply auto
          apply hypsubst_thin
      subgoal for p op' x
        apply (auto dest!: step_id_op_Inp step_comp_op_cases step_map_op_inv step_loop_op split: sum.splits; hypsubst_thin?)
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
         apply force
        apply (rule step_wstep)
        apply (rule step_map_op[of "Inp (Inl _) _"])
         apply simp_all
        apply (rule step_Inp_Inl_loop_op)
        apply (rule step_map_op[of "Inp (Inl _) _"])
         apply simp_all
        apply (rule step_comp_op_L_Inp)
        apply (rule step_map_op[of "Inp (Inl _) _"])
         apply simp_all
        apply (rule step_comp_op_L_Inp)
        apply (metis case_sum_BENQ_L step_id_op_Read)
        done
      subgoal for p op' x
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        subgoal for io op'
          apply (drule step_comp_op_cases)
          apply auto
          apply (drule step_map_op_inv)
          apply (auto; hypsubst_thin?)
          apply (drule step_comp_op_cases)
          apply auto
          apply (drule step_id_op_Out)
           apply auto
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force
          apply (rule step_wstep)
          apply (rule step_map_op[of "Out (Inl _) _"])
           apply simp_all
          apply (rule step_Out_Inl_loop_op)
          apply (rule step_map_op[of "Out (Inr _) _"])
           apply simp_all
          apply (rule step_comp_op_R_Out)
          apply auto
          done
        done
      subgoal for op''
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        apply (drule step_comp_op_cases)
        apply auto
           apply (drule step_comp_op_cases)
           apply auto
        subgoal for x p op2'
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force+
          done
        subgoal for x p
          apply (drule step_id_op_Out)
           apply (auto; hypsubst_thin?)
          apply auto
          apply hypsubst_thin
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force
          apply (rule step_tau_star_tau) 
          apply (rule step_Tau_loop_op)
          apply (rule step_map_op[of Tau])
           apply simp_all
          apply (rule step_comp_op_L_Tau)
          apply (rule step_map_op[of Tau])
           apply simp_all
          apply (rule step_Tau_comp_op_L)
          apply (metis case_sum_BTL_L old.sum.simps(5) step_id_op_Write)
          done
        subgoal for p op2'
          apply (cases p)
          subgoal for lp
            apply auto
            apply (drule step_map_op_inv)
            apply (auto; hypsubst_thin?)
            apply (drule step_comp_op_cases)
            apply auto
            subgoal for op1'
              apply (intro exI conjI[rotated])
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force+
              done
            done
          subgoal for rp
            apply auto
               apply (drule step_map_op_inv)
               apply (auto; hypsubst_thin?)
               apply (drule step_comp_op_cases)
               apply auto
            subgoal for op1'
              apply (intro exI conjI[rotated])
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force
              apply (rule step_tau_tau_tau_star_tau) 
                apply (rule step_tau_loop_op_Inp_Inr_case_sum)
                 apply (rule step_map_op[of "Inp (Inl (Inr _)) _"])
                  apply simp_all
                apply (rule step_comp_op_L_Inp)
                apply (rule step_map_op[of "Inp (Inl (Inr _)) _"])
                 apply simp_all
                apply (rule step_comp_op_L_Inp)
                apply (rule step_id_op_Read)
               apply simp_all
               apply (rule step_Tau_loop_op)
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_comp_op_L_Tau)
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_comp_op_L)
                apply (rule step_id_op_Write[where p="Inr rp"])
                 apply blast
                apply simp_all
              apply (rule step_Tau_loop_op)
              apply (rule step_map_op[of Tau])
               apply simp_all
              apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op[of Tau])
               apply simp_all
              using step_Tau_comp_op_R
              apply (metis (no_types, lifting) BENQ_access BHD_BENQ_empty BTL_BENQ_empty snoc_eq_iff_butlast)
              done
            subgoal
              apply (drule step_map_op_inv)
              apply (auto; hypsubst_thin?)
              apply (drule step_comp_op_cases)
              apply auto
              apply (intro exI conjI[rotated])
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force+
              done
            subgoal
              apply (drule step_map_op_inv)
              apply (auto; hypsubst_thin?)
              apply (drule step_comp_op_cases)
              apply auto
              apply (intro exI conjI[rotated])
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force
              apply (rule step_tau_tau_star_tau) 
               apply (rule step_Tau_loop_op)
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_comp_op_L_Tau)
               apply (rule step_map_op[of Tau])
                apply simp_all
               apply (rule step_Tau_comp_op_L)
                apply (rule step_id_op_Write[where p="Inr rp"])
                 apply blast
                apply simp_all
              apply (rule step_Tau_loop_op)
              apply (rule step_map_op[of Tau])
               apply simp_all
              apply (rule step_comp_op_L_Tau)
              apply (rule step_map_op[of Tau])
               apply simp_all
              using step_Tau_comp_op_R
              apply (metis (no_types, lifting) BENQ_access BHD_BENQ_empty BTL_BENQ_empty snoc_eq_iff_butlast)
              done
            subgoal
              apply (drule step_map_op_inv)
              apply (auto; hypsubst_thin?)
              apply (drule step_comp_op_cases)
              apply auto
              apply (intro exI conjI[rotated])
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force+
              done
            done
          done
        subgoal for op2'
          apply (drule step_comp_op_cases)
          apply (auto; hypsubst_thin?)
          subgoal for op2'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply (subst (asm) id_op_code)
             apply auto
            done
          subgoal for op2'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply force+
            done
          done
        subgoal for op2'
          apply (drule step_map_op_inv)
          apply (auto; hypsubst_thin?)
          apply (drule step_comp_op_cases)
          apply auto
          subgoal for p x op1'
            apply (cases p)
            subgoal
              apply (intro exI conjI[rotated])
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force+
              done
            subgoal for rp
              apply (intro exI conjI[rotated])
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force
              apply hypsubst_thin
              apply (rule step_tau_star_tau) 
              apply (rule step_Tau_loop_op)
              apply (rule step_map_op[of Tau])
               apply simp_all
              using step_Tau_comp_op_L[of rp x "map_op projl projr (comp_op Some (case_sum buf4' buf1'') (id_op (case_sum buf4 buf1')) op1)" _ buf3 "(buf2 >> buf2') >> buf2''" "comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf3') op2"] 
              apply force
              done
            done
          subgoal for p op2'
            apply (drule step_id_op_Inp)
             apply auto
            apply (cases p)
            subgoal
              apply auto
              apply (intro exI conjI[rotated])
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force+
              done
            subgoal
              apply auto
              apply (intro exI conjI[rotated])
               apply (rule wbc_sym)
               apply (rule wbc_base)
               apply force+
              done
            done
          subgoal for op1'
            apply (intro exI conjI[rotated])
             apply (rule wbc_sym)
             apply (rule wbc_base)
             apply force+
            done
          subgoal
            apply (subst (asm) id_op_code)
            apply auto
            done
          done
        done
      subgoal for op p
        apply hypsubst_thin
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        apply (drule step_comp_op_cases)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for op2'
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force
          apply (rule transitive_closurep_trans'(6))
           apply (rule step_map_op[of Tau])
            apply simp_all
           apply (rule step_Tau_loop_op)
           apply (rule step_map_op[of Tau])
            apply simp_all
           apply (rule step_Tau_comp_op_R)
             apply (rule step_comp_op_R_Inp)
              apply assumption
             apply simp_all
          apply (simp add: BULK_BENQ_def)
          done
        done
      subgoal for op p x
        apply hypsubst_thin
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        apply (drule step_comp_op_cases)
        apply auto
        apply (drule step_map_op_inv)
        apply (auto; hypsubst_thin?)
        apply (drule step_comp_op_cases)
        apply auto
        apply (drule step_id_op_Out)
         apply (auto; hypsubst_thin?)
        apply auto
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
         apply force
        apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
        done
      done
    done
  done


lemma loop_op_commutes_inner_scomp_op:
  "(\<stileturn>op1 \<bullet> (\<I> \<parallel> op2))\<up> \<approx> ((\<I> \<parallel> op2) \<bullet> op1\<turnstile>)\<up>"
  unfolding feedback_op_def scomp_op_def pcomp_op_def
  using loop_op_commutes_inner_scomp_op_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"  "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" _ "\<lambda> _. []"   ] by force

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

section \<open>Axiom F2: Transpose looped is identity\<close>
lemma transp_op_loop_id_gen:
  "map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some \<circ> Inr)) (case_sum undefined buf') (transp_op (case_sum buf buf''))) \<approx> id_op (buf >> buf' >> buf'')"
  apply (coinduction arbitrary: buf buf' buf'' rule: wbisim_coinduct_upto)
  subgoal for buf buf' buf''
    unfolding wsim_def
    apply auto
    subgoal for io op'
      apply (drule step_map_op_inv)
      apply (auto; hypsubst_thin?)
      apply (drule step_loop_op)
      apply (auto; hypsubst_thin?)
      subgoal for p op'' x
        apply (drule step_transp_op_Inp)
         apply auto
        apply hypsubst_thin
        apply (intro exI conjI[rotated])
         apply (rule wbc_base)
         apply force
        apply (metis BAPPEND_BENQ step_id_op_Read step_wstep)
        done
      subgoal for p op'' x
        apply (drule step_transp_op_Out)
          apply auto
        apply hypsubst_thin
        apply (intro exI conjI[rotated])
         apply (rule wbc_base)
         apply force
        using BULK_BENQ_empty apply fastforce
        done
      subgoal
        by (meson no_step_transp_op_Tau)
      subgoal for op' p
        apply (drule step_transp_op_Inp)
         apply auto
        apply hypsubst_thin
        apply (intro exI conjI[rotated])
         apply (rule wbc_base)
         apply force
        apply (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc rtranclp_intros_1')
        done
      subgoal for op' p x
        apply (drule step_transp_op_Out)
          apply auto
        apply hypsubst_thin
        apply (intro exI conjI[rotated])
         apply (rule wbc_base)
         apply force+
        done
      done
    subgoal for op op1'
      apply (erule step_id_op_cases)
      subgoal for p x
        apply (auto; hypsubst_thin?)
        apply (intro exI conjI[rotated])
         apply (rule wbc_sym)
         apply (rule wbc_base)
         apply force
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_Inp_Inl_loop_op)
         apply simp_all
        apply (metis case_sum_BENQ_L step_transp_op_Read)
        done
      subgoal for p x
        apply (auto; hypsubst_thin?)
        subgoal 
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force
          apply (rule step_tau_step_tau_step_io_wstep)
            apply (rule step_map_op[of Tau])
             apply simp_all
            apply (rule step_Out_Inr_loop_op[where p=p])
            apply (rule step_transp_op_Write[where p="Inl p"])
               apply simp_all
           apply (rule step_map_op[of Tau])
            apply simp_all
           apply (rule step_Inp_Inr_loop_op[where p=p])
            apply simp_all
           apply (rule step_transp_op_Read)
          apply simp
          apply (rule step_map_op[of "Out (Inl _) _"])
           apply simp_all
          apply (metis (mono_tags, lifting) BENQ_access BHD_BENQ_empty BTL_BENQ_empty case_sum_BTL_R not_Cons_self2 self_append_conv2 step_Out_Inl_loop_op step_transp_op_Write sum.case(2))
          done
        subgoal
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force
          apply (rule step_wstep)
          apply (rule step_map_op[of "Out (Inl _) _"])
           apply simp_all
          apply (metis case_sum_BTL_R old.sum.simps(6) step_Out_Inl_loop_op step_transp_op_Write)
          done
        subgoal
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force
          apply (rule step_tau_step_io_wstep)
           apply (rule step_map_op[of Tau])
            apply simp_all
           apply (rule step_Inp_Inr_loop_op[where p=p])
            apply simp_all
           apply (rule step_transp_op_Read)
          apply simp
          apply (rule step_map_op[of "Out (Inl _) _"])
           apply simp_all
          apply (smt (verit, ccfv_threshold) BENQ_access BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_R not_Cons_self2 old.sum.simps(6) self_append_conv2 step_Out_Inl_loop_op step_transp_op_Write)
          done
        subgoal
          apply (intro exI conjI[rotated])
           apply (rule wbc_sym)
           apply (rule wbc_base)
           apply force
          apply (rule step_wstep)
          apply (rule step_map_op[of "Out (Inl _) _"])
           apply simp_all
          apply (metis case_sum_BTL_R old.sum.simps(6) step_Out_Inl_loop_op step_transp_op_Write)
          done
        done
      done
    done
  done

lemma transp_op_loop_id: \<open>\<X>\<up> \<approx> \<I>\<close>
  unfolding feedback_op_def 
  using transp_op_loop_id_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] by auto

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
  sorry


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
  sorry

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