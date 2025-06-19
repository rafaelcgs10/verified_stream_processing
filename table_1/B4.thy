theory B4

imports
  "../BNA_Operators"
   B3
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

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
              apply (simp add: c\<UU>.rep_eq)
              apply (intro conjI)
               apply (rule disjI2)
               apply (intro conjI exI)
                 apply (erule \<UU>_I)
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

lemma B4_1:
  "op\<turnstile> \<bullet> \<I> \<approx> op\<turnstile>"
  using bisim_wbisim B3.B3 scomp_op_id_id wbisim_refl wbisim_scomp_op_cong wbisim_trans by blast

lemma B4_2:
  "\<I> \<bullet> \<stileturn>op \<approx> \<stileturn>op"
  by (smt (verit, best) bisim_wbisim B3.B3 scomp_op_id_id wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans)

end