section \<open>The BNA operators\<close>
  \<comment> \<open>The basic operators - except compositions, loop and fair merge- from the BNA book "Network Algebra for Synchronous and Asynchronous Dataflow" (https://staff.fnwi.uva.nl/c.a.middelburg/papers/P9508.pdf) \<close>
  \<comment> \<open>Here we list most of the axioms from Table 1, and Table 4\<close>
theory BNA_Operators

imports
  Operator
  Composition_Choices
begin

section \<open>spin_op/end_op/silent_op/I_0\<close>
  \<comment> \<open>spin_op/end_op is I_0 in the BNA book\<close>
  \<comment> \<open>In the transition system this is a dead-lock\<close>

corec spin_op :: "('a, 'b, 'd) op" ("\<otimes>") where
  "spin_op = Choice (cimage (\<lambda> _. spin_op) (csingle ()))"

primcorec silent_op where
  "silent_op = Silent silent_op"

abbreviation "ARead i f op \<equiv> Choice (cimage (\<lambda> x. if x then op else Read i f) (cinsert True (csingle False)))"
lemma ARead_simp[simp]: "ARead i f op = Choice ({| op, Read i f |})"
  by simp

lemma finished_spin_op[simp]:
  "finished \<otimes>"
  apply coinduction
  apply (subst spin_op.code)
  apply auto
  done

lemma finished_end_op[simp]:
  "finished \<oslash>"
  by coinduction blast

lemma step_end_op[simp]: "step l \<oslash> t' = False"
  by auto

lemma spin_op_finished[simp]:
  "finished \<otimes>"
  apply coinduction
  apply (subst spin_op.code)
  apply (auto 0 0 simp add:  sup_cset.rep_eq cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq; hypsubst_thin?)
  done

lemma choices_spin_op[simp]:
  "choices \<otimes> = {||}"
  by (simp add: finished_choices_empty)

lemma traces_end_op[simp]:
  "traces \<oslash> = {LNil}"
  by (auto simp: traces_def intro: finished.intros traced.intros step.intros elim: traced.cases)

lemma step_spin_op_no_label:
  "step io \<otimes> op \<Longrightarrow> False"
  using spin_op_finished step_not_finished by blast

lemma spin_op_parallel:
  "\<otimes> \<parallel> \<otimes> ~ \<otimes> "
  apply (coinduction rule: bisim_coinduct_upto)
  apply safe
  subgoal
    unfolding pcomp_op_def sim_def
    apply auto
    apply (subst (asm) comp_op_code)
    apply auto
    done
  subgoal
    unfolding pcomp_op_def sim_def
    apply auto
    using step_spin_op_no_label apply blast
    done
  done

lemma spin_op_silent_op:
  "\<otimes> \<approx> silent_op"
  apply (coinduction rule: wbisim_coinduct_upto)
  unfolding wsim_def
  apply auto
  subgoal
    using step_spin_op_no_label by blast
  subgoal
    apply (subst (asm) silent_op.code)
    apply auto
    apply hypsubst_thin
    by (metis (mono_tags, lifting) rtranclp.rtrancl_refl wbc_base wbc_sym)
  done

\<comment> \<open>TODO: both are delta\<close>
lemma "\<otimes> ~ \<oslash>"
  oops

subsection \<open>Axiom: B2\<close>
\<comment> \<open>Neutral element parallel composition\<close>

section \<open>id_op/\<I>/I_m\<close>
    \<comment> \<open>id_op is I_m in the BNA paper\<close>

datatype (discs_sels) ('m, 'd) id_op_aux =
  id_Read_aux "'m" "'d \<Rightarrow> ('m \<Rightarrow> 'd buf)"
  | id_Write_aux "('m \<Rightarrow> 'd buf)" "'m" 'd 
  | id_Silent_aux "('m \<Rightarrow> 'd buf)"

abbreviation eval_id_op_aux where
  "eval_id_op_aux c aux \<equiv> (case aux of
    id_Read_aux p f \<Rightarrow> Read p (\<lambda>y. let buf = f y in c buf)
  | id_Write_aux buf q x \<Rightarrow> (Write (c buf) q x))"

corec id_op :: "_ \<Rightarrow> ('m :: countable, 'm, 'd) op" where
  "id_op buf = Choice (cimage (eval_id_op_aux id_op) (cUn 
    (cimage (\<lambda> p. id_Read_aux p (\<lambda> x. BENQ p x buf)) (cUNIV :: 'm cset)) 
    (cimage (\<lambda> p. id_Write_aux (BTL p buf) p (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (cUNIV :: 'm cset)))))"

abbreviation id_empty_op ("\<I>") where
  "\<I> \<equiv> id_op (\<lambda> _. [])"

lemma id_op_code:
  "id_op buf = Choice (cUn 
    (cimage (\<lambda> p. Read p ((\<lambda> x. id_op (BENQ p x buf)))) (cUNIV :: 'm cset))
    (cimage (\<lambda> p. Write (id_op (BTL p buf)) p  (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (cUNIV :: ('m :: countable) cset))))"
  apply (subst id_op.code)
  apply (unfold cimage_cUn cimage_cinsert op.inject)
  apply simp
  apply (rule arg_cong2[where f = cUn])
   apply (auto simp add: cset.map_comp o_def cimage_cUn intro!: arg_cong2[where f = cUn] cimage_cong
      split: id_op_aux.splits op.splits option.splits)
  done

subsection \<open>Some basic properties id_op\<close>
lemma step_id_op_Inp:
  "step io (id_op buf) op' \<Longrightarrow>
   io = Inp p x \<Longrightarrow>
   op' = id_op (BENQ p x buf)"
  apply (induct io "id_op buf" op' arbitrary: buf rule: step.induct)
     apply simp_all
   apply (subst (asm) id_op_code)
   apply simp
  apply (subst (asm) (3) id_op_code)
  apply auto
  done

lemma step_id_op_Out:
  "step io (id_op buf) op' \<Longrightarrow>
   io = Out p x \<Longrightarrow>
   op' = id_op (BTL p buf) \<and> BHD p buf = x \<and> buf p \<noteq> []"
  apply (induct io "id_op buf" op' arbitrary: buf rule: step.induct)
     apply simp_all
   apply (subst (asm) id_op_code)
   apply simp
  apply (subst (asm) (3) id_op_code)
  apply auto
  done

lemma choices_id_op[simp]:
  "choices (id_op buf) = cUn (cUnion (cimage choices (cimage (\<lambda>p. Read p (\<lambda>x. id_op (buf(p := bulk_benq [x] (buf p))))) cUNIV)))
       (cUnion (cimage choices (cimage (\<lambda>p. Write (id_op (buf(p := btl (buf p)))) p (BHD p buf)) (cfilter (\<lambda>p. buf p \<noteq> []) cUNIV))))"
  apply (subst id_op_code)
  apply simp
  done



subsection \<open>User defined operators\<close>
abbreviation buffered ("\<stileturn> _ \<turnstile>" [150]151) where
  "\<stileturn>op\<turnstile> \<equiv> \<I> \<bullet> op \<bullet> \<I>"


subsection \<open>Compositional properties id_op\<close>
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

subsection \<open>Axiom: B4\<close>
\<comment> \<open>Neutral element sequential composition\<close>
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

subsection \<open>Axiom: B6\<close>
  \<comment> \<open>TODO\<close>
lemma pcomp_op_id_id:
  "\<I> \<parallel> \<I> ~ \<I>"
  oops

subsection \<open>Axiom: F1\<close>
  \<comment> \<open>TODO\<close>


  section \<open>dummy_source_op\<close>                                     
abbreviation dummy_source_op ("\<exclamdown>") where
  "\<exclamdown> \<equiv> \<oslash> \<bullet> \<I>"

subsection \<open>Axiom: A12\<close>
lemma dummy_source_op_end_op:
  \<comment> \<open>TODO\<close>
  "\<exclamdown> ~ \<oslash>"
  oops
  \<comment> \<open>TODO\<close>
lemma dummy_source_op_spin_op:
  "\<exclamdown> = \<otimes>"
  oops

  subsection \<open>Axiom: A13\<close>
  \<comment> \<open>TODO\<close>
lemma pcomp_opdummy_source:
  "\<exclamdown> \<parallel> \<exclamdown> ~ \<exclamdown>"
  oops

  section \<open>sink_op\<close>                                     
corec drain_op :: "('m :: countable, 'o, 'd) op" where
  "drain_op = Choice ((cimage (\<lambda> p. Read p (\<lambda> x. drain_op)) (cUNIV :: 'm cset)))"

abbreviation "sink_gen_op buf \<equiv> id_op (\<lambda> _. []) \<bullet> drain_op"
abbreviation sink_op ("!") where
  "! \<equiv> \<I> \<bullet> drain_op"
abbreviation "sink_0_op \<equiv> \<oslash>"

subsection \<open>Axiom: A16\<close>
lemma
  "sink_0_op = \<oslash>"
  by simp

subsection \<open>Axiom: A9\<close>
  \<comment> \<open>TODO\<close>
lemma
  "\<exclamdown> \<bullet> sink_0_op ~ \<oslash>"
  oops
  \<comment> \<open>TODO\<close>
lemma
  "\<exclamdown> \<bullet> ! = \<otimes>"
  oops
subsection \<open>Axiom: A17\<close>
  \<comment> \<open>TODO\<close>

section \<open>transp_op - transposition operator\<close>
  \<comment> \<open>TODO: define the operator + write and prove axioms: B7, B8, B9, B10, F2 \<close>

datatype (discs_sels) ('m, 'n, 'd) transp_op_aux =
  transp_Read_aux "'m + 'n" "'d \<Rightarrow> ('m + 'n \<Rightarrow> 'd buf)"
  | transp_Write_aux "('m + 'n \<Rightarrow> 'd buf)" "'n + 'm" 'd 

abbreviation eval_transp_op_aux where
  "eval_transp_op_aux c aux \<equiv> (case aux of
    transp_Read_aux p f \<Rightarrow> Read p (\<lambda>y. let buf = f y in c buf)
  | transp_Write_aux buf q x \<Rightarrow> (Write (c buf) q x))"

corec transp_op :: "_ \<Rightarrow> ('m :: countable + 'n :: countable, 'n + 'm, 'd) op" where
  "transp_op buf = Choice (cimage (eval_transp_op_aux transp_op) (cUn 
    (cimage (\<lambda> p. transp_Read_aux p (\<lambda> x. BENQ p x buf)) (cUNIV :: ('m + 'n) cset)) 
    (cimage (\<lambda> p. transp_Write_aux (BTL p buf) (case_sum Inr Inl p) (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (cUNIV :: ('m + 'n) cset)))))"

lemma transp_op_code:
   "transp_op buf = Choice (cUn 
    (cimage (\<lambda> p. Read p (\<lambda> x. transp_op (BENQ p x buf))) (cUNIV :: ('m :: countable + 'n :: countable) cset)) 
    (cimage (\<lambda> p. Write (transp_op (BTL p buf)) (case_sum Inr Inl p) (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (cUNIV :: ('m + 'n) cset))))"
  apply (subst transp_op.code)
  apply (unfold cimage_cUn cimage_cinsert op.inject)
  apply simp
  apply (rule arg_cong2[where f = cUn])
   apply (auto simp add: cset.map_comp o_def cimage_cUn intro!: arg_cong2[where f = cUn] cimage_cong
      split: op.splits option.splits)
  done

section \<open>split_op - nondeterministic split operator\<close>
  \<comment> \<open>TODO: define the operator + write and prove axioms (Table 4): A6, A8, A18, A19, F4 \<close>
datatype (discs_sels) ('m) split_op_aux =
  split_Read_aux "'m"

abbreviation eval_split_op_aux where
  "eval_split_op_aux c aux \<equiv> (case aux of
    split_Read_aux p \<Rightarrow> Read p (\<lambda>y. choice2 (Write c (Inl p) y) (Write c (Inr p) y)))"

corec split_op :: "('m :: countable, 'm + 'm, 'a) op" where
  "split_op = Choice (cimage (eval_split_op_aux split_op) 
   (cimage (\<lambda> p. split_Read_aux p) (cUNIV :: 'm cset)))"

lemma split_op_code:
  "split_op = Choice (cimage (\<lambda> p. Read p (\<lambda> y. Choice {|Write split_op (Inl p) y, Write split_op (Inr p) y|})) (cUNIV :: 'm :: countable cset))"
  apply (subst split_op.code)
   apply (auto simp add: cset.map_comp o_def cimage_cUn intro!: arg_cong2[where f = cUn] cimage_cong
      split: op.splits option.splits)
  done

subsection \<open>Axiom: A6\<close>
lemma
  "split_op \<bullet> (transp_op buf) \<approx> map_op id (case_sum Inr Inl) split_op"
  oops

section \<open>merge_op - nondeterministic merge operator\<close>
  \<comment> \<open>TODO: define the operator + write and prove axioms (Table 4): A1, A2, A3, A4, A14, A15, F3 \<close>
datatype (discs_sels) ('m) merge_op_aux =
  merge_Read_aux "'m"

abbreviation eval_merge_op_aux where
  "eval_merge_op_aux c aux \<equiv> (case aux of
    merge_Read_aux p \<Rightarrow> choice2 (Read (Inl p) (\<lambda>y. Write c p y)) (Read (Inr p) (\<lambda>y. Write c p y)))"

corec merge_op :: "('m + 'm :: countable, 'm, 'a) op" where
  "merge_op = Choice (cimage (eval_merge_op_aux merge_op) 
   (cimage (\<lambda> p. merge_Read_aux p) (cUNIV :: 'm cset)))"

lemma merge_op_code:
  "merge_op = Choice (cimage (\<lambda> p. Choice {|Read (Inl p) (\<lambda>y. Write merge_op p y), Read (Inr p) (\<lambda>y. Write merge_op p y)|}) (cUNIV :: 'm :: countable cset))"
  apply (subst merge_op.code)
   apply (auto simp add: cset.map_comp o_def cimage_cUn intro!: arg_cong2[where f = cUn] cimage_cong
      split: op.splits option.splits)
  done

section \<open>acopy_op - async copy operator\<close>
  \<comment> \<open>TODO: define the operator + write and prove axioms (Table 3): A6, A8, A18, A19, F4 \<close>
datatype (discs_sels) ('m) acopy_op_aux =
  acopy_Read_aux "'m"

abbreviation eval_acopy_op_aux where
  "eval_acopy_op_aux c aux \<equiv> (case aux of
    acopy_Read_aux p \<Rightarrow> Read p (\<lambda>y. choice2 (Write (Write c (Inr p) y) (Inl p) y) (Write (Write c (Inl p) y) (Inr p) y)))"

corec acopy_op :: "('m :: countable, 'm + 'm, 'a) op" where
  "acopy_op = Choice (cimage (eval_acopy_op_aux acopy_op) 
   (cimage (\<lambda> p. acopy_Read_aux p) (cUNIV :: 'm cset)))"

lemma acopy_op_code:
  "acopy_op = Choice (cimage (\<lambda> p. Read p (\<lambda> y. Choice {|Write (Write acopy_op (Inr p) y) (Inl p) y, Write (Write acopy_op (Inl p) y) (Inr p) y|})) (cUNIV :: 'm :: countable cset))"
  apply (subst acopy_op.code)
   apply (auto simp add: cset.map_comp o_def cimage_cUn intro!: arg_cong2[where f = cUn] cimage_cong
      split: op.splits option.splits)
  done

section \<open>aeq_op - async equality operator\<close>
  \<comment> \<open>TODO: define the operator + write and prove axioms (Table 3): A1, A2, A3, A4, A14, A15, F3 \<close>
datatype (discs_sels) ('m) aeq_op_aux =
  aeq_Read_aux "'m"

abbreviation eval_aeq_op_aux where
  "eval_aeq_op_aux c aux \<equiv> (case aux of
    aeq_Read_aux p \<Rightarrow> choice2 (Read (Inl p) ((\<lambda> y. Read (Inr p) (\<lambda>x. if x = y then Write c p x else Silent c)))) (Read (Inr p) ((\<lambda> y. Read (Inl p) (\<lambda>x. if x = y then Write c p x else Silent c)))))"

corec aeq_op :: "('m + 'm :: countable, 'm, 'a) op" where
  "aeq_op = Choice (cimage (eval_aeq_op_aux aeq_op) 
   (cimage (\<lambda> p. aeq_Read_aux p) (cUNIV :: 'm cset)))"

lemma aeq_op_code:
  "aeq_op = Choice (cimage (\<lambda> p. Choice {|Read (Inl p) ((\<lambda> y. Read (Inr p) (\<lambda>x. if x = y then Write aeq_op p x else Silent aeq_op))), Read (Inr p) ((\<lambda> y. Read (Inl p) (\<lambda>x. if x = y then Write aeq_op p x else Silent aeq_op)))|}) (cUNIV :: 'm :: countable cset))"
  apply (subst aeq_op.code)
   apply (auto simp add: cset.map_comp o_def cimage_cUn intro!: cimage_cong
      split: op.splits option.splits if_splits)
  done

(* 
abbreviation "write op p x \<equiv> Write op p (Observed x)"
abbreviation "eob op p \<equiv> Write op p EOB"
abbreviation "eos op p \<equiv> Write op p EOS"

definition bna_feedback :: "('m + 'l, 'n + 'l, 'd) op \<Rightarrow> ('m, 'n, 'd) op" where
  "bna_feedback op = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (Some o Inr)) (\<lambda>_. BEmpty) op)"

corec (friend) cp_list where "cp_list \<pi> ps op = (case ps of p # ps \<Rightarrow> Read p (case_observation (Write (cp_list \<pi> ps op) (\<pi> p)) (cp_list \<pi> ps op) end_op) | [] \<Rightarrow> 
  (case op of end_op \<Rightarrow> end_op | Write op p x \<Rightarrow> Write op p x | Read p f \<Rightarrow> Read p f))"

lemma cp_list_code: "cp_list \<pi> ps op = (case ps of p # ps \<Rightarrow> Read p (case_observation (Write (cp_list \<pi> ps op) (\<pi> p)) (cp_list \<pi> ps op) end_op) | [] \<Rightarrow> op)"
  by (subst cp_list.code) (auto split: list.splits op.splits)

corec bna_identity :: "('m :: enum, 'm, 'd) op" where
  "bna_identity = (case Enum.enum :: 'm list of (p # ps) \<Rightarrow> Read p (case_observation (Write (cp_list id ps bna_identity) p) (cp_list id ps bna_identity) end_op))"

corec bna_transpose :: "('m :: enum + 'n :: enum, 'n + 'm, 'd) op" where
  "bna_transpose = (case Enum.enum :: 'm list of (p # ps) \<Rightarrow>
  Read (Inl p) (case_observation (Write (cp_list (case_sum Inr Inl) (map Inl ps @ map Inr Enum.enum) bna_transpose) (Inr p)) bna_transpose end_op))"

abbreviation "bna_parcomp \<equiv> pcomp_op"
abbreviation "bna_seqcomp \<equiv> scomp_op"


abbreviation sum_assoc :: \<open>('a + 'b) + 'c \<Rightarrow> 'a + ('b + 'c)\<close> where
  \<open>sum_assoc \<equiv> case_sum (case_sum Inl (Inr o Inl)) (Inr o Inr)\<close>

lemma
  assumes \<open>history (bna_parcomp a (bna_parcomp b c)) lin lout\<close> \<open>history (bna_parcomp (bna_parcomp a b) c) (lin o sum_assoc) rout\<close>
  shows \<open>lout (sum_assoc p) = rout p\<close>
  using assms unfolding history_def traced_pcomp_op'
  apply auto
  oops
  *)
end
