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

          apply (rule cinsertI1)

          find_theorems wstep

end
          apply (rule step_map_op[where f=projl and g=projr and io="Inp (Inl p) x", simplified])
           apply (subst comp_op_code)
           apply simp
           apply (rule SC)
            apply (simp add: Set.filter_def)
            apply (rule disjI2)
            apply simp
            apply (rule disjI1)
            apply (rule image_eqI)
             apply (rule refl)
            apply simp
            apply (rule disjI1)
            apply (intro exI)
            apply (rule refl)
           apply simp_all
          apply (rule SR)
          done
        subgoal
          apply (rule bc_sym)
          apply (rule bc_base)
          apply (intro conjI exI)
           apply simp_all
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
            apply (rule step_map_op[where f=projl and g=projr and io="Out (Inr p) x", simplified])
             apply (subst comp_op_code)
             apply simp
             apply (rule SC)
              apply (simp add: Set.filter_def)
              apply (rule disjI2)
              apply simp
              apply (rule disjI2)
              apply (rule image_eqI)
               apply (rule refl)
              apply (simp add: cUNIV.rep_eq)
              apply (intro conjI)
               apply (rule disjI2)
               apply (rule disjI2)
               apply (intro conjI exI)
                apply assumption
               apply (rule refl)
              apply (auto simp add: step.intros(2))
            done
          subgoal
            apply (rule bc_sym)
            apply (rule bc_base)
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
            apply (rule step_map_op[where f=projl and g=projr and io="Out (Inr p) x", simplified])
            apply (subst comp_op_code)
            apply simp
            apply (rule SC)
             apply simp
             apply (rule disjI2)+
             apply (rule image_eqI)
              apply (rule refl)
             apply (simp add: Set.filter_def cUNIV.rep_eq)
              apply (intro conjI)
               apply (rule disjI2)
               apply (rule disjI1)
            apply (intro conjI exI)
               apply simp_all
             apply force
            apply simp *)

\<comment> \<open>TODO: id o id is id\<close>
subsubsection \<open>Axiom: B4\<close>
lemma scomp_op_id_id:
  "\<I> \<bullet> \<I> \<approx> \<I>"
  unfolding scomp_op_def
 (*  using id_id_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] apply simp
  done *)
  oops

subsection \<open>Axiom: B6\<close>
subsubsection \<open>Auxiliary lemmas\<close>
subsubsection \<open>Axiom: B6\<close>
lemma pcomp_op_id_id:
  "\<I> \<parallel> \<I> ~ \<I>"
  oops

section \<open>dummy_source_op\<close>                                     
abbreviation dummy_source_op ("\<exclamdown>") where
  "\<exclamdown> \<equiv> \<oslash> \<bullet> \<I>"

subsection \<open>Axiom: A12\<close>
lemma dummy_source_op_end_op:
 "\<exclamdown> ~ \<oslash>"
  oops
lemma dummy_source_op_spin_op:
 "\<exclamdown> = \<otimes>"
  oops

subsection \<open>Axiom: A13\<close>
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
lemma
  "\<exclamdown> \<bullet> sink_0_op ~ \<oslash>"
  oops
lemma
  "\<exclamdown> \<bullet> ! = \<otimes>"
  oops


end
corec sink_op :: "('a, 'b, 'd) op" where
  "sink_op = Read 1 (\<lambda>_. sink_op)"

lemma choices_sink_op[simp]:
  "choices sink_op = {|Read 1 (\<lambda> _. sink_op)|}"
  unfolding choices_def
  apply safe
  subgoal premises prems for x n
    using prems(2) apply -
    apply (induct n)
     apply (subst (asm) sink_op.code)
     apply simp 
    apply (subst (asm) (3) sink_op.code)
    apply simp
    done
  subgoal for x
    apply auto
    apply (metis UNIV_witness natcUNIV.rep_eq choices_at.simps(1) cin.rep_eq cinsertI1 sink_op.code)
    done
  done

section \<open>transp_op - transposition operator\<close>
\<comment> \<open>TODO: define the operator + write and prove axioms B7, B8, B9, B10, R1, F2, \<close>

section \<open>User defined operators\<close>
abbreviation buffered ("\<stileturn> _ \<turnstile>" [150]151) where
  "\<stileturn>op\<turnstile> \<equiv> \<I> \<bullet> op \<bullet> \<I>"

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
