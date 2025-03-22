theory A1

imports
  "../BNA_Operators"
  "HOL-ex.Sketch_and_Explore"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A1: Merge commutes with identity\<close>


(* lemma                                                  
  assumes \<open>map_op projl projr (comp_op Some (case_sum (\<lambda> (1::1) . [1]) A2'')
    (merge_op (case_sum A1 A1') \<parallel> id_op A1'')
    (merge_op (case_sum A3 A3'')))
  \<approx> map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2')
      (id_op B1 \<parallel> merge_op (case_sum B1' B1''))
      (merge_op (case_sum B3 B3'))))\<close>
  shows False


end
 *)

lemma wfinished_map_op[simp]:
  "wfinished (map_op f g op) \<longleftrightarrow> wfinished op"
  apply (rule iffI)
  subgoal
    apply (coinduction arbitrary: op)
    subgoal for op
      apply (erule wfinished.cases)
       apply auto
       apply (metis (no_types, lifting) cimage.rep_eq image_eqI is_Choice_def op.map_disc_iff(3) op.map_sel(6) op.sel(6))
      apply (metis is_Silent_def op.map_disc_iff(4) op.map_sel(7) op.sel(7))
      done
    done
  subgoal
    apply (coinduction arbitrary: op)
    subgoal for op
      apply (erule wfinished.cases)
       apply auto
      done
    done
  done

lemma wstep_Silent_undo:
  "wstep io (Silent op) op' \<Longrightarrow>
   io \<noteq> Tau \<Longrightarrow>
   wstep io op op'"
  unfolding wstep_def
  apply (erule relcomppE converse_rtranclpE)+
  subgoal for op'' op'''
    apply hypsubst_thin
    apply (cases io)
      apply auto
    done
  subgoal for op' op'' op'''
    apply (cases io)
      apply auto
    done
  subgoal for op' op'' op'''
    apply (cases io)
      apply auto
    done
  done

lemma wstep_Choice_undo:
  "wstep io (Choice ops) op' \<Longrightarrow>
   io \<noteq> Tau \<Longrightarrow>
   op |\<in>| ops \<Longrightarrow>
   wstep io op op'"
  oops

lemma wstep_Tau_busy_wtraced:
  "(step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow>
   \<not> wfinished op' \<Longrightarrow>
   wtraced op' lxs \<Longrightarrow>
   wtraced op lxs"
  apply (induct op rule: converse_rtranclp_induct)
  apply (auto intro: )
  apply (smt (verit, best) rtranclp_induct step_Tau_wfinished wstep_trans_tau_1 wtraced.simps)
  done


lemma step_Tau_busy_wtraced:
  "step io op op' \<Longrightarrow>
   io = Tau \<Longrightarrow>
   \<not> wfinished op' \<Longrightarrow>
   wtraced op' lxs \<Longrightarrow>
   wtraced op lxs"
  apply (induction io op op' arbitrary: pred: step)
     apply simp_all
  subgoal for op
    apply (coinduction arbitrary: op lxs rule: wtraced.coinduct)
    subgoal for op lxs
      apply (erule wtraced.cases)
       apply simp_all
      apply blast
      done
    done
  subgoal for op ops io op'
    apply hypsubst_thin
    subgoal premises prems
      using prems apply -
    apply (coinduction arbitrary: op lxs rule: wtraced.coinduct)
      apply (erule wtraced.cases)
       apply simp_all
      subgoal for op lxs opa
        apply hypsubst_thin
        apply (auto simp add: wfinished_no_wstep)
        done
      subgoal for op lxs vio opa op' lxsa
        apply hypsubst_thin
        by (meson WSC cin.rep_eq)
      done
    done
  done

lemma short_bar:
  "step Tau op op1 \<Longrightarrow>
   op = map_op projl projr (comp_op Some X (merge_op A \<parallel> id_op C) (merge_op K)) \<Longrightarrow>
   \<exists> X A C K. op1 = map_op projl projr (comp_op Some X (merge_op A \<parallel> id_op C) (merge_op K))"
  apply hypsubst_thin
  unfolding pcomp_op_def
  apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; hypsubst_thin)
  done

lemma longer_bar:
  "(step Tau)\<^sup>*\<^sup>* op op1 \<Longrightarrow>
   op = map_op projl projr (comp_op Some X (merge_op A \<parallel> id_op C) (merge_op K)) \<Longrightarrow>
   \<exists> X A C K. op1 = map_op projl projr (comp_op Some X (merge_op A \<parallel> id_op C) (merge_op K))"
  apply (induct op arbitrary: X A C K rule: converse_rtranclp_induct)
  using short_bar apply blast
  using short_bar apply meson
  done

lemma bar:
  "(step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<parallel> id_op C) \<V>)) op1 \<Longrightarrow>
   \<exists> A B C D E. op1 = map_op projl projr (comp_op Some D (merge_op (case_sum A B) \<parallel> id_op C) (merge_op E))"
  apply (drule longer_bar)
   apply simp
  apply (metis surjective_sum)
  done
  
lemma wstep_inputs_not_in_defaults:
  "wstep (Inp p x) op op' \<Longrightarrow>
   inputs op \<inter> defaults = {} \<Longrightarrow>
   p \<notin> defaults"
  by (simp add: disjoint_iff wstep_Inp)

lemma reads_not_wfinished:
  "sub_op (Read p f) op n \<Longrightarrow> \<not> wfinished op"
proof (induct p op arbitrary: rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case 
    by (metis op.simps(10) op.simps(8) wfinished.cases)
next
  case (Read2 p p' f x d g)
  then show ?case 
    using wfinished.cases by blast
next
  case (Write p p' op' x d g)
  then show ?case 
    by (meson op.distinct(7) op.distinct(9) wfinished.simps)
next
  case (Silent p op' d)
  then show ?case by (meson ST' less_Suc_eq step_Tau_wfinished)
next
  case (Choice p ops d g)
  then show ?case  by (metis less_Suc_eq op.distinct(11) op.sel(6) wfinished.cases)
qed

lemma inputs_not_wfinished:
  "p \<in> inputs op \<Longrightarrow> \<not> wfinished op"
  apply (drule inputs_sub_op_Read)
  using reads_not_wfinished apply force
  done

lemma writes_not_wfinished:
  "sub_op (Write op' p x) op n \<Longrightarrow> \<not> wfinished op"
proof (induct p op arbitrary: rule: sub_op_Write_induct)
  case (Read p p' f x op2 y d)
  then show ?case  
    by (meson inputs_not_wfinished op.set_intros(1))
next
  case (Write1 p p' op' x op2 y d)
  then show ?case  
    by (metis op.distinct(7) op.simps(14) wfinished.simps)
next
  case (Silent p op' op2 y d)
  then show ?case  
    using lessI step_Tau_wfinished by blast
next
  case (Choice p op2 y d ops)
  then show ?case 
    by (metis lessI op.distinct(11) op.sel(6) wfinished.cases)
next
  case (Write2 p op' x)
  then show ?case
    using wfinished.simps by fastforce
qed

lemma no_IO_wfinished:
  "inputs op = {} \<Longrightarrow> outputs op = {} \<Longrightarrow> wfinished op"
  by (metis empty_iff estep.elims io_of_vio_not_Tau(2) wfinished_no_wstep wstep_Inp wstep_Out)

lemma outputs_not_wfinished:
  "p \<in> outputs op \<Longrightarrow> \<not> wfinished op"
  apply (drule outputs_sub_op_Write)
  using writes_not_wfinished apply force
  done

lemma wfinished_no_IO:
  "wfinished op \<longleftrightarrow> inputs op = {} \<and> outputs op = {}"
  by (metis ex_in_conv inputs_not_wfinished no_IO_wfinished outputs_not_wfinished)


lemma step_not_wfinished_alt:
  "step io op op' \<Longrightarrow>
   io \<noteq> Tau \<Longrightarrow>
   \<not> wfinished op"
  by (metis step_not_wfinished vio_of_io_inverse)

lemma bar_not_wfinished:
  "p |\<in>| (c\<UU> :: ('a :: {countable, defaults}) cset) \<Longrightarrow>
   \<not> wfinished (comp_op Some X (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op A) (id_op (C :: 'a :: {countable,defaults} \<Rightarrow> 'b buf))) (merge_op E))"
  apply (rule step_not_wfinished_alt[where io="Inp (Inl (Inr p)) undefined"])
   apply simp_all
  apply force
  done

lemma foo:
  "wstep io op op' \<Longrightarrow>
   io = Inp (Inr p) x \<Longrightarrow>
   op = map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<parallel> id_op C) \<V>) \<Longrightarrow>
   wtraced op' lxs \<Longrightarrow>
    wstep (Inp (Inr p) x) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C)) \<V>))) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B (BENQ p x C))) \<V>))) \<and>
    wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<parallel> id_op (BENQ p x C)) \<V>)) lxs"
  apply (intro conjI)
  subgoal
    unfolding pcomp_op_def
    apply (rule step_wstep)
    apply (rule step_map_op)+
      apply (rule step_comp_op_L_Inp)
        apply (rule step_comp_op_R_Inp)
           apply (rule step_merge_op_Read_R[where p=p])
    subgoal 
      apply (subgoal_tac "Inr p \<notin> defaults")
       apply simp
      apply (rule wstep_inputs_not_in_defaults)
       apply simp
      apply (auto simp add: op.set_map; hypsubst_thin)
      using \<UU>_E inputs_merge_op apply blast
      done
           apply simp_all
    apply simp
    done
  subgoal premises prems
    using prems apply -
    unfolding wstep_def
    apply (erule relcomppE)+
    subgoal for op'' op'''
      apply hypsubst_thin
      apply simp
      apply (frule wstep_Tau_busy_wtraced[where op=op'''])
      subgoal premises prems2
        using prems2(2-) apply -
        apply (drule longer_bar)
         apply fast
        apply safe
        unfolding pcomp_op_def
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
        apply hypsubst_thin
        apply (frule longer_bar[unfolded pcomp_op_def])
         apply fast
        apply safe
        apply hypsubst_thin
        using bar_not_wfinished[where p=p] apply -
        apply simp
        apply force
        done
       apply simp
      subgoal premises prems2
        using prems2(2,5,3) apply -
        apply (induct op'' arbitrary: op''' rule: rtranclp_induct)
        subgoal
          unfolding pcomp_op_def
          apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases)
          done
        subgoal for op1 op2 op3
          apply (drule bar)
          apply (elim exE)
          apply hypsubst_thin
          apply (drule meta_spec)
          apply (drule meta_mp)
           defer
           apply (drule meta_mp)
          unfolding pcomp_op_def
            apply (rule step_map_op)+
             apply (rule step_comp_op_L_Inp)
               apply (rule step_comp_op_R_Inp)
                  apply (rule step_id_op_Read[where p=p])
          subgoal
            apply (subgoal_tac "Inr p \<notin> defaults")
             apply simp
            apply (auto 0 0 elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; hypsubst_thin?)
            done
                  apply simp_all
          unfolding pcomp_op_def
          apply (auto 0 0 elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; hypsubst_thin?)
          subgoal for A B C D E pc
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_L)
                 apply simp_all
             apply (rule step_comp_op_R_Out)
               apply (rule step_id_op_Write)
                  apply auto
               apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
              apply (metis BENQ_access BENQ_diff_access append_is_Nil_conv)
             apply (cases "p = pc")
              apply simp_all
              apply (simp add: BENQ_def BTL_def)
             apply (auto simp add: BENQ_def BTL_def)[1]
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for A B C D E pc
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_L)
                 apply simp_all
             apply (rule step_comp_op_L_Out)
                apply (simp add: step_merge_op_Write_L)
               apply simp_all
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal 
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply (rule step_Tau_comp_op_L)
                apply simp_all
             apply force
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal 
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply (rule step_Tau_comp_op_R)
                  apply blast
                 apply simp_all
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal 
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply (rule step_Tau_comp_op_R)
                  apply blast
                 apply simp_all
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          done
        done
      done
    done
  done

lemma foo2:
  "wstep (io_of_vio (VInp (Inl (Inl p)) x)) (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<parallel> id_op C) \<V>)) op' \<Longrightarrow>
    wtraced op' lxs \<Longrightarrow>
    wstep (io_of_vio (VInp (Inl (Inl p)) x)) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C)) \<V>))) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op (BENQ p x A) \<parallel> merge_op (case_sum B C)) \<V>))) \<and>
    wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum (BENQ p x A) B) \<parallel> id_op C) \<V>)) lxs"
  apply (intro conjI)
  subgoal
    unfolding pcomp_op_def
    apply (rule step_wstep)
    apply (rule step_map_op)+
      apply (rule step_comp_op_L_Inp)
        apply (rule step_comp_op_L_Inp)
          apply (rule step_id_op_Read[where p=p])
           apply simp_all
    subgoal 
      apply (subgoal_tac "Inl (Inl p) \<notin> defaults")
       apply force
      apply (rule wstep_inputs_not_in_defaults)
       apply simp
      apply (auto simp add: op.set_map; hypsubst_thin?)
      apply (meson DiffD2 inputs_sub_op_Read merge_op_reads)
      done
    apply simp_all
    done
  subgoal 
    unfolding wstep_def
    apply (erule relcomppE)+
    subgoal for op'' op'''
      apply simp
      apply (frule wstep_Tau_busy_wtraced[where op=op'''])
      subgoal premises prems2
        using prems2(2-) apply -
        apply (drule longer_bar)
         apply fast
        apply safe
        unfolding pcomp_op_def
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
        apply hypsubst_thin
        apply (frule longer_bar[unfolded pcomp_op_def])
         apply fast
        apply safe
        apply hypsubst_thin
        using bar_not_wfinished[where p=p] apply -
        apply simp
        apply force
        done
       apply assumption
      subgoal premises prems2
        using prems2(2,5,3) apply -
        apply (induct op'' arbitrary: op''' rule: rtranclp_induct)
        subgoal
          unfolding pcomp_op_def
          apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases)
          done
        apply (drule bar)
        apply (elim exE)
        apply hypsubst_thin
        apply (drule meta_spec)
        apply (drule meta_mp)
         defer
         apply (drule meta_mp)
        unfolding pcomp_op_def
          apply (rule step_map_op)+
           apply (rule step_comp_op_L_Inp)
             apply (rule step_comp_op_L_Inp)
               apply (rule step_merge_op_Read_L[where p=p and x=x])
        subgoal
          apply (subgoal_tac "Inr p \<notin> defaults")
           apply simp
          apply (auto 0 0 elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
          done
               apply simp_all
        subgoal
          unfolding pcomp_op_def
          apply (auto 0 0 elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; hypsubst_thin?)
          subgoal for pc
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_L)
                 apply simp_all
             apply (rule step_comp_op_R_Out)
               apply (rule step_id_op_Write)
                  apply auto
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for pc
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_L)
                 apply simp_all
             apply (rule step_comp_op_L_Out)
                apply (rule step_merge_op_Write_L)
                   apply auto
            subgoal
              apply (cases "pc = p")
               apply auto
               apply (simp add: BENQ_def BTL_def)
              apply (auto simp add: BENQ_def BTL_def)[1]
              done
              apply (metis BENQ_access BENQ_diff_access snoc_eq_iff_butlast)
             apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for pc
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_L)
                 apply simp_all
             apply (rule step_comp_op_L_Out)
                apply (rule step_merge_op_Write_R)
                   apply simp_all
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for pc
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_R)
                   apply simp_all
             apply blast
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for pc
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_R)
                   apply simp_all
             apply blast
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          done
        done
      done
    done
  done

lemma foo3:
  "wstep (io_of_vio (VInp (Inl (Inr p)) x)) (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<parallel> id_op C) \<V>)) op' \<Longrightarrow>
    wtraced op' lxs \<Longrightarrow>
    wstep (io_of_vio (VInp (Inl (Inr p)) x)) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C)) \<V>))) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum (BENQ p x B) C)) \<V>))) \<and>
    wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A (BENQ p x B)) \<parallel> id_op C) \<V>)) lxs"
 apply (intro conjI)
  subgoal
    unfolding pcomp_op_def
    apply (rule step_wstep)
    apply (rule step_map_op)+
      apply (rule step_comp_op_L_Inp)
        apply (rule step_comp_op_R_Inp)
           apply (rule step_merge_op_Read_L[where p=p])
    apply simp_all
    subgoal 
      apply (subgoal_tac "Inl (Inr p) \<notin> defaults")
       apply force
      apply (rule wstep_inputs_not_in_defaults)
       apply simp
      apply (auto simp add: op.set_map; hypsubst_thin?)
      apply (meson DiffD2 inputs_sub_op_Read merge_op_reads)
      done
    apply simp_all
    done
  subgoal 
  unfolding wstep_def
    apply (erule relcomppE)+
    subgoal for op'' op'''
      apply simp
      apply (frule wstep_Tau_busy_wtraced[where op=op'''])
      subgoal premises prems2
        using prems2(2-) apply -
        apply (drule longer_bar)
         apply fast
        apply safe
        unfolding pcomp_op_def
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
        apply hypsubst_thin
        apply (frule longer_bar[unfolded pcomp_op_def])
         apply fast
        apply safe
        apply hypsubst_thin
        using bar_not_wfinished[where p=p] apply -
        apply simp
        apply force
        done
       apply assumption
      subgoal premises prems2
        using prems2(2,5,3) apply -
        apply (induct op'' arbitrary: op''' rule: rtranclp_induct)
        subgoal
          unfolding pcomp_op_def
          apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases)
          done
   apply (drule bar)
        apply (elim exE)
        apply hypsubst_thin
        apply (drule meta_spec)
        apply (drule meta_mp)
         defer
         apply (drule meta_mp)
        unfolding pcomp_op_def
          apply (rule step_map_op)+
           apply (rule step_comp_op_L_Inp)
             apply (rule step_comp_op_L_Inp)
               apply (rule step_merge_op_Read_R[where p=p and x=x])
        subgoal
          apply (subgoal_tac "Inr p \<notin> defaults")
           apply simp
          apply (auto 0 0 elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
          done
               apply simp_all
        subgoal
          unfolding pcomp_op_def
          apply (auto 0 0 elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; hypsubst_thin?)
          subgoal for pc
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_L)
                 apply simp_all
             apply (rule step_comp_op_R_Out)
               apply (rule step_id_op_Write)
                  apply auto
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for pc
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_L)
                 apply simp_all
             apply (rule step_comp_op_L_Out)
                apply (rule step_merge_op_Write_L)
                   apply auto
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for pc
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_L)
                 apply simp_all
             apply (rule step_comp_op_L_Out)
                apply (rule step_merge_op_Write_R)
                   apply simp_all
 subgoal
              apply (cases "pc = p")
               apply auto
               apply (simp add: BENQ_def BTL_def)
              apply (auto simp add: BENQ_def BTL_def)[1]
              done
              apply (metis BENQ_access BENQ_diff_access snoc_eq_iff_butlast)
             apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for pc
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_R)
                   apply simp_all
             apply blast
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for pc
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_R)
                   apply simp_all
             apply blast
            subgoal 
              using bar_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          done
        done
      done
    done
  done

lemma wfinished_comp_op_intro:
  "wfinished op1 \<Longrightarrow>
   wfinished op2 \<Longrightarrow>
   wfinished (comp_op wire buf op1 op2)"
  apply (simp add: wfinished_no_IO)
  apply auto
  done

lemma no_usable_ports_wfinished:
  "\<nexists>p :: 'a. p \<in> \<UU> \<Longrightarrow>
   wfinished (comp_op Some X (id_op (A :: 'a :: {countable,defaults} \<Rightarrow> 'b buf) \<parallel> merge_op B) (merge_op P))"
  unfolding pcomp_op_def
  apply (intro wfinished_comp_op_intro)
  apply (meson \<UU>_I equals0I inputs_id_op_alt no_IO_wfinished outputs_id_op_dest)
   apply (metis Diff_disjoint \<UU>_I bot.extremum_uniqueI inf_absorb2 inputs_merge_op no_IO_wfinished outputs_merge_op subsetI sum_in_defaults)+
  done

lemma L_R:
  \<open>wtraced (map_op projl projr (comp_op Some (case_sum (\<lambda> _. []) (\<lambda> _. []))
    (merge_op (case_sum A B) \<parallel> id_op C)
    (merge_op (case_sum (\<lambda> _. []) (\<lambda> _. []))))) lxs \<Longrightarrow>
  wtraced (map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda> _. []) (\<lambda> _. []))
      (id_op (A :: 'a :: {countable,defaults} \<Rightarrow> 'b buf) \<parallel> merge_op (case_sum B C))
      (merge_op (case_sum (\<lambda> _. []) (\<lambda> _. [])))))) lxs\<close>
  apply (coinduction arbitrary: A B C lxs rule: wtraced.coinduct)
  subgoal for A B C lxs
    apply (cases lxs)
    subgoal
      apply simp
      apply (cases "\<exists> p :: 'a. p \<in> \<UU>")
      subgoal
      apply (erule wtraced.cases)
       apply simp_all
      apply hypsubst_thin
      apply (rule FalseE)
        apply simp
        apply safe
        subgoal for p
          using bar_not_wfinished[where p=p] apply -
          apply simp
          unfolding pcomp_op_def
          apply blast
          done
        done
      subgoal
        apply hypsubst_thin
        using no_usable_ports_wfinished apply blast
        done
      done
    subgoal for x lxs
      apply simp
      apply hypsubst_thin
      apply (erule wtraced.cases)
       apply simp_all    
      apply hypsubst_thin
      apply (cases x)
      subgoal for vio op op' p x
        apply hypsubst_thin
        apply (cases p)
        subgoal for p
          apply hypsubst_thin
          apply (cases p)
          subgoal for p
            apply hypsubst_thin
            apply (drule foo2)
             apply assumption
            apply auto
            done
        subgoal for p
          apply hypsubst_thin
          apply (drule foo3)
           apply auto
          done
        done
        subgoal for p
          apply hypsubst_thin
        apply simp
          apply (drule foo)
             apply (rule refl)+
           apply assumption
          apply auto
          done
        done
      subgoal
        sorry
      done
    done
  done

lemma R_L:
  \<open>wtraced (map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda> _. []) (\<lambda> _. []))
      (id_op (A :: 'a :: {countable,defaults} \<Rightarrow> 'b buf) \<parallel> merge_op (case_sum B C))
      (merge_op (case_sum (\<lambda> _. []) (\<lambda> _. [])))))) lxs \<Longrightarrow>
   wtraced (map_op projl projr (comp_op Some (case_sum (\<lambda> _. []) (\<lambda> _. []))
    (merge_op (case_sum A B) \<parallel> id_op C)
    (merge_op (case_sum (\<lambda> _. []) (\<lambda> _. []))))) lxs\<close>
  sorry

lemma A1:
  \<open>(\<V> \<parallel> \<I>) \<bullet> \<V> \<equiv>\<^sub>t map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>)\<close>
  using L_R[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []", simplified]  R_L[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []", simplified] by (metis Collect_cong scomp_op_def wtraces_def)

end