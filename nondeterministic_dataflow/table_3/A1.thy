theory A1

imports
  "../BNA_Operators"
  "HOL-ex.Sketch_and_Explore"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A1: Merge commutes with identity\<close>

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

lemma short_foo:
  "step Tau op op1 \<Longrightarrow>
   op = map_op projl projr (comp_op Some X (map_op projl projr (comp_op Some R (merge_op A) (id_op V)) \<parallel> id_op C) (map_op projl projr (comp_op Some D (merge_op K) (id_op P)))) \<Longrightarrow>
   \<exists>X A C K V P D R. op1 = map_op projl projr (comp_op Some X (map_op projl projr (comp_op Some R (merge_op A) (id_op V)) \<parallel> id_op C) (map_op projl projr (comp_op Some D (merge_op K) (id_op P))))"
  apply hypsubst_thin
  unfolding pcomp_op_def
  apply (auto 10 10 elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; hypsubst_thin?)
  done

lemma longer_foo:
  "(step Tau)\<^sup>*\<^sup>* op op1 \<Longrightarrow>
   op = map_op projl projr (comp_op Some X (map_op projl projr (comp_op Some R (merge_op A) (id_op V)) \<parallel> id_op C) (map_op projl projr (comp_op Some D (merge_op K) (id_op P)))) \<Longrightarrow>
   \<exists>X A C K V P D R. op1 = map_op projl projr (comp_op Some X (map_op projl projr (comp_op Some R (merge_op A) (id_op V)) \<parallel> id_op C) (map_op projl projr (comp_op Some D (merge_op K) (id_op P))))"
  unfolding scomp_op_def
  apply (induct op arbitrary: X A C K V P D R rule: converse_rtranclp_induct)
  using short_foo apply blast
  using short_foo apply meson
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

lemma foo_not_wfinished:
  "p |\<in>| (c\<UU> :: ('a :: {countable, defaults}) cset) \<Longrightarrow>
   \<not> wfinished (comp_op Some X (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some F (merge_op A) (id_op H))) (id_op (C :: 'a :: {countable,defaults} \<Rightarrow> 'b buf))) (map_op projl projr (comp_op Some G (merge_op E) (id_op I))))"
  unfolding scomp_op_def
  apply (rule step_not_wfinished_alt[where io="Inp (Inl (Inr p)) undefined"])
   apply simp_all
  apply force
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
   wfinished (comp_op Some X (id_op (A :: 'a :: {countable,defaults} \<Rightarrow> 'b buf) \<parallel> (merge_op B)\<turnstile>) ((merge_op P)\<turnstile>))"
  unfolding pcomp_op_def scomp_op_def
  apply (intro wfinished_comp_op_intro)
    apply (meson \<UU>_I equals0I inputs_id_op_alt no_IO_wfinished outputs_id_op_dest)
   apply (metis Diff_disjoint \<UU>_I bot.extremum_uniqueI inf_absorb2 inputs_id_op_alt inputs_merge_op no_IO_wfinished outputs_id_op_dest outputs_merge_op subsetI sum_in_defaults wfinished_comp_op_intro wfinished_map_op)
  apply (metis Diff_disjoint \<UU>_I bot.extremum_uniqueI inf_absorb2 inputs_id_op_alt inputs_merge_op no_IO_wfinished outputs_id_op_dest outputs_merge_op subsetI sum_in_defaults wfinished_comp_op_intro wfinished_map_op)  done

lemma foo1:
  "wstep io op op' \<Longrightarrow>
   io = Inp (Inr p) x \<Longrightarrow>
   op = map_op projl projr (comp_op Some (\<lambda>_. []) ((merge_op (case_sum A B))\<turnstile> \<parallel> id_op C) (\<V>\<turnstile>)) \<Longrightarrow>
   wtraced op' lxs \<Longrightarrow>
    wstep (Inp (Inr p) x) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> (merge_op (case_sum B C))\<turnstile>) (\<V>\<turnstile>)))) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> (merge_op (case_sum B (BENQ p x C)))\<turnstile>) (\<V>\<turnstile>)))) \<and>
    wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) ((merge_op (case_sum A B))\<turnstile> \<parallel> id_op (BENQ p x C)) (\<V>\<turnstile>))) lxs"
  apply (intro conjI)
  subgoal
    unfolding pcomp_op_def scomp_op_def
    apply (rule step_wstep)
    apply (rule step_map_op)+
      apply (rule step_comp_op_L_Inp)
        apply (rule step_comp_op_R_Inp)
           apply (rule step_map_op)+
            apply (rule step_comp_op_L_Inp)
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
        apply (drule longer_foo)
        unfolding scomp_op_def
         apply fast
        apply safe
        unfolding pcomp_op_def
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
        apply hypsubst_thin
        apply (drule longer_foo[unfolded pcomp_op_def])
         apply fast
        apply safe
        apply hypsubst_thin
        using foo_not_wfinished[where p=p] apply -
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
          apply (drule longer_foo)
          unfolding scomp_op_def apply blast
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
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            subgoal
              by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
            subgoal
              by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
            subgoal
              by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
            subgoal
              by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
            subgoal
              by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
            subgoal
              by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
            subgoal
              by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
            subgoal
              by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
            subgoal
              by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
            subgoal
              by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
            done
                  apply simp_all
          unfolding pcomp_op_def
          apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
          subgoal for X A C K V P D R io' op'' pa xa op1' q paa xaa op2'
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply (rule step_Tau_comp_op_L)
                apply simp_all
             apply (rule step_comp_op_R_Out)
               apply simp_all
             apply (rule step_id_op_Write)
                apply simp_all
               apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
              apply (metis BENQ_access BENQ_diff_access append_is_Nil_conv)
             apply (cases "p = paa")
              apply simp_all
              apply (simp add: BENQ_def BTL_def)
             apply (auto simp add: BENQ_def BTL_def)[1]
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force 
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force 
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply (rule step_comp_op_L_Tau)
               apply simp_all         
             apply (rule step_comp_op_L_Tau)
               apply (rule step_map_op)+
                apply simp_all
             apply (metis step_Tau_comp_op_L step_merge_op_Write_L)
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply (rule step_comp_op_L_Tau)
               apply simp_all         
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply (rule step_comp_op_R_Tau)
               apply (rule step_map_op)+
                apply simp_all         
             apply (rule step_Tau_comp_op_L)
                apply simp_all
             apply (rule step_merge_op_Write_L)
                apply auto
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
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
  "wstep (io_of_vio (VInp (Inl (Inl p)) x)) (map_op projl projr (comp_op Some (\<lambda>_. []) ((merge_op (case_sum A B))\<turnstile> \<parallel> id_op C) \<V>')) op' \<Longrightarrow>
    wtraced op' lxs \<Longrightarrow>
    wstep (io_of_vio (VInp (Inl (Inl p)) x)) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> ((merge_op (case_sum B C)))\<turnstile>) \<V>'))) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op (BENQ p x A) \<parallel> ((merge_op (case_sum B C)))\<turnstile>) \<V>'))) \<and>
    wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) ((merge_op (case_sum (BENQ p x A) B))\<turnstile> \<parallel> id_op C) \<V>')) lxs"
  apply (intro conjI)
  subgoal
    unfolding pcomp_op_def scomp_op_def
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
        unfolding scomp_op_def
        apply (drule longer_foo)
         apply fast
        apply safe
        unfolding pcomp_op_def
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
        apply hypsubst_thin
        apply (frule longer_foo[unfolded pcomp_op_def])
         apply fast
        apply safe
        apply hypsubst_thin
        using foo_not_wfinished[where p=p] apply -
        apply simp
        apply force
        done
       apply assumption
      subgoal premises prems2
        using prems2(2,5,3) apply -
        apply (induct op'' arbitrary: op''' rule: rtranclp_induct)
        subgoal
          unfolding pcomp_op_def scomp_op_def
          apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases)
          done
        apply (drule longer_foo)
        unfolding scomp_op_def
         apply fast
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
               apply (rule step_map_op)+
                apply (rule step_comp_op_L_Inp)
                  apply (rule step_merge_op_Read_L[where p=p and x=x])
        subgoal
          apply (subgoal_tac "Inr p \<notin> defaults")
           apply simp
          apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          done
                  apply simp_all
        subgoal
          unfolding pcomp_op_def
          apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)

          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for io' op'' op1' op1'a io'a op''a pb xb op1'b q pc
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_comp_op_L_Tau)
                apply simp_all
             apply (rule step_comp_op_L_Tau)
               apply (rule step_map_op)+
                apply simp_all
             apply (rule step_Tau_comp_op_L)
                apply simp_all
             apply (rule step_merge_op_Write_L)
                apply simp_all
               apply (cases "p = pc")
                apply auto
            subgoal
              by (simp add: BENQ_def BTL_def)
            subgoal
              by (auto simp add: BENQ_def BTL_def)[1]
              apply (metis BENQ_access BENQ_diff_access append_is_Nil_conv)
             apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_comp_op_L_Tau)
                apply simp_all
             apply (rule step_comp_op_L_Tau)
               apply (rule step_map_op)+
                apply (rule step_Tau_comp_op_L)
                   apply (rule step_merge_op_Write_R)
                      apply simp_all
               apply (metis case_sum_BENQ_L case_sum_BTL_R case_sum_expand_Inr_pointfree)
              apply (simp add: BENQ_diff_access)
             apply (simp add: BENQ_diff_access BHD_def)
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_comp_op_L_Tau)
                apply simp_all
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_comp_op_R_Tau)
                apply simp_all
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_L)
                 apply (rule step_merge_op_Write_L)
                    apply simp_all
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_comp_op_R_Tau)
                apply simp_all
             apply (rule step_map_op)+
              apply force
             apply simp_all
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for io' op'' op2' io'a op''a pa xa op2'a pb
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_comp_op_R_Tau)
                apply simp_all
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_R[where p=pb])
                   apply blast
                  apply simp_all
            subgoal 
              using foo_not_wfinished[where p=p] apply -
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
  "wstep (io_of_vio (VInp (Inl (Inr p)) x)) (map_op projl projr (comp_op Some (\<lambda>_. []) ((merge_op (case_sum A B))\<turnstile> \<parallel> id_op C) \<V>')) op' \<Longrightarrow>
    wtraced op' lxs \<Longrightarrow>
    wstep (io_of_vio (VInp (Inl (Inr p)) x)) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> (merge_op (case_sum B C))\<turnstile>) \<V>'))) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> (merge_op (case_sum (BENQ p x B) C))\<turnstile>) \<V>'))) \<and>
    wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) ((merge_op (case_sum A (BENQ p x B)))\<turnstile> \<parallel> id_op C) \<V>')) lxs"
  apply (intro conjI)
  subgoal
    unfolding pcomp_op_def scomp_op_def
    apply (rule step_wstep)
    apply (rule step_map_op)+
      apply (rule step_comp_op_L_Inp)
        apply (rule step_comp_op_R_Inp)
           apply (rule step_map_op)+
            apply (rule step_comp_op_L_Inp)
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
        unfolding scomp_op_def
        apply (drule longer_foo)
         apply fast
        apply safe
        unfolding pcomp_op_def
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
        apply hypsubst_thin
        apply (frule longer_foo[unfolded pcomp_op_def])
         apply fast
        apply safe
        apply hypsubst_thin
        using foo_not_wfinished[where p=p] apply -
        apply simp
        apply force
        done
       apply assumption
      subgoal premises prems2
        using prems2(2,5,3) apply -
        apply (induct op'' arbitrary: op''' rule: rtranclp_induct)
        subgoal
          unfolding pcomp_op_def scomp_op_def
          apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases)
          done
        apply (drule longer_foo)
        unfolding scomp_op_def
         apply fast
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
               apply (rule step_map_op)+
                apply (rule step_comp_op_L_Inp)
                  apply (rule step_merge_op_Read_R[where p=p and x=x])
                   apply simp_all
        subgoal
          apply (subgoal_tac "Inr p \<notin> defaults")
           apply simp
          apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          subgoal
            by (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits)
          done
        apply simp_all
        subgoal
          unfolding pcomp_op_def
          apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply (rule step_comp_op_L_Tau)
               apply (rule step_comp_op_L_Tau)
                 apply (rule step_map_op)+
                  apply (rule step_Tau_comp_op_L)
                     apply (rule step_merge_op_Write_L)
                        apply simp_all
               apply (metis case_sum_BENQ_R case_sum_BTL_L case_sum_expand_Inr_pointfree)
              apply (simp add: BENQ_diff_access)
             apply (simp add: BENQ_diff_access BHD_def)
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for io' op'' op1' op1'a io'a op''a pb xb op1'b q pc
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply (rule step_comp_op_L_Tau)
               apply (rule step_comp_op_L_Tau)
                 apply (rule step_map_op)+
                  apply simp_all
             apply (rule step_Tau_comp_op_L)
                apply (rule step_merge_op_Write_R)
                   apply simp_all
               apply (cases "p = pc")
                apply auto
            subgoal
              by (simp add: BENQ_def BTL_def)
            subgoal
              by (auto simp add: BENQ_def BTL_def)[1]
              apply (metis BENQ_access BENQ_diff_access append_is_Nil_conv)
             apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply simp_all
             apply force
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_comp_op_R_Tau)
                apply simp_all
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_L)
                 apply (rule step_merge_op_Write_L)
                    apply simp_all
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_comp_op_R_Tau)
                apply simp_all
             apply (rule step_map_op)+
              apply force
             apply simp_all
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for io' op'' op2' io'a op''a pa xa op2'a pb
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
              apply (rule step_comp_op_R_Tau)
                apply simp_all
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_R[where p=pb])
                   apply blast
                  apply simp_all
            subgoal 
              using foo_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          done
        done
      done
    done
  done
(*
lemma "(step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B)) \<I>) \<parallel> id_op C) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))) op2 \<Longrightarrow>
    step (Out p x) op2 op3 \<Longrightarrow>
    wtraced op3 lxs \<Longrightarrow>
    wstep (Out p x) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>')))
     (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op (BTL p A) \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>'))) \<and>
    wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum (BTL p A) B) \<turnstile> \<parallel> id_op C) \<V>')) lxs \<or>
    wstep (Out p x) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>')))
     (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum (BTL p B) C) \<turnstile>) \<V>'))) \<and>
    wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A (BTL p B)) \<turnstile> \<parallel> id_op C) \<V>')) lxs \<or>
    wstep (Out p x) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>')))
     (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B (BTL p C)) \<turnstile>) \<V>'))) \<and>
    wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<turnstile> \<parallel> id_op (BTL p C)) \<V>')) lxs"
*)
definition "has_one D1 D1' D2 D3 D4 D5 D6 D6' p =
  (length (D1 p) + length (D2 p) + length (D3 p) + length (D4 p) + length (D5 p) + length (D6 p) + length (D6' p) = 1 \<and> 
   (\<forall> q. q \<noteq> p \<longrightarrow> D1 q = [] \<and> D1' q = [] \<and> D2 q = [] \<and> D3 q = [] \<and> D4 q = [] \<and> D5 q = [] \<and> D6 q = [] \<and> D6 q = []))"


definition "all_empty D1 D1' D2 D3 D4 D5 D6 D6' =
   (\<forall> q. D1 q = [] \<and> D1' q = [] \<and> D2 q = [] \<and> D3 q = [] \<and> D4 q = [] \<and> D5 q = [] \<and> D6 q = [] \<and> D6 q = [])"


lemma *: "(step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow>
    op = map_op projl projr (comp_op Some (case_sum D1 D1') (map_op projl projr (comp_op Some D2 (merge_op (case_sum A B)) (id_op D3)) \<parallel> id_op C) (map_op projl projr (comp_op Some D5 (merge_op (case_sum D6 D6')) (id_op D4)))) \<Longrightarrow>
    all_empty D1 D1' D2 D3 D4 D5 D6 D6' \<or> has_one D1 D1' D2 D3 D4 D5 D6 D6' p \<Longrightarrow>
    step (Out p x) op' op'' \<Longrightarrow> \<exists>ops op''' A' B' C'.
      (A p \<noteq> [] \<and> A' = BTL p A \<and> B' = B \<and> C' = C \<or> 
       B p \<noteq> [] \<and> A' = A \<and> B' = BTL p B \<and> C' = C \<or> 
       C p \<noteq> [] \<and> A' = A \<and> B' = B \<and> C' = BTL p C \<or>
       has_one D1 D1' D2 D3 D4 D5 D6 D6' p \<and> A' = A \<and> B' = B \<and> C' = C) \<and> 
      ops \<noteq> [] \<and> chain (\<lambda>op1 op2. step Tau op1 op2 \<and> (\<exists>D1 D1' D2 D3 D4 D5 D6 D6'. has_one D1 D1' D2 D3 D4 D5 D6 D6' p \<and>
      op2 = map_op projl projr (comp_op Some (case_sum D1 D1') (map_op projl projr (comp_op Some D2 (merge_op (case_sum A' B')) (id_op D3)) \<parallel> id_op C') (map_op projl projr (comp_op Some D5 (merge_op (case_sum D6 D6')) (id_op D4)))))) (op # ops) \<and> step (Out p x) (last ops) op''' \<and> (step Tau)\<^sup>*\<^sup>* op''' op''"
(*   apply (induct op' rule: rtranclp_induct)
   apply simp
  subgoal sorry
  subgoal for op1 op2
    apply simp *)
    apply hypsubst_thin
      apply (subst (asm) rtranclp_is_Sup_relpowp)
      apply (unfold Sup_fun_def Sup_bool_def)
      apply simp
    apply (elim exE conjE)
    subgoal for n
      apply (induct n arbitrary: op' rule: less_induct)
      subgoal for n op'
        apply (cases n)
        subgoal sorry
        subgoal for n
          apply hypsubst_thin
          apply (erule relpowp_Suc_E2)
          apply simp
          oops



lemma chain_mono: "chain P ops \<Longrightarrow> P \<le> Q \<Longrightarrow> chain Q ops"
  apply (induct ops rule: chain.induct)
   apply (auto intro: chain.intros)
  done

lemma foo4:
  "wstep (Out p x) (map_op projl projr (comp_op Some (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B)) \<I>) \<parallel> id_op C) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))) op' \<Longrightarrow>
   wtraced op' lxs \<Longrightarrow>
   wstep (Out p x) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>')))
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op (BTL p A) \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>'))) \<and>
   wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum (BTL p A) B) \<turnstile> \<parallel> id_op C) \<V>')) lxs
\<or>
    wstep (Out p x) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>')))
     (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum (BTL p B) C) \<turnstile>) \<V>'))) \<and>
    wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A (BTL p B)) \<turnstile> \<parallel> id_op C) \<V>')) lxs
\<or>
    (wstep (Out p x) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>')))
     (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B (BTL p C)) \<turnstile>) \<V>'))) \<and>
    wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<turnstile> \<parallel> id_op (BTL p C)) \<V>')) lxs)"
  apply (subst (asm) wstep_def)
    apply (erule relcomppE)+
    subgoal for op'' op'''
      apply simp
      apply (frule wstep_Tau_busy_wtraced[where op=op'''])
        subgoal premises prems2
        using prems2(2-) apply -
        unfolding scomp_op_def
        apply (drule longer_foo)
         apply fast
        apply safe
        unfolding pcomp_op_def
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
        apply hypsubst_thin
        apply (frule longer_foo[unfolded pcomp_op_def])
         apply fast
        apply safe
        apply hypsubst_thin
        using foo_not_wfinished[where p=p] apply -
        apply simp
        apply force
        done
       apply assumption
    (*   apply (drule *[OF _ refl])
       apply assumption
      apply (erule disjE exE conjE)+
      subgoal for ops op'' A' B' C'
        apply (rule disjI1)
        apply (subgoal_tac "op'' = map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum (BTL p A) B) \<turnstile> \<parallel> id_op C) \<V>')")
        apply (rule conjI[rotated])
          apply simp
          apply (rule wstep_Tau_busy_wtraced)
            apply assumption
        subgoal sorry
          apply assumption
        subgoal sorry
        subgoal sorry
        find_theorems chain last

          apply (drule chain_mono[where Q="step Tau"])
           apply blast
          apply (drule chain_rtranclp)
          apply (simp)
        apply (rule wstep_trans)
        find_theorems wstep step
        find_theorems chain name: mono
        find_theorems chain rtranclp

      subgoal premises prems
        using prems (2,3) apply -
   apply (induct op'' arbitrary: op''' rule: rtranclp_induct)
        subgoal
          unfolding pcomp_op_def scomp_op_def
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
          done
        subgoal for op1 op2 op3
          apply (drule longer_foo)
          unfolding scomp_op_def apply blast
          apply (elim exE)
          apply hypsubst_thin
          apply (drule meta_spec)
          oops
 *)
      oops

lemma foo4:
  "wstep (Out (p :: 'a :: {countable,defaults}) x) op op' \<Longrightarrow>
   op = map_op projl projr (comp_op Some (case_sum D1 D1') (map_op projl projr (comp_op Some D2 (merge_op (case_sum A B)) (id_op D3)) \<parallel> id_op C) (map_op projl projr (comp_op Some D5 (merge_op (case_sum D6 D6')) (id_op D4)))) \<Longrightarrow>
   all_empty D1 D1' D2 D3 D4 D5 D6 D6' \<or>
   has_one D1 D1' D2 D3 D4 D5 D6 D6' p \<Longrightarrow>
   wtraced op' lxs \<Longrightarrow>
     has_one D1 D1' D2 D3 D4 D5 D6 D6' p \<and>
     wstep (Out p x) op
      (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>'))) \<and>
     wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<turnstile> \<parallel> id_op C) \<V>')) lxs
  \<or>
     all_empty D1 D1' D2 D3 D4 D5 D6 D6' \<and>
     wstep (Out p x) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>')))
      (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op (BTL p A) \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>'))) \<and>
     wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum (BTL p A) B) \<turnstile> \<parallel> id_op C) \<V>')) lxs
  \<or>
     all_empty D1 D1' D2 D3 D4 D5 D6 D6' \<and>
      wstep (Out p x) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>')))
      (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum (BTL p B) C) \<turnstile>) \<V>'))) \<and>
      wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A (BTL p B)) \<turnstile> \<parallel> id_op C) \<V>')) lxs
  \<or>
     all_empty D1 D1' D2 D3 D4 D5 D6 D6' \<and>
     (wstep (Out p x) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>')))
     (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B (BTL p C)) \<turnstile>) \<V>'))) \<and>
     wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<turnstile> \<parallel> id_op (BTL p C)) \<V>')) lxs)"
 apply (subst (asm) wstep_def)
    apply (erule relcomppE)+
    subgoal for op'' op'''
      apply (frule wstep_Tau_busy_wtraced[where op=op'''])
        subgoal premises prems2
        using prems2(1,3-) apply -
        unfolding scomp_op_def
        apply (drule longer_foo)
        apply simp
        apply safe
        unfolding pcomp_op_def
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
        apply hypsubst_thin
        apply (frule longer_foo[unfolded pcomp_op_def])
         apply fast
        apply safe
        apply hypsubst_thin
        using foo_not_wfinished[where p=p] apply -
        apply simp
         apply force
        done
       apply assumption
      subgoal premises prems
        using prems (4,1,2,5-) apply -
        apply (induct op'' arbitrary: op''' rule: rtranclp_induct)
        subgoal sorry
         apply simp
        apply hypsubst_thin
        subgoal for op1 op2 op3
          apply (cases "\<exists> op2'. step (Out p x) op1 op2'")
          apply (elim exE conjE)
          subgoal for op2'
            apply (subgoal_tac " step Tau op2' op3")
            subgoal
            apply (drule meta_spec[of _ op2'])
            apply simp
            apply (drule meta_mp)
            apply auto[1]
            apply (drule meta_mp)
             apply (rule step_Tau_busy_wtraced)
                apply assumption
               apply simp_all
            subgoal sorry
            done
          subgoal
            sorry
          done
          subgoal
            apply (elim disjE conjE)
            subgoal sorry
            oops
(* 
        find_theorems Sup name: "E"

end
        apply (induction op arbitrary: op''' D1 D1' D2 D3 D4 D5 D6 D6' rule: converse_rtranclp_induct)
        subgoal for op''' D1 D1' D2 D3 D4 D5 D6 D6'
          unfolding pcomp_op_def scomp_op_def
          apply hypsubst_thin
          apply simp
          apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin?)
          
          apply (erule disjE)
          apply (auto simp add: all_empty_def)[1]
          apply (elim conjE)
          apply hypsubst_thin
          apply simp
          apply (intro disjI1 conjI)
          subgoal sorry
          subgoal sorry
          done
        subgoal for op1 op2 op3 D1 D1' D2 D3 D4 D5 D6 D6'
          apply hypsubst_thin
          apply simp

          find_theorems rtranclp
          apply (drule longer_foo)
          unfolding scomp_op_def apply blast
          apply (elim exE)
          apply hypsubst_thin
          apply (drule meta_spec)
          sorry
        done
      done
    done *)


(* 
lemma foo4_wstep:
  "wstep (Out p x) (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<turnstile> \<parallel> id_op C) \<V>')) op' \<Longrightarrow>
   (A p \<noteq> [] \<and> BHD p A = x) \<or> (B p \<noteq> [] \<and> BHD p B = x) \<or> (C p \<noteq> [] \<and> BHD p C = x) "


end *)

lemma L_R:
  \<open>wtraced (map_op projl projr (comp_op Some (case_sum (\<lambda> _. []) (\<lambda> _. []))
    ((merge_op (case_sum A B))\<turnstile> \<parallel> id_op C)
    ((merge_op (case_sum (\<lambda> _. []) (\<lambda> _. [])))\<turnstile>))) lxs \<Longrightarrow>
  wtraced (map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda> _. []) (\<lambda> _. []))
      (id_op (A :: 'a :: {countable,defaults} \<Rightarrow> 'b buf) \<parallel> (merge_op (case_sum B C)\<turnstile>))
      ((merge_op (case_sum (\<lambda> _. []) (\<lambda> _. [])))\<turnstile>)))) lxs\<close>
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
          using foo_not_wfinished[where p=p] apply -
          apply simp
          unfolding pcomp_op_def scomp_op_def
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
          apply (drule foo1)
             apply auto
          done
        done
      subgoal for vio op op' p x
        apply hypsubst_thin
        apply simp
        unfolding scomp_op_def
        apply (drule foo4[unfolded scomp_op_def, where A=A and B=B and C=C, of _ _ _ _ "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"])
           apply (simp_all add: has_one_def all_empty_def)
        apply auto
        done
      done
    done
  done

lemma oof_not_wfinished:
  "p |\<in>| (c\<UU> :: ('a :: {countable, defaults}) cset) \<Longrightarrow>
  \<not> wfinished (comp_op Some T (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (A :: 'a :: {countable,defaults} \<Rightarrow> 'b buf)) (map_op projl projr (comp_op Some V (merge_op B) (id_op X)))) (map_op projl projr (comp_op Some H (merge_op P) (id_op W))))"
  unfolding scomp_op_def pcomp_op_def
  apply (rule step_not_wfinished_alt[where io="Inp (Inl (Inl p)) undefined"])
   apply simp_all
  apply force
  done

lemma oof_no_usable_ports_wfinished:
  "\<nexists>p :: 'a. p \<in> \<UU> \<Longrightarrow>
   wfinished (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<turnstile> \<parallel> id_op (C :: 'a :: {countable,defaults} \<Rightarrow> 'b buf)) \<V>')"
  unfolding pcomp_op_def scomp_op_def
  apply (intro wfinished_comp_op_intro)
    apply (metis Diff_disjoint \<UU>_I bot.extremum_uniqueI inf_absorb2 inputs_id_op_alt inputs_merge_op no_IO_wfinished outputs_id_op_dest outputs_merge_op subsetI sum_in_defaults wfinished_comp_op_intro wfinished_map_op)
   apply (meson \<UU>_I equals0I inputs_id_op_alt no_IO_wfinished outputs_id_op_dest)
  apply (metis Diff_disjoint \<UU>_I bot.extremum_uniqueI inf_absorb2 inputs_id_op_alt inputs_merge_op no_IO_wfinished outputs_id_op_dest outputs_merge_op subsetI sum_in_defaults wfinished_comp_op_intro wfinished_map_op)
  done

lemma short_oof:
  "step Tau (map_op assoc id (map_op projl projr (comp_op Some X (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A) (map_op projl projr (comp_op Some R (merge_op (case_sum B C)) (id_op V)))) (map_op projl projr (comp_op Some D (merge_op K) (id_op P)))))) op1 \<Longrightarrow>
   \<exists>X A C K V P D R B. op1 = map_op assoc id (map_op projl projr (comp_op Some X (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A) (map_op projl projr (comp_op Some R (merge_op (case_sum B C)) (id_op V)))) (map_op projl projr (comp_op Some D (merge_op K) (id_op P)))))"
  unfolding pcomp_op_def scomp_op_def
  apply (auto 10 10 elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim; hypsubst_thin?)
  done

lemma longer_oof:
  "(step Tau)\<^sup>*\<^sup>* op op1 \<Longrightarrow>
   op = map_op assoc id (map_op projl projr (comp_op Some X (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A) (map_op projl projr (comp_op Some R (merge_op (case_sum B C)) (id_op V)))) (map_op projl projr (comp_op Some D (merge_op K) (id_op P))))) \<Longrightarrow>
   \<exists>X A C K V P D R B. op1 = map_op assoc id (map_op projl projr (comp_op Some X (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op A) (map_op projl projr (comp_op Some R (merge_op (case_sum B C)) (id_op V)))) (map_op projl projr (comp_op Some D (merge_op K) (id_op P)))))"
  unfolding pcomp_op_def scomp_op_def
  apply (induct op arbitrary: X A C K V P D R B rule: converse_rtranclp_induct)
   apply blast
  apply hypsubst_thin
  apply (drule short_oof)
  apply auto
  done

lemma oof1:
  "wstep (Inp (Inl (Inl p)) x) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>'))) op' \<Longrightarrow>
   wtraced op' lxs \<Longrightarrow>
   wstep (Inp (Inl (Inl p)) x) (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<turnstile> \<parallel> id_op C) \<V>')) (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum (BENQ p x A) B) \<turnstile> \<parallel> id_op C) \<V>')) \<and>
   wtraced (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op (BENQ p x A) \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>'))) lxs"
  apply (intro conjI)
  subgoal
    unfolding pcomp_op_def scomp_op_def
    apply (rule step_wstep)
    apply (rule step_map_op)+
     apply (rule step_comp_op_L_Inp)
       apply (rule step_comp_op_L_Inp)
         apply (rule step_map_op)+
          apply (rule step_comp_op_L_Inp)
            apply (rule step_merge_op_Read_L)
             apply simp_all
    subgoal 
      apply (subgoal_tac "Inl (Inl p) \<notin> defaults")
       apply force
      apply (rule wstep_inputs_not_in_defaults)
       apply simp
      apply (auto simp add: op.set_map split: sum.splits; hypsubst_thin?)
       apply (meson Diff_iff Inl_in_defaults inputs_merge_op subsetD)
      using inputs_merge_op apply fastforce
      done
    done
  subgoal 
    unfolding wstep_def
    apply (erule relcomppE)+
    subgoal for op'' op'''
      apply simp
      apply (frule wstep_Tau_busy_wtraced[where op=op'''])
      subgoal premises prems2
        using prems2(2-) apply -
        unfolding scomp_op_def pcomp_op_def
        apply (drule longer_oof)
         apply fast
        apply safe
        unfolding pcomp_op_def
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
        apply hypsubst_thin
        apply (frule longer_oof[unfolded pcomp_op_def])
         apply fast
        apply safe
        apply hypsubst_thin
        using oof_not_wfinished[where p=p,unfolded pcomp_op_def scomp_op_def] apply -
        apply simp
        apply force
        done
       apply assumption
      subgoal premises prems2
        using prems2(2,5,3) apply -
        apply (induct op'' arbitrary: op''' rule: rtranclp_induct)
        subgoal
          unfolding pcomp_op_def scomp_op_def
          apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases)
          done
        apply (drule longer_oof)
        unfolding scomp_op_def pcomp_op_def
         apply fast
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
                apply simp_all
          apply (rule step_id_op_Read)
           apply simp_all
        subgoal for z op''' X A C K V P D R B
          apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          done
        apply simp_all
        subgoal
          unfolding pcomp_op_def
          apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)

          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for io' op'' io'a op''a pa xa op1' q paa xaa op1'a
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply (rule step_Tau_comp_op_L)
                apply simp_all
             apply (rule step_comp_op_L_Out)
                apply (rule step_id_op_Write)
                   apply simp_all
               apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
              apply (metis BENQ_access BENQ_diff_access snoc_eq_iff_butlast)
             apply (cases "p = paa")
            subgoal
              by (simp add: BENQ_def BTL_def)
            subgoal
              subgoal
                by (auto simp add: BENQ_def BTL_def)[1]
              done
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for io' op'' op1' op1'a io'a op''a pb xb op1'b q pc
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply (rule step_comp_op_L_Tau)
               apply (rule step_comp_op_R_Tau)
                 apply (rule step_map_op)+
                  apply simp_all
             apply (metis case_sum_BHD_L case_sum_BTL_L old.sum.simps(5) step_Tau_comp_op_L step_merge_op_Write_L)
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply (rule step_comp_op_L_Tau)
                 apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply (rule step_comp_op_L_Tau)
                 apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply (rule step_comp_op_R_Tau)
               apply (rule step_map_op)+
                apply simp_all
             apply (metis step_Tau_comp_op_L step_merge_op_Write_L)
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for io' op'' op2' io'a op''a pa xa op2'a pb
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          done
        done
      done
    done
  done

lemma oof2:
  "wstep (Inp (Inl (Inr p)) x) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>'))) op' \<Longrightarrow>
   wtraced op' lxs \<Longrightarrow>
   wstep (Inp (Inl (Inr p)) x) (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<turnstile> \<parallel> id_op C) \<V>')) (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A (BENQ p x B)) \<turnstile> \<parallel> id_op C) \<V>')) \<and>
   wtraced (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum (BENQ p x B) C) \<turnstile>) \<V>'))) lxs"
  apply (intro conjI)
  subgoal
    unfolding pcomp_op_def scomp_op_def
    apply (rule step_wstep)
    apply (rule step_map_op)+
     apply (rule step_comp_op_L_Inp)
       apply (rule step_comp_op_L_Inp)
         apply (rule step_map_op)+
          apply (rule step_comp_op_L_Inp)
            apply (rule step_merge_op_Read_R)
             apply simp_all
    subgoal 
      apply (subgoal_tac "Inl (Inr p) \<notin> defaults")
       apply force
      apply (rule wstep_inputs_not_in_defaults)
       apply simp
      apply (auto simp add: op.set_map split: sum.splits; hypsubst_thin?)
       apply (meson Diff_iff Inl_in_defaults inputs_merge_op subsetD)
      using inputs_merge_op apply fastforce
      done
    done
  subgoal 
    unfolding wstep_def
    apply (erule relcomppE)+
    subgoal for op'' op'''
      apply simp
      apply (frule wstep_Tau_busy_wtraced[where op=op'''])
      subgoal premises prems2
        using prems2(2-) apply -
        unfolding scomp_op_def pcomp_op_def
        apply (drule longer_oof)
         apply fast
        apply safe
        unfolding pcomp_op_def
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
        apply hypsubst_thin
        apply (frule longer_oof[unfolded pcomp_op_def])
         apply fast
        apply safe
        apply hypsubst_thin
        using oof_not_wfinished[where p=p] apply -
        apply simp
        apply force
        done
       apply assumption
      subgoal premises prems2
        using prems2(2,5,3) apply -
        apply (induct op'' arbitrary: op''' rule: rtranclp_induct)
        subgoal
          unfolding pcomp_op_def scomp_op_def
          apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases)
          done
        apply (drule longer_oof)
        unfolding scomp_op_def pcomp_op_def
         apply fast
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
                 apply simp_all
          apply (rule step_map_op)+
           apply (rule step_comp_op_L_Inp)
             apply (rule step_merge_op_Read_L[where p=p and x=x])
              apply simp_all
        subgoal
          apply (subgoal_tac "Inr p \<notin> defaults")
           apply simp
          apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          subgoal
            by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
          done
         apply simp_all
        subgoal
          unfolding pcomp_op_def
          apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for io' op'' io'a op''a op1' op2' io'b op''b pb xb op1'a q pc
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply (rule step_comp_op_L_Tau)
               apply (rule step_comp_op_R_Tau)
                 apply (rule step_map_op)+
                  apply simp_all
             apply (rule step_Tau_comp_op_L)
                apply simp_all
             apply (rule step_merge_op_Write_L)
                apply simp_all
               apply (cases "p = pc")
            subgoal
              by (simp add: BENQ_def BTL_def)
            subgoal
              by (auto simp add: BENQ_def BTL_def)[1]
              apply (metis BENQ_access BENQ_diff_access butlast.simps(1) butlast_snoc)
             apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for io' op'' op1' op1'a io'a op''a pb xb op1'b q pc
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply (rule step_comp_op_R_Tau)
               apply simp_all
             apply (rule step_map_op)+
              apply (rule step_Tau_comp_op_L)
                 apply (rule step_merge_op_Write_L)
                    apply simp_all
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply (rule step_comp_op_R_Tau)
                 apply simp_all
             apply (rule step_map_op)+
              apply force
             apply simp_all
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for io' op'' op2' io'a op''a pa xa op2'a pb
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          done
        done
      done
    done
  done


lemma oof3:
  "wstep (Inp (Inr p) x) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B C) \<turnstile>) \<V>'))) op' \<Longrightarrow>
    wtraced op' lxs \<Longrightarrow>
    wstep (Inp (Inr p) x) (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<turnstile> \<parallel> id_op C) \<V>')) (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<turnstile> \<parallel> id_op (BENQ p x C)) \<V>')) \<and>
    wtraced (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (id_op A \<parallel> merge_op (case_sum B (BENQ p x C)) \<turnstile>) \<V>'))) lxs"
  apply (intro conjI)
  subgoal
    unfolding pcomp_op_def scomp_op_def
    apply (rule step_wstep)
    apply (rule step_map_op)+
     apply (rule step_comp_op_L_Inp)
       apply simp_all
    apply (rule step_comp_op_R_Inp)
       apply (rule step_id_op_Read)
        apply simp_all
    subgoal 
      apply (subgoal_tac "Inr p \<notin> defaults")
       apply simp
      apply (rule wstep_inputs_not_in_defaults)
       apply simp
      apply (auto simp add: op.set_map; hypsubst_thin?)
      apply (metis Diff_iff Inl_in_defaults Inr_in_defaults inputs_merge_op subsetD sum.case_eq_if sum_in_defaults)
      done
    done
  subgoal premises prems
    using prems apply -
    unfolding wstep_def
    apply (erule relcomppE)+
    subgoal for op'' op'''
      apply simp
      apply (frule wstep_Tau_busy_wtraced[where op=op'''])
      subgoal premises prems2
        using prems2(2-) apply -
        apply (drule longer_oof)
        unfolding scomp_op_def pcomp_op_def
         apply fast
        apply safe
        unfolding pcomp_op_def
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim)
        apply hypsubst_thin
        apply (drule longer_oof[unfolded pcomp_op_def])
         apply fast
        apply safe
        apply hypsubst_thin
        using oof_not_wfinished[where p=p] apply -
        apply simp      
        apply force
        done
       apply simp
      subgoal premises prems2
        using prems2(2,5,3) apply -
        apply (induct op'' arbitrary: op''' rule: rtranclp_induct)
        subgoal
          unfolding pcomp_op_def scomp_op_def
          apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim split: sum.splits; hypsubst_thin?)
          done
        subgoal for op1 op2 op3
          apply (drule longer_oof)
          unfolding scomp_op_def pcomp_op_def apply blast
          apply (elim exE)
          apply hypsubst_thin
          apply (drule meta_spec)
          apply (drule meta_mp)
           defer
           apply (drule meta_mp)
          unfolding pcomp_op_def
            apply (rule step_map_op)+
              apply (rule step_comp_op_L_Inp)
                apply simp_all
            apply (rule step_comp_op_R_Inp)
               apply simp_all                
            apply (rule step_map_op)+
             apply (rule step_comp_op_L_Inp)
               apply simp_all
            apply (rule step_merge_op_Read_R[where p=p])
             apply simp_all
          subgoal
            apply (subgoal_tac "Inr p \<notin> defaults")
             apply simp
            apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
            subgoal
              by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
            subgoal
              by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
            subgoal
              by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
            subgoal
              by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
            subgoal
              by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
            subgoal
              by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
            subgoal
              by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
            subgoal
              by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
            subgoal
              by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
            subgoal
              by (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits)
            done
          unfolding pcomp_op_def
          apply (elim step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim exE conjE; simp split: if_splits sum.splits; hypsubst_thin)
          subgoal for X A C K V P D R io' op'' pa xa op1' q paa xaa op2'
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force 
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force 
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply (rule step_comp_op_L_Tau)
               apply simp_all         
             apply (rule step_comp_op_R_Tau)
               apply simp_all
             apply (rule step_map_op)+
              apply simp_all
             apply (metis case_sum_BHD_L case_sum_BTL_L old.sum.simps(5) step_Tau_comp_op_L step_merge_op_Write_L)
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal for X A C K V P D R B io' op'' io'a op''a op1' op2' io'b op''b pb xb op1'a q pc
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply (rule step_comp_op_L_Tau)
               apply simp_all         
             apply (rule step_comp_op_R_Tau)
               apply simp_all
             apply (rule step_map_op)+
              apply simp_all
             apply (rule step_Tau_comp_op_L)
                apply simp_all
             apply (rule step_merge_op_Write_R)
                apply simp_all
               apply (cases "pc = p")
            subgoal
              by (simp add: BENQ_def BTL_def)
            subgoal
              by (auto simp add: BENQ_def BTL_def)[1]
              apply (metis BENQ_access BENQ_diff_access snoc_eq_iff_butlast)
             apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply (rule step_comp_op_R_Tau)
               apply (rule step_map_op)+
                apply simp_all         
             apply (rule step_Tau_comp_op_L)
                apply simp_all
             apply (rule step_merge_op_Write_L)
                apply auto
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          subgoal
            apply (auto elim!: step_merge_op_elim step_map_op_elim step_comp_op_elim step_id_op_cases split: sum.splits if_splits; hypsubst_thin)
            apply (erule step_Tau_busy_wtraced[OF _ refl, rotated 2])
             apply (rule step_map_op)+
               apply simp_all
             apply force
            subgoal 
              using oof_not_wfinished[where p=p] apply -
              apply simp
              apply force
              done
            done
          done
        done
      done
    done
  done


lemma R_L:
  \<open>wtraced (map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda> _. []) (\<lambda> _. []))
      (id_op (A :: 'a :: {countable,defaults} \<Rightarrow> 'b buf) \<parallel> (merge_op (case_sum B C)\<turnstile>))
      ((merge_op (case_sum (\<lambda> _. []) (\<lambda> _. [])))\<turnstile>)))) lxs \<Longrightarrow>
   wtraced (map_op projl projr (comp_op Some (case_sum (\<lambda> _. []) (\<lambda> _. []))
    ((merge_op (case_sum A B))\<turnstile> \<parallel> id_op C)
    ((merge_op (case_sum (\<lambda> _. []) (\<lambda> _. [])))\<turnstile>))) lxs\<close>
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
          using oof_not_wfinished[where p=p] apply -
          apply simp
          unfolding pcomp_op_def scomp_op_def
          apply blast
          done
        done
      subgoal
        apply hypsubst_thin
        using oof_no_usable_ports_wfinished apply blast
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
        apply simp
        apply hypsubst_thin
        apply (cases p)
        subgoal for p
          apply hypsubst_thin
          apply (cases p)
          subgoal for p
            apply hypsubst_thin
            apply (drule oof1)
             apply auto
            done
          subgoal for p
            apply hypsubst_thin
            apply (drule oof2)
             apply auto
            done
          done
        subgoal for p
          apply hypsubst_thin
          apply (drule oof3)
           apply auto
          done
        done
      subgoal for vio op op' p x
        apply simp
        apply hypsubst_thin
        sorry
      done
    done
  done

lemma A1:
  \<open>(\<V>' \<parallel> \<I>) \<bullet> \<V>' \<equiv>\<^sub>t map_op assoc id ((\<I> \<parallel> \<V>') \<bullet> \<V>')\<close>
  unfolding wtraces_def scomp_op_def
  using L_R[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []", simplified, unfolded scomp_op_def]  R_L[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []", simplified, unfolded scomp_op_def]
  apply force
  done

end