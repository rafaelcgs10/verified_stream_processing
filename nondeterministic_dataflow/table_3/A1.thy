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

coinductive busy where
 "(\<And>op' vio. wstep (io_of_vio vio) op op' \<Longrightarrow> busy op') \<Longrightarrow> \<not> wfinished op \<Longrightarrow> busy op"

lemma
   "busy (id_op buf)"
  apply (coinduction arbitrary: buf rule: busy.coinduct)
  subgoal for buf
    apply simp
    apply safe
    oops

lemma lfinite_wtraced_not_busy:
  "lfinite lxs \<Longrightarrow> busy op \<Longrightarrow> wtraced op lxs \<Longrightarrow> False"
  apply (induct lxs arbitrary: op rule: lfinite_induct)
  subgoal for xs op
    by (metis busy.simps not_lnull_conv wtraced.cases)
  subgoal for lxs op
    apply (cases lxs; simp)
    subgoal for x lxs
      apply hypsubst_thin
      apply (metis busy.cases llist.inject wtraced.simps)
      done
    done
  done

lemma busy_no_finite_traces:
  "busy op \<longleftrightarrow> (\<forall> lxs. wtraced op lxs \<longrightarrow> \<not> lfinite lxs)"
  apply (rule iffI)
  subgoal
    apply (intro impI allI)
    apply (erule wtraced.cases)
     apply auto
    subgoal 
      apply (erule busy.cases)
      apply auto
      done
    subgoal for vio op' lxs
      using lfinite_wtraced_not_busy by (metis busy.cases)
    done
  subgoal
    apply (coinduction arbitrary: op rule: busy.coinduct)
    subgoal for op
      apply simp
      apply (intro conjI impI allI disjI1)
      subgoal for x lxs
        by (meson lfinite_LConsI wtraced.Step)
      subgoal
        using wtraced.Nil by blast
      done
    done
  done

lemma busy_no_wtraced_LNil:
  "busy op \<Longrightarrow> \<not> wtraced op LNil"
  by (auto simp add: busy_no_finite_traces)

lemma busy_not_wfinished:
  "busy op \<Longrightarrow> \<not> wfinished op"
  by (metis busy.cases)

lemma
  "busy (Choice ops) \<Longrightarrow> op |\<in>| ops \<Longrightarrow> busy op"
  apply (erule busy.cases)
  apply (auto simp add: wfinished_no_wstep)
  oops

lemma wstep_Tau_busy_wtraced:
  "(step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow>
   busy op' \<Longrightarrow>
   wtraced op' lxs \<Longrightarrow>
   wtraced op lxs"
  apply (induct op rule: converse_rtranclp_induct)
  apply (auto intro: )
  apply (metis busy_no_wtraced_LNil wstep_trans_tau_1 wtraced.simps)
  done

lemma step_Tau_busy_wtraced:
  "step io op op' \<Longrightarrow>
   io = Tau \<Longrightarrow>
   busy op' \<Longrightarrow>
   wtraced op' lxs \<Longrightarrow>
   wtraced op lxs"
  apply (induction io op op' arbitrary: pred: step)
     apply simp_all
  subgoal for op
    apply (coinduction arbitrary: op lxs rule: wtraced.coinduct)
    subgoal for op lxs
      apply (erule wtraced.cases)
       apply simp_all
       apply (erule wfinished.intros)
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
        apply (auto simp add: busy_no_finite_traces wfinished_no_wstep)
        done
      subgoal for op lxs vio opa op' lxsa
        apply hypsubst_thin
        by (meson WSC cin.rep_eq)
      done
    done
  done

lemma busy_wstep:
 "busy op \<Longrightarrow> wstep io op op' \<Longrightarrow> io \<noteq> Tau \<Longrightarrow> busy op'"
  by (metis busy.cases vio_of_io_inverse)

lemma bar:
  "(step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some (\<lambda>_. []) (merge_op (case_sum A B) \<parallel> id_op C) \<V>)) op1 \<Longrightarrow>
   \<exists> A B C D E. op1 =  (map_op projl projr (comp_op Some D (merge_op (case_sum A B) \<parallel> id_op C) (merge_op E)))"
  sorry

lemma wstep_inputs_not_in_defaults:
  "wstep (Inp p x) op op' \<Longrightarrow>
   inputs op \<inter> defaults = {} \<Longrightarrow>
   p \<notin> defaults"
  by (simp add: disjoint_iff wstep_Inp)

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
        apply (rule busy_wstep[OF _ prems(1), unfolded prems])
      subgoal sorry
        apply simp
       apply assumption
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
    sorry
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
            subgoal sorry
            done
            subgoal sorry
            subgoal sorry
            subgoal sorry
            subgoal sorry
            done
          done
        done
      done
    done

lemma
  \<open>wtraced (map_op projl projr (comp_op Some (case_sum (\<lambda> _. []) (\<lambda> _. []))
    (merge_op (case_sum A B) \<parallel> id_op C)
    (merge_op (case_sum (\<lambda> _. []) (\<lambda> _. []))))) lxs \<Longrightarrow>
  wtraced (map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda> _. []) (\<lambda> _. []))
      (id_op A \<parallel> merge_op (case_sum B C))
      (merge_op (case_sum (\<lambda> _. []) (\<lambda> _. [])))))) lxs\<close>
  apply (coinduction arbitrary: A B C lxs rule: wtraced.coinduct)
  subgoal for A B C lxs
    apply (cases lxs)
    subgoal
      apply simp
      apply (erule wtraced.cases)
       apply simp_all
      apply hypsubst_thin
      apply (rule FalseE)
      sorry
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
        subgoal sorry
        subgoal for p
          apply hypsubst_thin
        apply simp
          apply (drule foo)
             apply (rule refl)+
           apply assumption
          apply auto
          done

      find_theorems wtraced Tau


(* fun interleaves :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>interleaves (x # xs) (y # ys) (z # zs) = (x = y \<and> interleaves xs ys (z # zs) \<or> x = z \<and> interleaves xs (y # ys) zs)\<close>
| \<open>interleaves (x # xs) (y # ys) [] = (x # xs = y # ys)\<close>
| \<open>interleaves (x # xs) [] (z # zs) = (x # xs = z # zs)\<close>
| \<open>interleaves (_ # _) [] [] = False\<close>
| \<open>interleaves [] [] [] = True\<close>
| \<open>interleaves _ _ _ = False\<close>
 *)
inductive merged where
  merged_base[intro]: \<open>merged [] [] []\<close>
| merged_append_L: \<open>merged xs ys zs \<Longrightarrow> merged (xs @ [x]) ys (zs @ [x])\<close>
| merged_append_R: \<open>merged xs ys zs \<Longrightarrow> merged xs (ys @ [x]) (zs @ [x])\<close>

(* 
lemma interleaves_length:
  \<open>interleaves xs ys zs \<Longrightarrow> length xs = length ys + length zs\<close>
  by (induct xs ys zs rule: interleaves.induct) auto

lemma interleaves_comm:
  \<open>interleaves xs ys zs = interleaves xs zs ys\<close>
  by (induction xs ys zs rule: interleaves.induct) auto

abbreviation merged where \<open>merged xs ys zs \<equiv> interleaves (rev xs) (rev ys) (rev zs)\<close>

lemma merged_length:
  \<open>merged xs ys zs \<Longrightarrow> length xs = length ys + length zs\<close>
  using interleaves_length by force

lemma merged_empty:
  \<open>merged [] ys zs \<Longrightarrow> ys = [] \<and> zs = []\<close>
  using interleaves.elims(2) by blast

lemma merged_comm:
  \<open>merged xs ys zs = merged xs zs ys\<close>
  using interleaves_comm by blast

lemma merged_empty_left:
  \<open>merged xs [] xs\<close>
  using interleaves.elims(3) by fastforce 

lemma merged_empty_right:
  \<open>merged xs xs []\<close>
  using merged_comm merged_empty_left by blast

lemma merge_append_L:
  \<open>merged xs ys zs \<Longrightarrow> merged (xs @ [x]) (ys @ [x]) zs\<close>
  using interleaves.elims(2) by fastforce

lemma merge_append_R:
  \<open>merged xs ys zs \<Longrightarrow> merged (xs @ [x]) ys (zs @ [x])\<close>
  using interleaves.elims(2) by fastforce*)

lemma progress_buffers1:
  assumes \<open>p \<notin> defaults\<close>
    and \<open>n = min (length (B1' p)) (length (B1 p))\<close>
    and \<open>merged xs (take n (B1' p)) (take n (B1 p))\<close>
  shows \<open>(step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2')
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1'')))
    (merge_op (case_sum B3 B3')))))
   (map_op assoc id (map_op projl projr (comp_op Some (case_sum (B2(p := [])) (B2'(p := [])))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (B1(p := []))) (merge_op (case_sum (B1'(p := drop n (B1' p))) (B1''(p := drop n (B1'' p))))))
    (merge_op (case_sum (B3(p := (B1 >> B2 >> B3) p)) (B3'(p := ((B2' >> B3') p) @ xs)))))))\<close>
  sorry

lemma A1_gen:
  assumes \<open>A'' = A1'' >> A2'' >> A3''\<close>
    and \<open>B = B1 >> B2 >> B3\<close>
    and \<open>\<forall>p. \<exists>xs ys zs. merged xs (A'' p) ((A2 >> A3) p @ ys) \<and> merged ys (A1 p) (A1' p)
      \<and> merged xs (B p) ((B2' >> B3') p @ zs) \<and> merged zs (B1' p) (B1'' p)\<close>
  shows \<open>map_op projl projr (comp_op Some (case_sum A2 A2'')
    (merge_op (case_sum A1 A1') \<parallel> id_op A1'')
    (merge_op (case_sum A3 A3'')))
  \<approx> map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2')
      (id_op B1 \<parallel> merge_op (case_sum B1' B1''))
      (merge_op (case_sum B3 B3'))))\<close>
  unfolding pcomp_op_def
using assms proof (coinduction arbitrary: A'' A1 A1' A1'' A2 A2'' A3 A3'' B B1 B1' B1'' B2 B2' B3 B3' rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
    (* apply - explore (auto elim!: step_map_op_elim step_comp_op_elim step_merge_op_elim step_id_op_cases; hypsubst_thin?) *)
  proof -
    have "\<exists>op2'. wstep (Inp (Inl (Inl pb)) xb) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3'))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A'' A1 A1' A1'' A2 A2'' A3 A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op A1'')) (merge_op (case_sum A3 A3''))) \<and> (\<exists>B1 B1' B1'' B2 B2' B3 B3'. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3')))) \<and> A'' = (A1'' >> A2'') >> A3'' \<and> (\<forall>p. \<exists>xs ys. merged xs (A'' p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))))) (map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BENQ pb xb A1) A1')) (id_op A1'')) (merge_op (case_sum A3 A3'')))) op2'"
      if "\<forall>p. \<exists>xs ys. merged xs (((A1'' >> A2'') >> A3'') p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))"
        and "pb \<notin> defaults"
      for pb :: 'a
        and xb :: 'b
      using that
      apply -
      apply (drule spec[of _ pb])
      apply (elim exE conjE)
      subgoal for xs ys zs
        apply (intro exI conjI)
         apply fastforce
        apply (rule wbc_base)
        apply (intro exI conjI)
           apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases \<open>p = pb\<close>)
           apply (rule exI[of _ \<open>xs @ [xb]\<close>])
           apply (rule exI[of _ \<open>ys @ [xb]\<close>])
           apply (smt (verit, del_insts) BAPPEND_BENQ BENQ_access append_eq_appendI merge_append_L merge_append_R)
          by (metis BAPPEND_BENQ BENQ_diff_access that(1))
        done
      done
    moreover have "\<exists>op2'. wstep (Inp (Inl (Inr pb)) xb) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3'))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A'' A1 A1' A1'' A2 A2'' A3 A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op A1'')) (merge_op (case_sum A3 A3''))) \<and> (\<exists>B1 B1' B1'' B2 B2' B3 B3'. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3')))) \<and> A'' = (A1'' >> A2'') >> A3'' \<and> (\<forall>p. \<exists>xs ys. merged xs (A'' p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))))) (map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 (BENQ pb xb A1'))) (id_op A1'')) (merge_op (case_sum A3 A3'')))) op2'"
      if "\<forall>p. \<exists>xs ys. merged xs (((A1'' >> A2'') >> A3'') p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))"
        and "pb \<notin> defaults"
      for pb :: 'a
        and xb :: 'b
      using that sorry
    moreover have "\<exists>op2'. wstep (Inp (Inr pb) xb) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3'))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A'' A1 A1' A1'' A2 A2'' A3 A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op A1'')) (merge_op (case_sum A3 A3''))) \<and> (\<exists>B1 B1' B1'' B2 B2' B3 B3'. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3')))) \<and> A'' = (A1'' >> A2'') >> A3'' \<and> (\<forall>p. \<exists>xs ys. merged xs (A'' p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))))) (map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op (BENQ pb xb A1''))) (merge_op (case_sum A3 A3'')))) op2'"
      if "\<forall>p. \<exists>xs ys. merged xs (((A1'' >> A2'') >> A3'') p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))"
        and "pb \<notin> defaults"
      for pb :: 'a
        and xb :: 'b
      using that sorry
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa A3)) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3'))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A'' A1 A1' A1'' A2 A2'' A3 A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op A1'')) (merge_op (case_sum A3 A3''))) \<and> (\<exists>B1 B1' B1'' B2 B2' B3 B3'. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3')))) \<and> A'' = (A1'' >> A2'') >> A3'' \<and> (\<forall>p. \<exists>xs ys. merged xs (A'' p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))))) (map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op A1'')) (merge_op (case_sum (BTL pa A3) A3'')))) op2'"
      if "\<forall>p. \<exists>xs ys. merged xs (((A1'' >> A2'') >> A3'') p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))"
        and "A3 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that
      apply -
      apply (drule spec[of _ pa])
      apply (elim exE conjE)
      subgoal for xs ys zs
        apply (intro exI conjI)
         apply (rule wstep_trans(1))
          apply (rule progress_buffers1)
            apply assumption
        sorry
      done
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa A3'')) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3'))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A'' A1 A1' A1'' A2 A2'' A3 A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op A1'')) (merge_op (case_sum A3 A3''))) \<and> (\<exists>B1 B1' B1'' B2 B2' B3 B3'. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3')))) \<and> A'' = (A1'' >> A2'') >> A3'' \<and> (\<forall>p. \<exists>xs ys. merged xs (A'' p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))))) (map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op A1'')) (merge_op (case_sum A3 (BTL pa A3''))))) op2'"
      if "\<forall>p. \<exists>xs ys. merged xs (((A1'' >> A2'') >> A3'') p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))"
        and "A3'' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3'))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A'' A1 A1' A1'' A2 A2'' A3 A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op A1'')) (merge_op (case_sum A3 A3''))) \<and> (\<exists>B1 B1' B1'' B2 B2' B3 B3'. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3')))) \<and> A'' = (A1'' >> A2'') >> A3'' \<and> (\<forall>p. \<exists>xs ys. merged xs (A'' p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))))) (map_op projl projr (comp_op Some (case_sum A2 (BENQ pb (BHD pb A1'') A2'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op (BTL pb A1''))) (merge_op (case_sum A3 A3'')))) op2'"
      if "\<forall>p. \<exists>xs ys. merged xs (((A1'' >> A2'') >> A3'') p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))"
        and "pb \<notin> defaults"
        and "A1'' pb \<noteq> []"
      for pb :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3'))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A'' A1 A1' A1'' A2 A2'' A3 A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op A1'')) (merge_op (case_sum A3 A3''))) \<and> (\<exists>B1 B1' B1'' B2 B2' B3 B3'. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3')))) \<and> A'' = (A1'' >> A2'') >> A3'' \<and> (\<forall>p. \<exists>xs ys. merged xs (A'' p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))))) (map_op projl projr (comp_op Some (case_sum (BENQ pb (BHD pb A1) A2) A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BTL pb A1) A1')) (id_op A1'')) (merge_op (case_sum A3 A3'')))) op2'"
      if "\<forall>p. \<exists>xs ys. merged xs (((A1'' >> A2'') >> A3'') p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))"
        and "A1 pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3'))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A'' A1 A1' A1'' A2 A2'' A3 A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op A1'')) (merge_op (case_sum A3 A3''))) \<and> (\<exists>B1 B1' B1'' B2 B2' B3 B3'. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3')))) \<and> A'' = (A1'' >> A2'') >> A3'' \<and> (\<forall>p. \<exists>xs ys. merged xs (A'' p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))))) (map_op projl projr (comp_op Some (case_sum (BENQ pb (BHD pb A1') A2) A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 (BTL pb A1'))) (id_op A1'')) (merge_op (case_sum A3 A3'')))) op2'"
      if "\<forall>p. \<exists>xs ys. merged xs (((A1'' >> A2'') >> A3'') p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))"
        and "A1' pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3'))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A'' A1 A1' A1'' A2 A2'' A3 A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op A1'')) (merge_op (case_sum A3 A3''))) \<and> (\<exists>B1 B1' B1'' B2 B2' B3 B3'. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3')))) \<and> A'' = (A1'' >> A2'') >> A3'' \<and> (\<forall>p. \<exists>xs ys. merged xs (A'' p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))))) (map_op projl projr (comp_op Some (case_sum (BTL pa A2) A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op A1'')) (merge_op (case_sum (BENQ pa (BHD pa A2) A3) A3'')))) op2'"
      if "\<forall>p. \<exists>xs ys. merged xs (((A1'' >> A2'') >> A3'') p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))"
        and "A2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3'))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A'' A1 A1' A1'' A2 A2'' A3 A3''. op1 = map_op projl projr (comp_op Some (case_sum A2 A2'') (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op A1'')) (merge_op (case_sum A3 A3''))) \<and> (\<exists>B1 B1' B1'' B2 B2' B3 B3'. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2 B2') (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1) (merge_op (case_sum B1' B1''))) (merge_op (case_sum B3 B3')))) \<and> A'' = (A1'' >> A2'') >> A3'' \<and> (\<forall>p. \<exists>xs ys. merged xs (A'' p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))))) (map_op projl projr (comp_op Some (case_sum A2 (BTL pa A2'')) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum A1 A1')) (id_op A1'')) (merge_op (case_sum A3 (BENQ pa (BHD pa A2'') A3''))))) op2'"
      if "\<forall>p. \<exists>xs ys. merged xs (((A1'' >> A2'') >> A3'') p) (bulk_benq ys ((A2 >> A3) p)) \<and> merged ys (A1 p) (A1' p) \<and> (\<exists>zs. merged xs (((B1 >> B2) >> B3) p) (bulk_benq zs ((B2' >> B3') p)) \<and> merged zs (B1' p) (B1'' p))"
        and "A2'' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that sorry
    ultimately show ?thesis
      using SIM1 by (auto elim !: step_map_op_elim step_comp_op_elim step_merge_op_elim step_id_op_cases)
  qed
next
  case SIM2
  then show ?case
    (* apply - apply (auto elim !: step_map_op_elim step_comp_op_elim step_merge_op_elim step_id_op_cases; hypsubst_thin?) *)
    sorry
qed

lemma A1:
  \<open>(\<V> \<parallel> \<I>) \<bullet> \<V> \<approx> map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>)\<close>
  unfolding scomp_op_def
  using A1_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  sorry



lemma aux1:
  "\<V> \<approx> map_op (case_sum Inr Inl) id \<V>"
  sorry

lemma A1_aux1:
  \<open>(\<V> \<parallel> \<I>) \<bullet> \<V> \<approx> (\<V> \<parallel> \<I>) \<bullet> (map_op (case_sum Inr Inl) id \<V>)\<close>
  using aux1 wbisim_refl wbisim_scomp_op_cong by blast

lemma A1_aux2:
  \<open>(op1 \<parallel> op2) \<bullet> (map_op (case_sum Inr Inl) id op3) \<approx> (op2 \<parallel> op1) \<bullet> op3\<close>
  sorry

lemma A1:
  \<open>(\<V> \<parallel> \<I>) \<bullet> \<V> \<approx> map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>)\<close>
  apply (rule wbisim_trans)
   apply (rule A1_aux1)
    apply (rule wbisim_trans)



lemma A1_aux2:
  \<open>(\<V> \<parallel> \<I>) \<bullet> (map_op (case_sum Inr Inl) id \<V>) \<approx> map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>)\<close>

end

lemma A1:
  \<open>(\<V> \<parallel> \<I>) \<bullet> \<V> \<approx> map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>)\<close>



end

end