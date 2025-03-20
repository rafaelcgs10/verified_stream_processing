theory A1

imports
  "../BNA_Operators"
  "HOL-ex.Sketch_and_Explore"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A1: Merge commutes with identity\<close>

fun interleaves :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>interleaves (x # xs) (y # ys) (z # zs) = (x = y \<and> interleaves xs ys (z # zs) \<or> x = z \<and> interleaves xs (y # ys) zs)\<close>
| \<open>interleaves (x # xs) (y # ys) [] = (x # xs = y # ys)\<close>
| \<open>interleaves (x # xs) [] (z # zs) = (x # xs = z # zs)\<close>
| \<open>interleaves (_ # _) [] [] = False\<close>
| \<open>interleaves [] [] [] = True\<close>
| \<open>interleaves _ _ _ = False\<close>

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
  using interleaves.elims(2) by fastforce

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

end