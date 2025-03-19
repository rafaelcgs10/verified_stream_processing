theory A1

imports
  "../BNA_Operators"
  "HOL-ex.Sketch_and_Explore"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom A1: Equality test commutes with identity\<close>

lemma A1_gen:
  assumes \<open>A = A1 >> A2 >> A3\<close>
    and \<open>B'' = B1'' >> B2'' >> B3''\<close>
    and \<open>\<forall>p. \<exists>m n C'. A1'' p = drop n (B'' p) \<and> A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p)
  \<and> (A2' >> A3') p = tested n (C' p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C' p)
  \<and> n \<le> length (C' p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p)\<close>
  shows \<open>map_op projl projr (comp_op Some (case_sum A2' A2)
  (aeq_op (case_sum A1'' A1') \<parallel> id_op A1)
  (aeq_op (case_sum A3' A3)))
  \<approx> map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2)
    (id_op B1'' \<parallel> aeq_op (case_sum B1' B1))
    (aeq_op (case_sum B3'' B3))))\<close>
  unfolding pcomp_op_def
using assms proof (coinduction arbitrary: A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3' B3 B3'' rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp (Inl (Inl pb)) y) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ pb y A1'') A1')) (id_op A1)) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "pb \<notin> defaults"
      for pb :: 'a
        and y :: "'b option"
      using that sorry
    moreover have "\<exists>op2'. wstep (Inp (Inl (Inr pb)) y) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' (BENQ pb y A1'))) (id_op A1)) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "pb \<notin> defaults"
      for pb :: 'a
        and y :: "'b option"
      using that sorry
    moreover have "\<exists>op2'. wstep (Inp (Inr pb) xb) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op (BENQ pb xb A1))) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "pb \<notin> defaults"
      for pb :: 'a
        and xb :: "'b option"
      using that sorry
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa A3)) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum (BTL pa A3') (BTL pa A3))))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A3' pa \<noteq> []"
        and "A3 pa \<noteq> []"
        and "pa \<notin> defaults"
        and "BHD pa A3' = BHD pa A3"
      for pa :: 'a
      using that sorry
    moreover have "\<exists>op2'. wstep (Out pa None) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum (BTL pa A3') (BTL pa A3))))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A3' pa \<noteq> []"
        and "A3 pa \<noteq> []"
        and "pa \<notin> defaults"
        and "BHD pa A3' \<noteq> BHD pa A3"
      for pa :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' (BENQ pb (BHD pb A1) A2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op (BTL pb A1))) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "pb \<notin> defaults"
        and "A1 pb \<noteq> []"
      for pb :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum (BENQ pb (BHD pb A1') A2') A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL pb A1'') (BTL pb A1'))) (id_op A1)) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A1'' pb \<noteq> []"
        and "A1' pb \<noteq> []"
        and "pb \<notin> defaults"
        and "BHD pb A1'' = BHD pb A1'"
      for pb :: 'a
      using that
      apply -
      apply (drule spec[of _ pb])
      apply (elim conjE exE)
      subgoal for m n C'
        apply (intro exI conjI)
         apply fast
        apply (rule wbc_base)
        apply (intro exI conjI)
            apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases "p = pb")
          subgoal
            apply hypsubst_thin
            apply (rule exI[of _ m])
            apply (rule exI[of _ "Suc n"])
            apply (intro conjI)
            subgoal
              by (metis BTL_access drop_Suc tl_drop)
            subgoal
            apply (rule exI[of _ C'])
              apply (intro conjI)
              apply simp_all
               apply (metis BTL_access drop_Suc tl_drop)
              by (metis BAPPEND_BENQ BENQ_access BHD_def hd_drop_conv_nth le_neq_implies_less tested_eq_Suc_gen)
            done
          subgoal
            using that(1) apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n' C''
              apply (rule exI[of _ m'])
              apply (rule exI[of _ "n'"])
              apply simp
              apply (intro conjI)
              subgoal
                by (metis BTL_diff_access)
              apply (rule exI[of _ C''])
              apply (intro conjI)
              apply simp_all
               apply (metis BTL_diff_access)
              by (metis BAPPEND_BENQ BENQ_diff_access)
            done
          done
        done
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum (BENQ pb None A2') A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL pb A1'') (BTL pb A1'))) (id_op A1)) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A1'' pb \<noteq> []"
        and "A1' pb \<noteq> []"
        and "pb \<notin> defaults"
        and "BHD pb A1'' \<noteq> BHD pb A1'"
      for pb :: 'a
      using that
      apply -
      apply (drule spec[of _ pb])
      apply (elim conjE exE)
      subgoal for m n C'
        apply (intro exI conjI)
         apply fast
        apply (rule wbc_base)
        apply (intro exI conjI)
            apply (rule refl)+
        apply (intro allI)
        subgoal for p
          apply (cases "p = pb")
          subgoal
            apply hypsubst_thin
            apply (rule exI[of _ m])
            apply (rule exI[of _ "Suc n"])
            apply (intro conjI)
            subgoal
              by (metis BTL_access drop_Suc tl_drop)
            subgoal
            apply (rule exI[of _ C'])
              apply (intro conjI)
              apply simp_all
               apply (metis BTL_access drop_Suc tl_drop)
              by (metis BAPPEND_BENQ BENQ_access BHD_def hd_drop_conv_nth le_neq_implies_less tested_diff_Suc_gen)
            done
          subgoal
            using that(1) apply -
            apply (drule spec[of _ p])
            apply (elim conjE exE)
            subgoal for m' n' C''
              apply (rule exI[of _ m'])
              apply (rule exI[of _ "n'"])
              apply simp
              apply (intro conjI)
              subgoal
                by (metis BTL_diff_access)
              apply (rule exI[of _ C''])
              apply (intro conjI)
              apply simp_all
               apply (metis BTL_diff_access)
              by (metis BAPPEND_BENQ BENQ_diff_access)
            done
          done
        done
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum (BTL pa A2') A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum (BENQ pa (BHD pa A2') A3') A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A2' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>A A1 A1' A1'' B'' B1 B1' B1'' A2 A2' B2 B2'' A3 A3'. op1 = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B3 B3''. op2 = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> B'' = (B1'' >> B2'') >> B3'' \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (B'' p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' (BTL pa A2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' (BENQ pa (BHD pa A2) A3))))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that sorry
    ultimately show ?thesis
      apply -
      subgoal premises prems
        using SIM1 by (auto elim !: step_map_op_elim step_comp_op_elim step_aeq_op_elim step_id_op_cases simp add: prems)
      done
  qed
next
  case SIM2
  then show ?case sorry
qed

lemma A1:
  \<open>(\<Q> \<parallel> \<I>) \<bullet> \<Q> \<approx> map_op assoc id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>)\<close>
  unfolding scomp_op_def
  using A1_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by force

end