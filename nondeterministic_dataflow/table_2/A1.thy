theory A1

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)


definition "tested n xs ys = map fst (filter (case_prod (=)) (zip (take n xs) (take n ys)))"

lemma tested_diff_Suc:
  "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> hd xs \<noteq> hd ys \<Longrightarrow> tested (Suc n) xs ys = tested n (tl xs) (tl ys)"
  unfolding tested_def by (simp add: take_Suc)

lemma tested_eq_Suc:
  "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> hd xs = hd ys \<Longrightarrow> tested (Suc n) xs ys = hd xs # tested n (tl xs) (tl ys)"
  unfolding tested_def by (simp add: take_Suc)

lemma tested_diff_Suc_gen:
  "length xs > n \<Longrightarrow> length ys > n \<Longrightarrow> xs ! n \<noteq> ys ! n \<Longrightarrow> tested (Suc n) xs ys = tested n xs ys"
  unfolding tested_def
  apply (induct n arbitrary: xs ys)
   apply (auto simp: take_Suc hd_conv_nth)
  subgoal for n xs ys
    apply (cases xs; cases ys; simp)
    done
  done

lemma tested_eq_Suc_gen:
  "length xs > n \<Longrightarrow> length ys > n \<Longrightarrow> xs ! n = ys ! n \<Longrightarrow> tested (Suc n) xs ys = tested n xs ys @ [xs ! n]"
  unfolding tested_def
  apply (induct n arbitrary: xs ys)
   apply (auto simp: take_Suc hd_conv_nth)
  subgoal for n xs ys
    apply (cases xs; cases ys; simp)
    done
  done

lemma length_tested_0[simp]:
  "tested 0 xs ys = []"
  unfolding tested_def by simp


lemma progress_buffers:
  assumes "p \<notin> defaults"
  and "n = min (length (B1' p)) (length (B1 p))"
  shows "(step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (id_op B1'' \<parallel> aeq_op (case_sum B1' B1)) (aeq_op (case_sum B3'' B3)))))
   (map_op assoc id (map_op projl projr (comp_op Some (case_sum (B2''(p := [])) (B2(p := []))) (id_op (B1''(p := [])) \<parallel> aeq_op (case_sum (B1'(p := drop n (B1' p))) (B1(p := drop n (B1 p))))) (aeq_op (case_sum (B3''(p := (B1'' >> B2'' >> B3'') p)) (B3(p := ((B2 >> B3) p) @ tested n (B1' p) (B1 p))))))))"
  sorry

lemma test_n:
  assumes "tested n (B3'' p) (B3 p) = []"
  and "p \<notin> defaults"
  shows  "(step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (id_op B1'' \<parallel> aeq_op (case_sum B1' B1)) (aeq_op (case_sum B3'' B3)))))
    (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (id_op B1'' \<parallel> aeq_op (case_sum B1' B1)) (aeq_op (case_sum (B3''(p := drop n (B3'' p))) (B3(p := drop n (B3 p))))))))"
  sorry

lemma finds_tested_first_equal:
  "tested n xs ys = z # zs \<Longrightarrow> n \<le> length xs \<Longrightarrow> n \<le> length ys \<Longrightarrow>
   \<exists> k. k < n \<and> nth xs k = z \<and> nth ys k = z \<and> tested k xs ys = []"
  apply (induction n arbitrary: xs ys)
   apply simp_all
  subgoal for n xs ys
    apply (cases xs; cases ys; simp)
    subgoal for x xs y ys
      apply hypsubst_thin
      apply (cases "x = y")
      apply (metis length_tested_0 list.discI list.sel(1) nat_less_le nth_Cons_0 tested_eq_Suc zero_less_Suc)
      apply (subst (asm) tested_diff_Suc)
         apply simp_all
      apply (drule meta_spec)+
      apply (drule meta_mp)
      apply assumption
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply assumption
      apply safe
      subgoal for k
        apply (rule exI[of _ "Suc k"])
        apply (simp add: tested_diff_Suc)
        done
      done
    done
  done

lemma tested_all:
  "tested (min (length A) (length C)) A C = map fst (filter (case_prod (=)) (zip A C))"
  unfolding tested_def by (metis map_fst_zip_take map_snd_zip_take zip_map_fst_snd)


lemma tested_min_helper:
  " B1' = drop m C \<Longrightarrow>
    B1 = drop m A \<Longrightarrow>
    B3 @ B2 = tested m A C \<Longrightarrow>
    tested (min (length A) (length C)) A C = B3 @ B2 @ tested (min (length B1) (length B1')) B1 B1'"
  apply (simp (no_asm) add: tested_all)
  apply (auto 0 0 simp add: tested_def)
  apply (metis append.assoc append_take_drop_id drop_zip filter_append map_append take_zip)
  done

lemma tested_comm:
  "tested n xs ys = tested n ys xs"
  apply (induct n arbitrary: xs ys)
   apply simp_all
  subgoal for n xs ys
    apply (cases xs; cases ys; simp)
    apply (simp_all add: tested_def)
    done
  done  

  
section \<open>Axiom A1: Equality test commutes with identity\<close>
lemma A1_gen:
  assumes "A = A1 >> A2 >> A3"
  and "B'' = B1'' >> B2'' >> B3''"
  and "\<forall> p. \<exists> m n C'. A1'' p = drop n (B'' p) \<and> A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and>
       (A2' >> A3') p = tested n (C' p) (B'' p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and>
        n \<le> length (C' p) \<and> n \<le> length (B'' p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p)"
shows  \<open>map_op projl projr (comp_op Some (case_sum A2' A2) (aeq_op (case_sum A1'' A1') \<parallel> id_op A1) (aeq_op (case_sum A3' A3)))
  \<approx> map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (id_op B1'' \<parallel> aeq_op (case_sum B1' B1)) (aeq_op (case_sum B3'' B3))))\<close>
  unfolding pcomp_op_def
using assms proof (coinduction arbitrary:A A1 A1' B1' A2 A3 A1'' A2' A3' B1 B2 B3 B'' B1'' B2'' B3'' rule: wbisim_coinduct)
  case SIM1
  then show ?case
    apply -
    explore (auto elim!: step_comp_op_elim step_map_op_elim step_aeq_op_elim step_id_op_cases split: if_splits sum.splits; hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp (Inl (Inl pb)) y) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>A A1 A1' B1' A2 A3 A1'' A2' A3'. op1xx = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B1 B2 B3 B1'' B2'' B3''. op2xx = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BENQ pb y A1'') A1')) (id_op A1)) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "pb \<notin> defaults"
      for pb :: 'a
        and y :: 'b
      using that sorry
    moreover have "\<exists>op2'. wstep (Inp (Inl (Inr pb)) y) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>A A1 A1' B1' A2 A3 A1'' A2' A3'. op1xx = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B1 B2 B3 B1'' B2'' B3''. op2xx = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' (BENQ pb y A1'))) (id_op A1)) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "pb \<notin> defaults"
      for pb :: 'a
        and y :: 'b
      using that sorry
    moreover have "\<exists>op2'. wstep (Inp (Inr pb) xb) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>A A1 A1' B1' A2 A3 A1'' A2' A3'. op1xx = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B1 B2 B3 B1'' B2'' B3''. op2xx = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op (BENQ pb xb A1))) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "pb \<notin> defaults"
      for pb :: 'a
        and xb :: 'b
      using that sorry
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa A3)) (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>A A1 A1' B1' A2 A3 A1'' A2' A3'. op1xx = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B1 B2 B3 B1'' B2'' B3''. op2xx = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum (BTL pa A3') (BTL pa A3))))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A3' pa \<noteq> []"
        and "A3 pa \<noteq> []"
        and "BHD pa A3' = BHD pa A3"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that 
  apply -
      apply (drule spec[of _ pa])
      apply (elim conjE exE)
      subgoal for m n C'
        using finds_tested_first_equal[where n=n and xs="C' pa" and ys="((B1'' >> B2'') >> B3'') pa" and z="BHD pa A3'" and zs="tl ((A2' >> A3') pa)"] apply -
        apply (drule meta_mp)
        apply (metis BHD_BULK_BENQ_cases BHD_def BULK_BENQ_empty list.collapse)
        apply (drule meta_mp)
        apply assumption
        apply (drule meta_mp)
         apply assumption
        apply (elim exE conjE)
        subgoal for k
        apply (intro exI conjI)
         apply (rule wstep_trans(1))
        apply (rule rtranclp_trans)
          apply (rule progress_buffers[unfolded pcomp_op_def])
           apply assumption
           apply (rule refl)+
          apply (rule test_n[unfolded pcomp_op_def, where n=k and p=pa])
          subgoal
            apply (subst (1 2) fun_upd_apply)
            apply (simp (no_asm)  add: BULK_BENQ_bulk_benq)
            apply (subst tested_min_helper[symmetric])
               apply assumption+
            using tested_comm apply (metis BULK_BENQ_def)
            apply (simp add: )

        find_theorems BULK_BENQ "_ @ _"




end
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>A A1 A1' B1' A2 A3 A1'' A2' A3'. op1xx = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B1 B2 B3 B1'' B2'' B3''. op2xx = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' (BENQ pb (BHD pb A1) A2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op (BTL pb A1))) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "pb \<notin> defaults"
        and "A1 pb \<noteq> []"
      for pb :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>A A1 A1' B1' A2 A3 A1'' A2' A3'. op1xx = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B1 B2 B3 B1'' B2'' B3''. op2xx = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum (BENQ pb (BHD pb A1') A2') A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL pb A1'') (BTL pb A1'))) (id_op A1)) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A1'' pb \<noteq> []"
        and "A1' pb \<noteq> []"
        and "BHD pb A1'' = BHD pb A1'"
        and "pb \<notin> defaults"
      for pb :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>A A1 A1' B1' A2 A3 A1'' A2' A3'. op1xx = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B1 B2 B3 B1'' B2'' B3''. op2xx = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum (BTL pa A2') A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum (BENQ pa (BHD pa A2') A3') A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A2' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>A A1 A1' B1' A2 A3 A1'' A2' A3'. op1xx = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B1 B2 B3 B1'' B2'' B3''. op2xx = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' (BTL pa A2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' (BENQ pa (BHD pa A2) A3))))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that sorry
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>A A1 A1' B1' A2 A3 A1'' A2' A3'. op1xx = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B1 B2 B3 B1'' B2'' B3''. op2xx = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum (BTL pb A1'') (BTL pb A1'))) (id_op A1)) (aeq_op (case_sum A3' A3)))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A1'' pb \<noteq> []"
        and "A1' pb \<noteq> []"
        and "BHD pb A1'' \<noteq> BHD pb A1'"
        and "pb \<notin> defaults"
      for pb :: 'a
 using that 
      apply -
      apply (drule spec[of _ pb])
      apply (elim conjE exE)
      subgoal for m n C'
        apply (intro exI conjI)
         apply fast
        apply (rule wbcr_base)
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
              apply (rule tested_diff_Suc_gen[symmetric])
              using nat_less_le apply blast
              using nless_le apply blast
              apply (metis BHD_def hd_drop_conv_nth nat_less_le)
              done
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
              done
            done
          done
        done
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3))))) op2' \<and> \<W> (\<lambda>op1xx op2xx. \<exists>A A1 A1' B1' A2 A3 A1'' A2' A3'. op1xx = map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum A3' A3))) \<and> (\<exists>B1 B2 B3 B1'' B2'' B3''. op2xx = map_op assoc id (map_op projl projr (comp_op Some (case_sum B2'' B2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op B1'') (aeq_op (case_sum B1' B1))) (aeq_op (case_sum B3'' B3)))) \<and> A = (A1 >> A2) >> A3 \<and> (\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (A p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (A p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (A p))))) (map_op projl projr (comp_op Some (case_sum A2' A2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (aeq_op (case_sum A1'' A1')) (id_op A1)) (aeq_op (case_sum (BTL pa A3') (BTL pa A3))))) op2'"
      if "\<forall>p. \<exists>m n. A1'' p = drop n (((B1'' >> B2'') >> B3'') p) \<and> (\<exists>C'. A1' p = drop n (C' p) \<and> B1' p = drop m (C' p) \<and> B1 p = drop m (((A1 >> A2) >> A3) p) \<and> (A2' >> A3') p = tested n (C' p) (((B1'' >> B2'') >> B3'') p) \<and> (B2 >> B3) p = tested m (((A1 >> A2) >> A3) p) (C' p) \<and> n \<le> length (C' p) \<and> n \<le> length (((B1'' >> B2'') >> B3'') p) \<and> m \<le> length (C' p) \<and> m \<le> length (((A1 >> A2) >> A3) p))"
        and "A3' pa \<noteq> []"
        and "A3 pa \<noteq> []"
        and "BHD pa A3' \<noteq> BHD pa A3"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that sorry
    ultimately show ?thesis
      using SIM1  by (auto elim !: step_comp_op_elim step_map_op_elim step_aeq_op_elim step_id_op_cases split: if_splits sum.splits)
  qed



end
next
  case SIM2
  then show ?case sorry
qed


end

lemma A1:
  \<open>(\<Q> \<parallel> \<I>) \<bullet> \<Q> ~ map_op assoc id ((\<I> \<parallel> \<Q>) \<bullet> \<Q>)\<close>
  unfolding scomp_op_def
  using A1_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp


end