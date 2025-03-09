theory A3

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)
no_notation nth (infixl "!" 100)

section \<open>Axiom A3: Equality test dummy source and identity\<close>

lemma A3_gen:
  assumes "D = ((map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) :: (0, 'a :: {countable,defaults}, 'd) op)"
    and "S = (! :: (0 + 'a :: {countable,defaults}, 0, 'd) op)"
  shows  \<open>map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (D \<parallel> id_op buf1) (aeq_op (case_sum (\<lambda>_. []) buf3))) \<approx>
          map_op projl projr (comp_op Some (\<lambda>_. []) S (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))\<close>
  unfolding pcomp_op_def
  using assms proof (coinduction arbitrary: buf1 buf2 buf3 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case 
    apply - 
    explore (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_aeq_op_elim split: if_splits; hypsubst_thin?)
  proof -
    have "\<exists>op2'. wstep (Inp (Inr pb::0 + 'a) xb) (map_op projl projr (comp_op (Some::0 \<Rightarrow> _ option) (\<lambda>_. []) ! (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. (\<exists>buf1 buf2 buf3. op1xx = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (aeq_op (case_sum (\<lambda>_. []) buf3)))) \<and> op2xx = map_op projl projr (comp_op (Some::0 \<Rightarrow> _ option) (\<lambda>_. []) ! (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op (BENQ pb xb buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) op2'"
      if "pb \<notin> defaults"
      for pb :: 'a
        and xb :: 'd
      using that
    apply -
      apply (intro conjI[rotated] exI wbc_base)
        apply force+
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op (Some::0 \<Rightarrow> _ option) (\<lambda>_. []) ! (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. (\<exists>buf1 buf2 buf3. op1xx = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::(0, 'a, 'd) op) \<I>)) (id_op buf1)) (aeq_op (case_sum (\<lambda>_. []) buf3)))) \<and> op2xx = map_op projl projr (comp_op (Some::0 \<Rightarrow> _ option) (\<lambda>_. []) ! (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ pb (BHD pb buf1) buf2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op (BTL pb buf1))) (aeq_op (case_sum (\<lambda>_. []) buf3)))) op2'"
      if "pb \<notin> defaults"
        and "buf1 pb \<noteq> []"
      for pb :: 'a
      using that
    apply -
      apply (intro conjI[rotated] exI wbc_base)
        apply force+
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op (Some::0 \<Rightarrow> _ option) (\<lambda>_. []) ! (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. (\<exists>buf1 buf2 buf3. op1xx = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) (\<oslash>::(0, 'a, 'd) op) \<I>)) (id_op buf1)) (aeq_op (case_sum (\<lambda>_. []) buf3)))) \<and> op2xx = map_op projl projr (comp_op (Some::0 \<Rightarrow> _ option) (\<lambda>_. []) ! (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BTL pa buf2)) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (aeq_op (case_sum (\<lambda>_. []) (BENQ pa (BHD pa buf2) buf3))))) op2'"
      if "buf2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that
    apply -
      apply (intro conjI[rotated] exI wbc_base)
        apply force+
      done
    ultimately show ?thesis
      using SIM1  by (auto elim !: step_map_op_elim step_comp_op_elim step_id_op_cases step_aeq_op_elim split: if_splits)
  qed
next
  case SIM2
  then show ?case 
    apply -
    explore (auto elim !: step_map_op_elim step_sink_op step_comp_op_elim step_id_op_cases step_aeq_op_elim split: if_splits; hypsubst_thin)
  proof -
    have "\<exists>op2'. wstep (Inp pa xa) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (aeq_op (case_sum (\<lambda>_. []) buf3)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. (\<exists>buf1 buf2 buf3. op1xx = map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) buf2) (comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)) (id_op buf1)) (aeq_op (case_sum (\<lambda>_. []) buf3)))) \<and> op2xx = map_op projl projr (comp_op (Some::0 \<Rightarrow> _ option) (\<lambda>_. []) ! (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' (map_op projl projr (comp_op (Some::0 \<Rightarrow> _ option) (\<lambda>_. []) ! (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>))))"
      if "pa \<notin> defaults"
      for pa :: "0 + 'a"
        and xa :: 'd
    proof (cases pa)
      case (Inl a)
      from this that show ?thesis 
        apply -
        apply (intro conjI[rotated] exI wbc_base)
          apply force+
        done
    next
      case (Inr b)
      from this that  show ?thesis 
        apply -
        apply (intro conjI[rotated] exI wbc_base)
          apply force+
        done
    qed
    then show ?thesis
      using SIM2 by (auto elim !: step_map_op_elim step_sink_op step_comp_op_elim step_id_op_cases step_aeq_op_elim split: if_splits)
  qed
qed

lemma A3:
  assumes "D = (\<exclamdown> :: (0, 'a :: {countable,defaults}, 'd) op)"
    and "S = (! :: (0 + 'a :: {countable,defaults}, 0, 'd) op)"
  shows  \<open>(D \<parallel> \<I>) \<bullet> \<Q> \<approx> S \<bullet> \<exclamdown>\<close>
  using assms 
 unfolding scomp_op_def
  using A3_gen[of D S \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>, simplified] by blast 

end