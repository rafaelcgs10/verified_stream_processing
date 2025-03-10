theory F5

imports
  "../BNA_Operators"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom F5\<close>

lemma F5_gen:
  "map_op projl projl
     (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. []))
       (map_op projl projr (comp_op Some (case_sum (\<lambda> _. []) (case_sum buf4 (\<lambda> _. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda> _. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) ((id_op buf1) :: ('m :: {countable,defaults}, 'm,  'd) op) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda> _. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. []))))))) \<approx>
    map_op projl projr (comp_op Some (\<lambda> _. []) (sink_buf_op (buf1 >> buf2>> buf3 >> buf4 >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))"
proof (coinduction arbitrary: buf1 buf2 buf3 buf4 buf5 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case 
  proof -
    have "\<exists>op2'. wstep (Inp pd x) (map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1 buf2 buf3 buf4 buf5. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. []))))))) \<and> op2xx = map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ pd x buf1)) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. [])))))))) op2'"
      if "pd \<notin> defaults"
      for x :: 'd
        and pd :: 'm
      using that by (intro exI conjI[rotated, OF wbc_base], force, force)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1 buf2 buf3 buf4 buf5. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. []))))))) \<and> op2xx = map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum (BENQ x2 (BHD x2 buf3) buf4) (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum (BTL x2 buf3) (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. [])))))))) op2'"
      if "x2 \<notin> defaults"
        and "buf3 x2 \<noteq> []"
      for x2 :: 'm
      using that 
      using that 
      apply -
      apply (intro exI conjI[rotated, OF wbc_base])
      apply force
      apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1 buf2 buf3 buf4 buf5. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. []))))))) \<and> op2xx = map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum (BTL pb buf4) (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum (BENQ pb (BHD pb buf4) buf5) (\<lambda>_. [])))))))) op2'"
      if "buf4 pb \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'm
      using that 
      apply -
      apply (intro exI conjI[rotated, OF wbc_base])
      apply force
      apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
      done
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1 buf2 buf3 buf4 buf5. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. []))))))) \<and> op2xx = map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum (BENQ pc (BHD pc buf1) buf2) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL pc buf1)) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. [])))))))) op2'"
      if "pc \<notin> defaults"
        and "buf1 pc \<noteq> []"
      for pc :: 'm
      using that by (intro exI conjI[rotated, OF wbc_base], force, force)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1 buf2 buf3 buf4 buf5. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. []))))))) \<and> op2xx = map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum (BTL x1 buf2) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum (BENQ x1 (BHD x1 buf2) buf3) (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. [])))))))) op2'"
      if "x1 \<notin> defaults"
        and "buf2 x1 \<noteq> []"
      for x1 :: 'm
      using that 
      apply -
      apply (intro exI conjI[rotated, OF wbc_base])
      apply force
      apply (metis (no_types, lifting) BAPPEND_BENQ_BHD BULK_BENQ_assoc Nitpick.rtranclp_unfold)
      done
    ultimately show ?thesis
      using SIM1 by (auto 0 0 elim !: step_aeq_op_elim step_acopy_op_elim step_transp_op_cases step_map_op_elim step_loop_op_elim step_comp_op_elim step_id_op_cases del: step_wstep intro!: step_wstep split: if_splits sum.splits)
  qed
next
  case SIM2
  then show ?case 
  proof -
    have "\<exists>op2'. wstep (Inp pa x) (map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. [])))))))) op2' \<and> wbisim_cong (\<lambda>op1xx op2xx. \<exists>buf1 buf2 buf3 buf4 buf5. op1xx = map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. [])) (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. []))) (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) \<C>) (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. []) (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>)))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (aeq_op (case_sum buf5 (\<lambda>_. []))))))) \<and> op2xx = map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)))) op2' (map_op projl projr (comp_op (Some::'a \<Rightarrow> _ option) (\<lambda>_. []) (sink_buf_op ((((BENQ pa x buf1 >> buf2) >> buf3) >> buf4) >> buf5)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>))))"
      if "(pa::'m) \<notin> defaults"
      for io' :: "('m + 'a, 'a + 'm, 'd) IO"
        and op'' :: "('m + 'a, 'a + 'm, 'd) op"
        and p :: 'm
        and x :: 'd
        and op1' :: "('m, 'a, 'd) op"
        and pa :: 'm
      using that by (intro exI conjI[rotated, OF wbc_base], force, (force del: step_wstep intro!: step_wstep))
    then show ?thesis
      using SIM2 by (elim exE step_sink_buf_op conjE step_aeq_op_elim step_acopy_op_elim step_transp_op_cases step_map_op_elim step_loop_op_elim step_comp_op_elim step_id_op_cases ; simp split: if_splits sum.splits ; hypsubst_thin ?)
  qed
qed

lemma F5:
  "((\<I> \<parallel> \<C>) \<bullet> map_op reassoc reassoc (\<X> \<parallel> \<I>) \<bullet> (\<I> \<parallel> \<Q>)) \<up> \<approx> ! \<bullet> \<exclamdown>"
  apply (rule wbisim_trans[rotated])
  apply (rule wbisim_scomp_op_cong)
  apply (rule bisim_wbisim)
  apply (rule sink_buf_op_sink)
  apply (rule wbisim_refl)
  unfolding feedback_op_def scomp_op_def pcomp_op_def
  using F5_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []"] apply force
  done

lemma F5'_gen:
  \<open>map_op projl projl (loop_op (case_sum (\<lambda>_. None) (\<lambda>p. if p \<in> defaults then None else Some (Inr p))) (case_sum undefined (\<lambda>_. []))
    (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (case_sum buf4 (\<lambda>_. [])))
      (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. []))
        (comp_op (\<lambda>_. None) (\<lambda>_. [])
          ((id_op buf1) :: ('a :: {countable,defaults}, 'a, 'b) op) \<C>)
        (map_op reassoc reassoc (comp_op (\<lambda>_. None) (\<lambda>_. [])
          (transp_op (case_sum buf3 (\<lambda>_. []))) \<I>))))
      (comp_op (\<lambda>_. None) (\<lambda>_. [])
        \<I>
        (map_op projl projr (comp_op Some (\<lambda>_. []) (aeq_op (case_sum buf5 (\<lambda>_. []))) \<I>))))))
  \<approx> map_op projl projr (comp_op Some (\<lambda>_. []) (!::('a, 0, 'b) op)
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<oslash> \<I>)::(0, 'a, 'b) op))\<close>
proof (coinduction arbitrary: buf1 buf2 buf3 buf4 buf5 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
    using SIM1 by (auto 0 0 elim!: step_map_op_elim step_loop_op_elim step_comp_op_elim step_id_op_cases step_acopy_op_elim step_transp_op_cases step_aeq_op_elim split: sum.splits if_splits)
    (force del: wbc_base intro!: wbc_base)+
next
  case SIM2
  then show ?case
    using SIM2 by (auto elim !: step_map_op_elim step_comp_op_elim step_sink_op step_id_op_cases split: if_splits sum.splits)
      (intro exI conjI[rotated, OF wbc_base], force, force del: step_wstep intro!: step_wstep)
qed

lemma F5':
  \<open>((\<I> \<parallel> \<C>) \<bullet> map_op reassoc reassoc (\<X> \<parallel> \<I>) \<bullet> (\<I> \<parallel> \<Q>')) \<up>
  \<approx> (!::('a :: {countable, defaults}, 0, 'b) op) \<bullet> (\<exclamdown>::(0, 'a, 'b) op)\<close>
  unfolding feedback_op_def scomp_op_def pcomp_op_def
  using F5'_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp


end