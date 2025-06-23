theory T3A1

imports
  "../BNA_Operators"
  "../Wstep_Composition_Left_Right"
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Proof against weak bisimulation\<close>

datatype (discs_sels) ('m, 'd) merge_op_aux' =
  merge_Read_aux' \<open>'m + 'm\<close> \<open>'d \<Rightarrow> 'm + 'm \<Rightarrow> 'd buf\<close> \<open>'m \<Rightarrow> 'd buf\<close>
  | merge_Write_aux' \<open>'m + 'm \<Rightarrow> 'd buf\<close> \<open>'m \<Rightarrow> 'd buf\<close> 'm 'd
  | merge_Silent_aux' \<open>'m + 'm \<Rightarrow> 'd buf\<close> \<open>'m \<Rightarrow> 'd buf\<close>

abbreviation eval_merge_op_aux' where
  \<open>eval_merge_op_aux' c aux \<equiv> (case aux of
    merge_Read_aux' p f buf' \<Rightarrow> Read p (\<lambda>x. c (f x) buf')
  | merge_Write_aux' buf buf' p x \<Rightarrow> Write (c buf buf') p x
  | merge_Silent_aux' buf buf' \<Rightarrow> Silent (c buf buf'))\<close>

corec merge_op' :: \<open>('m :: {countable, defaults} + 'm \<Rightarrow> 'd buf) \<Rightarrow> ('m \<Rightarrow> 'd buf) \<Rightarrow> ('m + 'm, 'm, 'd) op\<close> where
  \<open>merge_op' buf buf' = Choice (cimage (eval_merge_op_aux' merge_op') (cUn (cUn (cUn (cUn
    (cimage (\<lambda>p. merge_Read_aux' (Inl p) (\<lambda>x. BENQ (Inl p) x buf) buf') c\<UU>)
    (cimage (\<lambda>p. merge_Read_aux' (Inr p) (\<lambda>x. BENQ (Inr p) x buf) buf') c\<UU>))
    (cimage (\<lambda>p. merge_Write_aux' buf (BTL p buf') p (BHD p buf'))
      (cfilter (\<lambda>p. buf' p \<noteq> []) c\<UU>)))
    (cimage (\<lambda>p. merge_Silent_aux' (BTL (Inl p) buf) (BENQ p (BHD (Inl p) buf) buf'))
      (cfilter (\<lambda>p. buf (Inl p) \<noteq> []) c\<UU>)))
    (cimage (\<lambda>p. merge_Silent_aux' (BTL (Inr p) buf) (BENQ p (BHD (Inr p) buf) buf'))
      (cfilter (\<lambda>p. buf (Inr p) \<noteq> []) c\<UU>))))\<close>

lemma merge_op'_code:
  \<open>merge_op' buf buf' = Choice (cUn (cUn (cUn (cUn
    (cimage (\<lambda>p. Read (Inl p) (\<lambda>x. merge_op' (BENQ (Inl p) x buf) buf')) c\<UU>)
    (cimage (\<lambda>p. Read (Inr p) (\<lambda>x. merge_op' (BENQ (Inr p) x buf) buf')) c\<UU>))
    (cimage (\<lambda>p. Write (merge_op' buf (BTL p buf')) p (BHD p buf'))
      (cfilter (\<lambda>p. buf' p \<noteq> []) c\<UU>)))
    (cimage (\<lambda>p. Silent (merge_op' (BTL (Inl p) buf) (BENQ p (BHD (Inl p) buf) buf')))
      (cfilter (\<lambda>p. buf (Inl p) \<noteq> []) c\<UU>)))
    (cimage (\<lambda>p. Silent (merge_op' (BTL (Inr p) buf) (BENQ p (BHD (Inr p) buf) buf')))
      (cfilter (\<lambda>p. buf (Inr p) \<noteq> []) c\<UU>)))\<close>
  apply (subst merge_op'.code)
  apply (auto simp add: comp_def cset.map_comp o_def split: if_splits op.splits)
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI1)
     apply force
    apply auto
    done
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI2)
     apply (rule disjI1)
     apply force
    apply auto
    done
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI2)
     apply (rule disjI2)
     apply (rule disjI1)
     apply force
    apply auto
    done
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI2)
     apply (rule disjI2)
     apply (rule disjI2)
     apply (rule disjI1)
     apply force
    apply auto
    done
  subgoal
    apply (rule image_eqI[rotated])
     apply simp
     apply (rule disjI2)+
     apply force
    apply auto
    done
  done

lemma step_merge_op'_Inp_L:
  assumes \<open>step io (merge_op' buf buf') op\<close>
    and \<open>io = Inp (Inl p) x\<close>
  obtains \<open>op = merge_op' (BENQ (Inl p) x buf) buf'\<close> \<open>p \<notin> defaults\<close>
  using assms
  apply (subst (asm) merge_op'_code)
  by force

lemma step_merge_op'_Inp_R:
  assumes \<open>step io (merge_op' buf buf') op\<close>
    and \<open>io = Inp (Inr p) x\<close>
  obtains \<open>op = merge_op' (BENQ (Inr p) x buf) buf'\<close> \<open>p \<notin> defaults\<close>
  using assms
  apply (subst (asm) merge_op'_code)
  by force

lemma step_merge_op'_Out:
  assumes \<open>step io (merge_op' buf buf') op\<close>
    and \<open>io = Out p x\<close>
  obtains \<open>op = merge_op' buf (BTL p buf')\<close> \<open>buf' p \<noteq> []\<close> \<open>BHD p buf' = x\<close> \<open>p \<notin> defaults\<close>
  using assms
  apply (subst (asm) merge_op'_code)
  by auto

lemma step_merge_op'_Tau:
  assumes \<open>step io (merge_op' buf buf') op\<close>
    and \<open>io = Tau\<close>
  obtains p where \<open>op = merge_op' (BTL (Inl p) buf) (BENQ p (BHD (Inl p) buf) buf')\<close> \<open>buf (Inl p) \<noteq> []\<close> \<open>p \<notin> defaults\<close>
  |       p where \<open>op = merge_op' (BTL (Inr p) buf) (BENQ p (BHD (Inr p) buf) buf')\<close> \<open>buf (Inr p) \<noteq> []\<close> \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) merge_op'_code)
  apply auto
  by blast+

lemma step_merge_op'_elim:
  assumes \<open>step io (merge_op' buf buf') op\<close>
  obtains p x where \<open>io = Inp (Inl p) x\<close> \<open>op = merge_op' (BENQ (Inl p) x buf) buf'\<close> \<open>p \<notin> defaults\<close>
  |       p x where \<open>io = Inp (Inr p) x\<close> \<open>op = merge_op' (BENQ (Inr p) x buf) buf'\<close> \<open>p \<notin> defaults\<close>
  |       p x where \<open>io = Out p x\<close> \<open>op = merge_op' buf (BTL p buf')\<close> \<open>buf' p \<noteq> []\<close> \<open>BHD p buf' = x\<close> \<open>p \<notin> defaults\<close>
  |       p   where \<open>io = Tau\<close> \<open>op = merge_op' (BTL (Inl p) buf) (BENQ p (BHD (Inl p) buf) buf')\<close> \<open>buf (Inl p) \<noteq> []\<close> \<open>p \<notin> defaults\<close>
  |       p   where \<open>io = Tau\<close> \<open>op = merge_op' (BTL (Inr p) buf) (BENQ p (BHD (Inr p) buf) buf')\<close> \<open>buf (Inr p) \<noteq> []\<close> \<open>p \<notin> defaults\<close>
  apply atomize_elim
  using assms
  apply (subst (asm) merge_op'_code)
  by fastforce

lemma step_merge_op'_Read_L[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf'' = BENQ (Inl p) x buf \<Longrightarrow> buf''' = buf' \<Longrightarrow> step (Inp (Inl p) x) (merge_op' buf buf') (merge_op' buf'' buf''')\<close>
  apply (subst merge_op'_code)
  by fastforce

lemma step_merge_op'_Read_R[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf'' = BENQ (Inr p) x buf \<Longrightarrow> buf''' = buf' \<Longrightarrow> step (Inp (Inr p) x) (merge_op' buf buf') (merge_op' buf'' buf''')\<close>
  apply (subst merge_op'_code)
  by fastforce

lemma step_merge_op'_Write[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf'' = buf \<Longrightarrow> buf''' = BTL p buf' \<Longrightarrow> buf' p \<noteq> [] \<Longrightarrow> BHD p buf' = x \<Longrightarrow>
  step (Out p x) (merge_op' buf buf') (merge_op' buf'' buf''')\<close>
  apply (subst merge_op'_code)
  by fastforce

lemma step_merge_op'_Silent_L[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf'' = BTL (Inl p) buf \<Longrightarrow> buf''' = (BENQ p (BHD (Inl p) buf) buf') \<Longrightarrow> buf (Inl p) \<noteq> [] \<Longrightarrow>
  step Tau (merge_op' buf buf') (merge_op' buf'' buf''')\<close>
  apply (subst merge_op'_code)
  by fastforce

lemma step_merge_op'_Silent_R[intro!]:
  \<open>p \<notin> defaults \<Longrightarrow> buf'' = BTL (Inr p) buf \<Longrightarrow> buf''' = (BENQ p (BHD (Inr p) buf) buf') \<Longrightarrow> buf (Inr p) \<noteq> [] \<Longrightarrow>
  step Tau (merge_op' buf buf') (merge_op' buf'' buf''')\<close>
  apply (subst merge_op'_code)
  by fastforce

lemma choices_merge_op'[simp]:
  \<open>choices (merge_op' buf buf') = cUn (cUn (cUn (cUn
    (cUnion (cimage choices (cimage (\<lambda>p. Read (Inl p) (\<lambda>x. merge_op' (BENQ (Inl p) x buf) buf')) c\<UU>)))
    (cUnion (cimage choices (cimage (\<lambda>p. Read (Inr p) (\<lambda>x. merge_op' (BENQ (Inr p) x buf) buf')) c\<UU>))))
    (cUnion (cimage choices (cimage (\<lambda>p. Write (merge_op' buf (BTL p buf')) p (BHD p buf'))
      (cfilter (\<lambda>p. buf' p \<noteq> []) c\<UU>)))))
    (cUnion (cimage choices (cimage (\<lambda>p. Silent (merge_op' (BTL (Inl p) buf) (BENQ p (BHD (Inl p) buf) buf')))
      (cfilter (\<lambda>p. buf (Inl p) \<noteq> []) c\<UU>)))))
    (cUnion (cimage choices (cimage (\<lambda>p. Silent (merge_op' (BTL (Inr p) buf) (BENQ p (BHD (Inr p) buf) buf')))
      (cfilter (\<lambda>p. buf (Inr p) \<noteq> []) c\<UU>))))\<close>
  apply (subst merge_op'_code)
  by simp

lemma merge_op'_reads:
  \<open>sub_op (Read p f) (merge_op' buf buf') n \<Longrightarrow> p \<in> UNIV - defaults\<close>
proof (induct p \<open>merge_op' buf buf'\<close> arbitrary: buf buf' rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case by (subst (asm) merge_op'_code, simp)
next
  case (Read2 p p' f x d g)
  then show ?case by (subst (asm) merge_op'_code, simp)
next
  case (Write p p' op' x d g)
  then show ?case by (subst (asm) merge_op'_code, simp)
next
  case (Silent p op' d)
  then show ?case by (subst (asm) merge_op'_code, simp)
next
  case (Choice p ops d g)
  then show ?case by (subst (asm) (2) merge_op'_code, simp; force)
qed

lemma inputs_merge_op'[intro]:
  \<open>inputs (merge_op' buf buf') \<subseteq> UNIV - defaults\<close>
  by (intro subsetI, metis merge_op'_reads inputs_sub_op_Read)

lemma merge_op'_writes:
  \<open>sub_op (Write op p x) (merge_op' buf buf') n \<Longrightarrow> p \<in> UNIV - defaults\<close>
proof (induct p \<open>merge_op' buf buf'\<close> arbitrary: buf buf' rule: sub_op_Write_induct)
  case (Read p p' f x op2 y d)
  then show ?case by (subst (asm) merge_op'_code, simp)
next
  case (Write1 p p' op' x op2 y d)
  then show ?case by (subst (asm) merge_op'_code, simp)
next
  case (Silent p op' op2 y d)
  then show ?case by (subst (asm) merge_op'_code, simp)
next
  case (Choice p op2 y d ops)
  then show ?case by (subst (asm) (2) merge_op'_code, simp; force)
next
  case (Write2 p op' x)
  then show ?case by (subst (asm) merge_op'_code, simp)
qed

lemma outputs_merge_op'[intro]:
  \<open>outputs (merge_op' buf buf') \<subseteq> UNIV - defaults\<close>
  by (intro subsetI, metis merge_op'_writes outputs_sub_op_Write)

lemma merge_op'_merge_op_id_op_gen:
  \<open>merge_op' (case_sum buf1 buf1') (buf2 >> buf3)
  \<approx> map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))\<close>
proof (coinduction arbitrary: buf1 buf1' buf2 buf3 rule: wbisim_coinduct_upto'')
  case SIM1
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp (Inl p) x) (map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf3. op1 = merge_op' (case_sum buf1 buf1') (buf2 >> buf3) \<and> op2 = map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) (merge_op' (case_sum (BENQ p x buf1) buf1') (buf2 >> buf3)) op2'"
      if "p \<notin> defaults"
      for p :: 'a
        and x :: 'b
      using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. wstep (Inp (Inr p) x) (map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf3. op1 = merge_op' (case_sum buf1 buf1') (buf2 >> buf3) \<and> op2 = map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) (merge_op' (case_sum buf1 (BENQ p x buf1')) (buf2 >> buf3)) op2'"
      if "p \<notin> defaults"
      for p :: 'a
        and x :: 'b
      using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf2)) (map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf3. op1 = merge_op' (case_sum buf1 buf1') (buf2 >> buf3) \<and> op2 = map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) (merge_op' (case_sum buf1 buf1') (BTL p buf2 >> buf3)) op2'"
      if "buf2 p \<noteq> []"
        and "p \<notin> defaults"
        and "buf3 p = []"
      for p :: 'a
      using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. wstep (Out p (BHD p buf3)) (map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf3. op1 = merge_op' (case_sum buf1 buf1') (buf2 >> buf3) \<and> op2 = map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) (merge_op' (case_sum buf1 buf1') (buf2 >> BTL p buf3)) op2'"
      if "p \<notin> defaults"
        and "buf3 p \<noteq> []"
      for p :: 'a
      using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf3. op1 = merge_op' (case_sum buf1 buf1') (buf2 >> buf3) \<and> op2 = map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) (merge_op' (case_sum (BTL p buf1) buf1') (BENQ p (BHD p buf1) buf2 >> buf3)) op2'"
      if "buf1 p \<noteq> []"
        and "p \<notin> defaults"
      for p :: 'a
      using that
      apply (intro exI conjI[rotated, OF wbc_base])
       apply blast
      by (metis case_sum_BHD_L case_sum_BTL_L sum.simps(5) step_Tau_closure_single step_Tau_comp_op_L_alt
          step_merge_op_Write_L step_star_map_op)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf3. op1 = merge_op' (case_sum buf1 buf1') (buf2 >> buf3) \<and> op2 = map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) (merge_op' (case_sum buf1 (BTL p buf1')) (BENQ p (BHD p buf1') buf2 >> buf3)) op2'"
      if "buf1' p \<noteq> []"
        and "p \<notin> defaults"
      for p :: 'a
      using that
      apply (intro exI conjI[rotated, OF wbc_base])
       apply blast
      by fastforce
    ultimately show ?thesis
      using SIM1 by (auto elim!: step_merge_op'_elim split: if_splits)
  qed
next
  case SIM2
  then show ?case
  proof -
    have "\<exists>op2'. wstep (Inp (Inl pa) xa) (merge_op' (case_sum buf1 buf1') (buf2 >> buf3)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf3. op1 = merge_op' (case_sum buf1 buf1') (buf2 >> buf3) \<and> op2 = map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) op2' (map_op projl projr (comp_op Some buf2 (merge_op (case_sum (BENQ pa xa buf1) buf1')) (id_op buf3)))"
      if "pa \<notin> defaults"
      for pa :: 'a
        and xa :: 'b
      using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. wstep (Inp (Inr pa) xa) (merge_op' (case_sum buf1 buf1') (buf2 >> buf3)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf3. op1 = merge_op' (case_sum buf1 buf1') (buf2 >> buf3) \<and> op2 = map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) op2' (map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 (BENQ pa xa buf1'))) (id_op buf3)))"
      if "pa \<notin> defaults"
      for pa :: 'a
        and xa :: 'b
      using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. wstep (Out pa (BHD pa buf3)) (merge_op' (case_sum buf1 buf1') (buf2 >> buf3)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf3. op1 = merge_op' (case_sum buf1 buf1') (buf2 >> buf3) \<and> op2 = map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) op2' (map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op (BTL pa buf3))))"
      if "pa \<notin> defaults"
        and "buf3 pa \<noteq> []"
      for pa :: 'a
      using that by (fastforce del: wbc_base intro: wbc_base)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op' (case_sum buf1 buf1') (buf2 >> buf3)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf3. op1 = merge_op' (case_sum buf1 buf1') (buf2 >> buf3) \<and> op2 = map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) op2' (map_op projl projr (comp_op Some (BENQ pa (BHD pa buf1) buf2) (merge_op (case_sum (BTL pa buf1) buf1')) (id_op buf3)))"
      if "buf1 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that
      by (intro exI conjI[rotated, OF wbc_base], blast, simp add: step_Tau_closure_single step_merge_op'_Silent_L)
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op' (case_sum buf1 buf1') (buf2 >> buf3)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf3. op1 = merge_op' (case_sum buf1 buf1') (buf2 >> buf3) \<and> op2 = map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) op2' (map_op projl projr (comp_op Some (BENQ pa (BHD pa buf1') buf2) (merge_op (case_sum buf1 (BTL pa buf1'))) (id_op buf3)))"
      if "buf1' pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) auto
    moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (merge_op' (case_sum buf1 buf1') (buf2 >> buf3)) op2' \<and> wbisim_cong (\<lambda>op1 op2. \<exists>buf1 buf1' buf2 buf3. op1 = merge_op' (case_sum buf1 buf1') (buf2 >> buf3) \<and> op2 = map_op projl projr (comp_op Some buf2 (merge_op (case_sum buf1 buf1')) (id_op buf3))) op2' (map_op projl projr (comp_op Some (BTL pa buf2) (merge_op (case_sum buf1 buf1')) (id_op (BENQ pa (BHD pa buf2) buf3))))"
      if "buf2 pa \<noteq> []"
        and "pa \<notin> defaults"
      for pa :: 'a
      using that by (intro exI conjI[rotated, OF wbc_base]) auto
    ultimately show ?thesis
      using SIM2 by (auto elim!: step_map_op_elim step_comp_op_elim step_merge_op_elim step_id_op_cases)
  qed
qed

lemma merge_op'_merge_op_id_op:
  \<open>merge_op' (\<lambda>_. []) (\<lambda>_. []) \<approx> \<V>'\<close>
  unfolding scomp_op_def
  using merge_op'_merge_op_id_op_gen[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

(* TODO move *)
simproc_setup num1_eq (\<open>x :: 1\<close>) =
  \<open>K (K (fn ct =>
    if Thm.term_of ct aconv @{term \<open>1 :: 1\<close>} then NONE
    else SOME (mk_meta_eq @{thm num1_eq1})))\<close>

lemma wstep_Inp_Inl_Inl:
  assumes \<open>wstep (Inp (Inl (Inl 1)) (Suc 0)) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (\<V> :: (1 + 1, 1, nat) op)) (merge_op' (\<lambda>_. []) (\<lambda>_. []))))) op\<close>
  obtains \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 1 (\<lambda>_. []))) \<V>) (merge_op' (\<lambda>_. []) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 1 (\<lambda>_. [])))))\<close>
  apply atomize_elim
  using assms
  unfolding wstep_def
  apply simp
  apply (erule relcomppE)+
  apply (erule converse_rtranclpE)+
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L)[2]
   apply (erule converse_rtranclpE)
    apply fast
   apply (erule converse_rtranclpE)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp add: BENQ_diff_access)
  apply (erule converse_rtranclpE)
   apply fast
  by (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim)

lemma wstep_Inp_Inl_Inr1:
  assumes \<open>wstep (Inp (Inl (Inr 1)) 2) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 (Suc 0) (\<lambda>_. []))) (\<V> :: (1 + 1, 1, nat) op)) (merge_op' (\<lambda>_. []) (\<lambda>_. []))))) op\<close>
  obtains \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 1 (\<lambda>_. []))) (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op' (\<lambda>_. []) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 1 (\<lambda>_. []))) \<V>) (merge_op' (\<lambda>_. []) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 1 (\<lambda>_. []))) \<V>) (merge_op' (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ 1 1 (\<lambda>_. []))) \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op' (\<lambda>_. []) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op' (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 1 (BENQ 1 2 (\<lambda>_. []))))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op' (\<lambda>_. []) (BENQ 1 1 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 1 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (BENQ 1 1 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 2 (BENQ 1 1 (\<lambda>_. []))))))\<close>
  apply atomize_elim
  using assms
  unfolding wstep_def
  apply simp
  apply (erule relcomppE)+
  apply (erule converse_rtranclpE)+
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[2]
     apply (erule converse_rtranclpE)
        apply fast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (erule converse_rtranclpE)
        apply (metis case_sum_BENQ_L case_sum_BENQ_R surjective_sum)
        apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
     apply (erule converse_rtranclpE)
      apply (smt (verit, ccfv_threshold) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L surjective_sum)
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
       apply (smt (verit, ccfv_threshold) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L surjective_sum)
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
     apply (erule converse_rtranclpE)
      apply (smt (verit) BENQ_diff_access BHD_BENQ_empty BTL_BENQ_empty Inr_Inl_False case_sum_BENQ_L case_sum_BENQ_R surjective_sum)
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
  apply (smt (verit, del_insts) BENQ_diff_access BHD_BENQ_empty BTL_BENQ_empty Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inr_Inl_False)
     apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inr_Inl_False)
    apply (erule converse_rtranclpE)
     apply fast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (erule converse_rtranclpE)
     apply fast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (erule converse_rtranclpE)
       apply fast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
   apply (erule converse_rtranclpE)
    apply fast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (erule converse_rtranclpE)
     apply fast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
     apply (erule converse_rtranclpE)
  apply (metis (no_types, lifting) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_L case_sum_BHD_R case_sum_BTL_R
      surjective_sum)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
  apply (smt (verit, ccfv_threshold) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_L case_sum_BENQ_R case_sum_inject
      surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inr_Inl_False)
     apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inr_Inl_False)
       apply (erule converse_rtranclpE)
  apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_L case_sum_BENQ_R case_sum_if
      surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
           apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inr_not_Inl)
           apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inr_not_Inl)
         apply (erule converse_rtranclpE)
  apply (smt (verit) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L case_sum_BENQ_R
      surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
          apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
         apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
        apply (erule converse_rtranclpE)
  apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
          apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
         apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
        apply (erule converse_rtranclpE)
  apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_L case_sum_BENQ_R old.sum.simps(6)
      surjective_sum)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
           apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
  apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
         apply (metis (no_types, lifting) BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
  apply (metis (no_types, lifting) BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
        apply (erule converse_rtranclpE)
  apply (metis (no_types, lifting) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_L case_sum_BENQ_R case_sum_inject
      surjective_sum)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
  apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_L case_sum_BENQ_R case_sum_if
      surjective_sum)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
         apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
        apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (erule converse_rtranclpE)
  apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
         apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (erule converse_rtranclpE)
       apply (meson BENQ_diff_access Inr_Inl_False)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (erule converse_rtranclpE)
      apply force
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (erule converse_rtranclpE)
       apply blast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (erule converse_rtranclpE)
        apply (metis (no_types, lifting) case_sum_BENQ_L case_sum_BENQ_R surjective_sum)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
         apply blast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
  apply blast
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
  apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
  apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
  apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
        apply (erule converse_rtranclpE)
       apply force
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
       apply force
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
       apply force
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
      apply force
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
      apply force
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
      apply force
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
      apply force
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
     apply (meson BENQ_diff_access Inl_Inr_False)
    apply (meson BENQ_diff_access Inl_Inr_False)
        apply (erule converse_rtranclpE)
     apply (meson BENQ_diff_access Inl_Inr_False)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (erule converse_rtranclpE)
     apply blast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
     apply (erule converse_rtranclpE)
  apply (smt (verit) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L case_sum_BENQ_R case_sum_BTL_L
      surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
  apply (smt (verit) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L case_sum_BENQ_R
      surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
         apply (metis BTL_BENQ_empty BTL_access BTL_diff_access sum.distinct(1))
        apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
      apply (erule converse_rtranclpE)
  apply (smt (z3) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L case_sum_BENQ_R case_sum_BTL_L
      surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
        apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (erule converse_rtranclpE)
  apply (smt (z3) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L case_sum_BENQ_R case_sum_BTL_L
      surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
        apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
        apply (simp add: BENQ_diff_access BTL_access BTL_diff_access)
       apply (metis (no_types, lifting) BTL_BENQ_empty BTL_access BTL_diff_access sum.distinct(1))
       apply (erule converse_rtranclpE)
  apply (smt (verit, best) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L case_sum_BENQ_R
      case_sum_BTL_L surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (erule converse_rtranclpE)
  apply (smt (verit) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L case_sum_BENQ_R
      surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
        apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (erule converse_rtranclpE)
  apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (erule converse_rtranclpE)
  apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
      apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (erule converse_rtranclpE)
  apply (smt (verit) BHD_BENQ_empty BHD_def BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L case_sum_BENQ_R
      case_sum_BTL_L surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (erule converse_rtranclpE)
     apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (erule converse_rtranclpE)
      apply (metis case_sum_BENQ_L case_sum_BENQ_R surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
       apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
       apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
  apply (smt (verit, ccfv_threshold) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
  apply (smt (verit) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L case_sum_BENQ_R
      surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
     apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
      apply (erule converse_rtranclpE)
     apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
     apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
     apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
    apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
     apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
      apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
  apply (smt (verit, best) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L case_sum_BENQ_R
      case_sum_BTL_L surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
  apply (smt (verit) BHD_BENQ_empty BHD_def BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L case_sum_BENQ_R
      case_sum_BTL_L surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
      apply (erule converse_rtranclpE)
      apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
      apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
     apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
     apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
     apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
    apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
    apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
    apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
      apply (erule converse_rtranclpE)
    apply force
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[2]
  apply (erule converse_rtranclpE)+
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[2]
      apply (erule converse_rtranclpE)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[2]
      apply (erule converse_rtranclpE)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[2]
  apply (erule converse_rtranclpE)+
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
   apply (erule converse_rtranclpE)
  apply hypsubst_thin
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
  apply (smt (z3) BENQ_diff_access BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_L case_sum_BENQ_R case_sum_BTL_L
      surjective_sum)
       apply (simp add: BENQ_diff_access)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[3]
   apply hypsubst_thin
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
          apply (metis BENQ_diff_access BTL_BENQ_empty BTL_access Inr_not_Inl)
         apply (erule converse_rtranclpE)
  apply (smt (z3) BENQ_diff_access BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_L case_sum_BENQ_R case_sum_BTL_L
      surjective_sum)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
           apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
         apply (erule converse_rtranclpE)
  apply (smt (z3) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L case_sum_BENQ_R case_sum_BTL_L
      surjective_sum)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
           apply (simp add: BENQ_diff_access BTL_access)
         apply (erule converse_rtranclpE)
  apply (smt (verit) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_R case_sum_BHD_L case_sum_BTL_L
      surjective_sum)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
           apply (metis (no_types, lifting) BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
           apply (metis (no_types, lifting) BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
         apply (erule converse_rtranclpE)
  apply (smt (z3) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L case_sum_BENQ_R
      case_sum_BTL_L surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[3]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
  apply (erule converse_rtranclpE)
  apply (smt (verit) BHD_BENQ_empty BHD_def BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_R
      case_sum_BTL_L surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[3]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
  apply (erule converse_rtranclpE)
  apply (smt (verit, best) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L case_sum_BENQ_R
      case_sum_BTL_L surjective_sum)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
         apply (metis BTL_BENQ_empty BTL_access BTL_diff_access sum.distinct(1))
        apply (erule converse_rtranclpE)
  apply (smt (verit) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L case_sum_BENQ_R
      case_sum_BTL_L surjective_sum)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
         apply (meson BENQ_diff_access sum.simps(4))
        apply (erule converse_rtranclpE)
  apply (smt (verit) BHD_BENQ_empty BHD_def BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L
      case_sum_BENQ_R case_sum_BTL_L surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
        apply (erule converse_rtranclpE)
        apply (metis case_sum_BENQ_L case_sum_BENQ_R surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
        apply blast
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
        apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
  apply (metis (no_types, lifting) BENQ_diff_access BHD_BENQ_empty BHD_def BTL_BENQ_empty Inl_Inr_False
      case_sum_BENQ_L case_sum_BTL_R surjective_sum)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
        apply (erule converse_rtranclpE)
  apply (smt (verit, best) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[3]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
      apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
        apply (erule converse_rtranclpE)
      apply blast
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
        apply (erule converse_rtranclpE)
       apply blast
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
        apply (erule converse_rtranclpE)
        apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[3]
     apply (meson BENQ_diff_access sum.distinct(1))
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
          apply (meson BENQ_diff_access sum.distinct(2))
        apply (erule converse_rtranclpE)
          apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
          apply (erule converse_rtranclpE)
  apply (smt (verit, best) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L case_sum_BENQ_R
      case_sum_BTL_L surjective_sum)
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
          apply (erule converse_rtranclpE)
  apply (smt (verit) BHD_BENQ_empty BHD_def BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L
      case_sum_BENQ_R case_sum_BTL_L surjective_sum)
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
          apply (erule converse_rtranclpE)
          apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
          apply (erule converse_rtranclpE)
          apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
          apply (erule converse_rtranclpE)
         apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
          apply (erule converse_rtranclpE)
         apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
          apply (erule converse_rtranclpE)
         apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (meson BENQ_diff_access sum.distinct(1))
      apply (meson BENQ_diff_access sum.distinct(1))
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
     apply (erule converse_rtranclpE)
      apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
     apply (erule converse_rtranclpE)
      apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
     apply (erule converse_rtranclpE)
      apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (meson BENQ_diff_access sum.distinct(1))
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
  apply (rotate_tac 20)
  apply (erule converse_rtranclpE)
   apply hypsubst_thin
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
  apply (erule converse_rtranclpE)
       apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
  apply (erule converse_rtranclpE)
        apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
  apply (smt (verit, best) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access case_sum_BENQ_L case_sum_BENQ_R
      case_sum_BTL_L surjective_sum)
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
  apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False
      case_sum_BENQ_L case_sum_BENQ_R surjective_sum)
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
        apply (erule converse_rtranclpE)
        apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
        apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
       apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
       apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
       apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
       apply (meson BENQ_diff_access sum.distinct(1))
        apply (erule converse_rtranclpE)
     apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
        apply (erule converse_rtranclpE)
     apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (erule converse_rtranclpE)
     apply blast
         apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (erule converse_rtranclpE)
     apply blast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
   apply (meson BENQ_diff_access sum.distinct(1))
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
   apply (rotate_tac 20)
    apply (erule converse_rtranclpE)
    apply hypsubst_thin
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
    apply (erule converse_rtranclpE)
      apply blast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (erule converse_rtranclpE)
      apply blast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (erule converse_rtranclpE)
      apply blast
  apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R simp add: BENQ_diff_access BTL_access)[1]
    apply (meson BENQ_diff_access sum.distinct(1))
    apply (elim conjE step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim; hypsubst_thin?; simp; hypsubst_thin?)
  apply (rotate_tac 20)
    apply (erule converse_rtranclpE)
    apply (meson BENQ_diff_access sum.distinct(1))
    apply (meson BENQ_diff_access sum.distinct(1))
  done

lemma wstep_Inp_Inl_Inr2:
  assumes \<open>wstep (Inp (Inl (Inr 1)) 2) (map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 (Suc 0) (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (\<V> :: (1 + 1, 1, nat) op)) (merge_op' (\<lambda>_. []) (\<lambda>_. []))))) op\<close>
  obtains \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op' (\<lambda>_. []) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op' (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 1 (BENQ 1 2 (\<lambda>_. []))))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op' (\<lambda>_. []) (BENQ 1 1 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 1 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (BENQ 1 1 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 2 (BENQ 1 1 (\<lambda>_. []))))))\<close>
  apply atomize_elim
  using assms
  unfolding wstep_def
  apply simp
  apply (erule relcomppE)+
  apply (erule converse_rtranclpE)+
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[3]
       apply (erule converse_rtranclpE)
        apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (erule converse_rtranclpE)
  apply (metis (no_types, lifting) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False
      case_sum_BENQ_L case_sum_BENQ_R surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
           apply (metis BENQ_diff_access BTL_BENQ_empty BTL_access sum.distinct(2))
       apply (erule converse_rtranclpE)
  apply (smt (verit) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
         apply (erule converse_rtranclpE)
  apply (smt (z3) BENQ_diff_access BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_L case_sum_BENQ_R
      case_sum_BTL_L surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
            apply (simp add: BENQ_diff_access BTL_access)
           apply (erule converse_rtranclpE)
  apply (smt (z3) BENQ_diff_access BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_L case_sum_BENQ_R
      case_sum_BTL_L surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
            apply (metis BTL_BENQ_empty case_sum_BENQ_R case_sum_BTL_L surjective_sum)
  apply (metis BTL_BENQ_empty case_sum_BENQ_R case_sum_BTL_L surjective_sum)
           apply (erule converse_rtranclpE)
  apply (smt (z3) BENQ_diff_access BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_L case_sum_BENQ_R
      case_sum_BTL_L surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
           apply (erule converse_rtranclpE)
  apply (smt (verit, best) BENQ_diff_access BHD_BENQ_empty BTL_BENQ_empty Inl_Inr_False case_sum_BHD_L
      case_sum_BHD_R case_sum_BTL_L case_sum_BTL_R surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BENQ_diff_access BTL_BENQ_empty sum.simps(4))
           apply (metis BENQ_diff_access BTL_BENQ_empty sum.simps(4))
          apply (metis BENQ_diff_access BTL_BENQ_empty sum.distinct(2))
  apply (erule converse_rtranclpE)
  apply (metis (no_types, lifting) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_R case_sum_BHD_L
      case_sum_BTL_L surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
  apply (metis (no_types, lifting) BTL_BENQ_empty case_sum_BENQ_R case_sum_BTL_L case_sum_inject
      surjective_sum)
         apply (erule converse_rtranclpE)
  apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty case_sum_BENQ_R case_sum_BHD_L
      case_sum_BTL_L surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
          apply (meson BENQ_diff_access sum.distinct(2))
         apply (erule converse_rtranclpE)
  apply (smt (verit) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
        apply (meson BENQ_diff_access sum.distinct(1))
    apply (erule converse_rtranclpE)
     apply (simp add: BENQ_diff_access)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (erule converse_rtranclpE)
    apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (erule converse_rtranclpE)
    apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
         apply (metis BENQ_diff_access BTL_BENQ_empty Inr_not_Inl)
       apply (erule converse_rtranclpE)
    apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
         apply (simp add: BENQ_diff_access)
        apply (metis BENQ_diff_access BTL_BENQ_empty sum.distinct(2))
           apply (erule converse_rtranclpE)
    apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
           apply (erule converse_rtranclpE)
    apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
    apply (metis (no_types, lifting) BTL_BENQ_empty BTL_access BTL_diff_access sum.distinct(1))
        apply (smt (verit) BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (simp add: BENQ_diff_access BTL_access)
      apply (metis BENQ_diff_access BTL_BENQ_empty Inr_not_Inl)
     apply (meson BENQ_diff_access sum.simps(4))
           apply (erule converse_rtranclpE)
     apply (simp add: BENQ_diff_access)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
           apply (erule converse_rtranclpE)
      apply (simp add: BENQ_diff_access)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
           apply (erule converse_rtranclpE)
      apply (simp add: BENQ_diff_access)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
     apply (simp add: BENQ_diff_access)
    apply (metis BENQ_diff_access BTL_BENQ_empty sum.simps(4))
      apply (meson BENQ_diff_access sum.distinct(1))
    apply (erule converse_rtranclpE)
    apply blast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
    apply (erule converse_rtranclpE)
        apply blast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
          apply (metis BENQ_diff_access sum.distinct(1))
    apply (erule converse_rtranclpE)
          apply blast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
          apply (erule converse_rtranclpE)
    apply (metis (no_types, lifting) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
           apply (metis BENQ_diff_access BTL_BENQ_empty BTL_access sum.distinct(2))
          apply (erule converse_rtranclpE)
    apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
          apply (erule converse_rtranclpE)
    apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
          apply (erule converse_rtranclpE)
    apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
         apply (metis BENQ_diff_access BTL_BENQ_empty sum.simps(4))
          apply (erule converse_rtranclpE)
         apply blast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
         apply (meson BENQ_diff_access sum.simps(4))
        apply (erule converse_rtranclpE)
         apply blast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
         apply (meson BENQ_diff_access sum.simps(4))
        apply (erule converse_rtranclpE)
         apply blast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (meson BENQ_diff_access sum.simps(3))
         apply (meson BENQ_diff_access sum.simps(3))
        apply (erule converse_rtranclpE)
      apply blast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
        apply (erule converse_rtranclpE)
       apply blast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
         apply (meson BENQ_diff_access sum.simps(4))
        apply (erule converse_rtranclpE)
       apply blast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
         apply (meson BENQ_diff_access sum.simps(4))
        apply (erule converse_rtranclpE)
       apply blast
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
         apply (meson BENQ_diff_access sum.simps(3))
         apply (meson BENQ_diff_access sum.simps(3))
        apply (meson BENQ_diff_access sum.distinct(1))
    apply (rotate_tac 2)
    apply (erule converse_rtranclpE)
     apply hypsubst_thin
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
     apply (erule converse_rtranclpE)
      apply blast
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
     apply (erule converse_rtranclpE)
         apply blast
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
         apply (meson BENQ_diff_access sum.simps(4))
     apply (erule converse_rtranclpE)
           apply blast
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
     apply (erule converse_rtranclpE)
    apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
            apply (simp add: BENQ_diff_access BTL_access)
          apply (erule converse_rtranclpE)
    apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
          apply (erule converse_rtranclpE)
    apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
  apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
          apply (erule converse_rtranclpE)
    apply (smt (verit, del_insts) BHD_BENQ_empty BTL_BENQ_empty BTL_diff_access Inl_Inr_False case_sum_BENQ_L
      case_sum_BENQ_R surjective_sum)
  apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
             apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
         apply (metis BENQ_diff_access BTL_BENQ_empty Inr_Inl_False)
          apply (erule converse_rtranclpE)
  apply blast
  apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
         apply (meson BENQ_diff_access sum.simps(4))
        apply (erule converse_rtranclpE)
         apply blast
  apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
         apply (meson BENQ_diff_access sum.simps(4))
        apply (erule converse_rtranclpE)
         apply blast
  apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (meson BENQ_diff_access sum.simps(3))
         apply (meson BENQ_diff_access sum.simps(3))
        apply (erule converse_rtranclpE)
      apply blast
  apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
        apply (erule converse_rtranclpE)
       apply blast
  apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
         apply (meson BENQ_diff_access sum.simps(4))
        apply (erule converse_rtranclpE)
       apply blast
  apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
         apply (meson BENQ_diff_access sum.simps(4))
        apply (erule converse_rtranclpE)
       apply blast
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (meson BENQ_diff_access sum.simps(3))
       apply (meson BENQ_diff_access sum.simps(3))
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
    apply (rotate_tac 15)
    apply (erule converse_rtranclpE)
     apply hypsubst_thin
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
    apply (erule converse_rtranclpE)
      apply blast
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
    apply (erule converse_rtranclpE)
       apply blast
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
         apply (meson BENQ_diff_access sum.simps(4))
    apply (erule converse_rtranclpE)
       apply blast
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
         apply (meson BENQ_diff_access sum.simps(4))
    apply (erule converse_rtranclpE)
       apply blast
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (meson BENQ_diff_access sum.simps(3))
      apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (meson BENQ_diff_access sum.simps(3))
  apply (meson BENQ_diff_access sum.simps(3))
  done

lemma wstep_Inp_Inl_Inr3:
  assumes \<open>wstep (Inp (Inl (Inr 1)) 2) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (\<V> :: (1 + 1, 1, nat) op)) (merge_op' (case_sum (BENQ 1 (Suc 0) (\<lambda>_. [])) (\<lambda>_. [])) (\<lambda>_. []))))) op\<close>
  obtains \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op' (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (BENQ 1 1 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))) (\<lambda>_. []))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (BENQ 1 1 (\<lambda>_. [])) (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 1 (BENQ 1 2 (\<lambda>_. []))))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op' (\<lambda>_. []) (BENQ 1 1 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 1 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (BENQ 1 1 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 2 (BENQ 1 1 (\<lambda>_. []))))))\<close>
  apply atomize_elim
  using assms
  unfolding wstep_def
  apply simp
  apply (erule relcomppE)+
  apply (erule converse_rtranclpE)+
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[3]
   apply (erule converse_rtranclpE)
    apply fast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
    apply (meson BENQ_diff_access sum.distinct(2))
   apply (erule converse_rtranclpE)
          apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
   apply (erule converse_rtranclpE)
  apply (metis (no_types, lifting) BENQ_diff_access BHD_BENQ_empty BHD_def BTL_BENQ_empty Inl_Inr_False
      case_sum_BENQ_R case_sum_BTL_L surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
           apply (simp add: BENQ_diff_access BTL_access)
   apply (erule converse_rtranclpE)
  apply (smt (verit) BENQ_diff_access BHD_BENQ_empty BHD_def BTL_BENQ_empty Inl_Inr_False case_sum_BENQ_R
      case_sum_BTL_L surjective_sum)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
   apply (erule converse_rtranclpE)
          apply (simp add: BENQ_diff_access)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
   apply (erule converse_rtranclpE)
           apply (simp add: BENQ_diff_access)
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
       apply (metis BTL_BENQ_empty BTL_access BTL_diff_access Inl_Inr_False)
   apply (erule converse_rtranclpE)
         apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
    apply (meson BENQ_diff_access sum.distinct(2))
   apply (erule converse_rtranclpE)
         apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
         apply (meson BENQ_diff_access sum.distinct(2))
   apply (erule converse_rtranclpE)
         apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (meson BENQ_diff_access sum.distinct(1))
      apply (meson BENQ_diff_access sum.distinct(1))
   apply (erule converse_rtranclpE)
      apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
   apply (erule converse_rtranclpE)
       apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (meson BENQ_diff_access sum.distinct(2))
      apply (erule converse_rtranclpE)
       apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (meson BENQ_diff_access sum.distinct(2))
      apply (erule converse_rtranclpE)
       apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
      apply (meson BENQ_diff_access sum.distinct(1))
      apply (meson BENQ_diff_access sum.distinct(1))
   apply (rotate_tac 2)
   apply (erule converse_rtranclpE)
  apply hypsubst_thin
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
   apply (erule converse_rtranclpE)
     apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
   apply (erule converse_rtranclpE)
      apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (meson BENQ_diff_access sum.distinct(2))
   apply (erule converse_rtranclpE)
      apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
       apply (meson BENQ_diff_access sum.distinct(2))
   apply (erule converse_rtranclpE)
      apply blast
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
      apply (meson BENQ_diff_access sum.distinct(1))
       apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
  apply (rotate_tac 2)
  apply (erule converse_rtranclpE)
      apply (meson BENQ_diff_access sum.distinct(1))
      apply (meson BENQ_diff_access sum.distinct(1))
  done

lemma wstep_Inp_Inl_Inr4:
  assumes \<open>wstep (Inp (Inl (Inr 1)) 2) (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (\<V> :: (1 + 1, 1, nat) op)) (merge_op' (\<lambda>_. []) (BENQ 1 (Suc 0) (\<lambda>_. [])))))) op\<close>
  obtains \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. [])))) (merge_op' (\<lambda>_. []) (BENQ 1 1 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 1 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (case_sum (\<lambda>_. []) (BENQ 1 2 (\<lambda>_. []))) (BENQ 1 1 (\<lambda>_. [])))))\<close>
        | \<open>op = map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<I> \<V>) (merge_op' (\<lambda>_. []) (BENQ 1 2 (BENQ 1 1 (\<lambda>_. []))))))\<close>
  apply atomize_elim
  using assms
  unfolding wstep_def
  apply simp
  apply (erule relcomppE)+
  apply (erule converse_rtranclpE)+
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[3]
   apply (erule converse_rtranclpE)
      apply blast
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
    apply (meson BENQ_diff_access sum.distinct(2))
   apply (erule converse_rtranclpE)
    apply blast
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
    apply (meson BENQ_diff_access sum.distinct(2))
   apply (erule converse_rtranclpE)
    apply blast
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim simp flip: case_sum_BENQ_L case_sum_BENQ_R)[1]
  apply (meson BENQ_diff_access sum.distinct(1))
  done

lemma wstep_Out1:
  \<open>wstep (Out 1 2) (map_op assoc id (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. []))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1 :: (1, 1, nat) op)
      \<V>)
        (merge_op' (case_sum buf3 (\<lambda>_. [])) (BENQ 1 2 (\<lambda>_. []))))))
  (map_op assoc id (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. []))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1)
      \<V>)
        (merge_op' (case_sum buf3 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
  apply (rule step_wstep)
  apply (rule step_map_op)
   apply (rule step_map_op)
    apply (rule step_comp_op_R_Out)
      apply (rule step_merge_op'_Write[of 1])
          apply (simp_all add: defaults_num1_def)
  by simp

lemma wstep_Out2:
  \<open>wstep (Out 1 2) (map_op assoc id (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. []))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1 :: (1, 1, nat) op)
      \<V>)
        (merge_op' (case_sum buf3 (BENQ 1 2 (\<lambda>_. []))) (\<lambda>_. [])))))
  (map_op assoc id (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. []))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1)
      \<V>)
        (merge_op' (case_sum buf3 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
  apply (rule wstep_trans'(1))
   apply (rule rtranclp.intros(2))
    apply (rule rtranclp.intros(1))
   apply (rule step_map_op)
    apply (rule step_map_op)
     apply (rule step_comp_op_R_Tau)
       apply (rule step_merge_op'_Silent_R[of 1])
          apply (simp_all add: defaults_num1_def)
  using wstep_Out1 by simp

lemma wstep_Out3:
  \<open>wstep (Out 1 2) (map_op assoc id (map_op projl projr (comp_op Some (case_sum buf2 (BENQ 1 2 (\<lambda>_. [])))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1 :: (1, 1, nat) op)
      \<V>)
        (merge_op' (case_sum buf3 (\<lambda>_. [])) (\<lambda>_. [])))))
  (map_op assoc id (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. []))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1)
      \<V>)
        (merge_op' (case_sum buf3 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
  apply (rule wstep_trans'(1))
   apply (rule rtranclp.intros(2))
    apply (rule rtranclp.intros(1))
   apply (rule step_map_op)
    apply (rule step_map_op)
     apply (rule step_Tau_comp_op_R)
          apply (rule step_merge_op'_Read_R[of 1])
            apply (simp_all add: defaults_num1_def)
  using wstep_Out2 by (simp flip: case_sum_BENQ_R)

lemma wstep_Out4:
  \<open>wstep (Out 1 2) (map_op assoc id (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. []))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1 :: (1, 1, nat) op)
      (merge_op (case_sum (BENQ 1 2 (\<lambda>_. [])) (\<lambda>_. []))))
        (merge_op' (case_sum buf3 (\<lambda>_. [])) (\<lambda>_. [])))))
  (map_op assoc id (map_op projl projr (comp_op Some (case_sum buf2 (\<lambda>_. []))
    (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1)
      \<V>)
        (merge_op' (case_sum buf3 (\<lambda>_. [])) (\<lambda>_. [])))))\<close>
  apply (rule wstep_trans'(1))
   apply (rule rtranclp.intros(2))
    apply (rule rtranclp.intros(1))
   apply (rule step_map_op)
    apply (rule step_map_op)
     apply (rule step_Tau_comp_op_L)
        apply (rule step_comp_op_R_Out)
          apply (rule step_merge_op_Write_L[of 1])
             apply (simp_all add: defaults_num1_def)
  using wstep_Out3 by (simp flip: case_sum_BENQ_R)

lemma no_wstep_Out:
  \<open>wstep (Out 1 2) (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) \<V> (\<I> :: (1, 1, nat) op))
  (merge_op' (BENQ (Inl 1) 2 (BENQ (Inl 1) (Suc 0) (\<lambda>_. []))) (\<lambda>_. [])))) op \<Longrightarrow> False\<close>
  unfolding wstep_def
  apply (erule relcomppE)+
  apply (erule converse_rtranclpE)
   apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim)[2]
   apply (rotate_tac 2)
   apply (erule converse_rtranclpE)
    apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim)[2]
     apply (simp add: BHD_def)
    apply (rotate_tac 3)
    apply (erule converse_rtranclpE)
     apply (auto elim!: step_map_op_elim step_comp_op_elim step_id_op_cases step_merge_op_elim step_merge_op'_elim)[2]
      apply (simp add: BHD_def)
     apply (simp add: BTL_def)
    apply (simp add: BENQ_diff_access BTL_diff_access)
   apply (simp add: BENQ_diff_access BTL_diff_access)
  apply (simp add: BENQ_diff_access BTL_diff_access)
  done

lemma wstep_Inp_not_3:
  assumes \<open>wstep (Inp (Inr p) x) (map_op assoc id (map_op projl projr (comp_op Some buf1
    op\<^sub>1 (merge_op' buf2 buf3))) :: ((1 + 1) + 1, 1, nat) op) op\<close>
    and \<open>buf3 1 \<noteq> []\<close> and \<open>BHD 1 buf3 \<noteq> 3\<close>
  obtains op\<^sub>1' buf1' buf2' buf3' where \<open>op = map_op assoc id (map_op projl projr (comp_op Some buf1'
    op\<^sub>1' (merge_op' buf2' buf3')))\<close> \<open>buf3' 1 \<noteq> []\<close> \<open>BHD 1 buf3' \<noteq> 3\<close>
  apply atomize_elim
  using assms
  apply -
  apply (erule wstep_map_op_elim)
  apply (erule wstep_map_op_elim)
  apply hypsubst_thin
  apply (subst (asm) wstep_comp_op_L_R)
  apply (elim exE conjE)
  subgoal for _ _ io op buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2'
    apply (cases io; simp)
    subgoal for p
      apply (cases p; simp)
      subgoal for p
        apply (cases p; simp)
        subgoal for p
          apply (cases p; simp)
          apply hypsubst_thin
          apply (rule exI[of _ buf'])
          apply (rule exI[of _ op\<^sub>1'])
          apply (rotate_tac 2)
          apply (erule thin_rl)
          apply rotate_tac
          apply (erule thin_rl)
          apply (rotate_tac 2)
          apply (induct \<open>Tau :: ((1 + 1 + 1) + 1 + 1, (1 + 1) + 1, nat) IO\<close> _ \<open>merge_op' buf2 buf3\<close> _ arbitrary: buf2 buf3 pred: wstep_comp_op_R)
              apply simp_all
          subgoal for _ _ buf2 buf3
            apply (rule exI[of _ buf2])
            apply (rule exI[of _ buf3])
            apply simp
            done
          subgoal
            by (erule step_merge_op'_elim; simp)
          subgoal for op' buf op'' buf2 buf3
            apply (erule step_merge_op'_elim; simp)
             apply (drule meta_spec[of _ \<open>BTL (Inl 1) buf2\<close>])
             apply (drule meta_spec[of _ \<open>BENQ 1 (BHD (Inl 1) buf2) buf3\<close>])
             apply simp
             apply (drule meta_mp)
              apply (simp add: BHD_def)
             apply assumption
             apply (drule meta_spec[of _ \<open>BTL (Inr 1) buf2\<close>])
             apply (drule meta_spec[of _ \<open>BENQ 1 (BHD (Inr 1) buf2) buf3\<close>])
             apply simp
             apply (drule meta_mp)
              apply (simp add: BHD_def)
            apply assumption
            done
          done
        done
      done
    done
  done

lemma no_wstep_Out':
  \<open>wstep (Inp (Inr p) x) (map_op assoc id (map_op projl projr (comp_op Some buf1
    op\<^sub>1 (merge_op' buf2 buf3))) :: ((1 + 1) + 1, 1, nat) op) op \<Longrightarrow> buf3 1 \<noteq> [] \<Longrightarrow> BHD 1 buf3 \<noteq> 3 \<Longrightarrow>
  wstep (Out 1 3) op op' \<Longrightarrow> False\<close>
  apply (erule wstep_Inp_not_3)
    apply assumption
  apply assumption
  apply hypsubst_thin
  apply (erule wstep_map_op_elim)
  apply (erule wstep_map_op_elim)
  apply hypsubst_thin
  apply (subst (asm) wstep_comp_op_L_R)
  apply (elim exE conjE)
  subgoal for _ _ buf2 buf3 _ _ io
    apply (cases io; simp)
    subgoal for p
      apply (cases p; simp)
      apply hypsubst_thin
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (rotate_tac 2)
      apply (erule thin_rl)
      apply rotate_tac
      apply (erule thin_rl)
      apply (rotate_tac 2)
      apply (induct \<open>Out (Inr 1) 3 :: ((1 + 1 + 1) + 1 + 1, (1 + 1) + 1, nat) IO\<close> _ \<open>merge_op' buf2 buf3\<close> _ arbitrary: buf2 buf3 pred: wstep_comp_op_R)
          apply simp_all
      subgoal
        by (erule step_merge_op'_elim; auto)
      subgoal
        by (erule step_merge_op'_elim; simp)
      subgoal for op' buf op'' buf2 buf3
        apply (erule step_merge_op'_elim; simp)
         apply (drule meta_spec[of _ \<open>BTL (Inl 1) buf2\<close>])
         apply (drule meta_spec[of _ \<open>BENQ 1 (BHD (Inl 1) buf2) buf3\<close>])
         apply simp
         apply (drule meta_mp)
          apply (simp add: BHD_def)
         apply assumption
        apply (drule meta_spec[of _ \<open>BTL (Inr 1) buf2\<close>])
        apply (drule meta_spec[of _ \<open>BENQ 1 (BHD (Inr 1) buf2) buf3\<close>])
        apply simp
        apply (drule meta_mp)
         apply (simp add: BHD_def)
        apply assumption
        done
      done
    done
  done

lemma A1_not_wbisim_merge_op':
  \<open>(\<V> \<parallel> (\<I> :: (1, 1, nat) op)) \<bullet> merge_op' (\<lambda>_. []) (\<lambda>_. []) \<approx> map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> merge_op' (\<lambda>_. []) (\<lambda>_. [])) \<Longrightarrow> False\<close>
  unfolding scomp_op_def pcomp_op_def
  apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inl (Inl 1)) 1\<close>])
   apply (rule wstep_converse_trans(2))
    apply (rule step_map_op)
     apply (rule step_comp_op_L_Inp)
       apply (rule step_comp_op_L_Inp)
         apply (rule step_merge_op_Read_L[of 1])
          apply (simp_all add: defaults_num1_def flip: case_sum_BENQ_L)
   apply (rule rtranclp.intros(2))
    apply (rule rtranclp.intros(2))
     apply (rule rtranclp.intros(1))
    apply (rule step_map_op)
     apply (rule step_Tau_comp_op_L)
        apply (rule step_comp_op_L_Out)
           apply (rule step_merge_op_Write_L[of 1])
              apply (simp_all add: defaults_num1_def)
   apply (rule step_map_op)
    apply (rule step_Tau_comp_op_R)
         apply (rule step_merge_op'_Read_L[of 1])
         apply (simp_all add: defaults_num1_def)
  apply (erule wstep_Inp_Inl_Inl; clarsimp)
     apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inl (Inr 1)) 2\<close>])
      apply (rule wstep_converse_trans(2))
       apply (rule step_map_op)
        apply (rule step_comp_op_L_Inp)
          apply (rule step_comp_op_L_Inp)
            apply (rule step_merge_op_Read_R[of 1])
             apply (simp_all add: defaults_num1_def)
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(1))
       apply (rule step_map_op)
        apply (rule step_Tau_comp_op_L)
           apply (rule step_comp_op_L_Out)
              apply (rule step_merge_op_Write_R[of 1])
                 apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_Tau_comp_op_R)
            apply (rule step_merge_op'_Read_L[of 1])
              apply (simp_all add: defaults_num1_def)
     apply (erule wstep_Inp_Inl_Inr1; clarsimp; drule wbisim_sym)
                     apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
                      apply (rule wstep_Out4[of \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close> \<open>\<lambda>_. []\<close>, simplified])
                     apply (erule no_wstep_Out)
                    apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
                     apply (rule wstep_Out3[of \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close> \<open>\<lambda>_. []\<close>, simplified])
                    apply (erule no_wstep_Out)
                   apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
                    apply (rule wstep_Out2[of \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close> \<open>\<lambda>_. []\<close>, simplified])
                   apply (erule no_wstep_Out)
                  apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
                   apply (rule wstep_Out1[of \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close> \<open>\<lambda>_. []\<close>, simplified])
                  apply (erule no_wstep_Out)
                 apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
                  apply (rule wstep_Out4[of \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>, simplified])
                 apply (erule no_wstep_Out)
                apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
                 apply (rule wstep_Out3[of \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>, simplified])
                apply (erule no_wstep_Out)
               apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
                apply (rule wstep_Out2[of \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>, simplified])
               apply (erule no_wstep_Out)
              apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
               apply (rule wstep_Out1[of \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>, simplified])
              apply (erule no_wstep_Out)
             apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
              apply (rule wstep_Out4[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close>, simplified])
             apply (erule no_wstep_Out)
            apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
             apply (rule wstep_Out3[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close>, simplified])
            apply (erule no_wstep_Out)
           apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
            apply (rule wstep_Out2[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close>, simplified])
           apply (erule no_wstep_Out)
          apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
           apply (rule wstep_Out1[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close>, simplified])
          apply (erule no_wstep_Out)
         apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
          apply (rule step_wstep)
          apply (rule step_map_op)
           apply (rule step_map_op)
            apply (rule step_comp_op_R_Out)
              apply (rule step_merge_op'_Write[of 1])
                  apply (simp_all add: defaults_num1_def)
          apply (simp add: BHD_def)
         apply (erule no_wstep_Out)
        apply (drule wbisim_sym)
        apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inr 1) 3\<close>])
         apply (rule step_wstep)
         apply (rule step_map_op)
          apply (rule step_comp_op_L_Inp)
            apply (rule step_comp_op_R_Inp)
               apply (rule step_id_op_Read[of 1])
                apply (simp_all add: defaults_num1_def)
        apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 3\<close>])
         apply (rule wstep_trans(1))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(2))
             apply (rule rtranclp.intros(1))
            apply (rule step_map_op)
             apply (rule step_Tau_comp_op_L)
                apply (rule step_comp_op_R_Out)
                  apply (rule step_id_op_Write[of 1])
                     apply (simp_all add: defaults_num1_def)
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_R)
                 apply (rule step_merge_op'_Read_R[of 1])
                   apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_comp_op_R_Tau)
             apply (rule step_merge_op'_Silent_R[of 1])
                apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Out)
            apply (rule step_merge_op'_Write[of 1])
                apply (simp_all add: defaults_num1_def BENQ_diff_access)
        apply (erule no_wstep_Out')
          apply simp_all
       apply (drule wbisim_sym)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inr 1) 3\<close>])
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_comp_op_R_Inp)
              apply (rule step_id_op_Read[of 1])
               apply (simp_all add: defaults_num1_def)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 3\<close>])
        apply (rule wstep_trans(1))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_L)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write[of 1])
                    apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_merge_op'_Read_R[of 1])
                  apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Tau)
            apply (rule step_merge_op'_Silent_R[of 1])
               apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_merge_op'_Write[of 1])
               apply (simp_all add: defaults_num1_def BENQ_diff_access)
       apply (erule no_wstep_Out')
         apply simp_all
      apply (drule wbisim_sym)
      apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inr 1) 3\<close>])
       apply (rule step_wstep)
       apply (rule step_map_op)
        apply (rule step_comp_op_L_Inp)
          apply (rule step_comp_op_R_Inp)
             apply (rule step_id_op_Read[of 1])
              apply (simp_all add: defaults_num1_def)
      apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 3\<close>])
       apply (rule wstep_trans(1))
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(1))
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_L)
              apply (rule step_comp_op_R_Out)
                apply (rule step_id_op_Write[of 1])
                   apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_Tau_comp_op_R)
               apply (rule step_merge_op'_Read_R[of 1])
                 apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Tau)
           apply (rule step_merge_op'_Silent_R[of 1])
              apply (simp_all add: defaults_num1_def)
       apply (rule step_map_op)
        apply (rule step_comp_op_R_Out)
          apply (rule step_merge_op'_Write[of 1])
              apply (simp_all add: defaults_num1_def BENQ_diff_access)
      apply (erule no_wstep_Out')
        apply simp_all
     apply (drule wbisim_sym)
     apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inr 1) 3\<close>])
      apply (rule step_wstep)
      apply (rule step_map_op)
       apply (rule step_comp_op_L_Inp)
         apply (rule step_comp_op_R_Inp)
            apply (rule step_id_op_Read[of 1])
             apply (simp_all add: defaults_num1_def)
     apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 3\<close>])
      apply (rule wstep_trans(1))
       apply (rule rtranclp.intros(2))
        apply (rule rtranclp.intros(2))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(1))
         apply (rule step_map_op)
          apply (rule step_Tau_comp_op_L)
             apply (rule step_comp_op_R_Out)
               apply (rule step_id_op_Write[of 1])
                  apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_Tau_comp_op_R)
              apply (rule step_merge_op'_Read_R[of 1])
                apply (simp_all add: defaults_num1_def)
       apply (rule step_map_op)
        apply (rule step_comp_op_R_Tau)
          apply (rule step_merge_op'_Silent_R[of 1])
             apply (simp_all add: defaults_num1_def)
      apply (rule step_map_op)
       apply (rule step_comp_op_R_Out)
         apply (rule step_merge_op'_Write[of 1])
             apply (simp_all add: defaults_num1_def BENQ_diff_access)
     apply (erule no_wstep_Out')
       apply (simp_all add: BHD_def)
    apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inl (Inr 1)) 2\<close>])
     apply (rule wstep_converse_trans(2))
      apply (rule step_map_op)
       apply (rule step_comp_op_L_Inp)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_merge_op_Read_R[of 1])
            apply (simp_all add: defaults_num1_def)
     apply (rule rtranclp.intros(2))
      apply (rule rtranclp.intros(2))
       apply (rule rtranclp.intros(1))
      apply (rule step_map_op)
       apply (rule step_Tau_comp_op_L)
          apply (rule step_comp_op_L_Out)
             apply (rule step_merge_op_Write_R[of 1])
                apply (simp_all add: defaults_num1_def)
     apply (rule step_map_op)
      apply (rule step_Tau_comp_op_R)
           apply (rule step_merge_op'_Read_L[of 1])
             apply (simp_all add: defaults_num1_def)
    apply (erule wstep_Inp_Inl_Inr2; clarsimp; drule wbisim_sym)
                apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
                 apply (rule wstep_Out4[of \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>, simplified])
                apply (erule no_wstep_Out)
               apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
                apply (rule wstep_Out3[of \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>, simplified])
               apply (erule no_wstep_Out)
              apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
               apply (rule wstep_Out2[of \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>, simplified])
              apply (erule no_wstep_Out)
             apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
              apply (rule wstep_Out1[of \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>, simplified])
             apply (erule no_wstep_Out)
            apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
             apply (rule wstep_Out4[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close>, simplified])
            apply (erule no_wstep_Out)
           apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
            apply (rule wstep_Out3[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close>, simplified])
           apply (erule no_wstep_Out)
          apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
           apply (rule wstep_Out2[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close>, simplified])
          apply (erule no_wstep_Out)
         apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
          apply (rule wstep_Out1[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close>, simplified])
         apply (erule no_wstep_Out)
         apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
         apply (rule step_wstep)
         apply (rule step_map_op)
          apply (rule step_map_op)
           apply (rule step_comp_op_R_Out)
             apply (rule step_merge_op'_Write[of 1])
                 apply (simp_all add: defaults_num1_def)
         apply (simp add: BHD_def)
        apply (erule no_wstep_Out)
       apply (drule wbisim_sym)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inr 1) 3\<close>])
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_comp_op_R_Inp)
              apply (rule step_id_op_Read[of 1])
               apply (simp_all add: defaults_num1_def)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 3\<close>])
        apply (rule wstep_trans(1))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_L)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write[of 1])
                    apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_merge_op'_Read_R[of 1])
                  apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Tau)
            apply (rule step_merge_op'_Silent_R[of 1])
               apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_merge_op'_Write[of 1])
               apply (simp_all add: defaults_num1_def BENQ_diff_access)
       apply (erule no_wstep_Out')
         apply (simp_all add: BHD_def)
      apply (drule wbisim_sym)
      apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inr 1) 3\<close>])
       apply (rule step_wstep)
       apply (rule step_map_op)
        apply (rule step_comp_op_L_Inp)
           apply (rule step_comp_op_R_Inp)
              apply (rule step_id_op_Read[of 1])
               apply (simp_all add: defaults_num1_def)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 3\<close>])
        apply (rule wstep_trans(1))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_L)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write[of 1])
                    apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_merge_op'_Read_R[of 1])
                  apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Tau)
            apply (rule step_merge_op'_Silent_R[of 1])
               apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_merge_op'_Write[of 1])
               apply (simp_all add: defaults_num1_def BENQ_diff_access)
       apply (erule no_wstep_Out')
         apply (simp_all add: BHD_def)
       apply (drule wbisim_sym)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inr 1) 3\<close>])
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_comp_op_R_Inp)
              apply (rule step_id_op_Read[of 1])
               apply (simp_all add: defaults_num1_def)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 3\<close>])
        apply (rule wstep_trans(1))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_L)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write[of 1])
                    apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_merge_op'_Read_R[of 1])
                  apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Tau)
            apply (rule step_merge_op'_Silent_R[of 1])
               apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_merge_op'_Write[of 1])
               apply (simp_all add: defaults_num1_def BENQ_diff_access)
       apply (erule no_wstep_Out')
         apply (simp_all add: BHD_def)
       apply (drule wbisim_sym)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inr 1) 3\<close>])
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_comp_op_R_Inp)
              apply (rule step_id_op_Read[of 1])
               apply (simp_all add: defaults_num1_def)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 3\<close>])
        apply (rule wstep_trans(1))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_L)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write[of 1])
                    apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_merge_op'_Read_R[of 1])
                  apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Tau)
            apply (rule step_merge_op'_Silent_R[of 1])
               apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_merge_op'_Write[of 1])
               apply (simp_all add: defaults_num1_def BENQ_diff_access)
       apply (erule no_wstep_Out')
         apply (simp_all add: BHD_def)
   apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inl (Inr 1)) 2\<close>])
    apply (rule wstep_converse_trans(2))
     apply (rule step_map_op)
      apply (rule step_comp_op_L_Inp)
        apply (rule step_comp_op_L_Inp)
          apply (rule step_merge_op_Read_R[of 1])
           apply (simp_all add: defaults_num1_def)
    apply (rule rtranclp.intros(2))
     apply (rule rtranclp.intros(2))
      apply (rule rtranclp.intros(1))
     apply (rule step_map_op)
      apply (rule step_Tau_comp_op_L)
         apply (rule step_comp_op_L_Out)
            apply (rule step_merge_op_Write_R[of 1])
               apply (simp_all add: defaults_num1_def)
    apply (rule step_map_op)
     apply (rule step_Tau_comp_op_R)
          apply (rule step_merge_op'_Read_L[of 1])
            apply (simp_all add: defaults_num1_def)
   apply (erule wstep_Inp_Inl_Inr3; clarsimp; drule wbisim_sym)
           apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
            apply (rule wstep_Out4[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close>, simplified])
           apply (erule no_wstep_Out)
          apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
           apply (rule wstep_Out3[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close>, simplified])
          apply (erule no_wstep_Out)
         apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
          apply (rule wstep_Out2[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close>, simplified])
         apply (erule no_wstep_Out)
        apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
         apply (rule wstep_Out1[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>BENQ 1 (Suc 0) (\<lambda>_. [])\<close>, simplified])
        apply (erule no_wstep_Out)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 2\<close>])
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Out)
            apply (rule step_merge_op'_Write[of 1])
                apply (simp_all add: defaults_num1_def)
        apply (simp add: BHD_def)
       apply (erule no_wstep_Out)
       apply (drule wbisim_sym)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inr 1) 3\<close>])
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_comp_op_R_Inp)
              apply (rule step_id_op_Read[of 1])
               apply (simp_all add: defaults_num1_def)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 3\<close>])
        apply (rule wstep_trans(1))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_L)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write[of 1])
                    apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_merge_op'_Read_R[of 1])
                  apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Tau)
            apply (rule step_merge_op'_Silent_R[of 1])
               apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_merge_op'_Write[of 1])
               apply (simp_all add: defaults_num1_def BENQ_diff_access)
       apply (erule no_wstep_Out')
         apply (simp_all add: BHD_def)
       apply (drule wbisim_sym)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inr 1) 3\<close>])
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_comp_op_R_Inp)
              apply (rule step_id_op_Read[of 1])
               apply (simp_all add: defaults_num1_def)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 3\<close>])
        apply (rule wstep_trans(1))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_L)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write[of 1])
                    apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_merge_op'_Read_R[of 1])
                  apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Tau)
            apply (rule step_merge_op'_Silent_R[of 1])
               apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_merge_op'_Write[of 1])
               apply (simp_all add: defaults_num1_def BENQ_diff_access)
       apply (erule no_wstep_Out')
         apply (simp_all add: BHD_def)
       apply (drule wbisim_sym)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inr 1) 3\<close>])
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_comp_op_R_Inp)
              apply (rule step_id_op_Read[of 1])
               apply (simp_all add: defaults_num1_def)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 3\<close>])
        apply (rule wstep_trans(1))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_L)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write[of 1])
                    apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_merge_op'_Read_R[of 1])
                  apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Tau)
            apply (rule step_merge_op'_Silent_R[of 1])
               apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_merge_op'_Write[of 1])
               apply (simp_all add: defaults_num1_def BENQ_diff_access)
       apply (erule no_wstep_Out')
         apply (simp_all add: BHD_def)
       apply (drule wbisim_sym)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inr 1) 3\<close>])
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_comp_op_R_Inp)
              apply (rule step_id_op_Read[of 1])
               apply (simp_all add: defaults_num1_def)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 3\<close>])
        apply (rule wstep_trans(1))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_L)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write[of 1])
                    apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_merge_op'_Read_R[of 1])
                  apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Tau)
            apply (rule step_merge_op'_Silent_R[of 1])
               apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_merge_op'_Write[of 1])
               apply (simp_all add: defaults_num1_def BENQ_diff_access)
       apply (erule no_wstep_Out')
         apply (simp_all add: BHD_def)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Inp (Inr 1) 3\<close>])
        apply (rule step_wstep)
        apply (rule step_map_op)
         apply (rule step_comp_op_L_Inp)
           apply (rule step_comp_op_R_Inp)
              apply (rule step_id_op_Read[of 1])
               apply (simp_all add: defaults_num1_def)
       apply (erule wbisim_wstep[OF wbisimulation_wbisim, where io=\<open>Out 1 3\<close>])
        apply (rule wstep_trans(1))
         apply (rule rtranclp.intros(2))
          apply (rule rtranclp.intros(2))
           apply (rule rtranclp.intros(2))
            apply (rule rtranclp.intros(1))
           apply (rule step_map_op)
            apply (rule step_Tau_comp_op_L)
               apply (rule step_comp_op_R_Out)
                 apply (rule step_id_op_Write[of 1])
                    apply (simp_all add: defaults_num1_def)
          apply (rule step_map_op)
           apply (rule step_Tau_comp_op_R)
                apply (rule step_merge_op'_Read_R[of 1])
                  apply (simp_all add: defaults_num1_def)
         apply (rule step_map_op)
          apply (rule step_comp_op_R_Tau)
            apply (rule step_merge_op'_Silent_R[of 1])
               apply (simp_all add: defaults_num1_def)
        apply (rule step_map_op)
         apply (rule step_comp_op_R_Out)
           apply (rule step_merge_op'_Write[of 1])
               apply (simp_all add: defaults_num1_def BENQ_diff_access)
       apply (erule no_wstep_Out')
    apply (simp_all add: BHD_def)
  done

lemma A1_not_wbisim:
  \<open>(\<V> \<parallel> (\<I> :: (1, 1, nat) op)) \<bullet> \<V>' \<approx> map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>') \<Longrightarrow> False\<close>
  using A1_not_wbisim_merge_op' merge_op'_merge_op_id_op
  by (smt (verit, best) wbisim_map_op wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans)

section \<open>Branching bisimulation\<close>

definition \<open>brsim R op\<^sub>1 op\<^sub>2 =
  (\<forall>io op\<^sub>1'. step io op\<^sub>1 op\<^sub>1' \<longrightarrow>
    (\<exists>op\<^sub>2' op\<^sub>2'' op\<^sub>2'''. (step Tau)\<^sup>*\<^sup>* op\<^sub>2 op\<^sub>2' \<and> estep io op\<^sub>2' op\<^sub>2'' \<and> (step Tau)\<^sup>*\<^sup>* op\<^sub>2'' op\<^sub>2''' \<and>
    R op\<^sub>1 op\<^sub>2' \<and> R op\<^sub>1' op\<^sub>2'' \<and> R op\<^sub>1' op\<^sub>2'''))\<close>

lemma brsim_mono[mono]: \<open>R \<le> S \<Longrightarrow> brsim R \<le> brsim S\<close>
  by (force simp: brsim_def le_fun_def)

coinductive brbisim (infix \<open>\<approx>\<^sub>b\<close> 40) where
  \<open>brsim (\<approx>\<^sub>b) op\<^sub>1 op\<^sub>2 \<Longrightarrow> brsim (\<approx>\<^sub>b) op\<^sub>2 op\<^sub>1 \<Longrightarrow> op\<^sub>1 \<approx>\<^sub>b op\<^sub>2\<close>

lemma brsim_wsim:
  \<open>brsim R op\<^sub>1 op\<^sub>2 \<Longrightarrow> wsim R op\<^sub>1 op\<^sub>2\<close>
  unfolding brsim_def wsim_def wstep_def
  by (meson relcomppI)

lemma brbisim_wbisim:
  \<open>op\<^sub>1 \<approx>\<^sub>b op\<^sub>2 \<Longrightarrow> op\<^sub>1 \<approx> op\<^sub>2\<close>
  by (smt (verit, ccfv_threshold) brbisim.cases brsim_def brsim_wsim wbisim.coinduct)

lemma A1_not_brbisim:
  \<open>(\<V> \<parallel> (\<I> :: (1, 1, nat) op)) \<bullet> \<V>' \<approx>\<^sub>b map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>') \<Longrightarrow> False\<close>
  using A1_not_wbisim brbisim_wbisim by blast

section \<open>Proof of trace equivalence\<close>

lemma wstep_Inp_Inl_Inl_Tau1:
  \<open>wstep (Inp (Inl (Inl p)) x)
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))
     op \<Longrightarrow>
  wstep Tau
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BENQ p x buf1) buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))
     op\<close>
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (rule wstep_map_op[of Tau])
  subgoal for io
    apply (subst (asm) wstep_comp_op_L_R)
    apply (subst wstep_comp_op_L_R)
    apply (elim exE conjE)
    apply (cases io; simp)
    subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2' p'
      apply (cases p'; simp)
      apply hypsubst_thin
      apply (rule exI[of _ buf'])
      apply (rule exI[of _ buf\<^sub>1])
      apply (rule exI[of _ buf\<^sub>2])
      apply (rule exI[of _ op\<^sub>1'])
      apply (rule exI[of _ op\<^sub>2'])
      apply simp
      apply rotate_tac
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (induct \<open>Inp (Inl (Inl (Inl p))) x :: ((('a + 'a) + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO\<close> _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3)\<close> _ arbitrary: buf1 buf2 buf3 pred: wstep_comp_op_L)
          apply simp_all
      subgoal
        by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
      subgoal for _ _ _ _ _ _ _ buf1 buf2 buf3
        apply (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp; hypsubst_thin)
        subgoal for p'
          apply (drule meta_spec[of _ buf1])
          apply (drule meta_spec[of _ buf2])
          apply (drule meta_spec[of _ \<open>BTL p' buf3\<close>])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_R_Out)
               apply (rule step_id_op_Write)
          by simp_all
        subgoal for p'
          apply (drule meta_spec[of _ \<open>BTL p' buf1\<close>])
          apply (drule meta_spec[of _ buf2])
          apply (drule meta_spec[of _ buf3])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_L_Out)
               apply (rule step_merge_op_Write_L)
                   apply simp_all
            apply (smt (verit, best) BENQ_def BTL_def fun_upd_def fun_upd_twist fun_upd_upd tl_append2)
           apply (metis BENQ_access BENQ_diff_access Nil_is_append_conv)
          by (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
        subgoal for p'
          apply (drule meta_spec[of _ buf1])
          apply (drule meta_spec[of _ \<open>BTL p' buf2\<close>])
          apply (drule meta_spec[of _ buf3])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_L_Out)
               apply (rule step_merge_op_Write_R)
          by simp_all
        done
      subgoal
        by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
      done
    done
  subgoal
    by simp
  done

lemma wtraced_Inp_Inl_Inl1:
  \<open>wtraced
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))
    (LCons (VInp (Inl (Inl p)) x) lxs) \<Longrightarrow>
  wtraced
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BENQ p x buf1) buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))
    lxs\<close>
  apply (cases lxs; simp)
   apply (rule wtraced.Nil)
  subgoal
    apply (erule wtraced.cases; simp; hypsubst_thin)
    apply (erule wtraced.cases; simp; hypsubst_thin)
    subgoal for _ _ _ op
      apply (rule wtraced.Step[where ?op'=op])
       apply (drule wstep_Inp_Inl_Inl_Tau1)
       apply (smt (verit, best) IO.exhaust io_of_vio_not_Tau(1) wstep_steps_Tau wstep_trans'(1,2))
      apply assumption
      done
    done
  done

lemma wstep_Inp_Inl_Inr_Tau1:
  \<open>wstep (Inp (Inl (Inr p)) x)
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))
     op \<Longrightarrow>
  wstep Tau
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 (BENQ p x buf2))) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))
     op\<close>
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (rule wstep_map_op[of Tau])
  subgoal for io
    apply (subst (asm) wstep_comp_op_L_R)
    apply (subst wstep_comp_op_L_R)
    apply (elim exE conjE)
    apply (cases io; simp)
    subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2' p'
      apply (cases p'; simp)
      apply hypsubst_thin
      apply (rule exI[of _ buf'])
      apply (rule exI[of _ buf\<^sub>1])
      apply (rule exI[of _ buf\<^sub>2])
      apply (rule exI[of _ op\<^sub>1'])
      apply (rule exI[of _ op\<^sub>2'])
      apply simp
      apply rotate_tac
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (induct \<open>Inp (Inl (Inl (Inr p))) x :: ((('a + 'a) + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO\<close> _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3)\<close> _ arbitrary: buf1 buf2 buf3 pred: wstep_comp_op_L)
          apply simp_all
      subgoal
        by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
      subgoal for _ _ _ _ _ _ _ buf1 buf2 buf3
        apply (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp; hypsubst_thin)
        subgoal for p'
          apply (drule meta_spec[of _ buf1])
          apply (drule meta_spec[of _ buf2])
          apply (drule meta_spec[of _ \<open>BTL p' buf3\<close>])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_R_Out)
               apply (rule step_id_op_Write)
          by simp_all
        subgoal for p'
          apply (drule meta_spec[of _ \<open>BTL p' buf1\<close>])
          apply (drule meta_spec[of _ buf2])
          apply (drule meta_spec[of _ buf3])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_L_Out)
               apply (rule step_merge_op_Write_L)
          by simp_all
        subgoal for p'
          apply (drule meta_spec[of _ buf1])
          apply (drule meta_spec[of _ \<open>BTL p' buf2\<close>])
          apply (drule meta_spec[of _ buf3])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_L_Out)
               apply (rule step_merge_op_Write_R)
                   apply simp_all
            apply (smt (verit, best) BENQ_def BTL_def fun_upd_def fun_upd_twist fun_upd_upd tl_append2)
           apply (metis BENQ_access BENQ_diff_access Nil_is_append_conv)
          by (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
        done
      subgoal
        by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
      done
    done
  subgoal
    by simp
  done

lemma wtraced_Inp_Inl_Inr1:
  \<open>wtraced
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))
    (LCons (VInp (Inl (Inr p)) x) lxs) \<Longrightarrow>
  wtraced
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 (BENQ p x buf2))) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))
    lxs\<close>
  apply (cases lxs; simp)
   apply (rule wtraced.Nil)
  subgoal
    apply (erule wtraced.cases; simp; hypsubst_thin)
    apply (erule wtraced.cases; simp; hypsubst_thin)
    subgoal for _ _ _ op
      apply (rule wtraced.Step[where ?op'=op])
       apply (drule wstep_Inp_Inl_Inr_Tau1)
       apply (smt (verit, best) IO.exhaust io_of_vio_not_Tau(1) wstep_steps_Tau wstep_trans'(1,2))
      apply assumption
      done
    done
  done

lemma wstep_Inp_Inr_Tau1:
  \<open>wstep (Inp (Inr p) x)
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))
     op \<Longrightarrow>
  wstep Tau
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op (BENQ p x buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))
     op\<close>
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (rule wstep_map_op[of Tau])
  subgoal for io
    apply (subst (asm) wstep_comp_op_L_R)
    apply (subst wstep_comp_op_L_R)
    apply (elim exE conjE)
    apply (cases io; simp)
    subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2' p'
      apply (cases p'; simp)
      apply hypsubst_thin
      apply (rule exI[of _ buf'])
      apply (rule exI[of _ buf\<^sub>1])
      apply (rule exI[of _ buf\<^sub>2])
      apply (rule exI[of _ op\<^sub>1'])
      apply (rule exI[of _ op\<^sub>2'])
      apply simp
      apply rotate_tac
      apply (erule thin_rl)
      apply (erule thin_rl)
      apply (induct \<open>Inp (Inl (Inr p)) x :: ((('a + 'a) + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO\<close> _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3)\<close> _ arbitrary: buf1 buf2 buf3 pred: wstep_comp_op_L)
          apply simp_all
      subgoal
        by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
      subgoal for _ _ _ _ _ _ _ buf1 buf2 buf3
        apply (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp; hypsubst_thin)
        subgoal for p'
          apply (drule meta_spec[of _ buf1])
          apply (drule meta_spec[of _ buf2])
          apply (drule meta_spec[of _ \<open>BTL p' buf3\<close>])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_R_Out)
               apply (rule step_id_op_Write)
                  apply simp_all
            apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
           apply (metis BENQ_access BENQ_diff_access Nil_is_append_conv)
          by (smt (verit, best) BENQ_def BTL_def fun_upd_def fun_upd_twist fun_upd_upd tl_append2)
        subgoal for p'
          apply (drule meta_spec[of _ \<open>BTL p' buf1\<close>])
          apply (drule meta_spec[of _ buf2])
          apply (drule meta_spec[of _ buf3])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_L_Out)
               apply (rule step_merge_op_Write_L)
          by simp_all
        subgoal for p'
          apply (drule meta_spec[of _ buf1])
          apply (drule meta_spec[of _ \<open>BTL p' buf2\<close>])
          apply (drule meta_spec[of _ buf3])
          apply simp
          apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_L_Out)
               apply (rule step_merge_op_Write_R)
          by simp_all
        done
      subgoal
        by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
      done
    done
  subgoal
    by simp
  done

lemma wtraced_Inp_Inr1:
  \<open>wtraced
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))
    (LCons (VInp (Inr p) x) lxs) \<Longrightarrow>
  wtraced
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op (BENQ p x buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))
    lxs\<close>
  apply (cases lxs; simp)
   apply (rule wtraced.Nil)
  subgoal
    apply (erule wtraced.cases; simp; hypsubst_thin)
    apply (erule wtraced.cases; simp; hypsubst_thin)
    subgoal for _ _ _ op
      apply (rule wtraced.Step[where ?op'=op])
       apply (drule wstep_Inp_Inr_Tau1)
       apply (smt (verit, best) IO.exhaust io_of_vio_not_Tau(1) wstep_steps_Tau wstep_trans'(1,2))
      apply assumption
      done
    done
  done

lemma inputs_not_defaults1:
  \<open>p \<in> inputs (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))) \<Longrightarrow>
  p \<notin> defaults\<close>
proof -
  assume \<open>p \<in> inputs
          (map_op projl projr
            (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
              (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))\<close>
  hence \<open>p \<in> projl ` inputs (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))\<close>
    using op.set_map(1) by metis
  hence \<open>p \<in> inputs (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))\<close>
    using inputs_scomp_op_le_dest by (smt (verit, ccfv_threshold) imageE image_eqI sum.sel(1))
  hence \<open>p \<in> Inl ` inputs (merge_op (case_sum buf1 buf2)) \<or> p \<in> Inr ` inputs (id_op buf3)\<close>
    by blast
  hence \<open>p \<notin> defaults\<close>
    using defaults_sum_def inputs_merge_op inputs_id_op by blast
  thus ?thesis .
qed

lemma outputs_not_defaults1:
  \<open>p \<in> outputs (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))) \<Longrightarrow>
  p \<notin> defaults\<close>
proof -
  assume \<open>p \<in> outputs
          (map_op projl projr
            (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
              (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))\<close>
  hence \<open>p \<in> projr ` outputs (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))\<close>
    using op.set_map(2) by metis
  hence \<open>p \<in> outputs (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (\<I> :: ('a, 'a, 'b) op)))\<close>
    using outputs_scomp_op_le_dest by (smt (verit, ccfv_threshold) imageE image_eqI sum.sel(2))
  hence \<open>p \<in> projr ` outputs (comp_op Some (\<lambda>_. []) \<V> (\<I> :: ('a, 'a, 'b) op))\<close>
    using op.set_map(2) by metis
  hence \<open>p \<in> outputs (\<I> :: ('a, 'a, 'b) op)\<close>
    using outputs_scomp_op_le_dest by (smt (verit, best) imageE sum.sel(2))
  hence \<open>p \<notin> defaults\<close>
    using outputs_id_op by blast
  thus ?thesis .
qed

(* TODO rename *)
lemma foo:
  \<open>wstep_comp_op_R wire (Out (Inr p) x) buf (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)) op \<Longrightarrow>
  buf \<noteq> (\<lambda>_. [])\<close>
  by (erule wstep_comp_op_R.cases)
    (auto elim!: step_map_op_elim step_comp_op_elim step_merge_op_elim step_id_op_cases)

lemma wstep_Out_Tau1:
  assumes \<open>wstep (Out p x)
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))
    op\<close>
  obtains \<open>buf1 p \<noteq> []\<close> \<open>x = BHD p buf1\<close> \<open>wstep Tau (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BTL p buf1) buf2)) (id_op buf3)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))) op\<close>
  | \<open>buf2 p \<noteq> []\<close> \<open>x = BHD p buf2\<close> \<open>wstep Tau (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 (BTL p buf2))) (id_op buf3)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))) op\<close>
  | \<open>buf3 p \<noteq> []\<close> \<open>x = BHD p buf3\<close> \<open>wstep Tau (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op (BTL p buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))) op\<close>
  apply atomize_elim
  using assms
  apply -
  apply (erule wstep_map_op_elim)
  apply (subst (asm) wstep_comp_op_L_R)
  apply (elim exE conjE)
  apply hypsubst_thin
  subgoal for io op' buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2'
    apply (subgoal_tac \<open>buf1 p \<noteq> [] \<and>
       x = BHD p buf1 \<and>
       wstep Tau
        (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BTL p buf1) buf2)) (id_op buf3))
            (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))
        (comp_op Some buf' op\<^sub>1' op\<^sub>2') \<or>
       buf2 p \<noteq> [] \<and>
       x = BHD p buf2 \<and>
       wstep Tau
        (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 (BTL p buf2))) (id_op buf3))
            (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))
        (comp_op Some buf' op\<^sub>1' op\<^sub>2') \<or>
       buf3 p \<noteq> [] \<and>
       x = BHD p buf3 \<and>
       wstep Tau
        (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op (BTL p buf3)))
            (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))
        (comp_op Some buf' op\<^sub>1' op\<^sub>2')\<close>)
    subgoal
      by auto
    apply (subst (1 2 3) wstep_comp_op_L_R)
    apply (cases io; simp)
    subgoal for p'
      apply (cases p'; simp; hypsubst_thin)
      apply (subgoal_tac \<open>buf1 p \<noteq> [] \<and>
    x = BHD p buf1 \<and> buf\<^sub>2 (Inl p) \<noteq> [] \<and>
        wstep_comp_op_L Some (Tau :: ((('a + 'a) + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO) (BTL (Inl p) buf\<^sub>1) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BTL p buf1) buf2)) (id_op buf3))
         op\<^sub>1' \<and>
        wstep_comp_op_R Some (Tau :: ((('a + 'a) + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO) (BTL (Inl p) buf\<^sub>2) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)) op\<^sub>2' \<or>
    buf2 p \<noteq> [] \<and> buf\<^sub>2 (Inl p) \<noteq> [] \<and>
    x = BHD p buf2 \<and>
        wstep_comp_op_L Some (Tau :: ((('a + 'a) + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO) (BTL (Inl p) buf\<^sub>1) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 (BTL p buf2))) (id_op buf3))
         op\<^sub>1' \<and>
        wstep_comp_op_R Some (Tau :: ((('a + 'a) + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO) (BTL (Inl p) buf\<^sub>2) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)) op\<^sub>2' \<or>
    buf3 p \<noteq> [] \<and> buf\<^sub>2 (Inr p) \<noteq> [] \<and>
    x = BHD p buf3 \<and>
        wstep_comp_op_L Some (Tau :: ((('a + 'a) + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO) (BTL (Inr p) buf\<^sub>1) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op (BTL p buf3)))
         op\<^sub>1' \<and>
        wstep_comp_op_R Some (Tau :: ((('a + 'a) + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO) (BTL (Inr p) buf\<^sub>2) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)) op\<^sub>2'\<close>)
      subgoal
        apply (elim disjE conjE)
        subgoal
          apply (intro disjI1 conjI)
            apply assumption
           apply assumption
          apply (rule exI[of _ buf'])
          apply (rule exI[of _ \<open>BTL (Inl p) buf\<^sub>1\<close>])
          apply (rule exI[of _ \<open>BTL (Inl p) buf\<^sub>2\<close>])
          apply (rule exI[of _ op\<^sub>1'])
          apply (rule exI[of _ op\<^sub>2'])
          apply simp
          apply (rule allI)
          subgoal for p'
            apply (cases \<open>p' = Inl p\<close>; simp?)
             apply (metis BTL_access Nitpick.size_list_simp(2) append_eq_conv_conj append_take_drop_id drop_Suc nat_le_linear
                  take_all tl_take)
            by (metis BTL_diff_access)
          done
        subgoal
          apply (rule disjI2)
          apply (intro disjI1 conjI)
            apply assumption
           apply assumption
          apply (rule exI[of _ buf'])
          apply (rule exI[of _ \<open>BTL (Inl p) buf\<^sub>1\<close>])
          apply (rule exI[of _ \<open>BTL (Inl p) buf\<^sub>2\<close>])
          apply (rule exI[of _ op\<^sub>1'])
          apply (rule exI[of _ op\<^sub>2'])
          apply simp
          apply (rule allI)
          subgoal for p'
            apply (cases \<open>p' = Inl p\<close>; simp?)
             apply (metis BTL_access Nitpick.size_list_simp(2) append_eq_conv_conj append_take_drop_id drop_Suc nat_le_linear
                  take_all tl_take)
            by (metis BTL_diff_access)
          done
        subgoal
          apply (intro disjI2 conjI)
            apply assumption
           apply assumption
          apply (rule exI[of _ buf'])
          apply (rule exI[of _ \<open>BTL (Inr p) buf\<^sub>1\<close>])
          apply (rule exI[of _ \<open>BTL (Inr p) buf\<^sub>2\<close>])
          apply (rule exI[of _ op\<^sub>1'])
          apply (rule exI[of _ op\<^sub>2'])
          apply simp
          apply (rule allI)
          subgoal for p'
            apply (cases \<open>p' = Inr p\<close>; simp?)
             apply (metis BTL_access Nitpick.size_list_simp(2) append_eq_conv_conj append_take_drop_id drop_Suc nat_le_linear
                  take_all tl_take)
            by (metis BTL_diff_access)
          done
        done
      apply (induct \<open>Tau :: ((('a + 'a) + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO\<close> _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3)\<close> _ arbitrary: buf1 buf2 buf3 pred: wstep_comp_op_L)
          apply simp_all
      subgoal
        apply (drule foo)
        by presburger
      subgoal for pa xa op' q buf op'' buf'a buf1 buf2 buf3
        apply (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp; hypsubst_thin)
        subgoal for p'
          apply (drule meta_spec[of _ buf1])
          apply (drule meta_spec[of _ buf2])
          apply (drule meta_spec[of _ \<open>BTL p' buf3\<close>])
          apply simp
          sorry
        subgoal sorry
        subgoal sorry
        done
      subgoal
        by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
      done
    done
  done

lemma wtraced_Out1:
  assumes \<open>wtraced
    (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op buf3))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))
    (LCons (VOut p x) lxs)\<close>
  obtains \<open>p \<notin> defaults\<close> \<open>buf1 p \<noteq> []\<close> \<open>x = BHD p buf1\<close> \<open>wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BTL p buf1) buf2)) (id_op buf3)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))) lxs\<close>
  | \<open>p \<notin> defaults\<close> \<open>buf2 p \<noteq> []\<close> \<open>x = BHD p buf2\<close> \<open>wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 (BTL p buf2))) (id_op buf3)) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))) lxs\<close>
  | \<open>p \<notin> defaults\<close> \<open>buf3 p \<noteq> []\<close> \<open>x = BHD p buf3\<close> \<open>wtraced (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op (BTL p buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))) lxs\<close>
  apply atomize_elim
  using assms
  apply -
  apply (erule wtraced.cases; simp; hypsubst_thin; simp)
  apply (erule wstep_Out_Tau1)
  using assms wtraced_outputs outputs_not_defaults1
  by (smt (verit, del_insts) VIO.set_intros(2) estep.elims io_of_vio_not_Tau(1) lset_intros(1) wstep_steps_Tau
    wstep_trans'(1,2) wtraced.simps)+

lemma wstep_Inp_Inl_Inl_Tau2:
  \<open>wstep (Inp (Inl (Inl p)) x)
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))) op \<Longrightarrow>
  wstep Tau
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ p x buf1)) (merge_op (case_sum buf2 buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))) op\<close>
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (rule wstep_map_op[of Tau])
   apply (rule wstep_map_op[of Tau])
  subgoal for _ _ io
    apply (subst (asm) wstep_comp_op_L_R)
    apply (subst wstep_comp_op_L_R)
    apply (elim exE conjE)
    apply (cases io; simp)
    subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2' p'
      apply (cases p'; simp)
      subgoal for p''
        apply (cases p''; simp)
         apply hypsubst_thin
         apply (rule exI[of _ buf'])
         apply (rule exI[of _ buf\<^sub>1])
         apply (rule exI[of _ buf\<^sub>2])
         apply (rule exI[of _ op\<^sub>1'])
         apply (rule exI[of _ op\<^sub>2'])
         apply simp
         apply rotate_tac
         apply (erule thin_rl)
         apply (erule thin_rl)
         apply (induct \<open>Inp (Inl (Inl p)) x :: (('a + 'a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO\<close> _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))\<close> _ arbitrary: buf1 buf2 buf3 pred: wstep_comp_op_L)
             apply simp_all
        subgoal
          by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
        subgoal for _ _ _ _ _ _ _ buf1 buf2 buf3
          apply (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp; hypsubst_thin)
          subgoal for p'
            apply (drule meta_spec[of _ buf1])
            apply (drule meta_spec[of _ \<open>BTL p' buf2\<close>])
            apply (drule meta_spec[of _ buf3])
            apply simp
            apply (rule wstep_comp_op_L.intros(4))
               apply (rule step_comp_op_R_Out)
                 apply (rule step_merge_op_Write_L)
            by simp_all
          subgoal for p'
            apply (drule meta_spec[of _ buf1])
            apply (drule meta_spec[of _ buf2])
            apply (drule meta_spec[of _ \<open>BTL p' buf3\<close>])
            apply simp
            apply (rule wstep_comp_op_L.intros(4))
             apply (rule step_comp_op_R_Out)
                 apply (rule step_merge_op_Write_R)
            by simp_all
          subgoal for p'
            apply (drule meta_spec[of _ \<open>BTL p' buf1\<close>])
            apply (drule meta_spec[of _ buf2])
            apply (drule meta_spec[of _ buf3])
            apply simp
            apply (rule wstep_comp_op_L.intros(4))
               apply (rule step_comp_op_L_Out)
                  apply (rule step_id_op_Write)
                     apply simp_all
              apply (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
             apply (metis BENQ_access BENQ_diff_access Nil_is_append_conv)
            by (smt (verit, best) BENQ_def BTL_def fun_upd_def fun_upd_twist fun_upd_upd tl_append2)
          done
        subgoal
          by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
        subgoal
          by (metis Inr_not_Inl sum.exhaust sum.simps(5,6))
        done
      done
    done
  subgoal
    by simp
  subgoal
    by simp
  done

lemma wtraced_Inp_Inl_Inl2:
  \<open>wtraced
     (map_op assoc id
       (map_op projl projr
         (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
           (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))))
     (LCons (VInp (Inl (Inl p)) x) lxs) \<Longrightarrow>
  wtraced
     (map_op assoc id
       (map_op projl projr
         (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ p x buf1)) (merge_op (case_sum buf2 buf3)))
           (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))))
     lxs\<close>
  apply (cases lxs; simp)
   apply (rule wtraced.Nil)
  apply (erule wtraced.cases; simp; hypsubst_thin)
  apply (erule wtraced.cases; simp; hypsubst_thin)
  subgoal for _ _ _ _ _op
    apply (rule wtraced.Step[where ?op'=op])
     apply (drule wstep_Inp_Inl_Inl_Tau2)
     apply (smt (verit, best) IO.exhaust io_of_vio_not_Tau(1) wstep_steps_Tau wstep_trans'(1,2))
    apply assumption
    done
  done

lemma wstep_Inp_Inl_Inr_Tau2:
  \<open>wstep (Inp (Inl (Inr p)) x)
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))) op \<Longrightarrow>
  wstep Tau
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum (BENQ p x buf2) buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))) op\<close>
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (rule wstep_map_op[of Tau])
   apply (rule wstep_map_op[of Tau])
  subgoal for _ _ io
    apply (subst (asm) wstep_comp_op_L_R)
    apply (subst wstep_comp_op_L_R)
    apply (elim exE conjE)
    apply (cases io; simp)
    subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2' p'
      apply (cases p'; simp)
      subgoal for p''
        apply (cases p''; simp)
        subgoal for p'''
          apply (cases p'''; simp)
          apply hypsubst_thin
          apply (rule exI[of _ buf'])
          apply (rule exI[of _ buf\<^sub>1])
          apply (rule exI[of _ buf\<^sub>2])
          apply (rule exI[of _ op\<^sub>1'])
          apply (rule exI[of _ op\<^sub>2'])
          apply simp
          apply rotate_tac
          apply (erule thin_rl)
          apply (erule thin_rl)
          apply (induct \<open>Inp (Inl (Inr (Inl p))) x :: (('a + 'a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO\<close> _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))\<close> _ arbitrary: buf1 buf2 buf3 pred: wstep_comp_op_L)
              apply simp_all
          subgoal
            by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
          subgoal for _ _ _ _ _ _ _ buf1 buf2 buf3
            apply (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp; hypsubst_thin)
            subgoal for p'
              apply (drule meta_spec[of _ buf1])
              apply (drule meta_spec[of _ \<open>BTL p' buf2\<close>])
              apply (drule meta_spec[of _ buf3])
              apply simp
              apply (rule wstep_comp_op_L.intros(4))
                 apply (rule step_comp_op_R_Out)
                 apply (rule step_merge_op_Write_L)
                      apply simp_all
                apply (smt (verit, best) BENQ_def BTL_def fun_upd_def fun_upd_twist fun_upd_upd tl_append2)
               apply (metis BENQ_access BENQ_diff_access Nil_is_append_conv)
              by (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
            subgoal for p'
              apply (drule meta_spec[of _ buf1])
              apply (drule meta_spec[of _ buf2])
              apply (drule meta_spec[of _ \<open>BTL p' buf3\<close>])
              apply simp
              apply (rule wstep_comp_op_L.intros(4))
                 apply (rule step_comp_op_R_Out)
                   apply (rule step_merge_op_Write_R)
              by simp_all
            subgoal for p'
              apply (drule meta_spec[of _ \<open>BTL p' buf1\<close>])
              apply (drule meta_spec[of _ buf2])
              apply (drule meta_spec[of _ buf3])
              apply simp
              apply (rule wstep_comp_op_L.intros(4))
                 apply (rule step_comp_op_L_Out)
                    apply (rule step_id_op_Write)
              by simp_all
            done
          subgoal
            by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
          done
        done
      done
    done
  subgoal
    by simp
  subgoal
    by simp
  done

lemma wtraced_Inp_Inl_Inr2:
  \<open>wtraced
     (map_op assoc id
       (map_op projl projr
         (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
           (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))))
     (LCons (VInp (Inl (Inr p)) x) lxs) \<Longrightarrow>
  wtraced
     (map_op assoc id
       (map_op projl projr
         (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum (BENQ p x buf2) buf3)))
           (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))))
     lxs\<close>
  apply (cases lxs; simp)
   apply (rule wtraced.Nil)
  apply (erule wtraced.cases; simp; hypsubst_thin)
  apply (erule wtraced.cases; simp; hypsubst_thin)
  subgoal for _ _ _ _ _ op
    apply (rule wtraced.Step[where ?op'=op])
     apply (drule wstep_Inp_Inl_Inr_Tau2)
     apply (smt (verit, best) IO.exhaust io_of_vio_not_Tau(1) wstep_steps_Tau wstep_trans'(1,2))
    apply assumption
    done
  done

lemma wstep_Inp_Inr_Tau2:
  \<open>wstep (Inp (Inr p) x)
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))) op \<Longrightarrow>
  wstep Tau
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 (BENQ p x buf3))))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))) op\<close>
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (erule wstep_map_op_elim; hypsubst_thin)
  apply (rule wstep_map_op[of Tau])
   apply (rule wstep_map_op[of Tau])
  subgoal for _ _ io
    apply (subst (asm) wstep_comp_op_L_R)
    apply (subst wstep_comp_op_L_R)
    apply (elim exE conjE)
    apply (cases io; simp)
    subgoal for buf' buf\<^sub>1 buf\<^sub>2 op\<^sub>1' op\<^sub>2' p'
      apply (cases p'; simp)
      subgoal for p''
        apply (cases p''; simp)
        subgoal for p'''
          apply (cases p'''; simp)
          apply hypsubst_thin
          apply (rule exI[of _ buf'])
          apply (rule exI[of _ buf\<^sub>1])
          apply (rule exI[of _ buf\<^sub>2])
          apply (rule exI[of _ op\<^sub>1'])
          apply (rule exI[of _ op\<^sub>2'])
          apply simp
          apply rotate_tac
          apply (erule thin_rl)
          apply (erule thin_rl)
          apply (induct \<open>Inp (Inl (Inr (Inr p))) x :: (('a + 'a + 'a) + 'a + 'a, ('a + 'a) + 'a, 'b) IO\<close> _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))\<close> _ arbitrary: buf1 buf2 buf3 pred: wstep_comp_op_L)
              apply simp_all
          subgoal
            by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
          subgoal for _ _ _ _ _ _ _ buf1 buf2 buf3
            apply (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp; hypsubst_thin)
            subgoal for p'
              apply (drule meta_spec[of _ buf1])
              apply (drule meta_spec[of _ \<open>BTL p' buf2\<close>])
              apply (drule meta_spec[of _ buf3])
              apply simp
              apply (rule wstep_comp_op_L.intros(4))
                 apply (rule step_comp_op_R_Out)
                 apply (rule step_merge_op_Write_L)
              by simp_all
            subgoal for p'
              apply (drule meta_spec[of _ buf1])
              apply (drule meta_spec[of _ buf2])
              apply (drule meta_spec[of _ \<open>BTL p' buf3\<close>])
              apply simp
              apply (rule wstep_comp_op_L.intros(4))
                 apply (rule step_comp_op_R_Out)
                   apply (rule step_merge_op_Write_R)
                      apply simp_all
                apply (smt (verit, best) BENQ_def BTL_def fun_upd_def fun_upd_twist fun_upd_upd tl_append2)
               apply (metis BENQ_access BENQ_diff_access Nil_is_append_conv)
              by (metis BENQ_access BENQ_diff_access BHD_def hd_append2)
            subgoal for p'
              apply (drule meta_spec[of _ \<open>BTL p' buf1\<close>])
              apply (drule meta_spec[of _ buf2])
              apply (drule meta_spec[of _ buf3])
              apply simp
              apply (rule wstep_comp_op_L.intros(4))
                 apply (rule step_comp_op_L_Out)
                    apply (rule step_id_op_Write)
              by simp_all
            done
          subgoal
            by (elim step_comp_op_elim step_merge_op_elim step_id_op_cases; simp)
          done
        done
      done
    done
  subgoal
    by simp
  subgoal
    by simp
  done

lemma wtraced_Inp_Inr2:
  \<open>wtraced
     (map_op assoc id
       (map_op projl projr
         (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
           (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))))
     (LCons (VInp (Inr p) x) lxs) \<Longrightarrow>
  wtraced
     (map_op assoc id
       (map_op projl projr
         (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 (BENQ p x buf3))))
           (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))))
     lxs\<close>
  apply (cases lxs; simp)
   apply (rule wtraced.Nil)
  apply (erule wtraced.cases; simp; hypsubst_thin)
  apply (erule wtraced.cases; simp; hypsubst_thin)
  subgoal for _ _ _ _ _ op
    apply (rule wtraced.Step[where ?op'=op])
     apply (drule wstep_Inp_Inr_Tau2)
     apply (smt (verit, best) IO.exhaust io_of_vio_not_Tau(1) wstep_steps_Tau wstep_trans'(1,2))
    apply assumption
    done
  done

lemma assoc_defaults:
  \<open>(p :: 'a :: {defaults} + 'b :: {defaults} + 'c :: {defaults}) \<in> defaults \<longleftrightarrow> assoc p \<in> defaults\<close>
  by (smt (verit, ccfv_threshold) Inl_in_defaults Inr_in_defaults assoc.simps(1,2,3) sum.exhaust_sel)

lemma inputs_not_defaults2:
  \<open>p \<in> inputs (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))) \<Longrightarrow>
  p \<notin> defaults\<close>
proof -
  assume \<open>p \<in> inputs
          (map_op assoc id
            (map_op projl projr
              (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
                (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))))\<close>
  hence \<open>p \<in> assoc ` inputs (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))\<close>
    using op.set_map(1) by metis
  hence \<open>p \<in> assoc ` projl` inputs (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))\<close>
    using op.set_map(1) by metis
  hence \<open>p \<in> assoc ` inputs (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))\<close>
    using inputs_scomp_op_le_dest by (smt (verit, ccfv_threshold) imageE image_eqI sum.sel(1))
  hence \<open>p \<in> assoc ` Inl ` inputs (id_op buf1) \<or> p \<in> assoc ` Inr ` inputs (merge_op (case_sum buf2 buf3))\<close>
    by (smt (verit, ccfv_threshold) image_iff inputs_pcomp_op_le_dest)
  hence \<open>p \<notin> defaults\<close>
    using assoc_defaults
    by (smt (verit) DiffE Inl_in_defaults Inr_in_defaults imageE inputs_id_op_alt inputs_sub_op_Read merge_op_reads)
  thus ?thesis .
qed

lemma outputs_not_defaults2:
  \<open>p \<in> outputs (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))) \<Longrightarrow>
  p \<notin> defaults\<close>
proof -
  assume \<open>p \<in> outputs
          (map_op assoc id
            (map_op projl projr
              (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
                (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))))\<close>
  hence \<open>p \<in> outputs (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))\<close>
    using op.set_map(2) id_apply image_id by metis
  hence \<open>p \<in> projr ` outputs (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))\<close>
    using op.set_map(2) by metis
  hence \<open>p \<in> outputs (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> (\<I> :: ('a, 'a, 'b) op)))\<close>
    using outputs_scomp_op_le_dest by (smt (verit, ccfv_threshold) imageE image_eqI sum.sel(2))
  hence \<open>p \<in> projr ` outputs (comp_op Some (\<lambda>_. []) \<V> (\<I> :: ('a, 'a, 'b) op))\<close>
    using op.set_map(2) by metis
  hence \<open>p \<in> outputs (\<I> :: ('a, 'a, 'b) op)\<close>
    using outputs_scomp_op_le_dest by (smt (verit, best) imageE sum.sel(2))
  hence \<open>p \<notin> defaults\<close>
    using outputs_id_op by blast
  thus ?thesis .
qed

lemma wstep_Out_Tau2:
  assumes \<open>wstep (Out p x)
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))))
    op\<close>
  obtains \<open>buf1 p \<noteq> []\<close> \<open>x = BHD p buf1\<close> \<open>wstep Tau (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL p buf1)) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))) op\<close>
  | \<open>buf2 p \<noteq> []\<close> \<open>x = BHD p buf2\<close> \<open>wstep Tau (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum (BTL p buf2) buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))) op\<close>
  | \<open>buf3 p \<noteq> []\<close> \<open>x = BHD p buf3\<close> \<open>wstep Tau (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 (BTL p buf3)))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))) op\<close>
  sorry

lemma wtraced_Out2:
  assumes \<open>wtraced
    (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 buf3)))
      (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))))
    (LCons (VOut p x) lxs)\<close>
  obtains \<open>p \<notin> defaults\<close> \<open>buf1 p \<noteq> []\<close> \<open>x = BHD p buf1\<close> \<open>wtraced (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL p buf1)) (merge_op (case_sum buf2 buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))) lxs\<close>
  | \<open>p \<notin> defaults\<close> \<open>buf2 p \<noteq> []\<close> \<open>x = BHD p buf2\<close> \<open>wtraced (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum (BTL p buf2) buf3))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))) lxs\<close>
  | \<open>p \<notin> defaults\<close> \<open>buf3 p \<noteq> []\<close> \<open>x = BHD p buf3\<close> \<open>wtraced (map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 (BTL p buf3)))) (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))) lxs\<close>
 apply atomize_elim
  using assms
  apply -
  apply (erule wtraced.cases; simp; hypsubst_thin; simp)
  apply (erule wstep_Out_Tau2)
  using assms wtraced_outputs outputs_not_defaults2
  by (smt (verit, del_insts) VIO.set_intros(2) estep.elims io_of_vio_not_Tau(1) lset_intros(1) wstep_steps_Tau
    wstep_trans'(1,2) wtraced.simps)+

lemma A1_trace_eq_gen:
  \<open>(merge_op (case_sum buf1 buf2) \<parallel> id_op buf3) \<bullet> \<V>' \<equiv>\<^sub>t map_op assoc id ((id_op buf1 \<parallel> merge_op (case_sum buf2 buf3)) \<bullet> \<V>')\<close>
  unfolding wtraces_def pcomp_op_def scomp_op_def
  apply (rule Collect_eqI)
  apply (rule iffI)
  subgoal for lxs
    apply (coinduction arbitrary: buf1 buf2 buf3 lxs pred: wtraced)
    subgoal for buf1 buf2 buf3 lxs
      apply (cases lxs; simp; hypsubst_thin)
      subgoal for vio lxs
        apply (cases vio; simp; hypsubst_thin)
        subgoal for p x
          apply (cases p; simp; hypsubst_thin)
          subgoal for p
            apply (cases p; simp; hypsubst_thin)
            subgoal for p
              apply (intro exI[of _ \<open>map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. [])
  (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BENQ p x buf1)) (merge_op (case_sum buf2 buf3)))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))\<close>] conjI)
               apply (rule step_wstep)
               apply (rule step_map_op)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Inp)
                   apply (rule step_comp_op_L_Inp)
                     apply (rule step_id_op_Read)
                      apply simp_all
              using wtraced_inputs inputs_not_defaults1
                apply (metis Inl_in_defaults VIO.set_intros(1) lset_intros(1))
               apply fastforce
              using wtraced_Inp_Inl_Inl1
              by metis
            subgoal for p
              apply (intro exI[of _ \<open>map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. [])
  (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum (BENQ p x buf2) buf3)))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))\<close>] conjI)
               apply (rule step_wstep)
               apply (rule step_map_op)
                apply (rule step_map_op)
                 apply (rule step_comp_op_L_Inp)
                   apply (rule step_comp_op_R_Inp)
                     apply (rule step_merge_op_Read_L)
                      apply simp_all
              using wtraced_inputs inputs_not_defaults1
                apply (metis Inl_in_defaults Inr_in_defaults VIO.set_intros(1) llist.set_intros(1))
               apply fastforce
              using wtraced_Inp_Inl_Inr1
              by metis
            done
          subgoal for p
            apply (intro exI[of _ \<open>map_op assoc id (map_op projl projr (comp_op Some (\<lambda>_. [])
  (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 (BENQ p x buf3))))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>))))\<close>] conjI)
             apply (rule step_wstep)
             apply (rule step_map_op)
            apply (rule step_map_op)
               apply (rule step_comp_op_L_Inp)
                 apply (rule step_comp_op_R_Inp)
                    apply (rule step_merge_op_Read_R)
                     apply simp_all
            using wtraced_inputs inputs_not_defaults1
              apply (metis Inr_in_defaults VIO.set_intros(1) llist.set_intros(1))
             apply fastforce
            using wtraced_Inp_Inr1
            by metis
          done
        subgoal for p x
          apply (erule wtraced_Out1)
            apply (intro exI[of _ \<open>(map_op assoc id (map_op projl projr
  (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op (BTL p buf1)) (merge_op (case_sum buf2 buf3)))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))))\<close>] conjI)
             apply (rule wstep_trans(1))
              apply (rule rtranclp.intros(2))
               apply (rule rtranclp.intros(2))
                apply (rule rtranclp.intros(2))
                 apply (rule rtranclp.intros(2))
                  apply (rule rtranclp.intros(1))
                 apply (rule step_map_op)
                  apply (rule step_map_op)
                   apply (rule step_Tau_comp_op_L)
                      apply (rule step_comp_op_L_Out)
                         apply (rule step_id_op_Write)
                            apply simp_all
                apply (rule step_map_op)
                 apply (rule step_map_op)
                  apply (rule step_Tau_comp_op_R)
                       apply (rule step_map_op)
                        apply (rule step_comp_op_L_Inp)
                          apply (rule step_merge_op_Read_L[of p])
                           apply simp_all
                apply simp
               apply (rule step_map_op)
                apply (rule step_map_op)
                 apply (rule step_comp_op_R_Tau)
                   apply (rule step_map_op)
                    apply (rule step_Tau_comp_op_L)
                       apply (rule step_merge_op_Write_L[of p])
                          apply simp_all
              apply (rule step_map_op)
               apply (rule step_map_op)
                apply (rule step_comp_op_R_Tau)
                  apply (rule step_map_op)
                   apply (rule step_Tau_comp_op_R)
                        apply (rule step_id_op_Read)
                         apply simp_all
              apply simp
             apply fastforce
            apply blast
           apply (intro exI[of _ \<open>(map_op assoc id (map_op projl projr
  (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum (BTL p buf2) buf3)))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))))\<close>] conjI)
            apply (rule wstep_trans(1))
             apply (rule rtranclp.intros(2))
              apply (rule rtranclp.intros(2))
               apply (rule rtranclp.intros(2))
                apply (rule rtranclp.intros(2))
                 apply (rule rtranclp.intros(1))
                apply (rule step_map_op)
                 apply (rule step_map_op)
                  apply (rule step_Tau_comp_op_L)
                     apply (rule step_comp_op_R_Out)
                       apply (rule step_merge_op_Write_L)
                          apply simp_all
               apply (rule step_map_op)
                apply (rule step_map_op)
                 apply (rule step_Tau_comp_op_R)
                      apply (rule step_map_op)
                       apply (rule step_comp_op_L_Inp)
                         apply (rule step_merge_op_Read_R[of p])
                          apply simp_all
               apply simp
              apply (rule step_map_op)
               apply (rule step_map_op)
                apply (rule step_comp_op_R_Tau)
                  apply (rule step_map_op)
                   apply (rule step_Tau_comp_op_L)
                      apply (rule step_merge_op_Write_R[of p])
                         apply simp_all
             apply (rule step_map_op)
              apply (rule step_map_op)
               apply (rule step_comp_op_R_Tau)
                 apply (rule step_map_op)
                  apply (rule step_Tau_comp_op_R)
                       apply (rule step_id_op_Read)
                        apply simp_all
             apply simp
            apply fastforce
           apply blast
          apply (intro exI[of _ \<open>(map_op assoc id (map_op projl projr
  (comp_op Some (\<lambda>_. []) (comp_op (\<lambda>_. None) (\<lambda>_. []) (id_op buf1) (merge_op (case_sum buf2 (BTL p buf3))))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))))\<close>] conjI)
           apply (rule wstep_trans(1))
            apply (rule rtranclp.intros(2))
             apply (rule rtranclp.intros(2))
              apply (rule rtranclp.intros(2))
               apply (rule rtranclp.intros(2))
                apply (rule rtranclp.intros(1))
               apply (rule step_map_op)
                apply (rule step_map_op)
                 apply (rule step_Tau_comp_op_L)
                    apply (rule step_comp_op_R_Out)
                      apply (rule step_merge_op_Write_R)
                         apply simp_all
              apply (rule step_map_op)
               apply (rule step_map_op)
                apply (rule step_Tau_comp_op_R)
                     apply (rule step_map_op)
                      apply (rule step_comp_op_L_Inp)
                        apply (rule step_merge_op_Read_R[of p])
                         apply simp_all
              apply simp
             apply (rule step_map_op)
              apply (rule step_map_op)
               apply (rule step_comp_op_R_Tau)
                 apply (rule step_map_op)
                  apply (rule step_Tau_comp_op_L)
                     apply (rule step_merge_op_Write_R[of p])
                        apply simp_all
            apply (rule step_map_op)
             apply (rule step_map_op)
              apply (rule step_comp_op_R_Tau)
                apply (rule step_map_op)
                 apply (rule step_Tau_comp_op_R)
                      apply (rule step_id_op_Read)
                       apply simp_all
            apply simp
           apply fastforce
          apply blast
          done
        done
      done
    done
  subgoal for lxs
    apply (coinduction arbitrary: buf1 buf2 buf3 lxs pred: wtraced)
    subgoal for buf1 buf2 buf3 lxs
      apply (cases lxs; simp; hypsubst_thin)
      subgoal for vio lxs
        apply (cases vio; simp; hypsubst_thin)
        subgoal for p x
          apply (cases p; simp; hypsubst_thin)
          subgoal for p
            apply (cases p; simp; hypsubst_thin)
            subgoal for p
              apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (\<lambda>_. [])
  (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum (BENQ p x buf1) buf2)) (id_op buf3))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))\<close>] conjI)
               apply (rule step_wstep)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Inp)
                  apply (rule step_comp_op_L_Inp)
                    apply (rule step_merge_op_Read_L)
                     apply simp_all
              using wtraced_inputs inputs_not_defaults2
               apply (metis Inl_in_defaults VIO.set_intros(1) lset_intros(1))
              using wtraced_Inp_Inl_Inl2
              by metis
            subgoal for p
              apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (\<lambda>_. [])
  (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 (BENQ p x buf2))) (id_op buf3))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))\<close>] conjI)
               apply (rule step_wstep)
               apply (rule step_map_op)
                apply (rule step_comp_op_L_Inp)
                  apply (rule step_comp_op_L_Inp)
                    apply (rule step_merge_op_Read_R)
                     apply simp_all
              using wtraced_inputs inputs_not_defaults2
               apply (metis Inl_in_defaults Inr_in_defaults VIO.set_intros(1) llist.set_intros(1))
              using wtraced_Inp_Inl_Inr2
              by metis
            done
          subgoal for p
            apply (intro exI[of _ \<open>map_op projl projr (comp_op Some (\<lambda>_. [])
  (comp_op (\<lambda>_. None) (\<lambda>_. []) (merge_op (case_sum buf1 buf2)) (id_op (BENQ p x buf3)))
    (map_op projl projr (comp_op Some (\<lambda>_. []) \<V> \<I>)))\<close>] conjI)
             apply (rule step_wstep)
             apply (rule step_map_op)
              apply (rule step_comp_op_L_Inp)
                apply (rule step_comp_op_R_Inp)
                   apply (rule step_id_op_Read)
                    apply simp_all
            using wtraced_inputs inputs_not_defaults2
             apply (metis Inr_in_defaults VIO.set_intros(1) llist.set_intros(1))
            using wtraced_Inp_Inr2
            by metis
          done
        subgoal for p x
          sorry
        done
      done
    done
  done

lemma A1_trace_eq:
  \<open>(\<V> \<parallel> \<I>) \<bullet> \<V>' \<equiv>\<^sub>t map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>')\<close>
  oops

end