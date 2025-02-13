\<comment> \<open>Axioms from Table 4 for merge test and split\<close>
theory Asynchronous_Dataflow_Axioms

imports
  BNA_Operators
begin
no_notation Sublist.parallel (infixl "\<parallel>" 50)

section \<open>Axiom: A1: Merge commutes with identity\<close>

lemma merge_op_id_op_comp_op_bufs:
  \<open>map_op projl projr (comp_op Some buf2 (merge_op buf1 \<parallel> id_op buf1') (merge_op buf3))
  ~ map_op assoc id (map_op projl projr (comp_op Some buf2 (id_op buf1' \<parallel> merge_op buf1) (merge_op buf3)))\<close>
  apply (coinduction arbitrary: buf1 buf1' buf2 buf3 rule: bisim_coinduct_upto)
  subgoal for buf1 buf1' buf2 buf3
    unfolding sim_def pcomp_op_def
    apply auto
    subgoal
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for _ x
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p
          apply (erule step_merge_op_Inp)
           apply simp
          apply (cases p)
  oops

lemma merge_op_commutes_identity:
  "(\<V> \<parallel> \<I>) \<bullet> \<V> ~ map_op assoc id ((\<I> \<parallel> \<V>) \<bullet> \<V>)"
  oops

section \<open>Axiom: A2: Merge transpose is merge\<close>

lemma transp_op_merge_op_bufs:
  \<open>map_op projl projr (comp_op Some buf2 (transp_op buf1) (merge_op buf3))
  \<approx> merge_op buf\<close>
  apply (coinduction arbitrary: buf1 buf2 buf3 rule: wbisim_coinduct_upto)
  unfolding wsim_def
  subgoal for buf1 buf2 buf3
    apply auto
    subgoal
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (erule step_transp_op_Inp)
         apply simp
(*         apply (rule exI[of _ \<open>merge_op (BENQ p x buf1 >> (buf2 \<circ> case_sum Inr Inl) >> buf3)\<close>])
        apply auto
        apply (rule step_wstep)
        apply fastforce
        done
      subgoal for p
        apply (erule step_merge_op_Out)
          apply simp
        subgoal
          apply (rule exI[of _ \<open>merge_op (buf1 >> (buf2 \<circ> case_sum Inr Inl) >> BTL (Inl p) buf3)\<close>])
          apply auto
          by (metis BAPPEND_BTL BHD_BULK_BENQ_right_not_empty BULK_BENQ_empty step_merge_op_Write_L step_wstep)
        subgoal
          apply (rule exI[of _ \<open>merge_op (buf1 >> (buf2 \<circ> case_sum Inr Inl) >> BTL (Inr p) buf3)\<close>])
          apply auto
          by (metis BAPPEND_BTL BHD_BULK_BENQ_right_not_empty BULK_BENQ_empty step_merge_op_Write_R step_wstep)
        done
      subgoal for _ x
        apply (erule step_transp_op_Out)
          apply (auto split: sum.splits)
        subgoal for p
          apply (rule exI[of _ \<open>merge_op (buf1 >> (buf2 \<circ> case_sum Inr Inl) >> buf3)\<close>])
          apply auto
          apply (rule wbc_base)
          by (metis BAPPEND_BENQ_BHD BENQ_case_sum_compose sum.simps(5))
        subgoal for p
          apply (rule exI[of _ \<open>merge_op (buf1 >> (buf2 \<circ> case_sum Inr Inl) >> buf3)\<close>])
          apply auto
          apply (rule wbc_base)
          by (metis BAPPEND_BENQ_BHD BENQ_case_sum_compose sum.simps(6))
        done
      subgoal for p
        apply (erule step_merge_op_Inp)
         apply simp
        apply (rule exI[of _ \<open>merge_op (buf1 >> (buf2 \<circ> case_sum Inr Inl) >> buf3)\<close>])
        apply auto
        apply (rule wbc_base)
        apply (rule exI[of _ buf1])
        apply (rule exI[of _ \<open>BTL p buf2\<close>])
        apply (rule exI[of _ \<open>BENQ p (BHD p buf2) buf3\<close>])
        sorry
       apply (meson no_step_transp_op_Tau no_step_merge_op_Tau)+
      done
    subgoal
      apply (erule step_merge_op_cases)
      subgoal for p x
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some buf2 (transp_op (BENQ p x buf1)) (merge_op buf3))\<close>])
        apply (rule conjI)
         apply (rule step_wstep)
         apply fastforce
        apply (rule wbc_sym)
        apply auto
        done
      subgoal for p x
        sorry
      subgoal for p x
        sorry
      done
    done *)
  oops

lemma merge_op_transp_op:
  "\<X> \<bullet> \<V> \<approx> \<V>"
  oops

section \<open>Axiom: A3: Merge dummy source and identity\<close>
lemma merge_op_dummy_source_op:
  "map_op projr id (\<exclamdown> \<parallel> \<I>) \<bullet> \<V> \<approx> \<I>"
  oops

section \<open>Axiom: A4: Merge to sink\<close>
lemma merge_op_sink_op:
   "\<V> \<bullet> ! ~ ! \<parallel> !"
  oops

section \<open>Axiom: A6: Split to transpose\<close>

lemma split_op_transp_op_bufs:
  \<open>map_op projl projr (comp_op Some buf2 (split_op buf1) (transp_op buf3))
  \<approx> map_op id (case_sum Inr Inl) (split_op (buf1 >> buf2 >> buf3))\<close>
  apply (coinduction arbitrary: buf1 buf2 buf3 rule: wbisim_coinduct_upto)
  unfolding wsim_def
  subgoal for buf1 buf2 buf3
    apply auto
    subgoal
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (erule step_split_op_Inp)
          apply simp
        subgoal
          apply (rule exI[of _ \<open>map_op id (case_sum Inr Inl) (split_op (BENQ (Inl p) x buf1 >> buf2 >> buf3))\<close>])
          apply auto
          apply force
          done
        subgoal
          apply (rule exI[of _ \<open>map_op id (case_sum Inr Inl) (split_op (BENQ (Inr p) x buf1 >> buf2 >> buf3))\<close>])
          apply auto
          apply force
          done
        done
      subgoal
        apply (erule step_transp_op_Out)
          apply (auto split: sum.splits)
        subgoal for p
          apply (rule exI[of _ \<open>map_op id (case_sum Inr Inl) (split_op (buf1 >> buf2 >> BTL (Inr p) buf3))\<close>])
          apply auto
          apply (rule step_wstep)
          using BULK_BENQ_empty
          by fastforce
        subgoal for p
          apply (rule exI[of _ \<open>map_op id (case_sum Inr Inl) (split_op (buf1 >> buf2 >> BTL (Inl p) buf3))\<close>])
          apply auto
          apply (rule step_wstep)
          using BULK_BENQ_empty
          by fastforce
        done
      subgoal for p x
        apply (erule step_split_op_Out)
         apply simp
        apply (rule exI[of _ \<open>map_op id (case_sum Inr Inl) (split_op (buf1 >> buf2 >> buf3))\<close>])
        apply auto
        apply (rule wbc_base)
        apply fastforce
        done
      subgoal for p
        apply (erule step_transp_op_Inp)
         apply simp
        apply (rule exI[of _ \<open>map_op id (case_sum Inr Inl) (split_op (buf1 >> buf2 >> buf3))\<close>])
        apply auto
        apply (rule wbc_base)
        apply (rule exI[of _ buf1])
        apply (rule exI[of _ \<open>BTL p buf2\<close>])
        apply (rule exI[of _ \<open>BENQ p (BHD p buf2) buf3\<close>])
        by (metis BAPPEND_BENQ_BHD BULK_BENQ_assoc)
       apply (meson no_step_split_op_Tau no_step_transp_op_Tau)+
      done
    subgoal
      apply (drule step_map_op_inv)
      apply auto
      apply (erule step_split_op_cases)
        apply (auto split: sum.splits)
      subgoal for p x
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some buf2 (split_op (BENQ (Inl p) x buf1)) (transp_op buf3))\<close>])
        apply (rule conjI)
         apply fastforce
        apply blast
        done
      subgoal for p x
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some buf2 (split_op (BENQ (Inr p) x buf1)) (transp_op buf3))\<close>])
        apply (rule conjI)
         apply fastforce
        apply blast
        done
      subgoal for p
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some buf2 (split_op (BTL (Inl p) buf1)) (transp_op buf3))\<close>])
        apply (rule conjI)
        apply (rule step_tau_step_tau_step_io_wstep[of _
            \<open>map_op projl projr (comp_op Some (BENQ (Inl p) (BHD (Inl p) buf1) buf2) (split_op (BTL (Inl p) buf1)) (transp_op buf3))\<close>
            \<open>map_op projl projr (comp_op Some (BTL (Inl p) (BENQ (Inl p) (BHD (Inl p) buf1) buf2)) (split_op (BTL (Inl p) buf1)) (transp_op (BENQ (Inl p) (BHD (Inl p) buf1) buf3)))\<close>])
           apply fastforce
          apply fastforce
         apply simp
         apply (rule step_map_op[of \<open>Out (Inr (Inr p)) (BHD (Inl p) buf1)\<close>])
          apply (rule step_comp_op_R_Out)
          apply (rule step_transp_op_Write[of _ \<open>Inl p\<close>])
        apply simp_all
        apply blast
        done
      subgoal for p
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some buf2 (split_op buf1) (transp_op (BTL (Inl p) buf3)))\<close>])
        apply (rule conjI)
         apply fastforce
        apply blast
        done
      subgoal for p
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (BTL (Inl p) buf2) (split_op buf1) (transp_op buf3))\<close>])
        apply (rule conjI)
         apply (rule step_tau_step_io_wstep)
          apply fastforce
         apply (rule step_map_op[of \<open>Out (Inr (Inr p)) (BHD (Inl p) buf2)\<close>])
          apply (rule step_comp_op_R_Out)
          apply (rule step_transp_op_Write[of _ \<open>Inl p\<close>])
        apply simp_all
        apply blast
        done
      subgoal for p
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some buf2 (split_op buf1) (transp_op (BTL (Inl p) buf3)))\<close>])
        apply (rule conjI)
         apply fastforce
        apply blast
        done
      subgoal for p
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some buf2 (split_op (BTL (Inr p) buf1)) (transp_op buf3))\<close>])
        apply (rule conjI)
        apply (rule step_tau_step_tau_step_io_wstep[of _
            \<open>map_op projl projr (comp_op Some (BENQ (Inr p) (BHD (Inr p) buf1) buf2) (split_op (BTL (Inr p) buf1)) (transp_op buf3))\<close>
            \<open>map_op projl projr (comp_op Some (BTL (Inr p) (BENQ (Inr p) (BHD (Inr p) buf1) buf2)) (split_op (BTL (Inr p) buf1)) (transp_op (BENQ (Inr p) (BHD (Inr p) buf1) buf3)))\<close>])
           apply fastforce
          apply fastforce
         apply simp
         apply (rule step_map_op[of \<open>Out (Inr (Inl p)) (BHD (Inr p) buf1)\<close>])
          apply (rule step_comp_op_R_Out)
          apply (rule step_transp_op_Write[of _ \<open>Inr p\<close>])
        apply simp_all
        apply blast
        done
      subgoal for p
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some buf2 (split_op buf1) (transp_op (BTL (Inr p) buf3)))\<close>])
        apply (rule conjI)
         apply fastforce
        apply blast
        done
      subgoal for p
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (BTL (Inr p) buf2) (split_op buf1) (transp_op buf3))\<close>])
        apply (rule conjI)
         apply (rule step_tau_step_io_wstep)
          apply fastforce
         apply (rule step_map_op[of \<open>Out (Inr (Inl p)) (BHD (Inr p) buf2)\<close>])
          apply (rule step_comp_op_R_Out)
          apply (rule step_transp_op_Write[of _ \<open>Inr p\<close>])
        apply simp_all
        apply blast
        done
      subgoal for p
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some buf2 (split_op buf1) (transp_op (BTL (Inr p) buf3)))\<close>])
        apply (rule conjI)
         apply fastforce
        apply blast
        done
      done
    done
  done

lemma split_op_transp_op:
  \<open>\<Lambda> \<bullet> \<X> \<approx> map_op id (case_sum Inr Inl) \<Lambda>\<close>
  using split_op_transp_op_bufs[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  unfolding scomp_op_def
  by simp

section \<open>Axiom: A8: Split dummy source\<close>

lemma split_op_dummy_source:
  \<open>\<exclamdown> \<bullet> \<Lambda> ~ \<exclamdown> \<parallel> \<exclamdown>\<close>
  apply (coinduction rule: bisim_coinduct_upto)
  unfolding sim_def
  apply (rule conjI)
  subgoal
    unfolding scomp_op_def pcomp_op_def
    apply (subst comp_op_code)
    apply (subst split_op_code)
    apply auto
    done
  subgoal
    apply (metis cempty_iff choices_pcomp_op_dummy_source step_choicesE)
    done
  done

section \<open>Axiom: A9\<close>

lemma dummy_source_op_sink_op:
  \<open>\<exclamdown> \<bullet> ! ~ \<oslash>\<close>
  apply (coinduction rule: bisim_coinduct_upto)
  unfolding sim_def scomp_op_def
  apply auto
  apply (drule step_map_op_inv)
  apply auto
  apply (drule step_comp_op_cases)
  apply auto
  subgoal
    apply (drule step_map_op_inv)
    apply auto
    apply (drule step_comp_op_cases)
    apply auto
    done
  subgoal
    apply (drule step_map_op_inv)
    apply auto
    apply (drule step_comp_op_cases)
    using no_step_drain_op_Out
    apply fastforce
    done
  subgoal
    apply (drule step_map_op_inv)
    apply auto
    apply (drule step_comp_op_cases)
    apply auto
    apply (drule step_id_op_Out)
     apply auto
    done
  subgoal
    apply (drule step_map_op_inv)
    apply auto
    apply (drule step_comp_op_cases)
    apply auto
    using no_step_id_op_Tau
    apply blast
    done
  subgoal
    apply (drule step_map_op_inv)
    apply auto
    apply (drule step_comp_op_cases)
    apply auto
      apply (drule step_id_op_Out)
       apply auto
    using no_step_id_op_Tau no_step_drain_op_Tau
     apply blast+
    done
  done

section \<open>Axiom A13: Parallel dummy source\<close>

lemma dummy_source_op_pcomp_op:
  \<open>\<exclamdown> ~ \<exclamdown> \<parallel> \<exclamdown>\<close>
  apply (rule choices_Choice_bisim)
  apply (simp add: choices_pcomp_op_dummy_source)
  done

section \<open>Axiom A15: Transpose and merge\<close>

lemma merge_op_comp_op_transp_op_id_op_bufs:
  assumes "Vmn \<equiv> merge_op bufmnmn :: (('m :: countable + 'n :: countable) + 'm + 'n, 'm + 'n, 'd) op"
    and "Vm \<equiv> merge_op bufmm :: ('m + 'm, 'm, 'd) op"
    and "Vn \<equiv>  merge_op bufnn :: ('n + 'n, 'n, 'd) op"
    and "Imm \<equiv> id_op bufm :: ('m, 'm, 'd) op"
    and "Inn \<equiv> id_op bufn :: ('n, 'n, 'd) op"
    and "Xnm \<equiv> transp_op bufnm :: ('n + 'm, 'm + 'n, 'd) op"
  shows "Vmn \<approx> map_op projl projr (comp_op Some buf
      (map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xnm) \<parallel> Inn))
      (Vm \<parallel> Vn))"
  oops

lemma merge_op_transp_merge:
  assumes "Vmn \<equiv> \<V> :: (('m :: countable + 'n ::countable) + 'm + 'n, 'm + 'n, 'd) op"
    and "Vm \<equiv> \<V> :: ('m + 'm, 'm, 'd) op"
    and "Vn \<equiv>  \<V> :: ('n + 'n, 'n, 'd) op"
    and "Imm \<equiv> \<I> :: ('m, 'm, 'd) op"
    and "Inn \<equiv> \<I> :: ('n, 'n, 'd) op"
    and "Xnm \<equiv> \<X> :: ('n + 'm, 'm + 'n, 'd) op"
  shows "Vmn \<approx> map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xnm) \<parallel> Inn) \<bullet> (Vm \<parallel> Vn)"
  oops

section \<open>Axiom A17: Parallel sink\<close>

lemma sink_op_pcomp_op_bufs:
  \<open>map_op projl projr (comp_op Some (case_sum buf1' buf2') (id_op (case_sum buf1 buf2)) drain_op)
  ~ (map_op projl projr (comp_op Some buf1' (id_op buf1) drain_op)) \<parallel> (map_op projl projr (comp_op Some buf2' (id_op buf2) drain_op))\<close>
  apply (coinduction arbitrary: buf1 buf1' buf2 buf2' rule: bisim_coinduct_upto)
  subgoal for buf1 buf1' buf2 buf2'
    unfolding sim_def pcomp_op_def
    apply auto
    subgoal for io
      apply (drule step_map_op_inv)
      apply auto
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (drule step_id_op_Inp)
         apply simp
        apply (cases p)
        subgoal for p'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf1' (id_op (BENQ p' x buf1)) drain_op))
          (map_op projl projr (comp_op Some buf2' (id_op buf2) drain_op))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_base)
          apply auto
          done
        subgoal for p'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf1' (id_op buf1) drain_op))
          (map_op projl projr (comp_op Some buf2' (id_op (BENQ p' x buf2)) drain_op))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_base)
          apply auto
          done
        done
      subgoal
        using no_step_drain_op_Out
        apply meson
        done
      subgoal for p x
        apply (drule step_id_op_Out)
         apply (simp_all split: sum.splits)
        subgoal for p'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (BENQ p' x buf1') (id_op (BTL p' buf1)) drain_op))
          (map_op projl projr (comp_op Some buf2' (id_op buf2) drain_op))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_base)
          apply auto
          done
        subgoal for p'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf1' (id_op buf1) drain_op))
          (map_op projl projr (comp_op Some (BENQ p' x buf2') (id_op (BTL p' buf2)) drain_op))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_base)
          apply auto
          done
        done
      subgoal for p
        apply (erule step_drain_op_Inp)
        apply (auto split: sum.splits)
        subgoal for p'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some (BTL p' buf1') (id_op buf1) drain_op))
       (map_op projl projr (comp_op Some buf2' (id_op buf2) drain_op))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_base)
          apply fast
          done
        subgoal for p'
          apply (rule exI[of _ \<open>comp_op (\<lambda>_. None) (\<lambda>_. []) (map_op projl projr (comp_op Some buf1' (id_op buf1) drain_op))
       (map_op projl projr (comp_op Some (BTL p' buf2') (id_op buf2) drain_op))\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_base)
          apply fast
          done
        done
      using no_step_id_op_Tau no_step_drain_op_Tau
       apply meson+
      done
    subgoal for io
      apply (drule step_comp_op_cases)
      apply auto
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        apply (drule step_id_op_Inp)
         apply simp
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf1' buf2') (id_op (case_sum (BENQ p x buf1) buf2)) drain_op)\<close>])
        apply (rule conjI)
        subgoal
          apply (rule step_map_op[of \<open>Inp (Inl (Inl p)) x\<close>])
           apply simp_all
          apply (rule step_comp_op_L_Inp)
          apply (metis case_sum_BENQ_L step_id_op_Read)
          done
        subgoal
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        done
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        using no_step_drain_op_Out
        apply meson
        done
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        using no_step_drain_op_Out
        apply meson
        done
      subgoal for p x
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        apply (drule step_id_op_Inp)
         apply simp
        apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf1' buf2') (id_op (case_sum buf1 (BENQ p x buf2))) drain_op)\<close>])
        apply (rule conjI)
        subgoal
          apply (rule step_map_op[of \<open>Inp (Inl (Inr p)) x\<close>])
           apply simp_all
          apply (rule step_comp_op_L_Inp)
          apply (metis case_sum_BENQ_R step_id_op_Read)
          done
        subgoal
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        done
      subgoal
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p x
          apply (drule step_id_op_Out)
           apply simp
          apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum (BENQ p x buf1') buf2') (id_op (case_sum (BTL p buf1) buf2)) drain_op)\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        subgoal for p
          apply (erule step_drain_op_Inp)
           apply simp
          apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum (BTL p buf1') buf2') (id_op (case_sum buf1 buf2)) drain_op)\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        using no_step_id_op_Tau no_step_drain_op_Tau
         apply meson+
        done
      subgoal
        apply (drule step_map_op_inv)
        apply auto
        apply (drule step_comp_op_cases)
        apply auto
        subgoal for p x
          apply (drule step_id_op_Out)
           apply simp
          apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf1' (BENQ p x buf2')) (id_op (case_sum buf1 (BTL p buf2))) drain_op)\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        subgoal for p
          apply (erule step_drain_op_Inp)
           apply simp
          apply (rule exI[of _ \<open>map_op projl projr (comp_op Some (case_sum buf1' (BTL p buf2')) (id_op (case_sum buf1 buf2)) drain_op)\<close>])
          apply (rule conjI)
           apply fastforce
          apply (rule bc_sym)
          apply (rule bc_base)
          apply fast
          done
        using no_step_id_op_Tau no_step_drain_op_Tau
         apply meson+
        done
      done
    done
  done

lemma sink_op_pcomp_op:
  \<open>! ~ ! \<parallel> !\<close>
  unfolding scomp_op_def
  using sink_op_pcomp_op_bufs[of \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close> \<open>\<lambda>_. []\<close>]
  by simp

section \<open>Axiom A19: Split and transpose\<close>

lemma split_op_comp_op_transp_op_id_op_bufs:
  assumes "Smn \<equiv> split_op buf :: ('m :: countable + 'n :: countable, ('m + 'n) + 'm + 'n, 'd) op"
    and "Sm \<equiv> split_op buf1 :: ('m, 'm + 'm, 'd) op"
    and "Sn \<equiv> split_op buf1' :: ('n, 'n + 'n, 'd) op"
    and "Imm \<equiv> id_op buf3 :: ('m, 'm, 'd) op"
    and "Inn \<equiv> id_op buf3'' :: ('n, 'n, 'd) op"
    and "Xmn \<equiv> transp_op buf3' :: ('m + 'n, 'n + 'm, 'd) op"
  shows "Smn \<approx> map_op projl projr (comp_op Some buf2
      (Sm \<parallel> Sn)
      (map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xmn) \<parallel> Inn)))"
  oops

lemma split_op_transp_split:
  assumes "Smn \<equiv> \<Lambda> :: ('m + 'n,('m :: countable + 'n ::countable) + 'm + 'n,  'd) op"
    and "Sm \<equiv> \<Lambda> :: ('m, 'm + 'm, 'd) op"
    and "Sn \<equiv> \<Lambda> :: ('n, 'n + 'n, 'd) op"
    and "Imm \<equiv> \<I> :: ('m, 'm, 'd) op"
    and "Inn \<equiv> \<I> :: ('n, 'n, 'd) op"
    and "Xmn \<equiv> \<X> :: ('m + 'n, 'n + 'm, 'd) op"
  shows "Smn \<approx> (Sm \<parallel> Sn) \<bullet> map_op reassoc reassoc (map_op assoc assoc (Imm \<parallel> Xmn) \<parallel> Inn)"
  oops

section \<open>Axiom F3: Loop merge\<close>
lemma loop_op_merge_sink:
  "map_op id Inr \<V>\<up> ~ !"
  oops

section \<open>Axiom F4: Loop split\<close>
lemma loop_op_split_dummy_source:
  "map_op Inr id \<Lambda>\<up> ~ \<exclamdown>"
  oops

end