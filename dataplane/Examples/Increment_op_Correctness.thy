theory Increment_op_Correctness

imports
  Ooo_Input_op_Correctness
  Increment_op
  Source_op
  Dataplane.Timely_Dataflow_Op
begin

(* FIXME: BROKEN because I modified it to use release_caps *)

(* TODO Move. *)
lemma lshift_append_lshift:
  \<open>xs @@- (ys @ zs) @@- lxs = (xs @ ys) @@- zs @@- lxs\<close>
  using lappend_assoc lappend_llist_of lappend_llist_of_llist_of by metis

lemma append_append_lshift:
  \<open>(xs @ ys @ zs) @@- lxs = xs @@- (ys @ zs) @@- lxs\<close>
  using lappend_assoc lappend_llist_of lappend_llist_of_llist_of by metis

lemma ooo_input_op_increment_op_source_op:
  defines \<open>invariant f inc os1 buf os2 \<equiv> initia os1 \<and> en1 os1 = f
  \<and> timely_input_stream (es os1 1) (mset (ocaps os1 1)) \<and> (\<forall>x \<in> set (buf (Inr (1, 1))). is_Inr x)
  \<and> initia os2 \<and> intsum os2 1 1 = [inc] \<and> ocaps os2 1 = map (\<lambda>(_, t). t + inc) (input os2 1)\<close>
    and \<open>my_ooo_input_op os \<equiv> map_op
  (case_option (Inl (0 :: 2)) (\<lambda>(p :: 1). Inr (0 :: 2, 1))) (case_option (Inl (0 :: 2)) (\<lambda>(p :: 1). Inr (0 :: 2, 1)))
  (ooo_input_op {|1 :: 1|} os)\<close>
    and \<open>my_increment_op inc os' \<equiv> map_op
  (case_option (Inl (1 :: 2)) (\<lambda>(p :: 1). Inr (1 :: 2, 1))) (case_option (Inl (1 :: 2)) (\<lambda>(p :: 1). Inr (1 :: 2, 1)))
  (increment_op (1 :: 1) (1 :: 1) inc os')\<close>
    and \<open>my_source_op f inc os1 buf os2 \<equiv> map_op (\<lambda>(p :: 1). (1, 1)) (\<lambda>(p :: 1). (1, 1))
    (source_op ((\<lambda>(p :: 1). outpu os2 1 @@- lmap (\<lambda>(d, t). (d, t + inc))
      ((input os2 1 @ map projr (buf (Inr (1, 1))) @ outpu os1 1) @@- lmap (\<lambda>x. case x of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os1 1))))))\<close>
  assumes \<open>invariant f inc os1 buf os2\<close>
  shows \<open>dataflow_op sg (map_op (case_sum id id) (case_sum id id)
  (comp_op [Inr (0 :: 2, 1 :: 1) \<mapsto> Inr (1 :: 2, 1 :: 1)] buf (my_ooo_input_op os1) (my_increment_op inc os2)))
  \<approx> my_source_op f inc os1 buf os2\<close>
  using assms(5)
proof (coinduction arbitrary: sg os1 buf os2 rule: wbisim_coinduct_upto'')
  case SIM1
  show ?case (is \<open>\<exists>_. _ \<and> wbisim_cong ?R _ _\<close>)
  proof -
    define R where \<open>R = ?R\<close>
    have invariant_initia: \<open>invariant f inc os1 buf os2 \<Longrightarrow> initia os1\<close>
      \<open>invariant f inc os1 buf os2 \<Longrightarrow> initia os2\<close> unfolding invariant_def by blast+
    show ?thesis
    proof -
      have "\<exists>op2'. wstep (Out (1, 1) (d, t)) (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc (os2\<lparr>outpu := (outpu os2)(1 := xs)\<rparr>))))) op2'"
        (is \<open>\<exists>_. _ \<and> wbisim_cong _ (dataflow_op _ (map_op _ _ (comp_op _ _ _ (my_increment_op _ ?os2')))) _\<close>)
        if "invariant f inc os1 buf os2"
          and "outpu os2 1 = (d, t) # xs"
        for d :: 'b
          and t :: 'c
          and xs :: "('b \<times> 'c) buf"
      proof -
        have \<open>step (Out 1 (d, t))
  (source_op ((\<lambda>(p :: 1). outpu os2 1 @@- lmap (\<lambda>(d, t). (d, t + inc))
      ((input os2 1 @ map projr (buf (Inr (1, 1))) @ outpu os1 1) @@- lmap (\<lambda>x. case x of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os1 1))))))
  (source_op ((\<lambda>(p :: 1). outpu ?os2' 1 @@- lmap (\<lambda>(d, t). (d, t + inc))
      ((input ?os2' 1 @ map projr (buf (Inr (1, 1))) @ outpu os1 1) @@- lmap (\<lambda>x. case x of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os1 1))))))\<close>
          using that(2) defaults_num1_def by auto
        hence \<open>wstep (Out (1, 1) (d, t)) (my_source_op f inc os1 buf os2) (my_source_op f inc os1 buf ?os2')\<close>
          using my_source_op_def by auto
        thus ?thesis using that(1) unfolding R_def invariant_def by (fastforce intro!: wbc_base)
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] (BENQ (Inr (1, 1)) (Inr (d, t)) buf)
    (my_ooo_input_op (os1\<lparr>outpu := (outpu os1)(1 := xs)\<rparr>)) (my_increment_op inc os2)))) op2'"
        (is \<open>\<exists>_. _ \<and> wbisim_cong _ (dataflow_op _ (map_op _ _ (comp_op _ ?buf' (my_ooo_input_op ?os1') _))) _\<close>)
        if "invariant f inc os1 buf os2"
          and "outpu os1 1 = (d, t) # xs"
        for d :: 'b
          and t :: 'c
          and xs :: "('b \<times> 'c) buf"
      proof -
        have \<open>my_source_op f inc os1 buf os2 = my_source_op f inc ?os1' ?buf' os2\<close>
          using that(2) unfolding my_source_op_def by simp
        thus ?thesis using that(1) unfolding R_def invariant_def by (fastforce intro!: wbc_base)
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] (BTL (Inr (1, 1)) buf)
    (my_ooo_input_op os1) \<oslash>))) op2'"
        if "invariant f inc os1 buf os2"
          and "buf (Inr (1, 1)) \<noteq> []"
          and "is_Inl (BHD (Inr (1, 1)) buf)"
        using that sum.exhaust is_Inl.simps(2) is_Inr.simps(2) hd_in_set unfolding invariant_def BHD_def
        by (metis (no_types, opaque_lifting))
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] (BTL (Inr (1, 1)) buf)
    (my_ooo_input_op os1) (my_increment_op inc (consumes os2 1 t d))))) op2'"
        (is \<open>\<exists>_. _ \<and> wbisim_cong _ (dataflow_op _ (map_op _ _ (comp_op _ ?buf' _ (my_increment_op _ ?os2')))) _\<close>)
        if "invariant f inc os1 buf os2"
          and "buf (Inr (1, 1)) \<noteq> []"
          and "Inr (d, t) = BHD (Inr (1, 1)) buf"
        for d :: 'b
          and t :: 'c
      proof -
        have \<open>map ((\<lambda>(d, t). (d, t + inc)) \<circ> projr) (buf (Inr (1, 1)))
  = (d, t + inc) # map ((\<lambda>(d, t). (d, t + inc)) \<circ> projr) (BTL (Inr (1, 1)) buf (Inr (1, 1)))\<close>
          using that BHD_def BTL_access hd_Cons_tl hd_map list.map_disc_iff map_tl o_apply split_conv
            sum.sel(2) unfolding invariant_def by (smt (verit, best))
        hence \<open>my_source_op f inc os1 buf os2 = my_source_op f inc os1 ?buf' ?os2'\<close>
          unfolding my_source_op_def consumes_def add_caps_def by simp
        moreover have \<open>invariant f inc os1 ?buf' ?os2'\<close> using that(1) unfolding invariant_def BTL_def
            consumes_def add_caps_def enum_num1_def by (auto dest: in_set_tlD)
        ultimately show ?thesis unfolding R_def by blast
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
  (my_ooo_input_op os1') (my_increment_op inc os2)))) op2'"
        if "invariant f inc os1 buf os2"
          and "os1' |\<in>| ooo_input_op_logic {|1|} os1"
        for os1' :: "(1, 'b, 'a, 'c, 'd) input_state_scheme"
      proof -
        have \<open>my_source_op f inc os1 buf os2 = my_source_op f inc os1' buf os2\<close> using that
          unfolding invariant_def timely_input_stream_def my_source_op_def ooo_input_op_logic_def
            produce_def drop_cap_def add_cap_def by (fastforce simp flip: snoc_shift split: llist.splits)
        moreover have \<open>invariant f inc os1' buf os2\<close> using that
            timely_input_stream_ooo_input_op_logic[OF _ that(2)] unfolding invariant_def
            ooo_input_op_logic_def drop_caps_def produce_def drop_cap_def add_cap_def
          by (force split: llist.splits event.splits)
        ultimately show ?thesis unfolding R_def by blast
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
  (my_ooo_input_op os1) (my_increment_op inc os2')))) op2'"
        if "invariant f inc os1 buf os2"
          and "os2' |\<in>| increment_op_logic 1 1 inc os2"
        for os2' :: "(1, 'b, 'c, 'e) operator_state_scheme"
      proof -
        have outpu_os2': \<open>outpu os2' 1 = outpu os2 1 @ map (\<lambda>(d, t). (d, t + inc)) (input os2 1)\<close>
          using that(2) unfolding trace_simp increment_op_logic_def drop_caps_def release_caps_def produces_def by (simp split: prod.splits if_splits)
        have input_os2': \<open>input os2' 1 = []\<close> using that(2) unfolding increment_op_logic_def by (simp split: prod.splits if_splits)
        have \<open>my_source_op f inc os1 buf os2 = my_source_op f inc os1 buf os2'\<close>
          using outpu_os2' input_os2' unfolding my_source_op_def by (simp add: lshift_append_lshift)
        moreover have \<open>invariant f inc os1 buf os2'\<close> using that unfolding invariant_def
            increment_op_logic_def release_caps_def drop_caps_def produces_def enum_num1_def by (simp add: comp_def split: prod.splits if_splits)
        ultimately show ?thesis unfolding R_def by blast
      qed
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op (sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 1 (nxt sg) st) (pt_tr sg)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc os2')))) op2'"
        if "invariant f inc os1 buf os2"
          and "(os2', st) = obtain_progress os2"
        for st :: "(1, 'c) shared_state"
          and os2' :: "(1, 'b, 'c, 'e) operator_state_scheme"
        using that unfolding R_def invariant_def my_source_op_def obtain_progress_def by (fastforce intro!: wbc_base)
      moreover have "\<exists>op2'. (step Tau)\<^sup>*\<^sup>* (my_source_op f inc os1 buf os2) op2'
  \<and> wbisim_cong R (dataflow_op (sg\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg) (extract_progress 0 (nxt sg) st) (pt_tr sg)\<rparr>) (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
  (my_ooo_input_op os1') (my_increment_op inc os2)))) op2'"
        if "invariant f inc os1 buf os2"
          and "(os1', st) = obtain_progress os1"
        for st :: "(1, 'c) shared_state"
          and os1' :: "(1, 'b, 'a, 'c, 'd) input_state_scheme"
        using that unfolding R_def invariant_def my_source_op_def obtain_progress_def by (fastforce intro!: wbc_base)
      ultimately show ?thesis unfolding R_def[symmetric]
        by (sim_cases sim: SIM1
            defs: my_ooo_input_op_def ooo_input_op_def my_increment_op_def increment_op_def
            elims: step_dataflow_op_elim step_map_op_elim step_comp_op_elim step_builder_op_elim
            intros: invariant_initia)
    qed
  qed
next
  case SIM2
  show ?case (is \<open>\<exists>_. _ \<and> wbisim_cong ?R _ _\<close>)
  proof -
    define R where \<open>R = ?R\<close>
    have "\<exists>op2'. wstep (Out (1, 1) (d, t)) (dataflow_op sg (map_op (case_sum id id) (case_sum id id)
    (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf (my_ooo_input_op os1) (my_increment_op inc os2)))) op2'
  \<and> wbisim_cong R op2' (map_op (\<lambda>(p :: 1). (1, 1)) (\<lambda>p. (1, 1)) (source_op ((\<lambda>(p :: 1). LCons (d, t) lxs)(1 := lxs))))"
      if inv: "invariant f inc os1 buf os2"
        and source_llist: "outpu os2 1 @@- lmap (\<lambda>(d, t). (d, t + inc)) ((input os2 1 @ map projr (buf (Inr (1, 1))) @ outpu os1 1)
  @@- lmap (\<lambda>x. case x of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os1 1))) = LCons (d, t) lxs"
      for d :: 'b
        and t :: 'c
        and lxs :: "('b \<times> 'c) llist"
    proof (cases \<open>outpu os2 1\<close>)
      case outpu_os2_Nil: Nil
      show ?thesis
      proof (cases \<open>input os2 1\<close>)
        case input_os2_Nil: Nil
        show ?thesis
        proof (cases \<open>buf (Inr (1, 1))\<close>)
          case buf_Nil: Nil
          show ?thesis
          proof (cases \<open>outpu os1 1\<close>)
            case outpu_os1_Nil: Nil
            let ?lxs' = \<open>ltl (ldropWhile (Not \<circ> is_Data) (es os1 1))\<close>
            obtain t' d' where t'_d': \<open>ldropWhile (Not \<circ> is_Data) (es os1 1) = LCons (Data t' d') ?lxs'\<close>
              \<open>t' + inc = t\<close> \<open>f d' = d\<close>
            proof -
              have \<open>lmap (\<lambda>(d, t). (d, t + inc)) (lmap (\<lambda>x. case x of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os1 1)))
  = LCons (d, t) lxs\<close> using source_llist outpu_os2_Nil input_os2_Nil buf_Nil outpu_os1_Nil by simp
              then obtain t' where t': \<open>lmap (\<lambda>x. case x of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os1 1))
  = LCons (d, t') (ltl (lmap (\<lambda>x. case x of Data t d \<Rightarrow> (f d, t)) (lfilter is_Data (es os1 1))))\<close> \<open>t' + inc = t\<close>
                using lmap_eq_LCons_conv case_prod_Pair_iden case_prod_conv llist.sel(3) prod.simps(1)
                  split_cong by (smt (verit, ccfv_threshold))
              then obtain d' where d': \<open>lfilter is_Data (es os1 1) = LCons (Data t' d') (ltl (lfilter is_Data (es os1 1)))\<close> \<open>f d' = d\<close>
                using lmap_eq_LCons_conv event.case fun_comp_eq_conv is_Data_def ldropWhile_LConsD
                  lfilter_eq_LCons llist.sel(3) prod.simps(1) lfilter_eq_LConsD
                by (smt (verit, ccfv_threshold))
              thus ?thesis using that t'(2) d'(2) lfilter_eq_LCons llist.sel(3) by metis
            qed
            have lfinite_not_Data: \<open>lfinite (ltakeWhile (Not \<circ> is_Data) (es os1 1))\<close>
              using t'_d'(1) lfinite_ltakeWhile by fastforce
            let ?xs = \<open>list_of (ltakeWhile (Not \<circ> is_Data) (es os1 1))\<close>
            have set_not_Data: \<open>\<forall>e \<in> set ?xs. \<not> is_Data e\<close>
              using lfinite_not_Data set_list_of lset_ltakeWhileD trimono_spec_defs(3) by metis
            let ?os1_1 = \<open>foldl (ooo_input_os_Drop_Mint 1) (os1\<lparr>es := (es os1)(1 := ?lxs')\<rparr>) ?xs\<close>
            have en1_os1_1: \<open>en1 ?os1_1 = f\<close> using that(1) foldl_ooo_input_os_Drop_Mint(4)[OF set_not_Data]
              unfolding invariant_def by fast
            let ?os1_2 = \<open>produce ?os1_1 (Cap t' 1) [f d']\<close>
            have \<open>(step Tau)\<^sup>*\<^sup>* (ooo_input_op {|1 :: 1|} os1) (ooo_input_op {|1 :: 1|} ?os1_2)\<close>
              using that(1) step_Taus_ooo_input_op_Drop_Mint[OF lfinite_not_Data t'_d'(1)] en1_os1_1
              unfolding invariant_def timely_input_stream_def by simp
            hence step_Taus: \<open>(step Tau)\<^sup>*\<^sup>*
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc os2))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op ?os1_2) (my_increment_op inc os2))))\<close> unfolding my_ooo_input_op_def by fast
            have initia_os1_2: \<open>initia ?os1_2\<close> using that(1) foldl_ooo_input_os_Drop_Mint(1)[OF set_not_Data]
              unfolding invariant_def produce_def by fastforce
            have outpu_os1_2: \<open>outpu ?os1_2 1 = [(d, t')]\<close>
              using outpu_os1_Nil t'_d'(3) foldl_ooo_input_os_Drop_Mint(2)[OF set_not_Data, where os'=\<open>?os1_1\<close>]
              unfolding produce_def by simp
            have es_os1_2: \<open>es ?os1_2 1 = ?lxs'\<close>
              using foldl_ooo_input_os_Drop_Mint(5)[OF set_not_Data, where os'=\<open>?os1_1\<close>]
              unfolding produce_def by simp
            have timely_input_stream_os1_2: \<open>timely_input_stream ?lxs' (mset (ocaps ?os1_2 1))\<close>
              using that(1) timely_input_stream_foldl_ooo_input_os_Drop_Mint[OF lfinite_not_Data t'_d'(1)]
              unfolding invariant_def produce_def by simp
            let ?os1_3 = \<open>?os1_2\<lparr>outpu := (outpu ?os1_2)(1 := [])\<rparr>\<close>
            have step_Tau_1: \<open>step Tau
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op ?os1_2) (my_increment_op inc os2))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] (BENQ (Inr (1, 1)) (Inr (d, t')) buf)
    (my_ooo_input_op ?os1_3) (my_increment_op inc os2))))\<close> using initia_os1_2 outpu_os1_2
              unfolding my_ooo_input_op_def ooo_input_op_def
              by (auto intro!: step_Tau_dataflow_op_Tau_intro)
            let ?os2_1 = \<open>consumes os2 1 t' d\<close>
            have step_Tau_2: \<open>step Tau
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] (BENQ (Inr (1, 1)) (Inr (d, t')) buf)
    (my_ooo_input_op ?os1_3) (my_increment_op inc os2))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op ?os1_3) (my_increment_op inc ?os2_1))))\<close> using that(1) buf_Nil
              unfolding invariant_def my_increment_op_def increment_op_def
              by (auto intro!: step_Tau_dataflow_op_Tau_intro)
            obtain os2_2 where os2_2: \<open>os2_2 |\<in>| increment_op_logic 1 1 inc ?os2_1\<close>
              unfolding increment_op_logic_def trace_simp Let_def 
              using inv invariant_def by force
            hence initia_os2_2: \<open>initia os2_2\<close> using that(1) unfolding invariant_def increment_op_logic_def
                consumes_def add_caps_def drop_caps_def produces_def by simp
            have input_os2_2: \<open>input os2_2 1 = []\<close> using os2_2 unfolding increment_op_logic_def by (simp split: prod.splits if_splits)
            have outpu_os2_2: \<open>outpu os2_2 1 = [(d, t)]\<close> using outpu_os2_Nil input_os2_Nil os2_2 t'_d'(2)
              unfolding increment_op_logic_def consumes_def add_caps_def drop_caps_def produces_def
              by (simp split: prod.splits if_splits)
            have summar_os2_2: \<open>intsum os2_2 1 1 = [inc]\<close> using that(1) os2_2 unfolding invariant_def
                increment_op_logic_def consumes_def add_caps_def drop_caps_def produces_def by simp
            have ocaps_os2_2: \<open>ocaps os2_2 1 = []\<close> using os2_2 unfolding increment_op_logic_def
                consumes_def add_caps_def drop_caps_def produces_def enum_num1_def by (simp add: comp_def split: prod.splits if_splits)
            have \<open>step Tau (my_increment_op inc ?os2_1) (my_increment_op inc os2_2)\<close> using that(1)
                Cons os2_2 unfolding invariant_def my_increment_op_def increment_op_def consumes_def
                add_caps_def by (auto intro!: step_builder_op_Silent)
            hence step_Tau_3: \<open>step Tau
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op ?os1_3) (my_increment_op inc ?os2_1))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op ?os1_3) (my_increment_op inc os2_2))))\<close> by auto
            let ?os2_3 = \<open>os2_2\<lparr>outpu := (outpu os2_2)(1 := [])\<rparr>\<close>
            have \<open>step (Out (Inr (1, 1)) (Inr (d, t))) (my_increment_op inc os2_2) (my_increment_op inc ?os2_3)\<close>
              using that outpu_os2_Nil input_os2_Nil Cons t'_d'(2) initia_os2_2 outpu_os2_2
              unfolding invariant_def my_increment_op_def increment_op_def by auto
            hence \<open>step (Out (1, 1) (d, t))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op ?os1_3) (my_increment_op inc os2_2))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op ?os1_3) (my_increment_op inc ?os2_3))))\<close> by auto
            hence \<open>wstep (Out (1, 1) (d, t))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc os2))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op ?os1_3) (my_increment_op inc ?os2_3))))\<close> using step_Taus step_Tau_1 step_Tau_2
              step_Tau_3 step_tau_step_io_wstep wstep_trans'(1) wstep_trans_tau_1 by meson
            moreover have \<open>map_op (\<lambda>(p :: 1). (1, 1)) (\<lambda>(p :: 1). (1, 1)) (source_op ((\<lambda>(p :: 1). LCons (d, t) lxs)(1 := lxs)))
  = my_source_op f inc ?os1_3 buf ?os2_3\<close> using that(2) outpu_os2_Nil input_os2_Nil buf_Nil
              outpu_os1_Nil input_os2_2 es_os1_2 unfolding my_source_op_def
              by (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op] dest: arg_cong[where f=ltl] simp add: fun_eq_iff ltl_lfilter)
            moreover have \<open>invariant f inc ?os1_3 buf ?os2_3\<close> using that(1) initia_os1_2 en1_os1_1
                es_os1_2 timely_input_stream_os1_2 initia_os2_2 input_os2_2 summar_os2_2 ocaps_os2_2
              unfolding invariant_def produce_def by simp
            ultimately show ?thesis unfolding R_def by (fastforce intro!: wbc_base)
          next
            case (Cons x xs)
            then obtain t' where t': \<open>t' + inc = t\<close> \<open>x = (d, t')\<close>
              using source_llist outpu_os2_Nil input_os2_Nil buf_Nil by (simp split: prod.splits)
            let ?os1' = \<open>os1\<lparr>outpu := (outpu os1)(1 := xs)\<rparr>\<close>
            have step_Tau_1: \<open>step Tau
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc os2))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] (BENQ (Inr (1, 1)) (Inr (d, t')) buf)
    (my_ooo_input_op ?os1') (my_increment_op inc os2))))\<close> using that(1) Cons t'(2)
              unfolding invariant_def my_ooo_input_op_def ooo_input_op_def
              by (auto intro!: step_Tau_dataflow_op_Tau_intro)
            let ?os2_1 = \<open>consumes os2 1 t' d\<close>
            have step_Tau_2: \<open>step Tau
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] (BENQ (Inr (1, 1)) (Inr (d, t')) buf)
    (my_ooo_input_op ?os1') (my_increment_op inc os2))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op ?os1') (my_increment_op inc ?os2_1))))\<close> using that(1) buf_Nil
              unfolding invariant_def my_increment_op_def increment_op_def
              by (auto intro!: step_Tau_dataflow_op_Tau_intro)
            obtain os2_2 where os2_2: \<open>os2_2 |\<in>| increment_op_logic 1 1 inc ?os2_1\<close>
              unfolding increment_op_logic_def invariant_def trace_simp
              using SIM2(1) invariant_def by auto
            hence initia_os2_2: \<open>initia os2_2\<close> using that(1) unfolding invariant_def increment_op_logic_def
                consumes_def add_caps_def drop_caps_def produces_def by simp
            have input_os2_2: \<open>input os2_2 1 = []\<close> using os2_2 unfolding increment_op_logic_def by (simp split: prod.splits if_splits)
            have outpu_os2_2: \<open>outpu os2_2 1 = [(d, t)]\<close> using outpu_os2_Nil input_os2_Nil os2_2 t'(1)
              unfolding increment_op_logic_def consumes_def add_caps_def drop_caps_def produces_def
              by (simp split: prod.splits if_splits)
            have summar_os2_2: \<open>intsum os2_2 1 1 = [inc]\<close> using that(1) os2_2 unfolding invariant_def
                increment_op_logic_def consumes_def add_caps_def drop_caps_def produces_def by simp
            have ocaps_os2_2: \<open>ocaps os2_2 1 = []\<close> using os2_2 unfolding increment_op_logic_def
                consumes_def add_caps_def drop_caps_def produces_def enum_num1_def by (simp add: comp_def split: prod.splits if_splits)
            have \<open>step Tau (my_increment_op inc ?os2_1) (my_increment_op inc os2_2)\<close> using that(1)
                Cons os2_2 unfolding invariant_def my_increment_op_def increment_op_def consumes_def
                add_caps_def by (auto intro!: step_builder_op_Silent)
            hence step_Tau_3: \<open>step Tau
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op ?os1') (my_increment_op inc ?os2_1))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op ?os1') (my_increment_op inc os2_2))))\<close> by auto
            let ?os2_3 = \<open>os2_2\<lparr>outpu := (outpu os2_2)(1 := [])\<rparr>\<close>
            have \<open>step (Out (Inr (1, 1)) (Inr (d, t))) (my_increment_op inc os2_2) (my_increment_op inc ?os2_3)\<close>
              using that outpu_os2_Nil input_os2_Nil Cons t'(1) initia_os2_2 outpu_os2_2
              unfolding invariant_def my_increment_op_def increment_op_def by auto
            hence \<open>step (Out (1, 1) (d, t))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op ?os1') (my_increment_op inc os2_2))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op ?os1') (my_increment_op inc ?os2_3))))\<close> by auto
            hence \<open>wstep (Out (1, 1) (d, t))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc os2))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op ?os1') (my_increment_op inc ?os2_3))))\<close> using step_Tau_1 step_Tau_2 step_Tau_3
              by fast
            moreover have \<open>map_op (\<lambda>(p :: 1). (1, 1)) (\<lambda>(p :: 1). (1, 1)) (source_op ((\<lambda>(p :: 1). LCons (d, t) lxs)(1 := lxs)))
  = my_source_op f inc ?os1' buf ?os2_3\<close> using that outpu_os2_Nil input_os2_Nil buf_Nil Cons
              input_os2_2 outpu_os2_2 unfolding invariant_def my_source_op_def
              by (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op])
            moreover have \<open>invariant f inc ?os1' buf ?os2_3\<close> using that(1) initia_os2_2 input_os2_2
                summar_os2_2 ocaps_os2_2 unfolding invariant_def produce_def by simp
            ultimately show ?thesis unfolding R_def by (fastforce intro!: wbc_base)
          qed
        next
          case (Cons x xs)
          then obtain t' where t': \<open>t' + inc = t\<close> \<open>BHD (Inr (1, 1)) buf = Inr (d, t')\<close>
            using inv source_llist outpu_os2_Nil input_os2_Nil unfolding invariant_def BHD_def
            by (cases x; simp split: prod.splits)
          let ?os2_1 = \<open>consumes os2 1 t' d\<close>
          let ?buf' = \<open>BTL (Inr (1, 1)) buf\<close>
          have step_Tau_1: \<open>step Tau
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc os2))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] ?buf'
    (my_ooo_input_op os1) (my_increment_op inc ?os2_1))))\<close>  using that(1) Cons t'(2)
            unfolding invariant_def my_increment_op_def increment_op_def
            by (auto intro!: step_Tau_dataflow_op_Tau_intro)
          obtain os2_2 where os2_2: \<open>os2_2 |\<in>| increment_op_logic 1 1 inc ?os2_1\<close>
            unfolding increment_op_logic_def invariant_def trace_simp
            using SIM2(1) invariant_def by auto
          hence initia_os2_2: \<open>initia os2_2\<close> using that(1) unfolding invariant_def increment_op_logic_def
              consumes_def add_caps_def drop_caps_def produces_def by simp
          have input_os2_2: \<open>input os2_2 1 = []\<close> using os2_2 unfolding increment_op_logic_def by (simp add: comp_def split: prod.splits if_splits)
          have outpu_os2_2: \<open>outpu os2_2 1 = [(d, t)]\<close> using outpu_os2_Nil input_os2_Nil os2_2 t'(1)
            unfolding increment_op_logic_def consumes_def add_caps_def drop_caps_def produces_def
            by (simp add: comp_def split: prod.splits if_splits)
          have summar_os2_2: \<open>intsum os2_2 1 1 = [inc]\<close> using that(1) os2_2 unfolding invariant_def
              increment_op_logic_def consumes_def add_caps_def drop_caps_def produces_def by simp
          have ocaps_os2_2: \<open>ocaps os2_2 1 = []\<close> using os2_2 unfolding increment_op_logic_def
              consumes_def add_caps_def drop_caps_def produces_def enum_num1_def by (simp add: comp_def split: prod.splits if_splits)
          have \<open>step Tau (my_increment_op inc ?os2_1) (my_increment_op inc os2_2)\<close> using that(1)
              Cons os2_2 unfolding invariant_def my_increment_op_def increment_op_def consumes_def
              add_caps_def by (auto intro!: step_builder_op_Silent)
          hence step_Tau_2: \<open>step Tau
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] ?buf'
    (my_ooo_input_op os1) (my_increment_op inc ?os2_1))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] ?buf'
    (my_ooo_input_op os1) (my_increment_op inc os2_2))))\<close> by auto
          let ?os2_3 = \<open>os2_2\<lparr>outpu := (outpu os2_2)(1 := [])\<rparr>\<close>
          have \<open>step (Out (Inr (1, 1)) (Inr (d, t))) (my_increment_op inc os2_2) (my_increment_op inc ?os2_3)\<close>
            using that outpu_os2_Nil input_os2_Nil Cons t'(1) initia_os2_2 outpu_os2_2
            unfolding invariant_def my_increment_op_def increment_op_def by auto
          hence \<open>step (Out (1, 1) (d, t))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] ?buf'
    (my_ooo_input_op os1) (my_increment_op inc os2_2))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] ?buf'
    (my_ooo_input_op os1) (my_increment_op inc ?os2_3))))\<close> by auto
          hence \<open>wstep (Out (1, 1) (d, t))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc os2))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] ?buf'
    (my_ooo_input_op os1) (my_increment_op inc ?os2_3))))\<close> using step_Tau_1 step_Tau_2 by fast
          moreover have \<open>map_op (\<lambda>(p :: 1). (1, 1)) (\<lambda>(p :: 1). (1, 1)) (source_op ((\<lambda>(p :: 1). LCons (d, t) lxs)(1 := lxs)))
  = my_source_op f inc os1 ?buf' ?os2_3\<close> using that outpu_os2_Nil input_os2_Nil Cons input_os2_2
            outpu_os2_2 unfolding invariant_def my_source_op_def BTL_def
            by (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op])
          moreover have \<open>invariant f inc os1 ?buf' ?os2_3\<close> using that(1) initia_os2_2 input_os2_2
              summar_os2_2 ocaps_os2_2 unfolding invariant_def produce_def BTL_def
            by (auto dest: in_set_tlD)
          ultimately show ?thesis unfolding R_def by (fastforce intro!: wbc_base)
        qed
      next
        case (Cons _ xs)
        obtain os2' where os2': \<open>os2' |\<in>| increment_op_logic 1 1 inc os2\<close>
          unfolding increment_op_logic_def invariant_def trace_simp Let_def
          using inv invariant_def local.Cons by force
        hence initia_os2': \<open>initia os2'\<close> using that(1) unfolding invariant_def increment_op_logic_def
            drop_caps_def produces_def by (simp add: comp_def split: prod.splits if_splits)
        have input_os2': \<open>input os2' 1 = []\<close> using os2' unfolding increment_op_logic_def by (simp add: comp_def split: prod.splits if_splits)
        have outpu_os2': \<open>outpu os2' 1 = map (\<lambda>(d, t). (d, t + inc)) (input os2 1)\<close>
          using outpu_os2_Nil os2' unfolding increment_op_logic_def drop_caps_def produces_def
          by (simp add: comp_def split: prod.splits if_splits)
        have summar_os2': \<open>intsum os2' 1 1 = [inc]\<close> using that(1) os2' unfolding invariant_def
            increment_op_logic_def consumes_def add_caps_def drop_caps_def produces_def by (simp add: comp_def split: prod.splits if_splits)
        have ocaps_os2': \<open>ocaps os2' 1 = []\<close> using os2' unfolding increment_op_logic_def
            consumes_def add_caps_def drop_caps_def produces_def enum_num1_def by (simp add: comp_def split: prod.splits if_splits)
        have \<open>step Tau (my_increment_op inc os2) (my_increment_op inc os2')\<close> using that(1) Cons os2'
          unfolding invariant_def my_increment_op_def increment_op_def
          by (auto intro!: step_builder_op_Silent)
        hence step_Tau: \<open>step Tau
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc os2))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc os2'))))\<close> by auto
        let ?os2'' = \<open>os2'\<lparr>outpu := (outpu os2')(1 := tl (outpu os2' 1))\<rparr>\<close>
        have \<open>step (Out (Inr (1, 1)) (Inr (d, t))) (my_increment_op inc os2') (my_increment_op inc ?os2'')\<close>
          using that outpu_os2_Nil Cons initia_os2' outpu_os2' unfolding invariant_def my_increment_op_def
            increment_op_def by auto
        hence step_Out: \<open>step (Out (1, 1) (d, t))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc os2'))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc ?os2''))))\<close> by auto
        have \<open>map_op (\<lambda>(p :: 1). (1, 1)) (\<lambda>(p :: 1). (1, 1)) (source_op ((\<lambda>(p :: 1). LCons (d, t) lxs)(1 := lxs)))
  = my_source_op f inc os1 buf ?os2''\<close> using that outpu_os2_Nil Cons input_os2' outpu_os2'
          unfolding invariant_def my_source_op_def
          by (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op] simp add: append_append_lshift)
        moreover have \<open>invariant f inc os1 buf ?os2''\<close> using that(1) initia_os2' input_os2'
            summar_os2' ocaps_os2' unfolding invariant_def produce_def by simp
        ultimately show ?thesis using step_Tau step_Out unfolding R_def by (fastforce intro!: wbc_base)
      qed
    next
      case (Cons _ xs)
      let ?os2' = \<open>os2\<lparr>outpu := (outpu os2)(1 := xs)\<rparr>\<close>
      have \<open>wstep (Out (1, 1) (d, t))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc os2))))
  (dataflow_op sg (map_op (case_sum id id) (case_sum id id) (comp_op [Inr (0, 1) \<mapsto> Inr (1, 1)] buf
    (my_ooo_input_op os1) (my_increment_op inc ?os2'))))\<close> using that Cons unfolding invariant_def
        my_increment_op_def increment_op_def by (auto intro!: step_wstep)
      moreover have \<open>map_op (\<lambda>(p :: 1). (1, 1)) (\<lambda>(p :: 1). (1, 1)) (source_op ((\<lambda>(p :: 1). LCons (d, t) lxs)(1 := lxs)))
  = my_source_op f inc os1 buf ?os2'\<close> using that Cons unfolding invariant_def my_source_op_def
        by (auto intro!: arg_cong[where f=\<open>map_op _ _\<close>] arg_cong[where f=source_op])
      ultimately show ?thesis using that(1) unfolding invariant_def R_def by (fastforce intro!: wbc_base)
    qed
    thus ?thesis unfolding R_def[symmetric]
      by (sim_cases sim: SIM2 defs: my_source_op_def elims: step_map_op_elim step_source_op_elim)
  qed
qed

end