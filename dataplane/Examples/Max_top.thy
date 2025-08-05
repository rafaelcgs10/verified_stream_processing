theory Max_top

imports
  "../Timely_Infrastructure"
  Input_top
begin 

(* FIXME: move me *)
abbreviation "choice5 op1 op2 op3 op4 op5 \<equiv> choice3 (choice2 op1 op2) (choice2 op3 op4) op5"

find_consts "_ + _ \<Rightarrow> _" name: "is_"

abbreviation "mint_cap os p t \<equiv> os\<lparr> inter := inter os @ [(p, t, 1)] \<rparr>"

abbreviation "produces os batch \<equiv> os\<lparr> outpu := (\<lambda> p. outpu os p @ map (\<lambda> (x, cap). (x, time cap)) (filter (\<lambda> (x, cap). out cap = p) batch)), produ := produ os @ map (\<lambda> (x, cap). (out cap, time cap, 1)) batch \<rparr>"

abbreviation "drop_caps os caps \<equiv> (os\<lparr> inter := inter os @ map (\<lambda> cap. (out cap, time cap, -1)) caps \<rparr>)"


corec max_top' where
  "max_top' os buf caps = choice5
   (Read None (\<lambda> st. if is_Inl st \<and> is_Inr (projl st) then max_top' (os\<lparr> front := projr (projl st) \<rparr>) buf caps else \<oslash>))
   (let below_caps = [cap \<leftarrow> caps. less_than_frontier (front os 0) (time cap)] in
    let above_caps = [cap \<leftarrow> caps. \<not> less_than_frontier (front os 0) (time cap)] in
    let batch = map (\<lambda> cap. (Max (set (buf cap)), cap)) below_caps in
    let os' = produces os batch in
    let os'' = drop_caps os' below_caps in
    let buf' = (\<lambda> cap. if cap \<in> set below_caps then [] else buf cap) in
    Silent (max_top' os'' buf' above_caps))
   (Read (Some 0)
    (\<lambda> x. if is_Inl x then \<oslash> else
     let (n, t) = projr x in
     let (caps', os') = (if Cap t 0 \<in> set caps then (caps, os) else (caps @ [Cap t 0], mint_cap os 0 t)) in
     let buf' = BENQ (Cap t 0) n buf in
     max_top' os' buf' caps'))
    ((case outpu os 0 of
         [] \<Rightarrow> Silent (max_top' os buf caps)
       |  x # xs \<Rightarrow> send_output (max_top' (os\<lparr> outpu := (outpu os)(0 := xs ) \<rparr>) buf caps) 0 x))
    (let (os', st) = obtain_progress os in
     send_progress (max_top' os' buf caps) st)"

lemma step_max'_top_elim:
  assumes "step io (max_top' os buf caps) op"
  obtains
    st where "io = Inp None st" "\<not> is_Inl st \<or> (is_Inl st \<and> \<not> is_Inr (projl st))" "op = \<oslash>" 
  | st where "io = Inp None st" "is_Inl st" "is_Inr (projl st)" "op = max_top' (os\<lparr> front := projr (projl st) \<rparr>) buf caps" 
  | above_caps below_caps batch os' os'' buf' where "io = Tau" "below_caps = [cap \<leftarrow> caps. less_than_frontier (front os 0) (time cap)]"
    "above_caps = [cap \<leftarrow> caps. \<not> less_than_frontier (front os 0) (time cap)]"
    "batch = map (\<lambda> cap. (Max (set (buf cap)), cap)) below_caps"
    "os' = produces os batch"
    "os'' = drop_caps os' below_caps"
    "buf' = (\<lambda> cap. if cap \<in> set below_caps then [] else buf cap)"
    "op = max_top' os'' buf' above_caps"
  | x where "io = Inp (Some 0) x" "is_Inl x" "op = \<oslash>"
  | x n t caps' os' buf' where "io = Inp (Some 0) x" "\<not> is_Inl x" "(n, t) = projr x"
    "(caps', os') = (if Cap t 0 \<in> set caps then (caps, os) else (caps @ [Cap t 0], mint_cap os 0 t))"
    "buf' = BENQ (Cap t 0) n buf" "op = max_top' os' buf' caps'"
  | "io = Tau" "outpu os 0 = []" "op = max_top' os buf caps"
  | x xs where "io = Out (Some 0) (Inr x)" "outpu os 0 = x # xs"
    "op = max_top' (os\<lparr> outpu := (outpu os)(0 := xs ) \<rparr>) buf caps"
  | os' st where "io = Out None (Inl (Inl st))" "obtain_progress os = (os', st)"
    "op = max_top' os' buf caps"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) max_top'.code)
  apply (cases io)
  subgoal for p x
    apply simp
    apply (cases p; simp; hypsubst_thin)
    subgoal
      by (auto del: disjCI split: if_splits list.splits sum.splits; hypsubst_thin?)
    subgoal
      by (cases x; force split: if_splits list.splits sum.splits; hypsubst_thin?)
    done
  subgoal for p x
    apply simp
    apply (cases p; simp; hypsubst_thin)
    subgoal
      by (auto del: disjCI split: if_splits list.splits sum.splits; hypsubst_thin?)
    subgoal
      by (cases x; force split: if_splits list.splits sum.splits; hypsubst_thin?)
    done
  subgoal
    by (fastforce split: if_splits list.splits)
  done

(* 
  abbreviation "max_top \<equiv> max_top' []"
*)

term "THE x. P x"
term "SOME x. P x"

term The
term Eps
term the_enat

corec max_op where
  "max_op n inps = Choice (cimage (\<lambda> p. case ldropWhile ((=) []) (inps p) of
     LCons xs lxs \<Rightarrow> 
     Write 
     (max_op (n(p := n p + 1 + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (inps (p := lxs)))
       p (Max (set xs), n p + the_enat (llength (ltakeWhile ((=) []) (inps p)))))
     (cfilter (\<lambda> p. ldropWhile ((=) []) (inps p) \<noteq> LNil) c\<UU>))"


lemma step_max_op_elim:
  assumes "step io (max_op n inps) op"
  obtains p xs lxs where "io = Out p (Max (set xs), n p + the_enat (llength (ltakeWhile ((=) []) (inps p))))" "ldropWhile ((=) []) (inps p) = LCons xs lxs"
    "op = max_op (n (p := n p + 1 + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (inps(p := lxs))" "p \<notin> defaults"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) max_op.code)
  apply (clarsimp split: llist.splits list.splits)
  done

lemma step_max_op_Out_intro[intro]:
  "inps p = LCons xs lxs \<Longrightarrow>
   xs \<noteq> [] \<Longrightarrow>
   ys = inps(p := lxs) \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   step (Out p (Max (set xs), n p)) (max_op n inps) (max_op (n(p := Suc (n p))) ys)"
  apply (subst max_op.code)
  apply (clarsimp split: llist.splits)
  apply (rule SC)
   apply (rule cimage_eqI[rotated])
    apply force
   apply (rule refl)
  apply simp
  apply force
  done

lemma step_max_op_Out_intro2[intro]:
  "ldropWhile ((=) []) (inps p) = LCons xs lxs \<Longrightarrow>
   xs \<noteq> [] \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   step (Out p (Max (set xs), (n p) + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (max_op n inps) (max_op (n (p := n p + 1 + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (inps(p := lxs)))"
  apply (subst max_op.code)
  apply (rule SC)
   apply (rule cimage_eqI[rotated])
    apply force
   apply (rule refl)
  apply auto
  done

lemma step_max_op_not_Tau[simp]:
  "\<not> step Tau (max_op n inps) op"
  apply (subst max_op.code)
  apply (auto split: llist.splits list.splits dest!: ldropWhile_LConsD)
  done

lemma step_max_op_not_Inp[simp]:
  "\<not> step (Inp p x) (max_op n inps) op"
  apply (subst max_op.code)
  apply (auto split: llist.splits list.splits dest!: ldropWhile_LConsD)
  done

lemma wstep_max_op_simp[simp]:
  "io \<noteq> Tau \<Longrightarrow>
   wstep io (max_op n inps) op = step io (max_op n inps) op"
  unfolding wstep_def
  apply (cases io; simp)
  using converse_rtranclpE apply fastforce
  subgoal
    apply (rule iffI)
    subgoal
      apply clarsimp
      apply (metis converse_rtranclpE step_max_op_elim step_max_op_not_Tau)
      done
    subgoal
      by auto
    done
  done

abbreviation "inp_top os caps inps \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (input_top os caps inps)"
abbreviation "m_top os buf caps \<equiv>  map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (max_top' os buf caps)"

abbreviation "inp_m_top os1 caps1 inps buf1 os2 buf2 caps2 \<equiv>
   map_op (case_sum id id) (case_sum id id)
   (comp_op [Inr (0 :: 2, 0 :: 1) \<mapsto> Inr (1 :: 2, 0 :: 1)] buf1 (inp_top os1 caps1 inps) (m_top os2 buf2 caps2))"


(* FIXME: move me *)
lemma dataflow_op_extract_progress_append:
  "dataflow_op (sg\<lparr>lo_pt := lo_pt sg @ extract_progress nid (edges sg) \<lparr>cons = cs, inte = is, prod = ps\<rparr> @ extract_progress nid (edges sg) \<lparr>cons = cs', inte = is', prod = ps'\<rparr>\<rparr>) op =
   dataflow_op (sg\<lparr>lo_pt := lo_pt sg @ extract_progress nid (edges sg) \<lparr>cons = cs @ cs', inte = is @ is', prod = ps @ ps'\<rparr>\<rparr>) op"
  apply (rule dataflow_op_change_multiplicities)
     apply simp_all
  unfolding extract_progress_def
  apply simp
  apply (smt (verit, del_insts) change_multiplicities_append change_multiplicities_comm)
  done

lemma propagate_pointstamps_comm:
  "propagate_pointstamps summary conf (cbs1 @ cbs2) = propagate_pointstamps summary conf (cbs2 @ cbs1)"
  unfolding propagate_pointstamps_def Let_def
  by (simp add: change_multiplicities_comm)

lemma propagate_pointstamps_append:
  "propagate_pointstamps summary conf cbs1 = Some conf' \<Longrightarrow>
   propagate_pointstamps summary conf (cbs1 @ cbs2) = propagate_pointstamps summary conf' cbs2"
  apply (induct cbs2 arbitrary: cbs1 conf conf' rule: rev_induct) 
  subgoal for cbs1 conf conf'
    unfolding propagate_pointstamps_def change_multiplicities_def propagate_all_def
    apply simp
    apply (metis (no_types, lifting) while_option_stop while_option_unfold)
    done
  subgoal for a cbs2 cbs1 conf conf'
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply assumption
    unfolding propagate_pointstamps_def Let_def
    apply (simp; hypsubst_thin?)
    apply (subst change_multiplicities_append_comp)
    apply simp
    oops

(* edges sg = (\<lambda> l. if node l = 0 \<and> port l = Src 1 then [Loc 1 (Trg 0)] else []) \<Longrightarrow> *)

term "map (\<lambda> xs. case xs of [] \<Rightarrow> [] | xs \<Rightarrow> [Max (set xs)])"

(* FIXME: move me *)
lemma map_in_setD:
  "map f xs = ys \<Longrightarrow>
   x \<in> set xs \<Longrightarrow>
   f x \<in> set ys"
  by force

(* FIXME: move me *)
definition
  buf_dom :: "('a \<Rightarrow> 'b buf) \<Rightarrow> 'a set" where
  "buf_dom m = {a. m a \<noteq> []}"
no_notation shiftr  (infixl \<open>>>\<close> 55)

definition "list_to_buf xs = (\<lambda> t. map fst (filter (\<lambda> (x, t'). t' = t) xs))"

lemma list_to_buf_empty[simp]:
  "list_to_buf [] = (\<lambda>  _. [])"
  unfolding list_to_buf_def by auto

definition "update_caps caps xs = (fold (\<lambda> (x, t) caps. if Cap t (0 :: 1) \<in> set caps then caps else (caps @ [Cap t 0])) xs caps)"

lemma update_caps_empty[simp]:
  "update_caps caps [] = caps"
  unfolding update_caps_def by auto

definition "max_from_caps_buf caps buf = map (\<lambda> cap. (Max (set (buf cap)), time cap)) caps"

definition "max_from_buf caps buf xs = (let caps' = update_caps caps xs in
                                         let buf' = list_to_buf xs o time in max_from_caps_buf caps' (buf' >> buf))"

lemma update_caps_new_cap:
  "snd ` set xs = {t} \<Longrightarrow>
   Cap t (0 :: 1) \<notin> set caps \<Longrightarrow>
   update_caps caps xs = caps @ [Cap t 0]"
  unfolding update_caps_def
  apply (induct xs arbitrary: caps t rule: rev_induct)
   apply clarsimp
  subgoal for a xs caps
    apply (cases a; fastforce)
    done
  done

lemma update_caps_append[simp]:                
  "update_caps caps (ys @ xs) = update_caps (update_caps caps ys) xs"
  unfolding update_caps_def
  apply auto
  done

lemma update_caps_append2:
  "snd ` set xs \<inter> time ` set caps1 = {} \<Longrightarrow>
   caps = caps1 @ caps2 \<Longrightarrow>
   update_caps caps xs = caps1 @ update_caps caps2 xs"
  unfolding update_caps_def apply hypsubst_thin
  apply (induct xs arbitrary: caps1 caps2)
   apply (auto simp add: rev_image_eqI)
  done

lemma set_update_caps[simp]:
  "set (update_caps caps xs) = set caps \<union> (\<lambda> t. Cap t 0) ` snd ` set xs"
  unfolding update_caps_def
  apply (induct xs arbitrary: caps rule: rev_induct)
   apply clarsimp
  apply force
  done


lemma list_to_buf_append[simp]:
  "list_to_buf (ys @ xs) = list_to_buf xs >> list_to_buf ys"
  unfolding list_to_buf_def BULK_BENQ_def
  apply (rule ext)
  apply auto
  done

lemma max_from_buf_append[simp]:
  "max_from_buf caps buf (ys @ xs) = max_from_buf (update_caps caps ys) ((list_to_buf ys o time) >> buf) xs"
  unfolding max_from_buf_def Let_def 
  apply (clarsimp simp flip: Un_assoc)
  apply (metis BULK_BENQ_bulk_benq fun_comp_eq_conv)
  done

lemma max_from_buf_empty[simp]:
  "max_from_buf caps buf [] = max_from_caps_buf caps buf"
  unfolding max_from_buf_def max_from_caps_buf_def update_caps_def list_to_buf_def
  apply auto
  done

lemma max_from_buf_move_all:
  "max_from_buf caps buf xs = max_from_buf ((update_caps caps xs)) ((list_to_buf xs o time) >> buf) []" 
  by (metis append.right_neutral max_from_buf_append)

lemma max_from_caps_buf_append[simp]:
  "max_from_caps_buf (caps1 @ caps2) buf = max_from_caps_buf caps1 buf @ max_from_caps_buf caps2 buf"
  unfolding max_from_caps_buf_def by auto

lemma max_from_caps_buf_BULK_BENQ_empty:
  "buf_dom buf1 \<inter> set caps = {} \<Longrightarrow>
   max_from_caps_buf caps (buf1 >> buf2) = max_from_caps_buf caps buf2"
  unfolding max_from_caps_buf_def BULK_BENQ_def buf_dom_def apply clarsimp
  apply (metis (mono_tags, lifting) List.set_empty disjoint_iff mem_Collect_eq monoid.right_neutral sup_bot.monoid_axioms)
  done


(* FIXME: move me *)
lemma rtranclp_intros_1:
  "a = b \<Longrightarrow> r\<^sup>*\<^sup>* a b"
  by auto

lemma max_from_caps_buf_cong:
  "(\<forall> cap \<in> set caps. buf1 cap = buf2 cap) \<Longrightarrow>
   max_from_caps_buf caps buf1 = max_from_caps_buf caps buf2"
  unfolding max_from_caps_buf_def
  apply auto
  done

lemma not_less_than_frontier_mono[intro]:
  "t < t' \<Longrightarrow>
   \<not> less_than_frontier f t \<Longrightarrow> \<not> less_than_frontier f t'"
  unfolding less_than_frontier_def
  apply simp
  apply transfer
  apply clarsimp
  apply (metis (no_types, lifting) Set.is_empty_def dual_order.strict_trans empty_iff ex_min_if_finite finite_filter member_filter)
  done

lemma zequal_equal[simp]:
  "zequal A B \<longleftrightarrow> A = B"
  apply safe
  subgoal
  apply transfer
    apply (auto simp: equiv_zmset_def)
    subgoal for A B A' B'
      apply transfer
      oops

lemma take_step_PR_p_preserves_inv_imps_work_sum:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by ((take_step summary PR ^^ k) c)"
  sorry

lemma take_step_PR_p_preserves_inv_implications_nonneg:
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg ((take_step summary PR ^^ k) c)"
  sorry

lemma
  "dataflow_topology summary dataflow_topology_from_tree.followed_by \<Longrightarrow>
   reachable_locations summary = UNIV \<Longrightarrow>
   dataflow_topology.inv_imps_work_sum summary dataflow_topology_from_tree.followed_by c \<Longrightarrow>
   dataflow_topology_from_tree.inv_implications_nonneg c \<Longrightarrow>
   propagate_all summary c = Some c' \<Longrightarrow>
   (t \<in>\<^sub>A frontier (c_imp c' loc)) = (t \<in>\<^sub>A dataflow_topology.implied_frontier_alt summary dataflow_topology_from_tree.followed_by c' loc)"
  unfolding propagate_all_def worklist_is_empty_def
  apply (drule while_option_stop2)
  apply (rule Propagate.dataflow_topology.implication_frontier_iff_implied_frontier_alt_vacant)
     apply simp_all
  using take_step_PR_p_preserves_inv_imps_work_sum apply force
  using take_step_PR_p_preserves_inv_implications_nonneg apply force
  apply (rule Propagate.dataflow_topology.empty_worklists_vacant_to)
   apply simp_all
  oops

 
lemma
  \<open>xs 0 = outpu os2 0 \<Longrightarrow>
   ys 0 = max_from_buf caps buf2 ((map projr o buf1 o Inr o Pair 1) 0 @ outpu os1 0) \<Longrightarrow>
   (\<forall> x \<in> set (buf1 (Inr (1, 0))). is_Inr x) \<Longrightarrow>
   (\<forall> t \<in> snd ` set ((map projr o buf1 o Inr o Pair 1) 0 @ outpu os1 0). t < n 0) \<Longrightarrow>
   (\<forall> t \<in> time ` set caps. t < n 0) \<Longrightarrow>
   set caps = buf_dom buf2 \<Longrightarrow>
   (\<forall> t \<in> snd ` set ((map projr o buf1 o Inr o Pair 1) 0 @ outpu os1 0). \<not> less_than_frontier (front os2 1) t) \<Longrightarrow>
   (\<forall> t. t  \<in>\<^sub>A (frontier (c_imp (pt_tr sg) (Loc 1 (Trg 0)))) \<longrightarrow> \<not> less_than_frontier (front os2 1) t) \<Longrightarrow>
   \<not> less_than_frontier (front os2 1) (n 0) \<Longrightarrow>
   dataflow_op sg (inp_m_top os1 (\<lambda> p. n p) inps buf1 os2 buf2 caps) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (source_op (\<lambda> p. xs p @@- ys p @@- lconcat (lmap (\<lambda> (xs, t). case xs of [] \<Rightarrow> [] | _ \<Rightarrow> [(Max (set xs), t)]) (lzip (inps p) (iterates ((+) 1) (n p))))))\<close>
proof (coinduction arbitrary: xs ys os1 os2 n caps buf1 buf2 inps sg rule: weakBisimWeakUptoBisimCong)
  case SIM1
  then show ?case
    apply -
    unfolding wsim_def
    apply (intro allI conjI impI)
    subgoal premises prems for io op1'
      using prems(10-) apply -
      apply (elim step_max'_top_elim step_map_op_elim step_comp_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp split: if_splits; hypsubst_thin?)
      prefer 12
      subgoal for nid op'' imp_fron sg' io' op''a p op2' io'a op''b
      using prems(1,2) apply -
        apply (intro exI conjI[rotated])
         apply (intro relcomppI)
           apply (rule bisim_refl)
          defer
          apply (rule wbisim_refl)
         defer
         apply (rule wb_upto_b_base)
         apply (intro conjI exI)
                   apply (rule refl)+
        using prems(3) apply simp
        using prems(4) apply simp
        using prems(5) apply simp
        using prems(6) apply simp
        subgoal
          apply (simp split: option.splits)
          apply (intro allI impI)
          subgoal for c' t
            using prems(7) apply -

end
          using prems(7) apply (auto simp add: less_than_frontier_def split: option.splits)

end
               prefer 6
      subgoal for op'' io' op''a op2' io'a op''b above_caps below_caps batch os' os'' buf'
        using prems(1,2) apply -
        apply (intro exI conjI[rotated])
         apply (intro relcomppI)
           apply (rule bisim_refl)
          defer
          apply (rule wbisim_refl)
         defer
         apply (rule wb_upto_b_base)
         apply (intro conjI exI)
                   apply (rule refl)+
        using prems(3) apply simp
        using prems(4) apply simp
        using prems(5) apply force
        subgoal
          using prems(6) apply -
          unfolding buf_dom_def
          apply auto
          done
           apply (simp add: prems(7))
        using prems(8) apply simp
        apply (rule rtranclp_intros_1)
        apply (rule arg_cong3[where f=map_op])
          apply simp_all
        apply (rule arg_cong[where f=source_op])
        apply (rule ext)
        apply (simp_all add: lshift_assoc)
        apply (rule arg_cong2[where f=lshift])
         apply simp_all
        apply (subst max_from_buf_move_all)
        apply simp
        apply (subst max_from_buf_move_all)
        apply (simp flip: update_caps_append)
        apply (subgoal_tac 
            "update_caps caps (map projr (buf1 (Inr (1, 1))) @ outpu os1 1) =
        filter (\<lambda>cap. less_than_frontier (front os2 1) (time cap)) caps @
        update_caps (filter (\<lambda>cap. \<not> less_than_frontier (front os2 1) (time cap)) caps) (map projr (buf1 (Inr (1, 1))) @ outpu os1 1)")
        subgoal
          apply simp
          apply (rule arg_cong2[where f=append])
          subgoal
            apply (subst max_from_caps_buf_BULK_BENQ_empty)
            subgoal 
              using prems(6,7) apply -
              unfolding buf_dom_def less_than_frontier_def list_to_buf_def
              apply auto
               apply (smt (verit, best) UnCI case_prod_beta filter_empty_conv image_eqI)
              apply (smt (verit, ccfv_SIG) Un_iff filter_empty_conv image_Un image_set map_in_setD split_def)
              done
            apply (subst max_from_caps_buf_def)
            apply simp
            done
          subgoal
            using prems(7) apply -
            apply (rule max_from_caps_buf_cong)
            apply (auto simp add: BULK_BENQ_bulk_benq split: sum.splits prod.splits)
            done
          done
        subgoal
          using prems(9)[symmetric] apply -
          apply (rule update_caps_append2)
           apply simp_all
          using prems(7) apply -
          apply clarsimp
          apply (smt (verit, best) disjointI imageE mem_Collect_eq)
          done
        done
      prefer 9
      subgoal for nid op'' imp_fron sg' io' op''a p op2' io'a op''b
        using prems(1,2) apply -
        apply (intro exI conjI[rotated])
         apply (intro relcomppI)
           apply (rule bisim_refl)
          defer
          apply (rule wbisim_refl)
         defer
         apply (rule wb_upto_b_base)
         apply (intro conjI exI)
                   apply (rule refl)+
        using prems(3) apply simp
        using prems(4) apply simp
        using prems(5) apply simp
        using prems(6) apply simp
        subgoal
          using prems(7) apply (auto simp add: less_than_frontier_def split: option.splits)

          find_theorems name: implication_frontier_iff_implied_frontier_alt_vacant

          thm dataflow_topology_from_tree.PR_next[where less_t="(<)", simplified]

          find_theorems name: PR_next

          sorry
        subgoal
        using prems(8) apply (auto simp add: less_than_frontier_def split: option.splits)
        sorry
      subgoal
        using prems(9) apply (auto simp add: less_than_frontier_def split: option.splits)
        sorry
      apply (simp add: comp_def)
      done


end
