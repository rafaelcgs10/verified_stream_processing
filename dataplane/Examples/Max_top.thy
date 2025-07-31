theory Max_top

imports
  "../Timely_Infrastructure"
  Input_top
begin 

(* FIXME: move me *)
abbreviation "choice5 op1 op2 op3 op4 op5 \<equiv> choice3 (choice2 op1 op2) (choice2 op3 op4) op5"

find_consts "_ + _ \<Rightarrow> _" name: "is_"

find_theorems is_Inl


abbreviation "mint_cap os p t \<equiv> os\<lparr> inter := inter os @ [(p, t, 1)] \<rparr>"

corec max_top' where
  "max_top' os buf caps = choice5
   (Read None (\<lambda> st. if is_Inl st \<and> is_Inr (projl st) then max_top' (os\<lparr> front := projr (projl st) \<rparr>) buf caps else \<oslash>))
   (let below_caps = [cap \<leftarrow> caps. less_than_frontier (front os 0) (time cap)] in
    let above_caps = [cap \<leftarrow> caps. \<not> less_than_frontier (front os 0) (time cap)] in
    let batches = map (\<lambda> cap. (Max (set (buf cap)), cap)) below_caps in
    let os' = foldl (\<lambda> os (m, cap). produce os cap [m]) os batches in
    let os'' = foldl drop_cap os' below_caps in
    let buf' = foldl (\<lambda> s cap. buf(cap := [])) buf below_caps in
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
  | above_caps below_caps batches os' os'' buf' where "io = Tau" "below_caps = [cap \<leftarrow> caps. less_than_frontier (front os 0) (time cap)]"
    "above_caps = [cap \<leftarrow> caps. \<not> less_than_frontier (front os 0) (time cap)]"
    "batches = map (\<lambda> cap. (Max (set (buf cap)), cap)) below_caps"
    "os' = foldl (\<lambda> os (m, cap). produce os cap [m]) os batches"
    "os'' = foldl drop_cap os' below_caps"
    "buf' = foldl (\<lambda> s cap. buf(cap := [])) buf below_caps"
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
    sorry
  done

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
  "set caps1 \<inter> set caps2 = {} \<Longrightarrow>
   max_from_caps_buf (caps1 @ caps2) buf = max_from_caps_buf caps1 buf @ max_from_caps_buf caps2 buf"
  unfolding max_from_caps_buf_def by auto

lemma max_from_caps_buf_BULK_BENQ_empty:
  "buf_dom buf1 \<inter> set caps = {} \<Longrightarrow>
   max_from_caps_buf caps (buf1 >> buf2) = max_from_caps_buf caps buf2"
  unfolding max_from_caps_buf_def BULK_BENQ_def buf_dom_def apply clarsimp
  apply (metis (mono_tags, lifting) List.set_empty disjoint_iff mem_Collect_eq monoid.right_neutral sup_bot.monoid_axioms)
  done

lemma
  \<open>xs 0 = outpu os2 0 \<Longrightarrow>
   ys 0 = max_from_buf caps buf2 ((map projr o buf1 o Inr o Pair 1) 0 @ outpu os1 0) \<Longrightarrow>
   (\<forall> x \<in> set (buf1 (Inr (1, 0))). is_Inr x) \<Longrightarrow>
   (\<forall> t \<in> snd ` set ((map projr o buf1 o Inr o Pair 1) 0 @ outpu os1 0). t < n 0) \<Longrightarrow>
   (\<forall> t \<in> time ` set caps. t < n 0) \<Longrightarrow>
   set caps = buf_dom buf2 \<Longrightarrow>
   dataflow_op sg (inp_m_top os1 (\<lambda> p. n p) inps buf1 os2 buf2 caps) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (source_op (\<lambda> p. xs p @@- ys p @@- lconcat (lmap (\<lambda> (xs, t). case xs of [] \<Rightarrow> [] | _ \<Rightarrow> [(Max (set xs), t)]) (lzip (inps p) (iterates ((+) 1) (n p))))))\<close>
proof (coinduction arbitrary: xs ys os1 os2 n caps buf1 buf2 inps sg rule: weakBisimWeakUptoBisimCong)
  case SIM1
  then show ?case
    apply -
    unfolding wsim_def
    apply (intro allI conjI impI)
    subgoal premises prems for io op1'
      using prems(7-) apply -
    apply (elim step_max'_top_elim step_map_op_elim step_comp_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp split: if_splits; hypsubst_thin?)
      subgoal for nid op'' x io' op''a pa op2' io'a op''b xs'
        using prems(1,2) apply -
        apply (intro conjI exI)
         apply (rule step_wstep)
         apply (rule step_map_op)
          apply (rule step_source_op_Out_intro[where p=0])
            apply simp
           apply (rule refl)
          apply (simp add: defaults_num1_def)
         apply simp
          apply (intro relcomppI)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
        apply simp
        apply (intro conjI exI)
            apply (rule refl)+
        defer
            apply (rule refl)+
        using prems(3) apply simp
        using prems(4) apply simp
        using prems(5) apply simp
        using prems(6) apply simp
               apply (rule arg_cong3[where f=map_op])
                 apply simp_all
        apply (rule arg_cong[where f=source_op])
         apply (rule ext)
        apply (simp_all add: comp_def)
        done
      prefer 6
      subgoal for op'' io' op''a op1' io'a op''b batch lxs cap os' os''
        apply (cases batch)
        defer
        subgoal for b batch'
        using prems(1,2) apply -
        apply (intro exI conjI)
         apply (subst iterates.code)
           apply (simp flip: snoc_shift)
           apply (rule rtranclp.intros(1))
     apply (intro relcomppI)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
          apply (intro conjI exI)
              apply (rule refl)+
           apply simp
        defer
              apply (rule refl)+
        using prems(3) apply simp
        subgoal
        using prems(4) apply simp
        apply auto
        apply (meson Un_iff image_eqI less_Suc_eq)
        done
      using prems(5) apply force
      using prems(6) apply simp
               apply (rule arg_cong3[where f=map_op])
                 apply simp_all
        apply (rule arg_cong[where f=source_op])
         apply (rule ext)
        apply simp_all
        apply (rule arg_cong2[where f=lshift])
        apply (simp_all flip: snoc_shift)
      apply (rule arg_cong2[where f=lshift])
        using prems(4,5,6) apply (simp_all flip: snoc_shift)
        apply hypsubst_thin
        apply (subst max_from_buf_move_all)
        apply simp
        apply (subst (1) max_from_buf_move_all)
        apply simp
        apply (subst (5) update_caps_new_cap[where t="n 1"])
          apply force
        subgoal
          apply (simp flip: update_caps_append)
          apply force
          done
        apply simp
        apply (subst max_from_caps_buf_append)
         apply force
        apply (subst (3) max_from_caps_buf_def)
        apply (clarsimp simp add: comp_def)
        apply (intro conjI)
        apply (simp flip: BULK_BENQ_assoc)
        apply (subst (2) max_from_caps_buf_BULK_BENQ_empty)
        subgoal
          unfolding buf_dom_def list_to_buf_def
          by (auto; force)
         apply simp
        subgoal
          unfolding list_to_buf_def BULK_BENQ_def
          apply clarsimp
          apply (rule arg_cong[where f=Max])
          apply (rule arg_cong2[where f=insert])
           apply simp
          apply (subgoal_tac "buf2 (Cap (n 1) 1) = [] \<and> {x \<in> projr ` set (buf1 (Inr (1, 1))). case x of (x, t') \<Rightarrow> t' = n 1} = {} \<and> {x \<in> set (outpu os1 1). case x of (x, t') \<Rightarrow> t' = n 1} = {}")
           apply clarsimp
           apply fast
          unfolding buf_dom_def
          apply auto
          done
        done

        find_theorems 

end
        apply (rule arg_cong2[where f=max_from_caps_buf])
          apply simp_all
        subgoal
          unfolding list_to_buf_def
          apply (rule ext)
          apply auto


          find_theorems update_caps Nil



end
        apply (intro conjI exI)
         apply force
          apply (intro relcomppI)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
        apply simp
        apply (rule exI[of _ "xs"])
          apply (rule exI)
          apply (rule exI[of _ os1])
        apply (rule exI[of _ os2])

        thm step_comp_op_elim

end
