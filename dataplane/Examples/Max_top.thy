theory Max_top

imports
  "../Timely_Infrastructure"
  Input_top
begin 



definition "maxs buf = [(n, c) \<leftarrow> buf. n = Max (set (map fst ((filter (\<lambda> (n' :: nat, c'). time c = time c') buf))))]"

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
     let buf' = buf((Cap t 0) := n # (buf (Cap t 0))) in
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
    "buf' = buf((Cap t 0) := n # (buf (Cap t 0)))" "op = max_top' os' buf' caps'"
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

term lzip

lemma
  \<open>xs 0 = outpu os2 0 @ buf2l 0 @ (map projr o buf1 o Inr o Pair 1) 0 @ outpu os1 0 \<Longrightarrow>
   buf2l = fold (\<lambda> cap f. f(out cap := f (out cap) @ map (\<lambda> x. (x, time cap)) (buf2 cap))) caps2 (\<lambda> p. []) \<Longrightarrow>
   (\<forall> (x, t) \<in> set (xs 0).  \<not> (\<exists> y. (y, t) \<in> set (remove1 (x, t) (xs 0)))) \<Longrightarrow>
   (\<forall> x \<in> set (buf1 (Inr (1, 0))). is_Inr x) \<Longrightarrow>
   dataflow_op sg (inp_m_top os1 (\<lambda> p. n p) inps buf1 os2 buf2 caps2) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (source_op (\<lambda> p. xs p @@- lconcat (lmap (\<lambda> (xs, t). case xs of [] \<Rightarrow> [] | _ \<Rightarrow> [(Max (set xs), t)]) (lzip (inps p) (iterates ((+) 1) (n p))))))\<close>
proof (coinduction arbitrary: xs n os1 os2 caps2 buf1 buf2 buf2l inps sg rule: weakBisimWeakUptoBisimCong)
  case SIM1
  then show ?case
    apply -
    unfolding wsim_def
    apply (intro allI conjI impI)
    subgoal premises prems for io op1'
      using prems(4-) apply -
    apply (elim step_max'_top_elim step_map_op_elim step_comp_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp split: if_splits; hypsubst_thin?)
      subgoal for nida op'' x io' op''a pa op2' io'a op''b xs'
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
        apply (rule exI[of _ "xs(1 := xs' @ fold (\<lambda>cap f. f(1 := f 1 @ map (\<lambda>x. (x, time cap)) (buf2 cap))) caps2 (\<lambda>p. []) 1 @ map projr (buf1 (Inr (1, 1))) @ outpu os1 1)"])
          apply (rule exI)
          apply (rule exI[of _ os1])
          apply (rule exI[of _ "os2\<lparr> outpu := (outpu os2)(1 := xs') \<rparr>"])
          apply (rule exI[of _ caps2])
          apply (rule exI[of _ buf1])
          apply (rule exI[of _ buf2])
          apply (rule exI[of _ inps])
          apply (intro exI[of _ sg] conjI)
           apply simp_all
               apply (rule arg_cong3[where f=map_op])
                 apply simp_all
        apply (rule arg_cong[where f=source_op])
         apply (rule ext)
         apply (simp_all)
        using prems(3) apply -
        apply (auto split: prod.splits if_splits)
        done
      subgoal for op'' io' op''a p op1' q io'a op''b xa xs'
        using prems(1,2) apply -
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
          apply (rule exI[of _ "os1\<lparr> outpu := (outpu os1)(1 := xs') \<rparr>"])
          apply (rule exI[of _ os2])
        apply (rule exI[of _ caps2])
          apply (rule exI[of _ "BENQ (Inr (1, 1)) (Inr xa) buf1"])
          apply (rule exI[of _ buf2])
          apply (rule exI[of _ inps])
          apply (intro exI[of _ sg] conjI)
           apply simp_all
         apply (rule arg_cong2[where f=dataflow_op])
        apply simp_all
               apply (rule arg_cong3[where f=map_op])
           apply simp_all
               apply (rule arg_cong4[where f=comp_op])
           apply simp_all
               apply (rule arg_cong3[where f=map_op])
           apply simp_all
         apply (rule arg_cong3[where f=input_top])
           apply simp_all
        apply force
        using prems(3) apply -
        apply (auto split: prod.splits if_splits)
        done
      subgoal for op'' io' op''a p x op2' io'a op''b xa
        using prems(1,2) apply -
        apply (rule FalseE)
        apply (cases "buf1 (Inr (1, 1))"; simp add: BHD_def split: sum.splits)
        subgoal for a
          by (cases a; simp)
        done
      subgoal for op'' io' op''a p x op2' io'a op''b xa n t caps'
        using prems(1,2) apply -
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
          apply (rule exI[of _ "os1"])
          apply (rule exI[of _ "os2"])
        apply (rule exI[of _ caps2])
          apply (rule exI[of _ "BTL (Inr (1, 1)) buf1"])
        sorry
             prefer 3
      subgoal for op'' io' op''a op1' io'a op''b batch lxs cap os' os''
        using prems(1,2) apply -
        apply (cases batch)
        defer
        subgoal for b batch'
        apply (intro exI conjI)
         apply (subst iterates.code)
           apply (simp flip: snoc_shift)
           apply (rule rtranclp.intros(1))
     apply (intro relcomppI)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply (rule wb_upto_b_base)
        apply (rule exI[of _ "xs(1 := xs 1 @ [(Max (insert b (set batch')), n 1)])"])
          apply (intro conjI exI)
              apply (rule refl)+
             apply simp
          apply simp


          find_theorems lshift LCons



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
