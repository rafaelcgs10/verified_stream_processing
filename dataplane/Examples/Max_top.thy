theory Max_top

imports
  "../Timely_Infrastructure"
  "HOL-Library.Finite_Map"
  Input_top
begin 

definition "maxs buf = [(n, c) \<leftarrow> buf. n = Max (set (map fst ((filter (\<lambda> (n' :: nat, c'). time c = time c') buf))))]"

(* FIXME: move me *)
abbreviation "choice5 op1 op2 op3 op4 op5 \<equiv> choice3 (choice2 op1 op2) (choice2 op3 op4) op5"

find_consts "  _ \<Rightarrow>(_ \<times> _) list \<Rightarrow> _ \<Rightarrow> _" 


abbreviation "mint_cap os p t \<equiv> os\<lparr> inter := inter os @ [(p, t, 1)] \<rparr>"


corec max_top' where
  "max_top' os buf caps = choice5
   (Read None (\<lambda> st. if is_Inl st \<and> is_Inr (projl st) then max_top' (os\<lparr> front := projr (projl st) \<rparr>) buf caps else \<oslash>))
   (Choice (cimage (\<lambda> p.
    let below_caps = [cap \<leftarrow> caps. less_than_frontier (front os p) (time cap)] in
    let above_caps = [cap \<leftarrow> caps. \<not> less_than_frontier (front os p) (time cap)] in
    let batches = map (\<lambda> cap. (Max (buf cap), cap)) below_caps in
    let os' = foldl (\<lambda> os (m, cap). produce os cap [m]) os batches in
    let os'' = foldl drop_cap os' below_caps in
    let buf' = foldl (\<lambda> s cap. buf(cap := {})) buf below_caps in
    Silent (max_top' os'' buf' above_caps)) c\<UU>))
   (Choice (cimage (\<lambda> p. 
    Read (Some p)
    (\<lambda> x. if isl x then \<oslash> else
     let (n, t) = projr x in
     let (caps', os') = (if Cap t p \<in> set caps then (caps, os) else (caps @ [Cap t p], mint_cap os p t)) in
     let buf' = buf((Cap t p) := insert n (buf (Cap t p))) in
     max_top' os' buf' caps')) c\<UU>))
    (Choice (cimage (\<lambda> p. (case outpu os p of
         x # xs \<Rightarrow> send_output (max_top' (os\<lparr> outpu := (outpu os)(p := xs ) \<rparr>) buf caps) p x)) 
    (cfilter (\<lambda> p. outpu os p \<noteq> []) c\<UU>)))
    (let (os', st) = obtain_progress os in
     send_progress (max_top' os' buf caps) st)"

lemma step_max'_top_elim:
  assumes "step io (max_top' os buf caps) op"
  obtains
    st where "io = Inp None st" "is_Inl st" "is_Inr (projl st)" "op = max_top' (os\<lparr> front := projr (projl st) \<rparr>) buf caps"
  | st where "io = Inp None st" "\<not> is_Inl st \<or> \<not> is_Inr (projl st)" "op = \<oslash>"
  | p above_caps below_caps batches os' os'' buf' where "io = Tau" "below_caps = [cap \<leftarrow> caps. less_than_frontier (front os p) (time cap)]"
    "above_caps = [cap \<leftarrow> caps. \<not> less_than_frontier (front os p) (time cap)]"
    "batches = map (\<lambda> cap. (Max (buf cap), cap)) below_caps"
    "os' = foldl (\<lambda> os (m, cap). produce os cap [m]) os batches"
    "os'' = foldl drop_cap os' below_caps"
    "buf' = foldl (\<lambda> s cap. buf(cap := {})) buf below_caps"
    "op = max_top' os'' buf' above_caps" "p \<notin> defaults"
  | p x where "io = Inp (Some p) x" "isl x" "op = \<oslash>"
  | p x n t caps' os' buf' where "io = Inp (Some p) x" "\<not> isl x" "(n, t) = projr x"
    "(caps', os') = (if Cap t p \<in> set caps then (caps, os) else (caps @ [Cap t p], mint_cap os p t))"
    "buf' = buf((Cap t p) := insert n (buf (Cap t p)))" "op = max_top' os' buf' caps'"
  | p x xs where "io = Out (Some p) (Inr x)" "outpu os p = x # xs"
    "op = max_top' (os\<lparr> outpu := (outpu os)(p := xs ) \<rparr>) buf caps" "p \<notin> defaults"
  | os' st where "io = Out None (Inl (Inl st))" "obtain_progress os = (os', st)"
    "op = max_top' os' buf caps"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) max_top'.code)
  apply (cases io)
  subgoal for p x
    apply simp
    apply (cases p; simp)
    subgoal
      by (auto 0 0 split: if_splits list.splits)
    subgoal
      by (fastforce split: prod.splits if_splits list.splits)
    done
  subgoal for p x
    apply simp
    apply (cases p; simp)
    subgoal
      by (auto 0 0 split: if_splits list.splits)
    subgoal
      by (fastforce split: prod.splits if_splits list.splits)
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
     (max_op (n(p := n p + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (inps (p := lxs)))
       p (Max (set xs), n p + the_enat (llength (ltakeWhile ((=) []) (inps p)))))
     (cfilter (\<lambda> p. ldropWhile ((=) []) (inps p) \<noteq> LNil) c\<UU>))"


lemma step_max_op_elim:
  assumes "step io (max_op n inps) op"
  obtains p xs lxs where "io = Out p (Max (set xs), n p + the_enat (llength (ltakeWhile ((=) []) (inps p))))" "ldropWhile ((=) []) (inps p) = LCons xs lxs"
    "op = max_op (n (p := n p + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (inps(p := lxs))" "p \<notin> defaults"
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
   step (Out p (Max (set xs), n p)) (max_op n inps) (max_op n ys)"
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
   step (Out p (Max (set xs), (n p) + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (max_op n inps) (max_op (n (p := n p + the_enat (llength (ltakeWhile ((=) []) (inps p))))) (inps(p := lxs)))"
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
   (comp_op [(map (\<lambda> p. Inr (0 :: 2, p)) enum_class.enum) [\<mapsto>] (map (\<lambda> p. Inr (1 :: 2, p)) enum_class.enum)] buf1 (inp_top os1 caps1 inps) (m_top os2 buf2 caps2))"


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

lemma
  \<open>input_invar (\<lambda> p. n p + length (xs1 p) + length (xs2 p)) xs3 (outpu os1) \<Longrightarrow>
   input_invar (\<lambda> p. n p + length (xs1 p)) xs2 (map projr o buf1 o Inr o Pair 1) \<Longrightarrow>
   dataflow_op sg (inp_m_top os1 (\<lambda> p. n p + length (xs1 p) + length (xs2 p) + length (xs3 p)) inps buf1 os2 buf2 caps2) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (max_op n (\<lambda> p. xs1 p @@- xs2 p @@- xs3 p @@- inps p))\<close>
  term "outpu os1"
  term buf2
  term xs3
  term "outpu os1"

  term "\<lambda> c. case c of Cap t p \<Rightarrow> (buf2 )"

proof (coinduction arbitrary: inps1 inps2 buf1 buf2 inrbufs1 xs ys i j sg rule: weakBisimWeakUptoBisim)
  case SIM2
  then show ?case
    apply -
    unfolding wsim_def
    apply safe
    apply (elim step_max'_top_elim step_map_op_elim step_comp_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp split: if_splits option.splits; hypsubst_thin)
    defer
  (*   subgoal for op'' io' op''a p op1' q io'a op''b xa xs
      apply (cases inps1; simp)
      subgoal for xs inps1'
        apply (cases xs; simp)
        subgoal for n xs'
          apply hypsubst_thin
          apply (rule exI)
          apply (rule conjI)
           apply (rule rtranclp.intros(1))
          apply (intro relcomppI)
            defer
          apply (rule exI[of _ "LCons xs' inps1'"])
          apply (rule exI[of _ "inps2"])
          apply (rule exI[of _ "BENQ (Inr (1, 1)) (Inr (n, i)) buf1"])
          apply (rule exI[of _ "buf2"])
          apply (rule exI[of _ "i"])
          apply (rule exI[of _ "j"])
          apply (rule exI[of _ "sg\<lparr> lo_pt := (lo_pt sg) @ extract_progress 0 (edges sg) \<lparr>cons = [], inte = [], prod = [(1, i, 1)]\<rparr> \<rparr>"])
          apply simp
          apply (intro conjI[rotated])
          subgoal
            apply (drule sym)
            apply simp
            subgoal premises prems
              apply (rule arg_cong2[where f=lshift])
               apply simp_all
              apply (rule arg_cong2[where f=lshift])
               apply (simp_all add: lconcat_correct)
              apply (subst (1 2) iterates.code)
              apply simp
              done
            done
             apply (rule refl)+
          apply (rule wbisim_refl)
          subgoal
            apply (subst (2) input_top.code)
            apply (simp add: comp_def)
            apply (cases xs'; simp)
            subgoal 
              apply (rule bisim_trans)
              apply (rule aux[where ps="[(1, i, 1)]" and ?is="[]" and cs="[]" and cs="[]" and ?is'="[(1, i, - 1), (1, Suc i, 1)]" and ?cs'="[]" and ?ps'="[]" and nid="0", simplified])
 *)


    subgoal for io op1' op'' io' op''a p x op2' io'a op''b t n
          apply (rule exI)
          apply (rule conjI)
           apply (rule rtranclp.intros(1))
          apply (intro relcomppI)
            defer
          apply (rule exI[of _ "inps1"])
          apply (rule exI[of _ "inps2"])
          apply (rule exI[of _ "BTL (Inr (1, 1)) buf1"])
          apply (rule exI[of _ "buf2 @ [(n, Cap t 1)]"])
          apply (rule exI[of _ "i"])
        apply (rule exI[of _ "j"])
        apply (rule exI[of _ "sg\<lparr> lo_pt := (lo_pt sg) @ extract_progress 1 (edges sg) \<lparr>cons = [(1, t, 1)], inte = [(1, t, 1)], prod = []\<rparr> \<rparr>"])
      apply (intro conjI exI)
            apply (rule refl)+
      subgoal sorry
      subgoal
        unfolding BTL_def
        by simp (meson in_set_tlD)
      subgoal 
        by simp
       apply (rule wbisim_refl)
      sorry
    prefer 5
    subgoal for io op1' nid op'' imp_fron sg' io' op''a p op2' io'a op''b ft below result
         apply (rule exI)
          apply (rule conjI)


