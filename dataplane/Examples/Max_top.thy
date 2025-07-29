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
  | x where "io = Inp (Some 0) x" "isl x" "op = \<oslash>"
  | x n t caps' os' buf' where "io = Inp (Some 0) x" "\<not> isl x" "(n, t) = projr x"
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

lemma
  \<open>input_invar (\<lambda> p. n p + length (xs1 p) + length (xs2 p) + length (xs3 p)) xs4 (outpu os1) \<Longrightarrow>
   input_invar (\<lambda> p. n p + length (xs1 p) + length (xs2 p)) xs3 (map projr o buf1 o Inr o Pair 1) \<Longrightarrow>
   buf2l = fold (\<lambda> cap f. f(out cap := f (out cap) @ map (\<lambda> x. (x, time cap)) (buf2 cap))) caps2 (\<lambda> p. []) \<Longrightarrow>
   input_invar (\<lambda> p. n p + length (xs1 p)) xs2 buf2l \<Longrightarrow>
   input_invar n (\<lambda> p. map (\<lambda> xs. case xs of [] \<Rightarrow> [] | xs \<Rightarrow> [Max (set xs)]) (xs1 p)) (outpu os2) \<Longrightarrow>
   dataflow_op sg (inp_m_top os1 (\<lambda> p. n p + length (xs1 p) + length (xs2 p) + length (xs3 p) + length (xs4 p)) inps buf1 os2 buf2 caps2) \<approx>
   map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (max_op n (\<lambda> p. xs1 p @@- xs2 p @@- xs3 p @@- xs4 p @@- inps p))\<close>
proof (coinduction arbitrary: os1 os2 n caps2 xs1 xs2 xs3 xs4 buf1 buf2 buf2l inps  sg rule: weakBisimWeakUptoBisimCong)
  case SIM1
  then show ?case
    apply -
    unfolding wsim_def
    apply safe
    apply (elim step_max'_top_elim step_map_op_elim step_comp_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp split: if_splits option.splits add: map_upd_upds_conv_if; hypsubst_thin)
    subgoal for io op1' nid op'' x io' op''a pa op2' io'a op''b xs
      apply (cases x; hypsubst_thin)
      apply (drule input_invar_elim[where buf="\<lambda>p. map (case_list [] (\<lambda>a list. [Max (insert a (set list))])) (xs1 1)"])
       apply assumption
      apply safe
      apply (clarsimp simp add: map_eq_append_conv split: list.splits)
      subgoal for l zs la zsa x xs'
        apply (intro conjI exI)
         apply (rule step_wstep)
         apply (rule step_map_op)
          apply (rule step_max_op_Out_intro2[where p=0])
            apply (subst ldropWhile_lshift[where x="x # xs'"])
              apply simp
             apply simp
            apply (subst dropWhile_append2)
        subgoal premises prems for x
          using prems(1,7,11) apply -
          apply (drule map_in_setD)
           apply assumption
          apply (auto split: list.splits)
          done
            apply simp
           apply simp
          apply (simp add: defaults_num1_def)
         apply simp
         apply (subst ltakeWhile_lfshift[where x="x # xs'"])
           apply simp
          apply simp
         apply simp
         apply (subst takeWhile_append2)
        subgoal premises prems for x
          using prems(1,7,11) apply -
          apply (drule map_in_setD)
           apply assumption
          apply (auto split: list.splits)
          done
         apply simp
         apply (metis (no_types, lifting) length_map)
        subgoal
          apply (intro relcomppI)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
          apply simp
          apply (rule wb_upto_b_base)
          apply simp
          apply (rule exI[of _ os1])
          apply (rule exI[of _ "os2\<lparr> outpu := (outpu os2)(1 := xs) \<rparr>"])
          apply (rule exI[of _ "n(1 := Suc (dataflow_topology_from_tree.followed_by (n 1) (the_enat (llength (ltakeWhile ((=) []) ((la @ (x # xs') # zsa) @@- xs2 1 @@- xs3 1 @@- xs4 1 @@- inps 1))))))"])
          apply (rule exI[of _ caps2])
          apply (rule exI[of _ "xs1(1 := zsa)"])
          apply (rule exI[of _ xs2])
          apply (rule exI[of _ xs3])
          apply (rule exI[of _ xs4])
          apply (rule exI[of _ buf1])
          apply (rule exI[of _ buf2])
          apply (rule exI[of _ inps])
          apply (intro exI[of _ sg] conjI)
          apply simp_all
          subgoal
               apply (rule arg_cong2[where f=dataflow_op])
                apply (rule refl)+
               apply (rule arg_cong3[where f=map_op])
                 apply simp_all
               apply (rule arg_cong4[where f=comp_op])
                  apply simp_all
               apply (rule arg_cong3[where f=map_op])
                 apply simp_all
               apply (rule arg_cong3[where f=input_top])
                 apply simp_all
               apply (rule ext)
            apply simp_all
            apply (subst ltakeWhile_lfshift[where x="x # xs'"])
                apply simp_all
   apply (subst takeWhile_append2)
        subgoal 
          apply (drule map_in_setD)
           apply assumption
          apply (auto split: list.splits)
          done
        apply simp
        done
      subgoal
        apply (rule arg_cong3[where f=map_op])
          apply simp_all
        apply (rule arg_cong2[where f=max_op])
         apply (rule ext)
         apply simp_all
        apply force
        done
      subgoal
        apply simp_all
        apply (subst ltakeWhile_lfshift[where x="x # xs'"])
          apply simp_all
        apply (subst takeWhile_append2)
        subgoal 
          apply (drule map_in_setD)
           apply assumption
          apply (auto split: list.splits)
          done
        apply simp
        subgoal
          apply (rule input_invar_cong)
             apply assumption
            apply simp_all
          apply (rule ext)
          apply auto
          done
        done
      subgoal
        apply (rule input_invar_cong[where ?buf'=xs3])
           apply assumption
          apply simp_all
        apply (rule ext)
        apply auto
        apply (subst ltakeWhile_lfshift[where x="x # xs'"])
          apply simp_all
        apply (subst takeWhile_append2)
        subgoal 
          apply (drule map_in_setD)
           apply assumption
          apply (auto split: list.splits)
          done
        apply simp
        done
 subgoal
        apply (rule input_invar_cong[where ?buf'=xs2])
           apply assumption
          apply simp_all
   apply (rule ext)
   apply auto
 apply (subst ltakeWhile_lfshift[where x="x # xs'"])
          apply simp_all
        apply (subst takeWhile_append2)
        subgoal 
          apply (drule map_in_setD)
           apply assumption
          apply (auto split: list.splits)
          done
        apply simp
        done
      subgoal premises prems2
        using prems2(1,2,6,7,9,10-) apply -
        apply (drule input_invar_Cons)
        apply simp
  apply (rule input_invar_cong)
           apply assumption
          apply auto
        apply (rule ext)
        apply auto
         apply (subst ltakeWhile_lfshift[where x="x # xs'"])
          apply simp_all
        apply (subst takeWhile_append2)
        subgoal 
          apply (drule map_in_setD)
           apply assumption
          apply (auto split: list.splits)
          done
        apply auto
        apply (metis length_map)
        done
      done
    done
  done
  subgoal for io op1' op'' io' op''a p op1'a q io'a op''b xa xs
    apply (cases xa; hypsubst_thin)
    apply (drule input_invar_elim)
     apply assumption
    apply safe
    apply simp
    subgoal for a l ys zs
      apply (rule exI[of _ "map_op (Pair 1) (Pair 1) (max_op n (\<lambda>p. xs1 1 @@- xs2 1 @@- (xs3 1 @ (map fst l @ [(a # ys)])) @@- map fst zs @@- inps 1))"])
      apply (intro conjI exI)
        apply (simp add: lshift_assoc)
    apply (intro relcomppI)
            apply (rule bisim_refl)
           defer
           apply (rule wbisim_refl)
    apply (rule wb_upto_b_base)
          apply (rule exI[of _ "os1\<lparr> outpu := (outpu os1)(1 := xs) \<rparr>"])
          apply (rule exI[of _ "os2"])
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI[of _ "xs3(1 := xs3 1 @ (map fst l) @ [a # ys])"])
          apply (rule exI[of _ "xs4(1 := map fst zs)"])
          apply (rule exI[of _ "BENQ (Inr (1, 1))
                    (Inr (a, dataflow_topology_from_tree.followed_by
                              (dataflow_topology_from_tree.followed_by (dataflow_topology_from_tree.followed_by (dataflow_topology_from_tree.followed_by (n 1) (length (xs1 1))) (length (xs2 1))) (length (xs3 1))) (length l)))
                    buf1"])
          apply (rule exI)
          apply (rule exI[of _ inps])
      apply (intro exI[of _ sg] conjI)
           apply simp
           defer
           apply (rule arg_cong3[where f=map_op])
             apply simp_all
           apply (rule arg_cong2[where f=max_op])
          apply force
      apply (rule ext)
         apply (simp flip: lshift_assoc)
      subgoal premises prems
        using prems(9) apply -


end

           apply (rule refl)+
    subgoal
        apply (rule input_invar_cong[where ?buf'=xs4])
           apply assumption
          apply simp_all
   apply (rule ext)
   apply auto


        find_theorems input_invar name: eli

end


        apply (subst ltakeWhile_lfshift[where x="x # xs'"])
                apply simp_all
        apply (subst takeWhile_append2)
        subgoal 
          using prems apply -
          apply (drule map_in_setD)
           apply assumption
          apply (auto split: list.splits)
          done
        apply simp
        done
        subgoal
          using prems(4) apply -
 apply (rule input_invar_cong)
             apply assumption
            apply simp_all
           apply (rule ext)
           apply auto
        apply (subst ltakeWhile_lfshift[where x="x # xs'"])
                apply simp_all
        apply (subst takeWhile_append2)
        subgoal 
          using prems apply -
          apply (drule map_in_setD)
           apply assumption
          apply (auto split: list.splits)
          done
        apply simp
        done
      subgoal
          using prems(5) apply -
          apply (rule input_invar_cong)
             apply assumption
            apply simp_all
           apply (rule ext)
           apply auto
        apply (subst ltakeWhile_lfshift[where x="x # xs'"])
                apply simp_all
        apply (subst takeWhile_append2)
        subgoal 
          using prems apply -
          apply (drule map_in_setD)
           apply assumption
          apply (auto split: list.splits)
          done
        apply simp
        done
    subgoal
          using prems(9,2) apply -
         
          find_theorems "concat _ = concat _"

end
          apply (rule exI[of _ os1])
            apply (rule exI[of _ "os2\<lparr> outpu := (outpu os2)(1 := xs) \<rparr>"])
            apply (rule exI[of _ "n(0 := Suc (dataflow_topology_from_tree.followed_by (n 0) (the_enat (llength (ltakeWhile ((=) []) ((la @ (x # xs') # zsa) @@- xs2 1 @@- xs3 1 @@- xs4 1 @@- inps 1))))))"])
            apply (rule exI[of _ caps2])
          apply (rule exI[of _ "xs1( 0 := zsa)"])
          apply (rule exI[of _ "xs2"])
          apply (rule exI[of _ "xs3"])
          apply (rule exI[of _ "xs4"])
            apply (rule exI[of _ "buf1"])
            apply (rule exI[of _ "buf2"])
          apply (rule exI[of _ "inps"])
            apply (intro exI[of _ sg] conjI)
                 apply (rule refl)+
                 apply simp
          subgoal
               apply (rule input_invar_cong)
          using prems(3) apply assumption 
                 defer
            apply (rule refl)+
          apply (rule ext)
          apply auto
        apply (subst ltakeWhile_lfshift[where x="x # xs'"])
            apply simp_all
                   apply (subst takeWhile_append2)
          using prems(1,7) apply -
          using
            \<open>\<And>xb. map (case_list [] (\<lambda>a list. [Max (insert a (set list))])) la = map fst l \<Longrightarrow> map (case_list [] (\<lambda>a list. [Max (insert a (set list))])) zsa = map fst zs \<Longrightarrow> input_invar (\<lambda>p. Suc (dataflow_topology_from_tree.followed_by (dataflow_topology_from_tree.followed_by (dataflow_topology_from_tree.followed_by (n 1) (dataflow_topology_from_tree.followed_by (length la) (length zsa))) (length (xs2 1))) (length (xs3 1)))) xs4 (outpu os1) \<Longrightarrow> input_invar (\<lambda>p. Suc (dataflow_topology_from_tree.followed_by (dataflow_topology_from_tree.followed_by (n 1) (dataflow_topology_from_tree.followed_by (length la) (length zsa))) (length (xs2 1)))) xs3 ((map projr \<circ> buf1 \<circ> Inr \<circ>\<circ> Pair) 1) \<Longrightarrow> input_invar (\<lambda>p. Suc (dataflow_topology_from_tree.followed_by (n 1) (dataflow_topology_from_tree.followed_by (length la) (length zsa)))) xs2 (fold (\<lambda>cap f. f(1 := f 1 @ map (\<lambda>x. (x, time cap)) (buf2 cap))) caps2 (\<lambda>p. [])) \<Longrightarrow> outpu os2 1 = (Max (insert x (set xs')), dataflow_topology_from_tree.followed_by (n 1) (length l)) # xs \<Longrightarrow> \<forall>x\<in>set l. fst x = [] \<Longrightarrow> [n 1..< dataflow_topology_from_tree.followed_by (n 1) (dataflow_topology_from_tree.followed_by (length la) (length zsa))] @ [dataflow_topology_from_tree.followed_by (n 1) (dataflow_topology_from_tree.followed_by (length la) (length zsa))] = map snd l @ dataflow_topology_from_tree.followed_by (n 1) (length l) # map snd zs \<Longrightarrow> input_invar (n(1 := dataflow_topology_from_tree.followed_by (n 1) (length l))) ((\<lambda>p. map fst l @ [Max (insert x (set xs'))] # map fst zs) (1 := [] # map fst zs)) ((outpu os2)(1 := xs)) \<Longrightarrow> xs1 1 = la @ (x # xs') # zsa \<Longrightarrow> xb \<in> set la \<Longrightarrow> [] = xb\<close>
            prems(10,2,3,4,5,6,8,9) apply blast
          apply simp
          done
        subgoal
               apply (rule input_invar_cong)
          using prems(4) apply assumption 
          apply (rule ext)
          apply auto
  apply (subst ltakeWhile_lfshift[where x="x # xs'"])
            apply simp_all
                   apply (subst takeWhile_append2)
          using prems(1,7) apply -
          using
            \<open>\<And>xb. map (case_list [] (\<lambda>a list. [Max (insert a (set list))])) la = map fst l \<Longrightarrow> map (case_list [] (\<lambda>a list. [Max (insert a (set list))])) zsa = map fst zs \<Longrightarrow> input_invar (\<lambda>p. Suc (dataflow_topology_from_tree.followed_by (dataflow_topology_from_tree.followed_by (dataflow_topology_from_tree.followed_by (n 1) (dataflow_topology_from_tree.followed_by (length la) (length zsa))) (length (xs2 1))) (length (xs3 1)))) xs4 (outpu os1) \<Longrightarrow> input_invar (\<lambda>p. Suc (dataflow_topology_from_tree.followed_by (dataflow_topology_from_tree.followed_by (n 1) (dataflow_topology_from_tree.followed_by (length la) (length zsa))) (length (xs2 1)))) xs3 ((map projr \<circ> buf1 \<circ> Inr \<circ>\<circ> Pair) 1) \<Longrightarrow> input_invar (\<lambda>p. Suc (dataflow_topology_from_tree.followed_by (n 1) (dataflow_topology_from_tree.followed_by (length la) (length zsa)))) xs2 (fold (\<lambda>cap f. f(1 := f 1 @ map (\<lambda>x. (x, time cap)) (buf2 cap))) caps2 (\<lambda>p. [])) \<Longrightarrow> outpu os2 1 = (Max (insert x (set xs')), dataflow_topology_from_tree.followed_by (n 1) (length l)) # xs \<Longrightarrow> \<forall>x\<in>set l. fst x = [] \<Longrightarrow> [n 1..< dataflow_topology_from_tree.followed_by (n 1) (dataflow_topology_from_tree.followed_by (length la) (length zsa))] @ [dataflow_topology_from_tree.followed_by (n 1) (dataflow_topology_from_tree.followed_by (length la) (length zsa))] = map snd l @ dataflow_topology_from_tree.followed_by (n 1) (length l) # map snd zs \<Longrightarrow> input_invar (n(1 := dataflow_topology_from_tree.followed_by (n 1) (length l))) ((\<lambda>p. map fst l @ [Max (insert x (set xs'))] # map fst zs) (1 := [] # map fst zs)) ((outpu os2)(1 := xs)) \<Longrightarrow> xs1 1 = la @ (x # xs') # zsa \<Longrightarrow> xb \<in> set la \<Longrightarrow> [] = xb\<close>
            prems(10,2,3,4,5,6,8,9) apply blast
          apply simp
          done
           apply simp_all
        prefer 3
        subgoal
          apply (rule wbisim_map_op)
          apply (rule wbisim_refl_alt)
          apply (rule arg_cong2[where f=max_op])
           apply auto
          apply (rule ext)
          apply auto

        find_theorems map_op wbisim


        find_theorems input_invar

end
                apply (rule wb_upto_b_base)
                defer
                apply (rule wbisim_refl)
               apply (rule bisim_refl)


          find_theorems takeWhile append

         thm map_eq_append_conv

end
             apply force
            apply simp
           apply simp
          apply (simp add: defaults_num1_def)
         apply simp
         apply (intro conjI)
        

      thm input_invar_elim

      find_theorems  defaults 


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


