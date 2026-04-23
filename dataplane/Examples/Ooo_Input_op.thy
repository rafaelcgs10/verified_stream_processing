theory Ooo_Input_op

imports
  Dataplane.Timely_Stream
  Source_op
begin

record ('p, 'd, 'd1, 't) input_state = "('p, 'd, 'd1, 't) operator_state_ty" + es:: "'p \<Rightarrow> ('t, 'd1) event llist"

definition \<open>ooo_input_op_logic ops os = cimage (\<lambda>p. case es os p of
    LNil \<Rightarrow> drop_caps os (map (\<lambda>t. Cap t p) (ocaps os p))
  | LCons (Data t d) lxs \<Rightarrow> produce (os\<lparr>es := (es os)(p := lxs)\<rparr>) (Cap t p) [en1 os d]
  | LCons (Drop t) lxs \<Rightarrow> drop_cap (os\<lparr>es := (es os)(p := lxs)\<rparr>) (Cap t p)
  | LCons (Mint t) lxs \<Rightarrow> add_cap (os\<lparr>es := (es os)(p := lxs)\<rparr>) p t)
    (cfilter (\<lambda>p. ocaps os p \<noteq> []) ops)\<close>

definition ooo_input_op where
  "ooo_input_op ops os = builder_op False {||} ops os (ooo_input_op_logic ops)"

record ('p, 'd, 'd1, 'd2, 't) input_state2 = "('p, 'd, 'd1, 'd2, 't) operator_state_ty2" + 
  es1:: "('t, 'd1) event llist" es2:: "('t, 'd2) event llist"

definition input_ty_fun where
  "input_ty_fun ess_update ess os p = (case ess os of
    LNil \<Rightarrow> drop_caps os (map (\<lambda> t. Cap t p) (ocaps os p))
  | LCons (Data t d) lxs \<Rightarrow> produce (ess_update (\<lambda> l. lxs) os) (Cap t p) [en1 os d]
  | LCons (Drop t) lxs \<Rightarrow> drop_cap (ess_update (\<lambda> l. lxs) os) (Cap t p)
  | LCons (Mint t) lxs \<Rightarrow> mint_cap (ess_update (\<lambda> l. lxs) os) p t)"

definition ooo_input_ty2_op where
  "ooo_input_ty2_op os = builder_op False {||} {|1 :: 2, 2|} os (\<lambda> os. (cimage (\<lambda>p.
  (if p = 1 
  then
   input_ty_fun es1_update es1 os p
  else
   input_ty_fun es2_update es2 os p))
    (cfilter (\<lambda>p. ocaps os p \<noteq> []) {| 1, 2|})))"

definition ooo_input_os_Drop_Mint where
  \<open>ooo_input_os_Drop_Mint p os e = (case e of
    Drop t \<Rightarrow> drop_cap os (Cap t p)
  | Mint t \<Rightarrow> add_cap os p t)\<close>


fun ocaps_updates where
  "ocaps_updates caps [] = caps"
| "ocaps_updates caps ((Data t d) # xs) = ocaps_updates caps xs"
| "ocaps_updates caps ((Drop t) # xs) = ocaps_updates (remove_last t caps) xs"
| "ocaps_updates caps ((Mint t) # xs) = ocaps_updates (caps @ [t]) xs"

lemma ooo_input_op_logic_iterates_n:
  "ocaps os p \<noteq> [] \<Longrightarrow>
   p |\<in>| P \<Longrightarrow>
   llength (es os p) \<ge> enat n \<Longrightarrow>
   os\<lparr>es := (es os)( p := ldropn n (es os p)),
      ocaps := (ocaps os)(p := ocaps_updates (ocaps os p) (ltaken n (es os p))),
      inter := inter os @ (map (\<lambda> ev. case ev of Drop t \<Rightarrow> (p, t, -1) | Mint t \<Rightarrow> (p, t, 1)) (filter (Not o is_Data) (ltaken n (es os p)))),
      produ := produ os @ (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (p, t, 1)) (filter is_Data (ltaken n (es os p)))),
      outpu := (outpu os)( p := outpu os p @ (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (en1 os d, t)) (filter is_Data (ltaken n (es os p)))) ) \<rparr> |\<in>|
   ((\<lambda>oss. cUnion (ooo_input_op_logic P |`| oss)) ^^ n) {|os|}"
  apply (induct n arbitrary: os rule: less_induct)
  subgoal for n os
    apply (cases n)
    subgoal
      by simp
    subgoal for n'
      apply (cases "es os p"; simp add: zero_enat_def flip: cin.rep_eq )
    subgoal for ev lxs
      apply (cases ev)
      subgoal for t d
        apply (clarsimp simp flip: cin.rep_eq)
        apply (cases n')
        subgoal
        apply (clarsimp simp flip: cin.rep_eq)
           apply simp_all
          unfolding ooo_input_op_logic_def produce_def
          apply (clarsimp simp add: image_iff simp flip: cin.rep_eq)
          apply (rule exI[of _ p])
          apply simp
          done
        subgoal for n''
          apply (clarsimp simp add: image_iff simp flip: cin.rep_eq)
          apply hypsubst_thin
          subgoal premises prems
            apply (rule cBexI[rotated])
            apply (simp add: cUNION_cimage flip: cin.rep_eq)
            apply (rule cBexI[rotated])
              apply (rule prems(1))
            using prems(2-) apply simp
            using prems(2-) apply simp
            subgoal
           using prems(2-) by (metis Suc_ile_eq llength_LCons nless_le)
           apply (subst ooo_input_op_logic_def)
          using prems(2-) apply -
           apply (simp add: cUNION_cimage flip: cin.rep_eq)
          apply (rule exI[of _ p])
           apply (simp add: cUNION_cimage flip: cin.rep_eq)
           apply (intro conjI)
            defer
            apply (rule refl)
           apply (clarsimp simp add: cUNION_cimage flip: cin.rep_eq split: llist.splits)

            find_theorems "cUnion ( _ |`| _) = _"



            find_theorems "_ |\<in>| cfilter _ _"

end


    apply (drule meta_spec[of _ "os\<lparr> es := (es os)(p := ltl (es os p)), produ := produ os @ [(p, t, 1)], outpu := (outpu os)( p := outpu os p @ [(en1 os d, t)]) \<rparr>"])
    apply simp
    apply (drule meta_mp)
    subgoal
      apply (metis eSuc_enat eSuc_ile_mono)
      done
    subgoal
      apply (clarsimp simp flip: cin.rep_eq)



end
      apply (rule exI[of _ "os\<lparr>es := (es os)(p := ldropn n lxs), ocaps := (ocaps os)(p := ocaps_updates (ocaps os p) (ltaken n lxs)),
         inter := operator_state.inter os @ map (case_event (\<lambda>a aa. undefined) (\<lambda>t. (p, t, - 1)) (\<lambda>t. (p, t, 1))) (filter (Not \<circ> is_Data) (ltaken n lxs)),
         produ := produ os @ (p, t, 1) # map (case_event (\<lambda>t d. (p, t, 1)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)),
         outpu := (outpu os)(p := outpu os p @ (en1 os d, t) # map (case_event (\<lambda>t d. (en1 os d, t)) (\<lambda>a. undefined) (\<lambda>a. undefined)) (filter is_Data (ltaken n lxs)))\<rparr>"])
      subgoal
        apply (intro conjI)
        subgoal premises temp
          using temp(7) apply -
          apply (cases n)
          subgoal
        unfolding ooo_input_op_logic_def drop_caps_def
        apply (auto simp flip: cin.rep_eq split: event.splits llist.splits)


end
      apply (rule exI[of _ "os\<lparr>es := (es os)(p := ldropn n (ltl (es os p)))\<rparr>"])
      apply (clarsimp simp flip: cin.rep_eq)
      apply (intro conjI[rotated])
      subgoal premises temp
        using temp(1,2,3,4) apply -
        unfolding ooo_input_op_logic_def drop_caps_def
        apply (auto simp flip: cin.rep_eq split: event.splits llist.splits)
        apply (intro exI conjI impI)
             defer
             apply assumption+
           apply simp
        subgoal
          by simp
        subgoal
          apply auto
          subgoal
            



end
    apply (auto simp flip: cin.rep_eq split: event.splits llist.splits)
    apply (rule cBexI[rotated])
    apply (simp flip: cin.rep_eq)

    find_theorems "_ |\<in>| cfilter _ _"

(* record ('p, 'd, 'd1, 'd2, 'd3, 't) input_state_ty3 = "('p, 'd, 'd1, 'd2, 't) input_state2" +  es3:: "('t, 'd3) event llist"

definition ooo_input_ty3_op where
  "ooo_input_ty3_op os = builder_op {||} {| 1, 2, 3|} os (\<lambda> os. (cimage (\<lambda>p.
  (if p = 1 
  then
   (case es1 os of
    LNil \<Rightarrow> drop_caps os (map (\<lambda> t. Cap t p) (ocaps os p))
  | LCons (Data t d) lxs \<Rightarrow> produce (os\<lparr> es1 := lxs \<rparr>) (Cap t p) [en1 os d]
  | LCons (Drop t) lxs \<Rightarrow> drop_cap (os\<lparr> es1 := lxs \<rparr>) (Cap t p)
  | LCons (Mint t) lxs \<Rightarrow> mint_cap (os\<lparr> es1 := lxs \<rparr>) p t)
  else (if p = 2 then
    (case es2 os of
    LNil \<Rightarrow> drop_caps os (map (\<lambda> t. Cap t p) (ocaps os p))
  | LCons (Data t d) lxs \<Rightarrow> produce (os\<lparr> es2 := lxs \<rparr>) (Cap t p) [en2 os d]
  | LCons (Drop t) lxs \<Rightarrow> drop_cap (os\<lparr> es2 := lxs \<rparr>) (Cap t p)
  | LCons (Mint t) lxs \<Rightarrow> mint_cap (os\<lparr> es2 := lxs \<rparr>) p t) 
  else (case es3 os of
    LNil \<Rightarrow> drop_caps os (map (\<lambda> t. Cap t p) (ocaps os p))
  | LCons (Data t d) lxs \<Rightarrow> produce (os\<lparr> es3 := lxs \<rparr>) (Cap t p) [en3 os d]
  | LCons (Drop t) lxs \<Rightarrow> drop_cap (os\<lparr> es3 := lxs \<rparr>) (Cap t p)
  | LCons (Mint t) lxs \<Rightarrow> mint_cap (os\<lparr> es3 := lxs \<rparr>) p t) )))
    (cfilter (\<lambda>p. ocaps os p \<noteq> []) {| 1, 2, 3|})))" *)

end