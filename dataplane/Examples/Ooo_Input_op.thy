theory Ooo_Input_op

imports
  "../Timely_Stream"
  "../Timely/Builder_Op"
begin

record ('p, 'd, 'd1, 't) input_state = "('p, 'd, 'd1, 't) operator_state_ty" + es:: "'p \<Rightarrow> ('t, 'd1) event llist"

definition \<open>ooo_input_op_logic ops os = cimage (\<lambda>p. case es os p of
    LNil \<Rightarrow> drop_caps os (map (\<lambda>t. Cap t p) (ocaps os p))
  | LCons (Data t d) lxs \<Rightarrow> produces (os\<lparr>es := (es os)(p := lxs)\<rparr>) [(en1 os d, Cap t p)]
  | LCons (Drop t) lxs \<Rightarrow> drop_caps (os\<lparr>es := (es os)(p := lxs)\<rparr>) [Cap t p]
  | LCons (Mint t) lxs \<Rightarrow> add_caps (os\<lparr>es := (es os)(p := lxs)\<rparr>) [Cap t p])
    (cfilter (\<lambda>p. ocaps os p \<noteq> []) ops)\<close>

definition ooo_input_op where
  "ooo_input_op ops os = builder_op False {||} ops os (ooo_input_op_logic ops)"

lemma nop_leaf_ooo_input_op:
  "nop_leaf None (ooo_input_op ops os)"
  unfolding ooo_input_op_def
  by (rule nop_leaf_builder_op) simp

lemma ooo_input_op_logic_front_initia[simp]:
  assumes "os' |\<in>| ooo_input_op_logic ops os"
  shows "front os' = front os" and "initia os' = initia os"
proof -
  obtain p where "os' = (case es os p of
      LNil \<Rightarrow> drop_caps os (map (\<lambda> t. Cap t p) (ocaps os p))
    | LCons (Data t d) lxs \<Rightarrow> produces (os\<lparr>es := (es os)(p := lxs)\<rparr>) [(en1 os d, Cap t p)]
    | LCons (Drop t) lxs \<Rightarrow> drop_caps (os\<lparr>es := (es os)(p := lxs)\<rparr>) [Cap t p]
    | LCons (Mint t) lxs \<Rightarrow> add_caps (os\<lparr>es := (es os)(p := lxs)\<rparr>) [Cap t p])"
    using assms unfolding ooo_input_op_logic_def by (auto simp flip: cin.rep_eq)
  then show "front os' = front os" and "initia os' = initia os"
    by (auto split: llist.splits event.splits)
qed

lemma ooo_input_op_logic_collapse[simp]:
  "os' |\<in>| ooo_input_op_logic ops os \<Longrightarrow>
   os'\<lparr>front := front os, initia := initia os\<rparr> = os'"
  by simp

record ('p, 'd, 'd1, 'd2, 't) input_state2 = "('p, 'd, 'd1, 'd2, 't) operator_state_ty2" + 
  es1:: "('t, 'd1) event llist" es2:: "('t, 'd2) event llist"

definition ooo_input_os_Drop_Mint where
  \<open>ooo_input_os_Drop_Mint p os e = (case e of
    Drop t \<Rightarrow> drop_caps os [Cap t p]
  | Mint t \<Rightarrow> add_caps os [Cap t p])\<close>


fun ocaps_updates where
  "ocaps_updates caps [] = caps"
| "ocaps_updates caps ((Data t d) # xs) = ocaps_updates caps xs"
| "ocaps_updates caps ((Drop t) # xs) = ocaps_updates (remove_last t caps) xs"
| "ocaps_updates caps ((Mint t) # xs) = ocaps_updates (caps @ [t]) xs"


lemma mset_ocaps_updates:
  "timely_input_stream (xs @@- lxs) (mset C) \<Longrightarrow>
   mset (ocaps_updates C xs) = mset C + event.time `# filter_mset is_Mint (mset xs) - event.time `# filter_mset is_Drop (mset xs)"
  apply (induct xs arbitrary: C)
   apply force
  subgoal for a xs' C'
    apply (cases a)
      apply (auto split: event.splits)
    subgoal
      by (smt (verit, ccfv_threshold) add_0 diff_diff_add_mset diff_union_single_convs(2) event.distinct(5) event.sel(2) event.simps(5) mset_remove_last timely_input_stream_DropI timely_input_stream_def
          timely_monotone_LConsE union_commute union_mset_add_mset_right)
    subgoal
      by (simp add: timely_input_stream_MintI)
    done
  done

lemma ooo_input_op_logic_iterates_DataI[intro]:
  "ocaps os p \<noteq> [] \<Longrightarrow>
   p |\<in>| P \<Longrightarrow>
   es os p = LCons (Data t d) lxs \<Longrightarrow>
   os' = os\<lparr>es := (es os)( p :=lxs ),
      produ := produ os @ [(p, t, 1)],
      outpu := (outpu os)( p := outpu os p @ [(en1 os d, t)] ) \<rparr> \<Longrightarrow>
   os' |\<in>|
   (ooo_input_op_logic P os)"
  unfolding ooo_input_op_logic_def produces_def
  apply (clarsimp simp add: image_iff simp flip: cin.rep_eq)
  apply (rule exI[of _ p])
  apply (simp add: fun_eq_iff)
  done

lemma ooo_input_op_logic_iterates_MintI[intro]:
  "ocaps os p \<noteq> [] \<Longrightarrow>
   p |\<in>| P \<Longrightarrow>
   es os p = LCons (Mint t) lxs \<Longrightarrow>
   os\<lparr>es := (es os)( p := lxs ),
      ocaps := (ocaps os)(p := ocaps os p @ [t]),
      inter := inter os @ [(p, t, 1)] \<rparr> |\<in>|
   (ooo_input_op_logic P os)"
  unfolding ooo_input_op_logic_def add_caps_singleton
  apply (clarsimp simp add: image_iff simp flip: cin.rep_eq)
  apply (rule exI[of _ p])
  apply simp
  done

lemma ooo_input_op_logic_iterates_DropI[intro]:
  "ocaps os p \<noteq> [] \<Longrightarrow>
   p |\<in>| P \<Longrightarrow>
   es os p = LCons (Drop t) lxs \<Longrightarrow>
   os\<lparr>es := (es os)( p := lxs ),
      ocaps := (ocaps os)(p := remove_last t (ocaps os p)),
      inter := inter os @ [(p, t, -1)] \<rparr> |\<in>|
   (ooo_input_op_logic P os)"
  unfolding ooo_input_op_logic_def drop_caps_singleton
  apply (clarsimp simp add: image_iff simp flip: cin.rep_eq)
  apply (rule exI[of _ p])
  apply simp
  done

lemma ooo_input_op_logic_cUn:
  "p |\<in>| P \<Longrightarrow>
   ((\<lambda>oss. cUnion (ooo_input_op_logic P |`| cfilter Q oss)) ^^ n) (cUn A B) =
   cUn (((\<lambda>oss. cUnion (ooo_input_op_logic P |`| cfilter Q oss)) ^^ n) A) (((\<lambda>oss. cUnion (ooo_input_op_logic P |`| cfilter Q oss)) ^^ n) B)"
  apply (induct n)
   apply (auto 10 10 simp flip: cin.rep_eq)
  done


lemma ooo_input_op_logic_iterates_n:
  "timely_input_stream (es os p) (mset (ocaps os p)) \<Longrightarrow>
   p |\<in>| P \<Longrightarrow>
   os |\<in>| OS \<Longrightarrow>
   initia os \<Longrightarrow>
   llength (es os p) \<ge> enat n \<Longrightarrow>
   os' = os\<lparr>es := (es os)( p := ldropn n (es os p)),
      ocaps := (ocaps os)(p := ocaps_updates (ocaps os p) (ltaken n (es os p))),
      inter := inter os @ (map (\<lambda> ev. case ev of Drop t \<Rightarrow> (p, t, -1) | Mint t \<Rightarrow> (p, t, 1)) (filter (Not o is_Data) (ltaken n (es os p)))),
      produ := produ os @ (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (p, t, 1)) (filter is_Data (ltaken n (es os p)))),
      outpu := (outpu os)( p := outpu os p @ (map (\<lambda> ev. case ev of Data t d \<Rightarrow> (en1 os d, t)) (filter is_Data (ltaken n (es os p)))) )\<rparr> \<Longrightarrow>
   os' |\<in>|
   ((\<lambda>oss. cUnion (ooo_input_op_logic P |`| cfilter (\<lambda>os. initia os \<and> (\<exists> p. ocaps os p \<noteq> [])) oss)) ^^ n) OS"
  apply (induct n arbitrary: os OS os')
  subgoal
    by simp
  subgoal premises prems for n os OS os'
    using prems(2-) apply - 
    apply (simp del: Nat.funpow.simps add:  flip: cin.rep_eq)
    apply (cases "es os p"; simp add: zero_enat_def del: Nat.funpow.simps flip: cin.rep_eq )
    subgoal for ev lxs
      apply (cases ev)
      subgoal for t d
        apply (clarsimp simp del: Nat.funpow.simps simp flip: cin.rep_eq)
        apply hypsubst_thin
        apply (subst funpow_Suc_right)
        apply (simp add:  flip: cin.rep_eq)
        apply (subgoal_tac "cUnion (ooo_input_op_logic P |`| (cfilter (\<lambda>os. initia os \<and> (\<exists> p. ocaps os p \<noteq> [])) OS)) = cUn (ooo_input_op_logic P os) (cUnion (ooo_input_op_logic P |`| ((cfilter (\<lambda>os. initia os \<and> (\<exists> p. ocaps os p \<noteq> [])) OS) - {| os |})))")
         defer
        subgoal 
          apply (subgoal_tac "ocaps os p \<noteq> []")
          subgoal
            by fastforce
          subgoal
            unfolding timely_input_stream_def
            apply auto
            done
          done
        subgoal
          apply simp
          apply (subst ooo_input_op_logic_cUn)
           apply (clarsimp del: disjCI simp flip: cin.rep_eq)
           apply assumption+
          apply (clarsimp del: disjCI simp flip: cin.rep_eq)
          apply (rule disjI1)
          apply (rule prems(1))
               prefer 3
               apply (rule ooo_input_op_logic_iterates_DataI[where p=p])
          subgoal
            unfolding timely_input_stream_def
            apply auto
            done
                 apply assumption+
               apply (rule refl)
              apply (clarsimp del: disjCI simp flip: cin.rep_eq)
              apply blast
             apply assumption+
            apply simp
           apply simp
          using Suc_ile_eq iless_Suc_eq apply blast
          apply simp
          done
        done
      subgoal for t
        apply (clarsimp simp del: Nat.funpow.simps simp flip: cin.rep_eq)
        apply hypsubst_thin
        apply (subst funpow_Suc_right)
        apply (simp add:  flip: cin.rep_eq)
        apply (subgoal_tac "cUnion (ooo_input_op_logic P |`| (cfilter (\<lambda>os. initia os \<and> (\<exists> p. ocaps os p \<noteq> [])) OS)) = cUn (ooo_input_op_logic P os) (cUnion (ooo_input_op_logic P |`| ((cfilter (\<lambda>os. initia os \<and> (\<exists> p. ocaps os p \<noteq> [])) OS) - {| os |})))")
         defer
        subgoal 
          apply (subgoal_tac "ocaps os p \<noteq> []")
          subgoal
            by fastforce
          subgoal
            unfolding timely_input_stream_def
            apply auto
            done
          done
        subgoal
          apply simp
          apply (subst ooo_input_op_logic_cUn)
           apply (clarsimp del: disjCI simp flip: cin.rep_eq)
           apply assumption
          apply (clarsimp del: disjCI simp flip: cin.rep_eq)
          apply (rule disjI1)
          apply (rule prems(1))
               prefer 3
               apply (rule ooo_input_op_logic_iterates_DropI[where p=p])
          subgoal
            unfolding timely_input_stream_def
            apply auto
            done
                apply assumption+
              apply simp
              apply blast
             apply assumption+
            apply simp
           apply simp
          using Suc_ile_eq iless_Suc_eq apply blast
          apply simp
          done
        done
      subgoal for t
        apply (clarsimp simp del: Nat.funpow.simps simp flip: cin.rep_eq)
        apply hypsubst_thin
        apply (subst funpow_Suc_right)
        apply (simp add:  flip: cin.rep_eq)
        apply (subgoal_tac "cUnion (ooo_input_op_logic P |`| (cfilter (\<lambda>os. initia os \<and> (\<exists> p. ocaps os p \<noteq> [])) OS)) = cUn (ooo_input_op_logic P os) (cUnion (ooo_input_op_logic P |`| ((cfilter (\<lambda>os. initia os \<and> (\<exists> p. ocaps os p \<noteq> [])) OS) - {| os |})))")
         defer
        subgoal 
          apply (subgoal_tac "ocaps os p \<noteq> []")
          subgoal
            by fastforce
          subgoal
            unfolding timely_input_stream_def
            apply auto
            done
          done
        subgoal
          apply simp
          apply (subst ooo_input_op_logic_cUn)
           apply (clarsimp del: disjCI simp flip: cin.rep_eq)
           apply assumption
          apply (clarsimp del: disjCI simp flip: cin.rep_eq)
          apply (rule disjI1)
          apply (rule prems(1))
               prefer 3
               apply (rule ooo_input_op_logic_iterates_MintI[where p=p])
          subgoal
            unfolding timely_input_stream_def
            apply auto
            done
                apply assumption+
              apply simp
              apply blast
             apply assumption+
            apply simp
           apply simp
          using Suc_ile_eq iless_Suc_eq apply blast
          apply simp
          done
        done
      done
    done
  done

section \<open>Introduction rules for ooo_input_op steps\<close>

lemma step_ooo_input_op_Write_None[intro]:
  assumes \<open>io = Out None (Inl (Inl st))\<close>
    and \<open>(os', st) = obtain_progress os\<close>
    and \<open>op = ooo_input_op ops os'\<close>
  shows \<open>step io (ooo_input_op ops os) op\<close>
  using assms unfolding ooo_input_op_def by auto

lemma step_ooo_input_op_Write_None_alt[intro]:
  assumes \<open>io = Out None (Inl (Inl (snd (obtain_progress os))))\<close>
    and \<open>op = ooo_input_op ops (fst (obtain_progress os))\<close>
  shows \<open>step io (ooo_input_op ops os) op\<close>
  by (rule step_ooo_input_op_Write_None[OF assms(1) _ assms(2)]) (rule prod.collapse)

lemma step_ooo_input_op_Write_Some[intro]:
  assumes \<open>io = Out (Some p) (Inr x)\<close>
    and \<open>p |\<in>| ops\<close>
    and \<open>outpu os p = x # xs\<close>
    and \<open>op = ooo_input_op ops (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>)\<close>
  shows \<open>step io (ooo_input_op ops os) op\<close>
  using assms unfolding ooo_input_op_def by auto

lemma steps_ooo_input_op_Write_Some[intro]:
  assumes \<open>p |\<in>| ops\<close>
    and \<open>outpu os p = xs @ ys\<close>
    and \<open>op = ooo_input_op ops (os\<lparr>outpu := (outpu os)(p := ys)\<rparr>)\<close>
    and \<open>zs = map (\<lambda>x. Out (Some p) (Inr x)) xs\<close>
  shows \<open>steps zs (ooo_input_op ops os) op\<close>
  using assms unfolding ooo_input_op_def by auto

lemma step_ooo_input_op_Silent[intro]:
  assumes \<open>io = Tau\<close>
    and \<open>initia os\<close>
    and \<open>os' |\<in>| ooo_input_op_logic ops os\<close>
    and \<open>op = ooo_input_op ops os'\<close>
  shows \<open>step io (ooo_input_op ops os) op\<close>
  unfolding assms(1,4) ooo_input_op_def
  apply (rule step_builder_op_Silent)
     apply (rule refl)
    apply (rule assms(2))
   apply (rule assms(3))
  apply (simp add: ooo_input_op_logic_collapse[OF assms(3)])
  done

lemma step_ooo_input_op_n_Silents[intro]:
  assumes \<open>os' |\<in>| ((\<lambda>oss. cUnion (cimage (ooo_input_op_logic ops)
      (cfilter (\<lambda>os. initia os \<and> (\<exists>p. ocaps os p \<noteq> [])) oss))) ^^ n) {|os|}\<close>
    and \<open>op = ooo_input_op ops os'\<close>
  shows \<open>(step Tau ^^ n) (ooo_input_op ops os) op\<close>
  using assms unfolding ooo_input_op_def
  by (intro step_builder_op_n_Silents_collapse) (auto simp: ooo_input_op_logic_collapse)

lemma steps_ooo_input_op_n_Silents[intro]:
  assumes \<open>os' |\<in>| ((\<lambda>oss. cUnion (cimage (ooo_input_op_logic ops)
      (cfilter (\<lambda>os. initia os \<and> (\<exists>p. ocaps os p \<noteq> [])) oss))) ^^ n) {|os|}\<close>
    and \<open>op = ooo_input_op ops os'\<close>
  shows \<open>(step Tau ^^ n) (ooo_input_op ops os) op\<close>
  using assms by (rule step_ooo_input_op_n_Silents)


lemma ooo_input_op_logic_LNilI[intro]:
  assumes \<open>ocaps os p \<noteq> []\<close>
    and \<open>p |\<in>| ops\<close>
    and \<open>es os p = LNil\<close>
    and \<open>os_next = drop_caps os (map (\<lambda>t. Cap t p) (ocaps os p))\<close>
  shows \<open>os_next |\<in>| ooo_input_op_logic ops os\<close>
  using assms unfolding ooo_input_op_logic_def
  apply (clarsimp simp add: image_iff simp flip: cin.rep_eq)
  apply (rule exI[of _ p])
  apply simp
  done

lemma step_ooo_input_op_LNil[intro]:
  assumes \<open>ocaps os p \<noteq> []\<close>
    and \<open>p |\<in>| ops\<close>
    and \<open>es os p = LNil\<close>
    and \<open>os_next = drop_caps os (map (\<lambda>t. Cap t p) (ocaps os p))\<close>
    and \<open>initia os\<close>
    and \<open>op = ooo_input_op ops os_next\<close>
  shows \<open>step Tau (ooo_input_op ops os) op\<close>
  using assms by (metis ooo_input_op_logic_LNilI step_ooo_input_op_Silent)

lemma ooo_input_op_logic_DataI[intro]:
  assumes \<open>ocaps os p \<noteq> []\<close>
    and \<open>p |\<in>| ops\<close>
    and \<open>es os p = LCons (Data t d) lxs\<close>
    and \<open>os_next = produces (os\<lparr>es := (es os)(p := lxs)\<rparr>) [(en1 os d, Cap t p)]\<close>
  shows \<open>os_next |\<in>| ooo_input_op_logic ops os\<close>
  using assms unfolding ooo_input_op_logic_def
  apply (clarsimp simp add: image_iff simp flip: cin.rep_eq)
  apply (rule exI[of _ p])
  apply simp
  done

lemma step_ooo_input_op_Data[intro]:
  assumes \<open>ocaps os p \<noteq> []\<close>
    and \<open>p |\<in>| ops\<close>
    and \<open>es os p = LCons (Data t d) lxs\<close>
    and \<open>os_next = produces (os\<lparr>es := (es os)(p := lxs)\<rparr>) [(en1 os d, Cap t p)]\<close>
    and \<open>initia os\<close>
    and \<open>op = ooo_input_op ops os_next\<close>
  shows \<open>step Tau (ooo_input_op ops os) op\<close>
  using assms by (metis ooo_input_op_logic_DataI step_ooo_input_op_Silent)

lemma ooo_input_op_logic_DropI[intro]:
  assumes \<open>ocaps os p \<noteq> []\<close>
    and \<open>p |\<in>| ops\<close>
    and \<open>es os p = LCons (Drop t) lxs\<close>
    and \<open>os_next = drop_caps (os\<lparr>es := (es os)(p := lxs)\<rparr>) [Cap t p]\<close>
  shows \<open>os_next |\<in>| ooo_input_op_logic ops os\<close>
  using assms unfolding ooo_input_op_logic_def
  apply (clarsimp simp add: image_iff simp flip: cin.rep_eq)
  apply (rule exI[of _ p])
  apply simp
  done

lemma step_ooo_input_op_Drop[intro]:
  assumes \<open>ocaps os p \<noteq> []\<close>
    and \<open>p |\<in>| ops\<close>
    and \<open>es os p = LCons (Drop t) lxs\<close>
    and \<open>os_next = drop_caps (os\<lparr>es := (es os)(p := lxs)\<rparr>) [Cap t p]\<close>
    and \<open>initia os\<close>
    and \<open>op = ooo_input_op ops os_next\<close>
  shows \<open>step Tau (ooo_input_op ops os) op\<close>
  using assms by (metis ooo_input_op_logic_DropI step_ooo_input_op_Silent)

lemma ooo_input_op_logic_MintI[intro]:
  assumes \<open>ocaps os p \<noteq> []\<close>
    and \<open>p |\<in>| ops\<close>
    and \<open>es os p = LCons (Mint t) lxs\<close>
    and \<open>os_next = add_caps (os\<lparr>es := (es os)(p := lxs)\<rparr>) [Cap t p]\<close>
  shows \<open>os_next |\<in>| ooo_input_op_logic ops os\<close>
  using assms unfolding ooo_input_op_logic_def
  apply (clarsimp simp add: image_iff simp flip: cin.rep_eq)
  apply (rule exI[of _ p])
  apply simp
  done

lemma step_ooo_input_op_Mint[intro]:
  assumes \<open>ocaps os p \<noteq> []\<close>
    and \<open>p |\<in>| ops\<close>
    and \<open>es os p = LCons (Mint t) lxs\<close>
    and \<open>os_next = add_caps (os\<lparr>es := (es os)(p := lxs)\<rparr>) [Cap t p]\<close>
    and \<open>initia os\<close>
    and \<open>op = ooo_input_op ops os_next\<close>
  shows \<open>step Tau (ooo_input_op ops os) op\<close>
  using assms by (metis ooo_input_op_logic_MintI step_ooo_input_op_Silent)




lemma step_compower_ooo_input_op_iterates_n[intro]:
  assumes \<open>timely_input_stream (es os p) (mset (ocaps os p))\<close>
    and \<open>p |\<in>| ops\<close>
    and \<open>initia os\<close>
    and \<open>llength (es os p) \<ge> enat n\<close>
    and \<open>os_next = os\<lparr>es := (es os)(p := ldropn n (es os p)),
      ocaps := (ocaps os)(p := ocaps_updates (ocaps os p) (ltaken n (es os p))),
      inter := inter os @ (map (\<lambda>ev. case ev of Drop t \<Rightarrow> (p, t, -1) | Mint t \<Rightarrow> (p, t, 1))
        (filter (Not \<circ> is_Data) (ltaken n (es os p)))),
      produ := produ os @ (map (\<lambda>ev. case ev of Data t d \<Rightarrow> (p, t, 1))
        (filter is_Data (ltaken n (es os p)))),
      outpu := (outpu os)(p := outpu os p @ (map (\<lambda>ev. case ev of Data t d \<Rightarrow> (en1 os d, t))
        (filter is_Data (ltaken n (es os p)))))\<rparr>\<close>
    and \<open>op = ooo_input_op ops os_next\<close>
  shows \<open>(step Tau ^^ n) (ooo_input_op ops os) op\<close>
  using assms ooo_input_op_logic_iterates_n[where OS = \<open>{|os|}\<close> and os = os and p = p and P = ops and n = n and os' = os_next]
  by auto


end