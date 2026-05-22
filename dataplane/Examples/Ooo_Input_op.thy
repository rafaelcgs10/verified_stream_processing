theory Ooo_Input_op

imports
  Dataplane.Timely_Stream
  Dataplane.Timely_Builder_Op
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
  unfolding ooo_input_op_logic_def produce_def
  apply (clarsimp simp add: image_iff simp flip: cin.rep_eq)
  apply (rule exI[of _ p])
  apply simp
  done

lemma ooo_input_op_logic_iterates_MintI[intro]:
  "ocaps os p \<noteq> [] \<Longrightarrow>
   p |\<in>| P \<Longrightarrow>
   es os p = LCons (Mint t) lxs \<Longrightarrow>
   os\<lparr>es := (es os)( p := lxs ),
      ocaps := (ocaps os)(p := ocaps os p @ [t]),
      inter := inter os @ [(p, t, 1)] \<rparr> |\<in>|
   (ooo_input_op_logic P os)"
  unfolding ooo_input_op_logic_def add_cap_def
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
  unfolding ooo_input_op_logic_def drop_cap_def
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

lemma remove_last_Nil:
  "remove_last t M = [] \<Longrightarrow>
   mset M - {# t #} = {#}"
  apply (induct M)
   apply simp
  apply (metis mset_remove_last mset.simps(1))
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