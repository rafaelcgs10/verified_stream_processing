theory Timely_Progress

imports
  Timely_Propagation_Exec
  Timely_Operator_State
begin

section \<open>Progress Extraction and Dataflow Wrapper\<close>

text \<open>
  This section defines progress extraction from operator-local buffers and the core
  wrapper helpers that couple data-plane progress updates with control-plane updates.
\<close>

definition "change_multiplicities summary xs conf = fold (\<lambda> (l, t, m) c. take_step summary (CM l t m) c) xs conf"

lemma change_multiplicities_append:
  "change_multiplicities su (xs @ ys) = (\<lambda> c. change_multiplicities su ys (change_multiplicities su xs c))"
  unfolding change_multiplicities_def
  apply (rule ext)
  apply simp
  done

lemma change_multiplicities_append_alt:
  "change_multiplicities su (xs @ ys) c = change_multiplicities su ys (change_multiplicities su xs c)"
  using change_multiplicities_append by metis

lemma change_multiplicities_append_comp:
  "change_multiplicities su (xs @ ys) = change_multiplicities su ys o change_multiplicities su xs"
  unfolding change_multiplicities_def
  by simp


lemma change_multiplicitie_rev[simp]:
  "change_multiplicities su (rev xs) c = change_multiplicities su xs c"
  unfolding change_multiplicities_def
  apply (subst fold_rev)
   apply (clarsimp simp add: take_step_comm)+
  done

lemma change_multiplicities_comm:
  "change_multiplicities su (xs @ ys) c = change_multiplicities su (ys @ xs) c"
  unfolding change_multiplicities_def
  by (metis (mono_tags, lifting) change_multiplicitie_rev change_multiplicities_append change_multiplicities_def rev_append)

lemma change_multiplicities_simps[simp]:
  "change_multiplicities su [] c = c"
  "change_multiplicities su ((l, t, m) # xs) c = change_multiplicities su xs (take_step summary (CM l t m) c)"
  unfolding change_multiplicities_def by simp+

lemma change_multiplicities_simp_alt:
  "change_multiplicities su ((l, t, m) # xs) c = take_step su (CM l t m) (change_multiplicities su xs c)"
proof -
  have "change_multiplicities su ((l, t, m) # xs) c = change_multiplicities su (rev ((l, t, m) # xs)) c" using change_multiplicitie_rev by metis
  also have "\<dots> = take_step su (CM l t m) (change_multiplicities su (rev xs) c)" by (simp add: change_multiplicities_def foldr_conv_fold)
  ultimately show ?thesis by (metis change_multiplicitie_rev)
qed

lemma c_pts_change_multiplicities:
  "c_pts (change_multiplicities su xs c) = (\<lambda> l. c_pts c l + zmset (map snd (filter (\<lambda> (l', t, d). l = l') xs)))"
  apply (induct xs arbitrary: c)
   apply simp
  subgoal for x xs c
    apply (rule ext)+
    apply (cases x)
    apply (auto split: if_splits prod.splits simp add: change_multiplicities_simp_alt update_zmultiset_plus_comm)
    done
  done

lemma concat_map_time_filter_out[simp]:
  "distinct ps \<Longrightarrow> p \<in> set ps \<Longrightarrow> concat (map (\<lambda>x. map time (filter (\<lambda>x. out x = p) (map (\<lambda>t'. Cap (t -+- t') x) (xs x)))) ps) = map ((-+-) t) (xs p)"
  apply (induct ps)
   apply simp
  subgoal premises prems for p' ps'
    apply (cases "p = p'")
    subgoal
      apply hypsubst_thin
      apply (clarsimp simp add: comp_def filter_empty_conv)
      using prems(2) apply -
      subgoal
        by (meson distinct.simps(2))
      done
    subgoal
      using prems apply -
      apply auto
      done
    done
  done

definition "has_progress st = (cons st \<noteq> [] \<or> inte st \<noteq> [] \<or> prod st \<noteq> [])"

abbreviation "not_nop sg op \<equiv> (case op of Read (Inl nid) f \<Rightarrow> upfro sg nid | Write _ (Inl _) (Inl (Inl st)) \<Rightarrow> has_progress st | _ \<Rightarrow> True)"

fun delay_nop where
  "delay_nop F 0 xs lxs = xs @@- lxs"
| "delay_nop F n xs LNil = llist_of xs"
| "delay_nop F (Suc n) xs (LCons x lxs) = (if F x then LCons x (delay_nop F n xs lxs) else delay_nop F n (xs @ [x]) lxs)"
declare delay_nop.simps[code del]
declare delay_nop.simps[simp del]

lemma delay_nop_code[code]:
  "delay_nop F n xs lxs =
  (if n = 0 then trace (STR ''Natural too small'') (xs @@- lxs) else
  (case lxs of LNil \<Rightarrow> llist_of xs | LCons x lxs \<Rightarrow> (if F x then LCons x (delay_nop F (n - 1) xs lxs) else trace (STR ''Delay'') (delay_nop F (n - 1) (xs @ [x]) lxs))))"
  apply (cases n)
  apply (simp_all add: delay_nop.simps split: llist.splits)
  done

definition "delay_cset (F :: ('a, 'b, 'c) op \<Rightarrow> bool) (n :: nat) (C :: (('a, 'b, 'c) op) cset) = C"
declare delay_cset_def[code drop]

lemma delay_cset_code_aux:
  "cUn (delay_cset F n (cset_of_llist lxs)) (cset_from_list xs)  = cset_of_llist (delay_nop F n xs lxs)"
  unfolding delay_cset_def
  apply (induct n arbitrary: lxs xs)
   apply (simp_all add: delay_nop.simps split: llist.splits)
  subgoal for n lxs xs
    apply (cases lxs)
   apply (simp_all add: delay_nop.simps split: llist.splits)
     apply (metis cset_of_llist_lshift shift_LNil)
   apply (auto simp add: delay_nop.simps split: llist.splits simp flip: cin.rep_eq)
    apply (metis cUn_cinsert_left cinsert_code)
    apply (metis cUn_cinsert_left cinsert_code)
    apply (metis cset_of_llist_lshift snoc_shift)
    apply (metis cset_of_llist_lshift snoc_shift)
    done
  done

lemma delay_cset_code[code]:
  "delay_cset F n (cset_of_llist lxs) = cset_of_llist (delay_nop F n [] lxs)"
  by (simp flip: delay_cset_code_aux)

lemma c_pts_change_multiplicities_append:
  "c_pts (change_multiplicities su (xs @ ys) c) l = (c_pts (change_multiplicities su xs c) l) + (c_pts (change_multiplicities su ys c) l) - c_pts c l"
  by (simp add: c_pts_change_multiplicities)


lemma change_multiplicities_extract_progress_append:
  "change_multiplicities su (extract_progress nid nt \<lparr>cons = C1 @ C2,  inte = I1 @ I2, prod = P1 @ P2 \<rparr>) c =
   change_multiplicities su (extract_progress nid nt \<lparr>cons = C2,  inte = I2, prod = P2 \<rparr>) (change_multiplicities su (extract_progress nid nt \<lparr>cons = C1,  inte = I1, prod = P1 \<rparr>) c)"
  unfolding extract_progress_def
  apply simp
  apply (smt (verit, del_insts) change_multiplicities_append change_multiplicities_comm)
  done

lemma c_imp_change_multiplicities[simp]:
  "c_imp (change_multiplicities su xs c) = c_imp c"
  apply (induct xs arbitrary: c)
   apply simp
  apply (auto split: if_splits prod.splits simp add: change_multiplicities_simp_alt update_zmultiset_plus_comm) 
  done

end
