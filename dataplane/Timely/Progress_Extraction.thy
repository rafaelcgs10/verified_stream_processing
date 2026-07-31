theory Progress_Extraction

imports
  Propagation_Exec
  Operator_State
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

lemma change_multiplicities_update_form:
  "change_multiplicities su xs c =
   c\<lparr>c_pts := c_pts (change_multiplicities su xs c),
     c_work := c_work (change_multiplicities su xs c)\<rparr>"
proof (induct xs arbitrary: c)
  case Nil
  show ?case by simp
next
  case (Cons x xs c)
  obtain l t m where xeq: "x = (l, t, m)" by (cases x) auto
  let ?c' = "take_step su (CM l t m) c"
  have "change_multiplicities su (x # xs) c = change_multiplicities su xs ?c'"
    unfolding change_multiplicities_def by (simp add: xeq)
  also have "\<dots> = ?c'\<lparr>c_pts := c_pts (change_multiplicities su xs ?c'),
                      c_work := c_work (change_multiplicities su xs ?c')\<rparr>"
    by (rule Cons.hyps)
  also have "\<dots> = c\<lparr>c_pts := c_pts (change_multiplicities su xs ?c'),
                    c_work := c_work (change_multiplicities su xs ?c')\<rparr>"
    by simp
  finally show ?case
    by (simp add: xeq)
qed

lemma c_work_change_multiplicities:
  "c_work (change_multiplicities su xs c) l =
   c_work c l + zmultiset_of_antichain (frontier (c_pts (change_multiplicities su xs c) l))
              - zmultiset_of_antichain (frontier (c_pts c l))"
proof (induct xs arbitrary: c)
  case Nil
  show ?case by simp
next
  case (Cons x xs c)
  obtain l' t m where xeq: "x = (l', t, m)" by (cases x) auto
  let ?c' = "take_step su (CM l' t m) c"
  have lhs: "c_work (change_multiplicities su (x # xs) c) l = c_work (change_multiplicities su xs ?c') l"
    unfolding change_multiplicities_def by (simp add: xeq)
  have pts_lhs: "c_pts (change_multiplicities su (x # xs) c) l = c_pts (change_multiplicities su xs ?c') l"
    unfolding change_multiplicities_def by (simp add: xeq)
  have ih: "c_work (change_multiplicities su xs ?c') l =
            c_work ?c' l + zmultiset_of_antichain (frontier (c_pts (change_multiplicities su xs ?c') l))
                         - zmultiset_of_antichain (frontier (c_pts ?c' l))"
    by (rule Cons.hyps)
  show ?case
  proof (cases "l = l'")
    case True
    have cw: "c_work ?c' l = c_work c l + zmultiset_of_antichain (frontier (c_pts ?c' l))
                                        - zmultiset_of_antichain (frontier (c_pts c l))"
      using True by simp
    show ?thesis using lhs pts_lhs ih cw by simp
  next
    case False
    have cw: "c_work ?c' l = c_work c l" using False by simp
    have cp: "c_pts ?c' l = c_pts c l" using False by simp
    show ?thesis using lhs pts_lhs ih cw cp by simp
  qed
qed

definition "CM_equiv xs ys = (\<forall> l \<in> fst ` set xs \<union> fst ` set ys. zmset (map snd (filter (\<lambda> (l', _, _). l = l') xs)) = zmset (map snd (filter (\<lambda> (l', _, _). l = l') ys)))"

lemma change_multiplicities_zmset_cong:
  "CM_equiv xs ys \<Longrightarrow>
   change_multiplicities su xs = change_multiplicities su ys"
  unfolding CM_equiv_def
proof (rule ext)
  fix c
  assume H: "\<forall> l \<in> fst ` set xs \<union> fst ` set ys. zmset (map snd (filter (\<lambda> (l', _, _). l = l') xs)) = zmset (map snd (filter (\<lambda> (l', _, _). l = l') ys))"
  have pts_eq: "c_pts (change_multiplicities su xs c) = c_pts (change_multiplicities su ys c)"
  proof (rule ext)
    fix l
    show "c_pts (change_multiplicities su xs c) l = c_pts (change_multiplicities su ys c) l"
    proof (cases "l \<in> fst ` set xs \<union> fst ` set ys")
      case True
      with H show ?thesis by (simp add: c_pts_change_multiplicities)
    next
      case False
      then have "filter (\<lambda> (l', _, _). l = l') xs = []" and "filter (\<lambda> (l', _, _). l = l') ys = []"
        by (force simp: filter_empty_conv image_iff)+
      then show ?thesis by (simp add: c_pts_change_multiplicities)
    qed
  qed
  have work_eq: "c_work (change_multiplicities su xs c) = c_work (change_multiplicities su ys c)"
    by (rule ext) (simp add: c_work_change_multiplicities pts_eq)
  show "change_multiplicities su xs c = change_multiplicities su ys c"
    by (subst change_multiplicities_update_form, subst (2) change_multiplicities_update_form, simp add: pts_eq work_eq)
qed


lemma zmset_filter_eq_if_c_pts_change_multiplicities_eq:
  assumes \<open>c_pts (change_multiplicities su xs c) l =
    c_pts (change_multiplicities su ys c) l\<close>
  shows \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') xs)) =
    zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys))\<close>
  using assms
  by (simp add: c_pts_change_multiplicities)

lemma CM_equiv_empty_filter_notin:
  assumes \<open>l \<notin> fst ` set xs\<close>
  shows \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') xs)) = {#}\<^sub>z\<close>
  using assms by (induct xs) auto

lemma CM_equiv_trans:
  assumes \<open>CM_equiv xs ys\<close> and \<open>CM_equiv ys zs\<close>
  shows \<open>CM_equiv xs zs\<close>
proof -
  have step: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') xs)) =
      zmset (map snd (filter (\<lambda>(l', _, _). l = l') zs))\<close>
    if \<open>l \<in> fst ` set xs \<union> fst ` set zs\<close> for l
  proof -
    have xy: \<open>l \<in> fst ` set xs \<union> fst ` set ys \<Longrightarrow>
      zmset (map snd (filter (\<lambda>(l', _, _). l = l') xs)) =
      zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys))\<close>
      using assms(1) unfolding CM_equiv_def by blast
    have yz: \<open>l \<in> fst ` set ys \<union> fst ` set zs \<Longrightarrow>
      zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys)) =
      zmset (map snd (filter (\<lambda>(l', _, _). l = l') zs))\<close>
      using assms(2) unfolding CM_equiv_def by blast
    show ?thesis
    proof (cases \<open>l \<in> fst ` set xs\<close>)
      case True
      have xs_ys: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') xs)) =
        zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys))\<close>
        using True xy by simp
      show ?thesis
      proof (cases \<open>l \<in> fst ` set ys \<union> fst ` set zs\<close>)
        case True
        then show ?thesis
          using xs_ys yz by simp
      next
        case False
        then have ys_empty: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys)) = {#}\<^sub>z\<close>
          by (intro CM_equiv_empty_filter_notin) auto
        have zs_empty: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') zs)) = {#}\<^sub>z\<close>
          using False by (intro CM_equiv_empty_filter_notin) auto
        show ?thesis
          using xs_ys ys_empty zs_empty by simp
      qed
    next
      case False_xs: False
      have xs_empty: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') xs)) = {#}\<^sub>z\<close>
        by (rule CM_equiv_empty_filter_notin[OF False_xs])
      have z_in: \<open>l \<in> fst ` set zs\<close>
        using that False_xs by simp
      have ys_zs: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys)) =
        zmset (map snd (filter (\<lambda>(l', _, _). l = l') zs))\<close>
        using z_in yz by simp
      show ?thesis
      proof (cases \<open>l \<in> fst ` set ys\<close>)
        case True
        have xs_ys: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') xs)) =
          zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys))\<close>
          using True xy by simp
        show ?thesis
          using xs_ys ys_zs by simp
      next
        case False
        have ys_empty: \<open>zmset (map snd (filter (\<lambda>(l', _, _). l = l') ys)) = {#}\<^sub>z\<close>
          by (rule CM_equiv_empty_filter_notin[OF False])
        show ?thesis
          using xs_empty ys_empty ys_zs by simp
      qed
    qed
  qed
  show ?thesis
    unfolding CM_equiv_def
    using step by blast
qed

lemma CM_equiv_append:
  assumes ac: "CM_equiv a c" and bd: "CM_equiv b d"
  shows "CM_equiv (a @ b) (c @ d)"
proof (unfold CM_equiv_def, intro ballI)
  fix l
  assume "l \<in> fst ` set (a @ b) \<union> fst ` set (c @ d)"
  let ?F = "\<lambda>xs. filter (\<lambda>(l', _, _). l = l') xs"
  have part_a: "zmset (map snd (?F a)) = zmset (map snd (?F c))"
  proof (cases "l \<in> fst ` set a \<union> fst ` set c")
    case True
    with ac show ?thesis unfolding CM_equiv_def by blast
  next
    case False
    hence "?F a = []" "?F c = []"
      by (force simp: filter_empty_conv image_iff split: prod.splits)+
    thus ?thesis by simp
  qed
  have part_b: "zmset (map snd (?F b)) = zmset (map snd (?F d))"
  proof (cases "l \<in> fst ` set b \<union> fst ` set d")
    case True
    with bd show ?thesis unfolding CM_equiv_def by blast
  next
    case False
    hence "?F b = []" "?F d = []"
      by (force simp: filter_empty_conv image_iff split: prod.splits)+
    thus ?thesis by simp
  qed
  show "zmset (map snd (?F (a @ b))) = zmset (map snd (?F (c @ d)))"
    by (simp add: part_a part_b)
qed

lemma filter_extract_progress_outside:
  assumes "node l \<noteq> nid"
  shows "filter (\<lambda>(l', _, _). l = l') (extract_progress nid nt st) =
    List.map_filter
      (\<lambda>(p, t, m). case nt (nid, p) of None \<Rightarrow> None
         | Some (nid', p') \<Rightarrow>
             if l = Loc nid' (Trg p') then Some (Loc nid' (Trg p'), t, m) else None)
      (prod st)"
proof -
  have cons_empty:
    "filter (\<lambda>(l', _, _). l = l')
       (map (\<lambda>(p, t, m). (Loc nid (Trg p), t, -m)) xs) = []" for xs
    by (induct xs) (use assms in \<open>auto split: prod.splits\<close>)
  have inte_empty:
    "filter (\<lambda>(l', _, _). l = l')
       (map (\<lambda>(p, y). (Loc nid (Src p), y)) xs) = []" for xs
    by (induct xs) (use assms in \<open>auto split: prod.splits\<close>)
  have prod_eq:
    "filter (\<lambda>(l', _, _). l = l')
       (List.map_filter
          (\<lambda>(p, t, m). case_option None (\<lambda>(nid', p'). Some (Loc nid' (Trg p'), t, m))
                          (nt (nid, p)))
          xs)
     = List.map_filter
        (\<lambda>(p, t, m). case nt (nid, p) of None \<Rightarrow> None
           | Some (nid', p') \<Rightarrow>
               if l = Loc nid' (Trg p') then Some (Loc nid' (Trg p'), t, m) else None)
        xs" for xs
    by (induct xs) (auto simp: List.map_filter_def split: option.splits prod.splits)
  show ?thesis
    unfolding extract_progress_def
    by (simp add: cons_empty inte_empty prod_eq)
qed

lemma filter_extract_progress_Trg:
  shows "filter (\<lambda>(l', _, _). Loc nid (Trg p) = l') (extract_progress nid' nt st) =
    (if nid = nid' then
       map (\<lambda>(p', t, m). (Loc nid (Trg p), t, -m))
         (filter (\<lambda>(p', _, _). p' = p) (cons st))
     else []) @
    List.map_filter (\<lambda>(p_in, t, m).
      case nt (nid', p_in) of None \<Rightarrow> None
      | Some (nid'', p''') \<Rightarrow>
          if nid = nid'' \<and> p = p''' then Some (Loc nid (Trg p), t, m) else None)
    (prod st)"
proof -
  have cons_simp:
    "filter (\<lambda>(l', _, _). Loc nid (Trg p) = l')
       (map (\<lambda>(p'', t, m). (Loc nid' (Trg p''), t, -m)) xs) =
     (if nid = nid' then
        map (\<lambda>(p'', t, m). (Loc nid (Trg p), t, -m))
          (filter (\<lambda>(p'', _, _). p'' = p) xs)
      else [])" for xs
    by (induct xs) (auto split: prod.splits cong: if_cong)
  have inter_empty:
    "filter (\<lambda>(l', _, _). Loc nid (Trg p) = l')
       (map (\<lambda>(p'', y). (Loc nid' (Src p''), y)) xs) = []" for xs
    by (induct xs) (auto split: prod.splits)
  have prod_simp:
    "filter (\<lambda>(l', _, _). Loc nid (Trg p) = l')
       (List.map_filter (\<lambda>(p_in, t, m). case_option None (\<lambda>(nid'', p''').
          Some (Loc nid'' (Trg p'''), t, m)) (nt (nid', p_in))) xs) =
     List.map_filter (\<lambda>(p_in, t, m).
       case nt (nid', p_in) of None \<Rightarrow> None
       | Some (nid'', p''') \<Rightarrow>
           if nid = nid'' \<and> p = p''' then Some (Loc nid (Trg p), t, m) else None)
     xs" for xs
    by (induct xs) (auto simp: List.map_filter_def split: option.splits prod.splits)
  show ?thesis
    unfolding extract_progress_def
    by (simp add: cons_simp inter_empty prod_simp split_beta)
qed

lemma filter_extract_progress_Src:
  shows "filter (\<lambda>(l', _, _). Loc nid (Src p) = l') (extract_progress nid' nt st) =
    (if nid = nid' then
      map (\<lambda>(p', y). (Loc nid (Src p), y))
        (filter (\<lambda>(p', _). p' = p) (inte st))
    else [])"
proof -
  have cons_empty:
    "filter (\<lambda>(l', _, _). Loc nid (Src p) = l')
       (map (\<lambda>(p'', t, m). (Loc nid' (Trg p''), t, -m)) xs) = []" for xs
    by (induct xs) (auto split: prod.splits)
  have inter_simp:
    "filter (\<lambda>(l', _, _). Loc nid (Src p) = l')
       (map (\<lambda>(p'', y). (Loc nid' (Src p''), y)) xs) =
     (if nid = nid' then
        map (\<lambda>(p'', y). (Loc nid (Src p), y))
          (filter (\<lambda>(p'', _). p'' = p) xs)
      else [])" for xs
    by (induct xs) (auto split: prod.splits cong: if_cong)
  have prod_empty:
    "filter (\<lambda>(l', _, _). Loc nid (Src p) = l')
       (List.map_filter (\<lambda>(p'', t, m). case_option None (\<lambda>(nid'', p'''). 
          Some (Loc nid'' (Trg p'''), t, m)) (nt (nid', p''))) xs) = []" for xs
    by (induct xs) (auto simp: List.map_filter_def split: option.splits prod.splits)
  show ?thesis
    unfolding extract_progress_def
    by (simp add: cons_empty inter_simp prod_empty split_beta)
qed
end
