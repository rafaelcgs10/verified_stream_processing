theory Consumes

imports
  General
  Dataplane.Timely_Stream
  Dataplane.MyProduct_Instances
  Dataplane.AntichainOrder
begin

declare cin.rep_eq[simp del]
declare enum_class.enum_UNIV[simp] enum_class.enum_distinct[simp]


lemma zmset_map_filter_Trg_extract_prog:
  "zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_prog Enum.enum (nxt sg) os))) = 
   (\<Sum>x\<in>UNIV. zmset (List.map_filter (\<lambda> (p', t, d). case_option None (\<lambda> (nid'', p''). if nid'' = nid \<and> p'' = p then Some (t, d) else None) (nxt sg (x, p'))) (produ (os x))))
     - zmset (map snd (filter (((=) (p :: 'p :: enum)) o fst) (consu (os nid)))) "
  unfolding extract_prog_def extract_progress_def obtain_progress_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits if_splits option.splits)
  apply (subst (1) monoid_add_class.sum_list_distinct_conv_sum_set)
   apply (clarsimp simp add: sum_subtractf uminus_add_conv_diff_mset split_beta filter_map map_filter_def comp_def sum_diff comm_monoid_add_class.sum.distrib enum_class.enum_distinct enum_class.enum_UNIV split: prod.splits if_splits option.splits)+
  apply (subst sum_subtractf_zmultiset)
   apply simp_all
  apply (rule arg_cong2[where f="(-)"])
   apply simp_all
  apply (rule sum.cong)
   apply simp_all
  subgoal for pp
    apply (rule arg_cong[where f="zmset"])
    apply (rule map_cong)
     apply (rule filter_cong)
      apply auto
    done
  done

lemma filter_loc_Trg_extract_prof_consumes_diff_nids[simp]:
  "nid \<noteq> nid' \<Longrightarrow>
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog Enum.enum (edges sg) (os(nid := consumes (os nid) p t d))) =
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog Enum.enum (edges sg) os)"
  unfolding extract_prog_def extract_progress_def obtain_progress_def consumes_def add_caps_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
  apply (rule arg_cong[where f=concat])
  apply (rule map_cong)
   apply auto
  done

lemma filter_loc_extract_prof_consumes_diff_ports[simp]:
  "p \<noteq> p' \<Longrightarrow>
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog Enum.enum (edges sg) (os(nid := consumes (os nid) p t d))) =
   filter (\<lambda>(l', t, d). Loc nid' (Trg p') = l') (extract_prog Enum.enum (edges sg) os)"
  unfolding extract_prog_def extract_progress_def obtain_progress_def consumes_def add_caps_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
  apply (rule arg_cong[where f=concat])
  apply (rule map_cong)
   apply auto
  done

lemma zmset_map_filter_Src_extract_prog[simp]:
  "distinct xs \<Longrightarrow>
   nid \<in> set xs \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p) = l') (extract_prog xs (edges sg) os))) = 
   zmset (map snd (filter (((=) (p :: 'p :: enum)) o fst) (inter (os nid)))) "
  unfolding extract_prog_def extract_progress_def obtain_progress_def consumes_def add_caps_def
  apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
  apply (subst conj.commute)
  apply (simp add: List.map_filter_def sum.distrib sum_list_distinct_conv_sum_set flip: filter_filter split: option.splits)+
  done

lemma set_extract_prog_consumesD:
  "(l, t', m) \<in> set (extract_prog Enum.enum (edges sg) (os(nid := consumes (os nid) p t d))) \<Longrightarrow>
   (l, t', m) \<in> set (extract_prog Enum.enum (edges sg) os) \<or>
   (l = Loc nid (Trg p) \<and> t = t' \<and> m = -1) \<or>
   (\<exists> p' t''. t'' \<in> set (intsum (os nid) p p') \<and> l = Loc nid (Src p') \<and> t' = t + t'' \<and> m = 1)"
  unfolding extract_prog_def obtain_progress_def consumes_def extract_progress_def add_caps_def
  apply (auto del: disjCI simp add: List.map_filter_def image_iff split_beta if_distrib split: option.splits prod.splits if_splits)
       apply fastforce
      apply fastforce
     apply (metis Pair_inject the_default.simps(1))
    apply fastforce
   apply fastforce
  apply (metis Pair_inject the_default.simps(1))
  done

lemma data_in_channel_justifies_c_pts:
  "Trg_caps_inv caps chnls \<Longrightarrow>
   c_pts_inv (change_multiplicities su (extract_prog Enum.enum ed os) c) caps \<Longrightarrow> 
   t \<in> snd ` set (chnls (nid, p)) \<Longrightarrow>
   (\<forall> n. \<forall> (p, t, m) \<in> set (produ (os n)). m \<ge> 0) \<Longrightarrow>
   (\<forall> n. \<forall> (p, t, m) \<in> set (consu (os n)). m \<ge> 0) \<Longrightarrow>
   zcount (c_pts c (Loc nid (Trg p))) t > 0 \<or> (\<exists> nid' p'. zcount (zmset (map snd ((filter ((=) p' o fst)) (produ (os nid'))))) t > 0 \<and> (ed (nid', p') = Some (nid, p)))"
  unfolding Trg_caps_inv_def
  apply (drule spec[of _ nid])
  apply (drule spec[of _ p])
  unfolding c_pts_inv_def
  apply (drule spec[of _ "Loc nid (Trg p)"])
  apply (simp add: c_pts_change_multiplicities)
  subgoal premises prems3
    using prems3(1,5) apply -
    unfolding extract_prog_def obtain_progress_def extract_progress_def
    apply (simp add:  BULK_BENQ_def zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
    apply (subst (asm) (1) monoid_add_class.sum_list_distinct_conv_sum_set)
     apply (simp_all add: enum_distinct enum_UNIV)
    apply (subst (asm) Groups.ab_group_add_class.ab_diff_conv_add_uminus)
    apply (subst (asm) comm_monoid_add_class.sum.distrib)
    apply (simp add: zmultiset_eq_iff)
    apply (drule spec[of _ t])+
    apply (simp add: zcount_sum)
    apply (subgoal_tac "zcount (to_zmset (map snd (chnls (nid, p)))) t > 0")
    subgoal
      apply (drule sym)
      apply simp
      apply (drule int_sum_minus_cases[where n="zcount (c_pts c (Loc nid (Trg p))) t" and
            m="(\<Sum>x\<in>UNIV. zcount (zmset (List.map_filter (\<lambda> (p', t, d). case_option None (\<lambda> (nid'', p''). if nid'' = nid \<and> p'' = p then Some (t, d) else None) (ed (x, p'))) (produ (os x)))) t)" and p="zcount (zmset (map snd (filter (\<lambda>x. p = fst x) (consu (os nid))))) t"])
      subgoal
        apply (clarsimp simp add: map_concat filter_concat filter_map comp_def List.map_filter_def split_beta split: if_splits prod.splits option.splits)
        apply (rule sum.cong)
         apply simp_all
        apply (rule arg_cong2[where f=zcount])
         apply simp_all
        apply (rule arg_cong[where f=zmset])
        apply (rule map_cong)
         apply simp_all
         apply (rule filter_cong)
          apply auto
        done
       apply (rule zcount_zmset_ge_0I)
       apply simp
      using prems3(3) apply blast
      apply (elim disjE)
       apply simp
      apply (rule disjI2)
      apply (drule sum_pos_ex_elem_pos)
      apply (clarsimp simp add: List.map_filter_def comp_def)+
      apply (drule zcount_zmset_gt_0_set_Ex)
      apply (clarsimp split: prod.splits)
      subgoal for _ nid' _ p' x m
        apply (rule exI[of _ nid'])
        apply (rule exI[of _ p'])
        apply (auto simp add: map_filter_map_filter)
         apply (rule zcount_zmset_gt_0I)
           apply (auto simp flip: map_filter_map_filter)
        using prems3(2) apply auto[1]
         apply (rule image_eqI[rotated])
          apply clarsimp
          apply fastforce
         apply (auto simp add: map_replicate_const split: prod.splits option.splits if_splits)
        done
      done
    subgoal
      apply (auto simp add: zcount_to_zmset)
      done
    done
  done


lemma set_extract_progressD:
  "(l, t, m) \<in> set (extract_progress nid ed (snd (obtain_progress (consumes (os nid) p t' d)))) \<Longrightarrow>
   (l, t, m) \<in> set (extract_progress nid ed (snd (obtain_progress (os nid)))) \<or> 
   (\<exists> m'. l = Loc nid (Trg p) \<and> m = -1 \<and> t = t') \<or>
   (\<exists> p' s. l = Loc nid (Src p') \<and> m = 1 \<and> t = t' + s \<and> s \<in> set (intsum (os nid) p p'))"
  unfolding extract_progress_def obtain_progress_def
  apply (auto simp add: split_beta image_iff enum_class.enum_UNIV)
  done

lemma zmset_filter_extract_progress_Trg_consumes_alt:
  "zmset (map snd (filter (\<lambda>(l, _, _). Loc nid (Trg p) = l) (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))))) = 
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid (Trg p) = l) (extract_progress nid nt (snd (obtain_progress (os nid)))))) - {# t #}\<^sub>z"
  unfolding extract_progress_def obtain_progress_def
  apply simp
  apply (metis update_zmultiset_one(1))
  done
lemma zmset_filter_extract_progress_Trg_consumes_diff_p:
  "p \<noteq> p' \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid (Trg p') = l) (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))))) = 
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid (Trg p') = l) (extract_progress nid nt (snd (obtain_progress (os nid))))))"
  unfolding extract_progress_def obtain_progress_def
  apply simp
  done
lemma zmset_filter_extract_progress_Trg_consumes_diff_nid:
  "nid \<noteq> nid' \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid' (Trg p') = l) (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))))) = 
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid' (Trg p') = l) (extract_progress nid nt (snd (obtain_progress (os nid))))))"
  unfolding extract_progress_def obtain_progress_def
  apply simp
  done
lemma zmset_filter_extract_progress_Trg_consumes_diff:
  "nid' = nid \<longrightarrow> p' \<noteq> p \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid' (Trg p') = l) (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))))) = 
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid' (Trg p') = l) (extract_progress nid nt (snd (obtain_progress (os nid))))))"
  unfolding extract_progress_def obtain_progress_def
  apply auto
  done
lemma zmset_filter_extract_progress_Src_consumes:
  "zmset (map snd (filter (\<lambda>(l, _, _). Loc nid (Src p') = l) (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))))) = 
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid (Src p') = l) (extract_progress nid nt (snd (obtain_progress (os nid)))))) + to_zmset (map ((-+-) t) (intsum (os nid) p p'))"
  by (clarsimp simp add: extract_progress_def obtain_progress_def filter_concat filter_map map_concat comp_def zmset_concat)
lemma zmset_filter_extract_progress_Src_consumes_no_intsum:
  "nid' = nid \<longrightarrow> intsum (os nid) p p' = [] \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l', t, d). Loc nid' (Src p') = l') (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))))) = 
   zmset (map snd (filter (\<lambda>(l', t, d). Loc nid' (Src p') = l') (extract_progress nid nt (snd (obtain_progress (os nid))))))"
  apply (clarsimp simp add: monoid_add_class.sum_list_distinct_conv_sum_set extract_progress_def obtain_progress_def filter_concat filter_map map_concat comp_def zmset_concat)
  apply (smt (verit) filter.simps(1) filter_empty_conv list.map(1) sum.neutral to_zmset.simps(1))
  done

lemma zmset_filter_extract_progress_Src_consumes_diff:
  "nid' \<noteq> nid \<Longrightarrow>
   zmset (map snd (filter (\<lambda>(l, _, _). Loc nid' (Src p') = l) (extract_progress nid nt oss))) = 
   {#}\<^sub>z"
  by (clarsimp simp add: List.map_filter_def split_beta extract_progress_def obtain_progress_def filter_concat filter_map map_concat comp_def zmset_concat split: option.splits)

lemma zmset_filter_Trg_not_nid:
  "(\<Sum>x\<in>UNIV - {nid}. zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_progress x nt (snd (obtain_progress (os x))))))) =
   (\<Sum>x\<in>UNIV - {nid}. zmset (List.map_filter (\<lambda>(p', t, d). case nt (x, p') of None \<Rightarrow> None | Some (nid'', p'') \<Rightarrow> if nid'' = nid \<and> p'' = p then Some (t, d) else None) (produ (os x))))"
  apply (clarsimp simp add: extract_progress_def List.map_filter_def obtain_progress_def filter_concat filter_map map_concat comp_def zmset_concat split: prod.splits if_splits option.splits)
  apply (rule sum.cong)
   apply simp
  apply (clarsimp simp add: extract_progress_def split_beta obtain_progress_def filter_concat filter_map map_concat comp_def zmset_concat split: prod.splits if_splits option.splits)
  apply (rule arg_cong[where f=zmset])
  apply (rule map_cong)
   apply (rule filter_cong)
    apply (auto simp add: extract_progress_def split_beta obtain_progress_def filter_concat filter_map map_concat comp_def zmset_concat split: prod.splits if_splits option.splits)
       apply (metis not_Some_eq2 option.sel option.simps(3))+
  done

lemma extract_prog_append[simp]:
  "extract_prog (xs @ ys) nt os = extract_prog xs nt os @ extract_prog ys nt os"
  unfolding extract_prog_def by auto
lemma extract_prog_Cons[simp]:
  "extract_prog (x#xs) nt os = extract_progress x nt (snd (obtain_progress (os x))) @ extract_prog xs nt os"
  unfolding extract_prog_def by auto
lemma extract_prog_skip_update[simp]:
  "nid \<notin> set xs \<Longrightarrow>
   extract_prog xs nt (os(nid := A)) = extract_prog xs nt os"
  unfolding extract_prog_def
  apply (induct xs)
   apply auto
  done
lemma extract_prog_empty[simp]:
  "extract_prog [] nt os = []"
  unfolding extract_prog_def by auto

lemma t_in_buf_cases:
  "cbufs (nid, p) = (d, t) # xs \<Longrightarrow>
   Trg_caps_inv caps (outputs_at_target su os >> cbufs) \<Longrightarrow>
   c_pts_inv (change_multiplicities su (extract_prog enum_class.enum nt os) c) caps \<Longrightarrow>
   0 < zcount (c_pts c (Loc nid (Trg p)) + zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_progress nid nt (snd (obtain_progress (os nid))))))) t \<or>
   0 < zcount
         (\<Sum>x\<in>UNIV - {nid}.
            zmset (List.map_filter (\<lambda>(p', t, d). case nt (x, p') of None \<Rightarrow> None | Some (nid'', p'') \<Rightarrow> if nid'' = nid \<and> p'' = p then Some (t, d) else None) (produ (os x))))
         t"
  unfolding Trg_caps_inv_def
  apply (drule spec[of _ nid])
  apply (drule spec[of _ p])
  unfolding c_pts_inv_def
  apply (drule spec[of _ "Loc nid (Trg p)"])
  apply (simp add: c_pts_change_multiplicities extract_prog_def filter_concat comp_def map_concat zmset_concat sum_list_distinct_conv_sum_set)
  apply (subst (asm) comm_monoid_add_class.sum.subset_diff[of "{nid}"])
    apply simp_all
  unfolding zmultiset_eq_iff
  apply (drule spec[of _ t])+
  apply (subgoal_tac  "zcount
       (c_pts c (Loc nid (Trg p)) +
        ((\<Sum>x\<in>UNIV - {nid}. zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_progress x nt (snd (obtain_progress (os x))))))) +
         zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_progress nid nt (snd (obtain_progress (os nid))))))))
       t > 0")
  subgoal premises prems3
    using prems3(4) 
    by (auto simp add: zmset_filter_Trg_not_nid)
  subgoal
    unfolding outputs_at_target_def BULK_BENQ_def
    apply (auto simp add: to_zmset_nenneg split: option.splits prod.splits)
    done
  done



lemma frontier_less_equal_sumI_alt:
  "finite S \<Longrightarrow>
   frontier_less_equal (frontier (sum f S)) t \<Longrightarrow>
   (\<forall> x\<in>S. frontier_less_equal (frontier (f x)) t \<longrightarrow> (\<exists> x'. frontier_less_equal (frontier (f' x)) t) ) \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (f l) t \<ge> 0) \<Longrightarrow>
   (\<forall> l \<in> S. \<forall> t. zcount (f' l) t \<ge> 0) \<Longrightarrow>
   frontier_less_equal (frontier (sum f' S)) t"
  apply (drule frontier_less_equal_sumE)
   apply assumption
  apply clarsimp
  apply (rule frontier_less_equal_sumI)
     apply simp_all
  apply blast
  done

find_theorems graph.path_weight name: trans name: Graph

find_consts "_ zmultiset" name: filter

term frontier

lemma frontier_filter_pos:
  "frontier M = frontier (filter_zmset (\<lambda> t. zcount M t > 0) M)"
  apply transfer'
  apply (auto simp add: minimal_antichain_def)
  done

lemma pos_zcount_image_zmset_inj: 
  "0 < zcount M t \<Longrightarrow>inj f \<Longrightarrow>  0 < zcount (image_zmset f M) (f t)"
  apply transfer
  subgoal for M t f
    apply (induct M)
    subgoal for Mp Mn
      apply simp
      apply (metis basic_trans_rules(22) count_image_mset_ge_count count_image_mset_inj)
      done
    done
  done

lemma in_frontier_zmset_imageD:
  "t \<in>\<^sub>A frontier {#t -+- s. t \<in>#\<^sub>z M#} \<Longrightarrow> (\<exists> t'. t = t' -+- s \<and> t' \<in>\<^sub>A frontier M)"
  apply transfer'
  apply (auto simp add: zcount_sum minimal_antichain_def)
  subgoal for t s M
    apply (drule zcount_zimageD)
    apply clarsimp
    subgoal for t'' t'
      apply (drule spec[of _ "t' -+- s"])
      apply (drule mp)
       apply (rule pos_zcount_image_zmset_inj)
        apply auto
      done
    done
  done

lemma frontier_less_equal_image_zmsetD:
  "frontier_less_equal (frontier {#t -+- s. t \<in>#\<^sub>z A#}) t \<Longrightarrow>
   \<exists> t'. frontier_less_equal (frontier A) t' \<and>t' -+- s \<le> t"
  unfolding frontier_less_equal_iff2
  apply clarsimp
  apply (drule in_frontier_zmset_imageD)
  apply auto
  done

lemma change_multiplicities_extract_progress_consumes:
  "change_multiplicities su (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))) =
   change_multiplicities su (extract_progress nid nt (snd (obtain_progress (os nid))) @ [(Loc nid (Trg p), t, -1)] @ concat (map (\<lambda> p'. map (\<lambda> t'. (Loc nid (Src p'),  (t -+- t'), 1)) (intsum (os nid) p p')) enum_class.enum))"
  unfolding extract_progress_def consumes_def obtain_progress_def
  apply (simp add: comp_def map_concat)
  apply (rule ext)
  subgoal for c
    using change_multiplicities_comm 
    by (smt (verit, ccfv_SIG) change_multiplicities_append_alt change_multiplicities_simp_alt)
  done

lemma change_multiplicities_extract_prog_consumes:
  "nid \<in> set xs \<Longrightarrow>
   distinct xs \<Longrightarrow>
   change_multiplicities su (extract_prog xs nt (os(nid := consumes (os nid) p t d))) =
   change_multiplicities su (extract_prog xs nt os @ [(Loc nid (Trg p), t, -1)]@ concat (map (\<lambda> p'. map (\<lambda> t'. (Loc nid (Src p'),  (t -+- t'), 1)) (intsum (os nid) p p')) enum_class.enum))"
   apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append)
    apply assumption+
  apply (simp add: change_multiplicities_append flip: change_multiplicities_append)
  apply (rule ext)
  apply (subst change_multiplicities_comm)
  apply (subst change_multiplicities_comm change_multiplicities_append)
  apply (subst change_multiplicities_comm)
  apply (simp add: change_multiplicities_append change_multiplicities_extract_progress_consumes)
  apply (smt (verit, best) change_multiplicities_append change_multiplicities_comm change_multiplicities_extract_prog_obtain_progress_remove1_append)
  done

lemma frontier_less_equal_trans_subset:
  "frontier_less_equal (frontier N) t' \<Longrightarrow>
   t' \<le> t \<Longrightarrow>
   N \<subseteq>#\<^sub>z M \<Longrightarrow>
   frontier_less_equal (frontier M) t"
  using frontier_less_equal_le_trans frontier_less_equal_trans frontier_lt_subseq by blast

lemma filter_Trg_extract_prog_produ:
  "distinct xs \<Longrightarrow>
   inj_on nt (dom nt) \<Longrightarrow>
   nid \<notin> set xs \<Longrightarrow>
   nid' \<in> set xs \<Longrightarrow>
   nt (nid', p') = Some (nid , p) \<Longrightarrow>
   filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_prog xs nt os) =
   map (\<lambda> (p'', t, m). (Loc nid (Trg p), t, m)) (filter (\<lambda> (p'', _, _). p'' = p') (produ (os nid')))"
  unfolding extract_prog_def obtain_progress_def extract_progress_def
  apply (clarsimp simp add: List.map_filter_def map_concat filter_concat comp_def filter_map split_beta split: option.splits)
  apply (induct xs rule: rev_induct)
   apply (auto simp add: List.map_filter_def map_concat filter_concat comp_def filter_map split_beta split: option.splits)
  subgoal for xs'
    apply (subst HOL.iffD2[OF concat_eq_Nil_conv])
    subgoal
      apply (auto simp add: filter_empty_conv)
      apply (metis Pair_inject domI inj_on_eq_iff not_Some_eq2)
      done
    apply simp
    apply (rule map_cong)
    subgoal
      apply (rule filter_cong)
       apply auto
      apply (metis domI inj_onD prod.inject)
      done
    apply auto
    done
  subgoal
    apply (auto simp add: filter_empty_conv)
    apply (metis (no_types, opaque_lifting) Pair_inject domIff inj_on_contraD not_Some_eq2)
    done
  done

lemma filter_Trg_extract_prog_produ_empty:
  "distinct xs \<Longrightarrow>
   inj_on nt (dom nt) \<Longrightarrow>
   nid \<notin> set xs \<Longrightarrow>
   nid \<notin> fst ` (ran nt) \<Longrightarrow>
   filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_prog xs nt os) = []"
  unfolding extract_prog_def obtain_progress_def extract_progress_def
  apply (auto simp add: filter_empty_conv List.map_filter_def map_concat filter_concat comp_def filter_map split_beta split: option.splits)
  apply (metis img_fst ranI)
  done

lemma in_frontier_c_pts_change_multiplicities_consumes_Trg:
  "ft \<in>\<^sub>A frontier (c_pts (change_multiplicities su (extract_progress nid nt (snd (obtain_progress (os nid)))) c) (Loc nid (Trg p))) \<Longrightarrow>
   t \<noteq> ft \<Longrightarrow>
   ft \<in>\<^sub>A frontier (c_pts (change_multiplicities su (extract_progress nid nt (snd (obtain_progress (consumes (os nid) p t d)))) c) (Loc nid (Trg p)))"
  apply (simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
  apply (smt (verit, best) Groups.add_ac(2,3) add_diff_cancel diff_add_cancel in_frontier_minusI)
  done

lemma
  assumes D: "dataflow_topology su (-+-)"
    and C: "cbufs (nid, p) = (d, t) # cbufs'"
    and S: "Src_caps_inv caps os"
    and T: "Trg_caps_inv caps (outputs_at_target su os >> cbufs)"
    and P: "c_pts_inv (change_multiplicities su (extract_prog enum_class.enum nt os) c) caps"
    and CA: "change_deltas_inv os"
    and G: "graph_summar_nt su nt os"
    and PR: "produ_supported su os c"
    and E: "extract_prog_changes_above_impl_inv su nt c os"
  shows 
    "extract_prog_changes_above_impl_inv su nt c (os(nid := consumes (os nid) p t d))"
  using C PR P T G CA apply -
  unfolding extract_prog_changes_above_impl_inv_def
  apply (auto 0 0)
  defer
  subgoal for nid' xs
    unfolding changes_above_impl_inv_def
    apply safe
    subgoal for l t' m
      apply (cases "nid \<in> set xs"; simp?)
       apply (cases "\<exists> s p'' t''. t'' \<in> set (intsum (os nid) p p'') \<and> s \<in>\<^sub>A graph.path_weight su (Loc nid (Src p'')) l \<and> t -+- t'' -+- s \<le> t'")
      subgoal
        apply clarsimp
        subgoal for s p'' t''
          apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, of s _ _ _ "t -+- t''"])
            apply assumption
          subgoal
            apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc nid (Src p'')", simplified, OF D])
            subgoal
              apply (rule graph.path_weight_refl)
              apply (rule dataflow_topology.axioms(1))
              using D apply assumption
              done
            subgoal
              subgoal
                using S apply -
                unfolding Src_caps_inv_def
                apply (drule spec[of _ nid])
                apply (drule spec[of _ p''])
                unfolding c_pts_inv_def
                apply (drule spec[of _ "Loc nid (Src p'')"])
                apply simp
                unfolding zmultiset_eq_iff
                apply (drule spec[of _ "t -+- t''"])+
                apply (simp add: c_pts_change_multiplicities)
                apply (subgoal_tac "zcount (c_pts c (Loc nid (Src p'')) + zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Src p'') = l') (extract_prog xs nt (os(nid := consumes (os nid) p t d)))))) (t -+- t'') > 0")
                subgoal
                  using frontier_less_equal_zcount_pos 
                  by force
                subgoal
                  apply simp
                  apply (subst zmset_map_filter_Src_extract_prog)
                    apply simp_all
                  apply (subst (asm) zmset_map_filter_Src_extract_prog)
                    apply (simp_all flip: add.assoc)
                  apply (subgoal_tac "zcount (zmset (map snd (filter ((=) p'' \<circ> fst) (concat (map (\<lambda>p'. map (\<lambda>t'. (p', t -+- t', 1)) (intsum (os nid) p p')) enum_class.enum))))) (t -+- t'') > 0")
                  subgoal
                    by (meson add_strict_increasing2 to_zmset_nenneg)
                  subgoal
                    apply (rule zcount_zmset_gt_0I)
                      apply (auto simp add: image_iff)
                    done
                  done
                done
              done
            done
          subgoal
            by fast
          done
        done
      subgoal
        using E[unfolded extract_prog_changes_above_impl_inv_def, rule_format, of "xs" nid', unfolded changes_above_impl_inv_def] apply -
        apply simp
        apply (drule bspec)
         apply assumption
        apply simp
        apply (subst (asm) extract_progress_def)
        apply (subst (asm) (1 2 3) obtain_progress_def)
        apply (clarsimp simp add: image_iff Misc.set_map_filter split: option.splits; hypsubst_thin?)
        subgoal for p' m
          apply (subst (asm) Propagate.dataflow_topology.implied_frontier_alt_def[OF D])
          apply (subst (asm) Groups_Big.comm_monoid_add_class.sum.subset_diff[where B="(\<lambda> (nid, p). Loc nid (Src p)) ` ((set xs - {nid}) \<times> UNIV) \<union> (\<lambda> (nid, p). Loc nid (Trg p)) ` ((set xs - {nid}) \<times> UNIV)"])
            apply simp_all
           apply fast
          apply (drule frontier_less_equal_add_cases)
          apply (elim disjE)
          subgoal
            apply (subst (asm) frontier_less_equal_iff2)
            apply clarsimp
            subgoal for ft
              apply (drule in_frontier_sumEx)
                apply (simp_all add: zcount_sum image_iff split_beta)
              subgoal
                by (auto intro: ordered_comm_monoid_add_class.sum_nonneg)
              subgoal
                apply (elim conjE bexE)
                apply (drule in_frontier_sumEx)
                  apply (simp_all add: zcount_sum image_iff split_beta)
                apply clarsimp
                subgoal for l' s
                  apply (drule in_frontier_zmset_imageD)
                  apply clarsimp
                  subgoal for ft
                    apply hypsubst_thin
                    apply (elim disjE rangeE)
                    subgoal 
                      apply (clarsimp simp add: split: prod.splits)
                      subgoal for nid'' p''
                        apply hypsubst_thin
                        apply (cases "nid'' = nid \<and> p'' = p")
                        subgoal
                          apply clarsimp
                          apply (simp_all flip: member_antichain.rep_eq)
                          apply hypsubst_thin
                          apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                            apply simp_all
                          apply (subgoal_tac "\<exists> t p'' s'. t \<in> set (intsum (os nid) p p'') \<and> s' \<in>\<^sub>A graph.path_weight su (Loc nid (Src p'')) (Loc nid' (Trg p')) \<and> s = t -+- s'")
                           defer
                          subgoal
                            using G[unfolded graph_summar_nt_def]
                            by blast
                          subgoal
                            apply clarsimp
                            subgoal for t'' p'' s'
                              apply hypsubst_thin
                              apply (drule spec2, drule mp, assumption)
                              apply (drule spec, drule mp, assumption)
                              apply (subgoal_tac "ft \<noteq> t")
                               defer
                              subgoal
                                by (metis dataflow_topology_from_tree.followed_by_summary)
                              apply (simp add: change_multiplicities_comm change_multiplicities_append_alt)
                              apply (drule in_frontier_c_pts_change_multiplicities_consumes_Trg[where t=t and d=d]) 
                               apply simp
                              apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D])
                                apply assumption
                               apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid (Trg p)" _ _ ft])
                              subgoal
                                apply (rule graph.path_weight_refl)
                                apply (rule dataflow_topology.axioms(1)[OF D])
                                done
                              subgoal
                                apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                  apply simp_all
                                apply (metis (no_types, opaque_lifting) change_multiplicities_append change_multiplicities_comm frontier_less_equal_zcount_pos member_frontier_pos_zmset)
                                done
                              subgoal
                                by auto
                              done
                            done
                          done
                        subgoal
                          apply clarsimp
                          apply (simp_all flip: member_antichain.rep_eq)
                          apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D])
                            apply assumption
                           defer
                           apply assumption
                          apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid'' (Trg p'')" _ _ ft, simplified])
                          subgoal
                            apply (rule graph.path_weight_refl)
                            apply (rule dataflow_topology.axioms(1)[OF D])
                            done
                          subgoal
                            apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                            apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                            apply (simp add: zmset_filter_extract_progress_Trg_consumes_diff c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                            unfolding frontier_less_equal_iff2
                            apply (rule exI[of _ ft])
                            apply auto
                            done
                          done
                        done
                      done
                    subgoal
                      apply clarsimp
                      subgoal for nid'' p''
                        apply (cases "nid'' = nid \<and> (\<exists> t. t \<in> set (intsum (os nid) p p''))")
                        subgoal
                          apply clarsimp
                          subgoal for t''
                            apply hypsubst_thin
                            apply (simp_all flip: member_antichain.rep_eq)
                            apply (drule spec2, drule mp, assumption)
                            apply (drule spec, drule mp, assumption)
                            apply (subgoal_tac " ft \<noteq> t -+- t''")
                             defer
                            subgoal
                              by fast
                            apply (drule in_frontier_addEx[where B="to_zmset (map ((-+-) t) (intsum (os nid) p p''))"])
                            subgoal
                              using to_zmset_nenneg by fast
                            apply clarsimp
                            subgoal for ft'
                              apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, where s=s and t=ft'])
                                apply assumption
                               defer
                              subgoal
                                by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(23))
                              apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid (Src p'')" _ _ ft', simplified])
                              subgoal
                                apply (rule graph.path_weight_refl)
                                apply (rule dataflow_topology.axioms(1)[OF D])
                                done
                              subgoal
                                apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                  apply simp_all
                                apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                  apply simp_all
                                apply (simp add: zmset_filter_extract_progress_Src_consumes c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                                apply (smt (verit, ccfv_SIG) Groups.add_ac(2) frontier_less_equal_zcount_pos group_cancel.add2 member_frontier_pos_zmset)
                                done
                              done
                            done
                          done
                        subgoal
                          apply (clarsimp simp flip: member_antichain.rep_eq)
                          apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, where s=s and t=ft])
                            apply assumption
                           defer
                           apply assumption
                          apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid'' (Src p'')" _ _ ft, simplified])
                          subgoal
                            apply (rule graph.path_weight_refl)
                            apply (rule dataflow_topology.axioms(1)[OF D])
                            done
                          subgoal
                            apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                            apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                            apply (simp add: zmset_filter_extract_progress_Src_consumes_no_intsum c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                            apply (meson frontier_less_equal_zcount_pos member_frontier_pos_zmset)
                            done
                          done
                        done
                      done
                    done
                  done
                done
              done
            done
          subgoal
            apply (subst Propagate.dataflow_topology.implied_frontier_alt_def[OF D])
            apply (subst Groups_Big.comm_monoid_add_class.sum.subset_diff[where B="(\<lambda> (nid, p). Loc nid (Src p)) ` ((set xs - {nid}) \<times> UNIV) \<union> (\<lambda> (nid, p). Loc nid (Trg p)) ` ((set xs - {nid}) \<times> UNIV)"])
              apply simp_all
             apply fast
            apply (rule frontier_less_equal_addI)
            subgoal
              apply (rule disjI2)
              apply (subst (asm) frontier_less_equal_iff2)
              apply clarsimp
              subgoal for ft
                apply (drule in_frontier_sumEx)
                  apply (simp_all add: zcount_sum image_iff split_beta)
                subgoal
                  by (auto intro: ordered_comm_monoid_add_class.sum_nonneg)
                subgoal
                  apply clarsimp
                  subgoal for l'
                    apply (drule in_frontier_sumEx)
                      apply (simp_all add: zcount_sum image_iff split_beta)
                    apply clarsimp
                    subgoal for s
                      apply (drule in_frontier_zmset_imageD)
                      apply clarsimp
                      subgoal for ft
                        apply hypsubst_thin
                        apply (rule frontier_less_equal_sumI[where l=l'])
                           apply simp
                        subgoal
                          by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
                        subgoal
                          by (clarsimp simp add: zcount_sum image_iff split_beta)
                        subgoal
                          apply (rule frontier_less_equal_sumI[where l=s])
                             apply simp_all
                          unfolding frontier_less_equal_iff2
                          apply (subst in_frontier_zmset_image)
                           apply simp_all
                          apply (subst change_multiplicities_extract_prog_consumes)
                            apply simp_all
                          apply (clarsimp simp add: c_pts_change_multiplicities)
                          apply (cases "l' = Loc nid (Trg p)"; simp)
                          apply (drule in_frontier_in_frontier_add[where t=ft and B="zmset (map snd (filter (\<lambda>(l'a, t, d). l' = l'a) (concat (map (\<lambda>p'. map (\<lambda>t'. (Loc nid (Src p'), t -+- t', 1)) (intsum (os nid) p p')) enum_class.enum))))"])
                          subgoal
                            by (clarsimp simp add: zcount_sum image_iff split_beta intro!: zcount_zmset_ge_0I)
                          apply clarsimp
                          subgoal for ft3
                            apply (rule exI[of _ "ft3 -+- s"])
                            apply simp
                            apply (intro conjI)
                             apply (metis (no_types, lifting) nat_arith.add1)
                            apply (meson assms(1) basic_trans_rules(23) dataflow_topology.results_in_mono(1)) 
                            done
                          done
                        done
                      done
                    done
                  done
                done
              done
            subgoal
              by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
            subgoal
              by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
            done
          done
        subgoal  for p'
          apply (subst (asm) Propagate.dataflow_topology.implied_frontier_alt_def[OF D])
          apply (subst (asm) Groups_Big.comm_monoid_add_class.sum.subset_diff[where B="(\<lambda> (nid, p). Loc nid (Src p)) ` ((set xs - {nid}) \<times> UNIV) \<union> (\<lambda> (nid, p). Loc nid (Trg p)) ` ((set xs - {nid}) \<times> UNIV)"])
            apply simp_all
           apply fast
          apply (drule frontier_less_equal_add_cases)
          apply (elim disjE)
          subgoal
            apply (subst (asm) frontier_less_equal_iff2)
            apply clarsimp
            subgoal for ft
              apply (drule in_frontier_sumEx)
                apply (simp_all add: zcount_sum image_iff split_beta)
              subgoal
                by (auto intro: ordered_comm_monoid_add_class.sum_nonneg)
              subgoal
                apply (elim conjE bexE)
                apply (drule in_frontier_sumEx)
                  apply (simp_all add: zcount_sum image_iff split_beta)
                apply clarsimp
                subgoal for l' s
                  apply (drule in_frontier_zmset_imageD)
                  apply clarsimp
                  subgoal for ft
                    apply hypsubst_thin
                    apply (elim disjE rangeE)
                    subgoal 
                      apply (clarsimp simp add: split: prod.splits)
                      subgoal for nid'' p''
                        apply hypsubst_thin
                        apply (cases "nid'' = nid \<and> p'' = p")
                        subgoal
                          apply clarsimp
                          apply (simp_all flip: member_antichain.rep_eq)
                          apply hypsubst_thin
                          apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                            apply simp_all
                          apply (subgoal_tac "\<exists> t p'' s'. t \<in> set (intsum (os nid) p p'') \<and> s' \<in>\<^sub>A graph.path_weight su (Loc nid (Src p'')) (Loc nid' (Src p')) \<and> s = t -+- s'")
                           defer
                          subgoal
                            using G[unfolded graph_summar_nt_def]
                            by blast
                          subgoal
                            apply clarsimp
                            subgoal for t'' p'' s'
                              apply hypsubst_thin
                              apply (drule spec2, drule mp, assumption)
                              apply (drule spec, drule mp, assumption)
                              apply (subgoal_tac "ft \<noteq> t")
                               defer
                              subgoal
                                by (metis dataflow_topology_from_tree.followed_by_summary)
                              apply (simp add: change_multiplicities_comm change_multiplicities_append_alt)
                              apply (drule in_frontier_c_pts_change_multiplicities_consumes_Trg[where t=t and d=d]) 
                               apply simp
                              apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D])
                                apply assumption
                               apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid (Trg p)" _ _ ft])
                              subgoal
                                apply (rule graph.path_weight_refl)
                                apply (rule dataflow_topology.axioms(1)[OF D])
                                done
                              subgoal
                                apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                  apply simp_all
                                apply (metis (no_types, opaque_lifting) change_multiplicities_append change_multiplicities_comm frontier_less_equal_zcount_pos member_frontier_pos_zmset)
                                done
                              subgoal
                                by auto
                              done
                            done
                          done
                        subgoal
                          apply clarsimp
                          apply (simp_all flip: member_antichain.rep_eq)
                          apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D])
                            apply assumption
                           defer
                           apply assumption
                          apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid'' (Trg p'')" _ _ ft, simplified])
                          subgoal
                            apply (rule graph.path_weight_refl)
                            apply (rule dataflow_topology.axioms(1)[OF D])
                            done
                          subgoal
                            apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                            apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                            apply (simp add: zmset_filter_extract_progress_Trg_consumes_diff c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                            unfolding frontier_less_equal_iff2
                            apply (rule exI[of _ ft])
                            apply auto
                            done
                          done
                        done
                      done


                    subgoal
                      apply clarsimp
                      subgoal for nid'' p''
                        apply (cases "nid'' = nid \<and> (\<exists> t. t \<in> set (intsum (os nid) p p''))")
                        subgoal
                          apply clarsimp
                          subgoal for t''
                            apply hypsubst_thin
                            apply (simp_all flip: member_antichain.rep_eq)
                            apply (drule spec2, drule mp, assumption)
                            apply (drule spec, drule mp, assumption)
                            apply (subgoal_tac " ft \<noteq> t -+- t''")
                             defer
                            subgoal
                              by fast
                            apply (drule in_frontier_addEx[where B="to_zmset (map ((-+-) t) (intsum (os nid) p p''))"])
                            subgoal
                              using to_zmset_nenneg by fast
                            apply clarsimp
                            subgoal for ft'
                              apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, where s=s and t=ft'])
                                apply assumption
                               defer
                              subgoal
                                by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(23))
                              apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid (Src p'')" _ _ ft', simplified])
                              subgoal
                                apply (rule graph.path_weight_refl)
                                apply (rule dataflow_topology.axioms(1)[OF D])
                                done
                              subgoal
                                apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                  apply simp_all
                                apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                  apply simp_all
                                apply (simp add: zmset_filter_extract_progress_Src_consumes c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                                apply (smt (verit, ccfv_SIG) Groups.add_ac(2) frontier_less_equal_zcount_pos group_cancel.add2 member_frontier_pos_zmset)
                                done
                              done
                            done
                          done
                        subgoal
                          apply (clarsimp simp flip: member_antichain.rep_eq)
                          apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, where s=s and t=ft])
                            apply assumption
                           defer
                           apply assumption
                          apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid'' (Src p'')" _ _ ft, simplified])
                          subgoal
                            apply (rule graph.path_weight_refl)
                            apply (rule dataflow_topology.axioms(1)[OF D])
                            done
                          subgoal
                            apply (subst (asm) (4) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                            apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                              apply simp_all
                            apply (simp add: zmset_filter_extract_progress_Src_consumes_no_intsum c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                            apply (meson frontier_less_equal_zcount_pos member_frontier_pos_zmset)
                            done
                          done
                        done
                      done
                    done
                  done
                done
              done
            done

          subgoal
            subgoal
              apply (subst Propagate.dataflow_topology.implied_frontier_alt_def[OF D])
              apply (subst Groups_Big.comm_monoid_add_class.sum.subset_diff[where B="(\<lambda> (nid, p). Loc nid (Src p)) ` ((set xs - {nid}) \<times> UNIV) \<union> (\<lambda> (nid, p). Loc nid (Trg p)) ` ((set xs - {nid}) \<times> UNIV)"])
                apply simp_all
               apply fast
              apply (rule frontier_less_equal_addI)
              subgoal
                apply (rule disjI2)
                apply (subst (asm) frontier_less_equal_iff2)
                apply clarsimp
                subgoal for ft
                  apply (drule in_frontier_sumEx)
                    apply (simp_all add: zcount_sum image_iff split_beta)
                  subgoal
                    by (auto intro: ordered_comm_monoid_add_class.sum_nonneg)
                  subgoal
                    apply clarsimp
                    subgoal for l'
                      apply (drule in_frontier_sumEx)
                        apply (simp_all add: zcount_sum image_iff split_beta)
                      apply clarsimp
                      subgoal for s
                        apply (drule in_frontier_zmset_imageD)
                        apply clarsimp
                        subgoal for ft
                          apply hypsubst_thin
                          apply (rule frontier_less_equal_sumI[where l=l'])
                             apply simp
                          subgoal
                            by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
                          subgoal
                            by (clarsimp simp add: zcount_sum image_iff split_beta)
                          subgoal
                            apply (rule frontier_less_equal_sumI[where l=s])
                               apply simp_all
                            unfolding frontier_less_equal_iff2
                            apply (subst in_frontier_zmset_image)
                             apply simp_all
                            apply (subst change_multiplicities_extract_prog_consumes)
                              apply simp_all
                            apply (clarsimp simp add: c_pts_change_multiplicities)
                            apply (cases "l' = Loc nid (Trg p)"; simp)
                            apply (drule in_frontier_in_frontier_add[where t=ft and B="zmset (map snd (filter (\<lambda>(l'a, t, d). l' = l'a) (concat (map (\<lambda>p'. map (\<lambda>t'. (Loc nid (Src p'), t -+- t', 1)) (intsum (os nid) p p')) enum_class.enum))))"])
                            subgoal
                              by (clarsimp simp add: zcount_sum image_iff split_beta intro!: zcount_zmset_ge_0I)
                            apply clarsimp
                            subgoal for ft3
                              apply (rule exI[of _ "ft3 -+- s"])
                              apply simp
                              apply (intro conjI)
                               apply (metis (no_types, lifting) nat_arith.add1)
                              apply (meson assms(1) basic_trans_rules(23) dataflow_topology.results_in_mono(1)) 
                              done
                            done
                          done
                        done
                      done
                    done
                  done
                done
              subgoal
                by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
              subgoal
                by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
              done
            done
          done


        subgoal for p' nid'' p''
          using PR apply -
          unfolding produ_supported_def
          apply (drule spec2, drule spec2, drule mp, assumption)
          apply (elim disjE)
          subgoal
            apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc nid' (Src p')", simplified, OF D])
            subgoal
              using G apply -
              unfolding graph_summar_nt_def
              by auto
            subgoal
              apply (subst change_multiplicities_extract_prog_consumes)
                apply simp_all
              apply (clarsimp simp add: c_pts_change_multiplicities )
              apply (subst filter_False)
              subgoal  apply -
                unfolding extract_prog_def extract_progress_def
                apply (auto simp add: Misc.set_map_filter split: option.splits)
                done
              apply simp
              apply (meson frontier_less_equal_zcount_pos)
              done
            done
          subgoal
            apply clarsimp
            using E[unfolded extract_prog_changes_above_impl_inv_def, rule_format, of "xs" nid', unfolded changes_above_impl_inv_def] apply -
            apply simp
            apply (drule bspec)
             apply (subst obtain_progress_def)
             apply (subst extract_progress_def)
             apply simp
             apply force
            apply simp
            subgoal premises temp for m'
              using temp(1,2,4-) apply -
              apply (rule frontier_less_equal_ifrontier_trans[of _ 0 "Loc nid' (Src p')", simplified, OF D])
              subgoal
                using G apply -
                unfolding graph_summar_nt_def
                by auto
              subgoal
                apply (subgoal_tac 
                    "nid \<in> set xs \<Longrightarrow>
    \<forall>s p''. s \<in>\<^sub>A graph.path_weight su (Loc nid (Src p'')) (Loc nid' (Src p')) \<longrightarrow> (\<forall>t''. t'' \<in> set (intsum (os nid) p p'') \<longrightarrow> \<not> t -+- t'' -+- s \<le> t') \<Longrightarrow>
    frontier_less_equal (ifrontier su (-+-) (change_multiplicities su (extract_prog xs nt os) c) (Loc nid' (Src p'))) t' \<Longrightarrow>
    nid' \<noteq> nid \<Longrightarrow> distinct xs \<Longrightarrow> nid' \<notin> set xs \<Longrightarrow> frontier_less_equal (ifrontier su (-+-) (change_multiplicities su (extract_prog xs nt (os(nid := consumes (os nid) p t d))) c) (Loc nid' (Src p'))) t'")
                subgoal
                  apply (drule meta_mp)
                   apply assumption
                  apply (drule meta_mp)
                  subgoal
                    apply safe
                    subgoal for s' p''' t''
                      apply (drule graph.path_weight_elem_trans[rotated 1, of _ _ _ _ 0 "Loc nid'' (Trg p'')"])
                      subgoal
                        using G apply -
                        unfolding graph_summar_nt_def
                        by auto
                      subgoal
                        by (rule dataflow_topology.axioms(1)[OF D])
                      apply clarsimp
                      apply (metis add.assoc le_iff_add)
                      done
                    done
                  apply (drule meta_mp)
                   apply assumption
                  apply (drule meta_mp)
                   apply assumption
                  apply (drule meta_mp)
                   apply assumption
                  apply (drule meta_mp)
                   apply assumption
                  apply simp
                  done
                subgoal premises temp
                  using temp(17-) apply -
                  apply (subst (asm) Propagate.dataflow_topology.implied_frontier_alt_def[OF D])
                  apply (subst (asm) Groups_Big.comm_monoid_add_class.sum.subset_diff[where B="(\<lambda> (nid, p). Loc nid (Src p)) ` ((set xs - {nid}) \<times> UNIV) \<union> (\<lambda> (nid, p). Loc nid (Trg p)) ` ((set xs - {nid}) \<times> UNIV)"])
                    apply simp_all
                   apply fast
                  apply (drule frontier_less_equal_add_cases)
                  apply (elim disjE)
                  subgoal
                    apply (subst (asm) frontier_less_equal_iff2)
                    apply clarsimp
                    subgoal for ft
                      apply (drule in_frontier_sumEx)
                        apply (simp_all add: zcount_sum image_iff split_beta)
                      subgoal
                        by (auto intro: ordered_comm_monoid_add_class.sum_nonneg)
                      subgoal
                        apply (elim conjE bexE)
                        apply (drule in_frontier_sumEx)
                          apply (simp_all add: zcount_sum image_iff split_beta)
                        apply clarsimp
                        subgoal for l' s
                          apply (drule in_frontier_zmset_imageD)
                          apply clarsimp
                          subgoal for ft
                            apply hypsubst_thin
                            apply (elim disjE rangeE)
                            subgoal 
                              apply (clarsimp simp add: split: prod.splits)
                              subgoal for nid'' p''
                                apply hypsubst_thin
                                apply (cases "nid'' = nid \<and> p'' = p")
                                subgoal
                                  apply clarsimp
                                  apply (simp_all flip: member_antichain.rep_eq)
                                  apply hypsubst_thin
                                  apply (subst (asm) (3) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                    apply simp_all
                                  apply (subgoal_tac "\<exists> t p'' s'. t \<in> set (intsum (os nid) p p'') \<and> s' \<in>\<^sub>A graph.path_weight su (Loc nid (Src p'')) (Loc nid' (Src p')) \<and> s = t -+- s'")
                                   defer
                                  subgoal
                                    using G[unfolded graph_summar_nt_def]
                                    by blast
                                  subgoal
                                    apply clarsimp
                                    subgoal for t'' p'' s'
                                      apply hypsubst_thin
                                      apply (drule spec2, drule mp, assumption)
                                      apply (drule spec, drule mp, assumption)
                                      apply (subgoal_tac "ft \<noteq> t")
                                       defer
                                      subgoal
                                        by (metis dataflow_topology_from_tree.followed_by_summary)
                                      apply (simp add: change_multiplicities_comm change_multiplicities_append_alt)
                                      apply (drule in_frontier_c_pts_change_multiplicities_consumes_Trg[where t=t and d=d]) 
                                       apply simp
                                      apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D])
                                        apply assumption
                                       apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid (Trg p)" _ _ ft])
                                      subgoal
                                        apply (rule graph.path_weight_refl)
                                        apply (rule dataflow_topology.axioms(1)[OF D])
                                        done
                                      subgoal
                                        apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                          apply simp_all
                                        apply (metis (no_types, opaque_lifting) change_multiplicities_append change_multiplicities_comm frontier_less_equal_zcount_pos member_frontier_pos_zmset)
                                        done
                                      subgoal
                                        by auto
                                      done
                                    done
                                  done
                                subgoal
                                  apply clarsimp
                                  apply (simp_all flip: member_antichain.rep_eq)
                                  apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D])
                                    apply assumption
                                   defer
                                   apply assumption
                                  apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid'' (Trg p'')" _ _ ft, simplified])
                                  subgoal
                                    apply (rule graph.path_weight_refl)
                                    apply (rule dataflow_topology.axioms(1)[OF D])
                                    done
                                  subgoal
                                    apply (subst (asm) (3) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                      apply simp_all
                                    apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                      apply simp_all
                                    apply (simp add: zmset_filter_extract_progress_Trg_consumes_diff c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                                    unfolding frontier_less_equal_iff2
                                    apply (rule exI[of _ ft])
                                    apply auto
                                    done
                                  done
                                done
                              done


                            subgoal
                              apply clarsimp
                              subgoal for nid'' p''
                                apply (cases "nid'' = nid \<and> (\<exists> t. t \<in> set (intsum (os nid) p p''))")
                                subgoal
                                  apply clarsimp
                                  subgoal for t''
                                    apply hypsubst_thin
                                    apply (simp_all flip: member_antichain.rep_eq)
                                    apply (drule spec2, drule mp, assumption)
                                    apply (drule spec, drule mp, assumption)
                                    apply (subgoal_tac " ft \<noteq> t -+- t''")
                                     defer
                                    subgoal
                                      by fast
                                    apply (drule in_frontier_addEx[where B="to_zmset (map ((-+-) t) (intsum (os nid) p p''))"])
                                    subgoal
                                      using to_zmset_nenneg by fast
                                    apply clarsimp
                                    subgoal for ft'
                                      apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, where s=s and t=ft'])
                                        apply assumption
                                       defer
                                      subgoal
                                        by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(23))
                                      apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid (Src p'')" _ _ ft', simplified])
                                      subgoal
                                        apply (rule graph.path_weight_refl)
                                        apply (rule dataflow_topology.axioms(1)[OF D])
                                        done
                                      subgoal
                                        apply (subst (asm) (3) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                          apply simp_all
                                        apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                          apply simp_all
                                        apply (simp add: zmset_filter_extract_progress_Src_consumes c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                                        apply (smt (verit, ccfv_SIG) Groups.add_ac(2) frontier_less_equal_zcount_pos group_cancel.add2 member_frontier_pos_zmset)
                                        done
                                      done
                                    done
                                  done
                                subgoal
                                  apply (clarsimp simp flip: member_antichain.rep_eq)
                                  apply (rule frontier_less_equal_ifrontier_trans_alt2[OF D, where s=s and t=ft])
                                    apply assumption
                                   defer
                                   apply assumption
                                  apply (rule frontier_less_equal_ifrontierI[OF D, of 0 "Loc nid'' (Src p'')" _ _ ft, simplified])
                                  subgoal
                                    apply (rule graph.path_weight_refl)
                                    apply (rule dataflow_topology.axioms(1)[OF D])
                                    done
                                  subgoal
                                    apply (subst (asm) (3) change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                      apply simp_all
                                    apply (subst change_multiplicities_extract_prog_obtain_progress_remove1_append[where nid=nid])
                                      apply simp_all
                                    apply (simp add: zmset_filter_extract_progress_Src_consumes_no_intsum c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                                    apply (meson frontier_less_equal_zcount_pos member_frontier_pos_zmset)
                                    done
                                  done
                                done
                              done
                            done
                          done
                        done
                      done
                    done

                  subgoal
                    subgoal
                      apply (subst Propagate.dataflow_topology.implied_frontier_alt_def[OF D])
                      apply (subst Groups_Big.comm_monoid_add_class.sum.subset_diff[where B="(\<lambda> (nid, p). Loc nid (Src p)) ` ((set xs - {nid}) \<times> UNIV) \<union> (\<lambda> (nid, p). Loc nid (Trg p)) ` ((set xs - {nid}) \<times> UNIV)"])
                        apply simp_all
                       apply fast
                      apply (rule frontier_less_equal_addI)
                      subgoal
                        apply (rule disjI2)
                        apply (subst (asm) frontier_less_equal_iff2)
                        apply clarsimp
                        subgoal for ft
                          apply (drule in_frontier_sumEx)
                            apply (simp_all add: zcount_sum image_iff split_beta)
                          subgoal
                            by (auto intro: ordered_comm_monoid_add_class.sum_nonneg)
                          subgoal
                            apply clarsimp
                            subgoal for l'
                              apply (drule in_frontier_sumEx)
                                apply (simp_all add: zcount_sum image_iff split_beta)
                              apply clarsimp
                              subgoal for s
                                apply (drule in_frontier_zmset_imageD)
                                apply clarsimp
                                subgoal for ft
                                  apply hypsubst_thin
                                  apply (rule frontier_less_equal_sumI[where l=l'])
                                     apply simp
                                  subgoal
                                    by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
                                  subgoal
                                    by (clarsimp simp add: zcount_sum image_iff split_beta)
                                  subgoal
                                    apply (rule frontier_less_equal_sumI[where l=s])
                                       apply simp_all
                                    unfolding frontier_less_equal_iff2
                                    apply (subst in_frontier_zmset_image)
                                     apply simp_all
                                    apply (subst change_multiplicities_extract_prog_consumes)
                                      apply simp_all
                                    apply (clarsimp simp add: c_pts_change_multiplicities)
                                    apply (cases "l' = Loc nid (Trg p)"; simp)
                                    apply (drule in_frontier_in_frontier_add[where t=ft and B="zmset (map snd (filter (\<lambda>(l'a, t, d). l' = l'a) (concat (map (\<lambda>p'. map (\<lambda>t'. (Loc nid (Src p'), t -+- t', 1)) (intsum (os nid) p p')) enum_class.enum))))"])
                                    subgoal
                                      by (clarsimp simp add: zcount_sum image_iff split_beta intro!: zcount_zmset_ge_0I)
                                    apply clarsimp
                                    subgoal for ft3
                                      apply (rule exI[of _ "ft3 -+- s"])
                                      apply simp
                                      apply (intro conjI)
                                       apply (metis (no_types, lifting) nat_arith.add1)
                                      apply (meson assms(1) basic_trans_rules(23) dataflow_topology.results_in_mono(1)) 
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          done
                        done
                      subgoal
                        by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
                      subgoal
                        by (clarsimp simp add: zcount_sum image_iff split_beta intro!: ordered_comm_monoid_add_class.sum_nonneg)
                      done
                    done
                  done

                done
              done
            done
          done
        done
      subgoal
        using E[unfolded extract_prog_changes_above_impl_inv_def, rule_format, of "xs" nid', unfolded changes_above_impl_inv_def] apply -
        apply simp
        apply (drule bspec)
         apply assumption
        apply auto
        done
      done
    done
  subgoal for xs
    unfolding changes_above_impl_inv_def
    apply safe
    subgoal for l t' m
      apply (cases "nid \<in> set xs"; simp?)
      apply (drule set_extract_progressD)
      apply clarsimp
      apply (elim disjE conjE exE; simp?; hypsubst_thin?)
      subgoal
        using E[unfolded extract_prog_changes_above_impl_inv_def, rule_format, of "xs" nid, unfolded changes_above_impl_inv_def] apply -
        apply simp
        apply (drule bspec)
         apply assumption
        apply simp
        done
      subgoal
        apply (subst Propagate.dataflow_topology.implied_frontier_alt_def[OF D])
        apply (subst Groups_Big.comm_monoid_add_class.sum.subset_diff[where B="(\<lambda> (nid, p). Loc nid (Src p)) ` ((set xs - {nid}) \<times> UNIV) \<union> (\<lambda> (nid, p). Loc nid (Trg p)) ` ((set xs - {nid}) \<times> UNIV)"])
          apply simp_all
         apply fast
        apply (rule frontier_less_equal_addI)
        subgoal
          apply (rule disjI2)
          apply (subst (asm) frontier_less_equal_iff2)
          apply clarsimp
          subgoal for ft


end

lemma dataplane_tracker_inv_consumes:
  "dataplane_tracker_inv os cbufs sg \<Longrightarrow>
   cbufs (nid, p) = (d, t) # xs \<Longrightarrow>
   dataflow_topology (summ sg) (-+-) \<Longrightarrow>
   graph_summar_nt (summ sg) (nxt sg) os \<Longrightarrow>
  dataplane_tracker_inv (os(nid := consumes (os nid) p (t :: 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) d)) (BTL (nid, p) cbufs) sg"
 unfolding dataplane_tracker_inv_def
  apply (elim conjE exE)
  apply simp
  apply hypsubst_thin
  subgoal for c c' cgs chns caps
    apply (rule exI[of _ 
          "(\<lambda> l. case l of 
        Loc nid' (Src p') \<Rightarrow> if nid' = nid then caps l + to_zmset (map (\<lambda> t'. t + t') (intsum (os nid) p p')) else caps l 
     | Loc nid' (Trg p') \<Rightarrow> if nid' = nid \<and> p = p' then caps l - {# t #}\<^sub>z else caps l)"])
    apply (intro conjI)
    subgoal premises prems
      using prems(4) apply -
      unfolding Src_caps_inv_def consumes_def add_caps_def to_zmset_correct
      apply (auto 0 0 simp add: filter_empty_conv)
      apply (auto 0 0 simp add:  comp_def  simp flip:  to_zmset_correct)
      subgoal premises prems2 for p''
        apply (simp flip: Multiset.mset_filter mset_map add: map_concat filter_concat comp_def)        
        done
      done
    subgoal premises prems
      using prems(1,5) apply -
      unfolding Trg_caps_inv_def
      apply (auto simp add: map_tl BHD_def BTL_def BULK_BENQ_def)
      done
    subgoal premises prems
      using prems(6) apply -       
      unfolding c_pts_inv_def
      apply (auto 0 0 split: location.splits port.splits simp add: c_pts_change_multiplicities)
      subgoal
        apply (subgoal_tac
            "zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_prog Enum.enum (subgraph.nxt sg) (os(nid := consumes (os nid) p t d))))) =
   zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_prog Enum.enum (subgraph.nxt sg) os))) - {#t#}\<^sub>z")
        subgoal
          by auto
        subgoal premises
          apply (auto cong: if_cong simp add: if_distrib zmset_map_filter_Trg_extract_prog comp_def)
          apply (rule arg_cong2[where f=minus])
          apply (simp_all add: update_zmultiset_singleton(2))
          apply metis
          done
        done
      subgoal for nid'
        apply (drule spec[of _ "Loc nid (Src nid')"])
        apply (drule sym)
        apply simp
        subgoal premises
          apply (simp add: zmset_concat map_concat filter_concat comp_def filter_map split_beta split: prod.splits)
          done
        done
      subgoal for nid' p'
        apply (clarsimp cong: if_cong simp add: if_distrib comp_def)
        apply (drule spec[of _ "Loc nid' (Src p')"])
        apply (simp add: comp_def)
        done
      done
    subgoal premises prems
      using prems(7) unfolding front_inv_def by auto
    subgoal premises prems
      using prems(1,9) apply -
      unfolding chnls_imp_front_inv_def
      apply (simp_all add: BHD_def BTL_def BULK_BENQ_def)
      done
    subgoal premises prems
      using prems(10) apply -
      unfolding change_deltas_inv_def extract_prog_def consumes_def obtain_progress_def extract_progress_def
      apply (clarsimp simp add: split_beta split: prod.splits)
      done
    subgoal premises prems
      using prems(12) apply -


      apply (auto 0 0)
      subgoal for xs
        using prems(12)

        apply (induct xs arbitrary:  rule: rev_induct)
        subgoal sorry
        subgoal for nid' xs
          apply (auto 0 0)
      using prems(11) apply -
      unfolding changes_above_impl_inv_def
      apply (clarsimp simp add: c_pts_change_multiplicities split: prod.splits)


end
      subgoal for l t' m
        apply (drule set_extract_prog_consumesD)
        apply (elim disjE exE conjE)
        subgoal
          by blast
        subgoal
          using prems(1,9) apply -
          apply hypsubst_thin
          unfolding chnls_imp_front_inv_def
          apply (drule spec[of _ nid])
          apply (drule spec[of _ p])
          apply (drule bspec[of _ _ t'])
          subgoal
            unfolding BULK_BENQ_def
            by simp
          subgoal
            by blast
          done
        subgoal premises prems2 for p' t''
          using prems(5,6) apply -
          apply (drule data_in_channel_justifies_c_pts[where t=t and p=p and nid=nid])
          apply assumption
          using prems(1) apply -
          unfolding BULK_BENQ_def
          apply clarsimp
          subgoal 
            using prems(10) apply -
            unfolding change_deltas_inv_def
            apply clarsimp
            apply (smt (verit, best))
            done
          subgoal
            using prems(10) apply -
            unfolding change_deltas_inv_def
            apply clarsimp
            apply (smt (verit, best))
            done
          apply (elim disjE)
          subgoal
            using prems2(4,5) apply hypsubst_thin
            apply (rule frontier_less_equal_ifrontierI_alt[where l="Loc nid (Trg p)"])
            using prems(2) apply blast
            subgoal
              using prems(3) prems2(3,2) apply -
              unfolding graph_summar_nt_def
              apply auto
              done
            subgoal
              using frontier_less_equal_zcount_pos by blast
            done
          subgoal
            apply clarsimp
            subgoal for nid' p''
              using prems(12) apply -
              unfolding changes_above_impl_inv_def
              apply clarsimp
              apply (drule gt_0_zcount_msetD)
              apply clarsimp
              subgoal for m
                apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m)"])
                subgoal premises premm
                  unfolding extract_prog_def extract_progress_def obtain_progress_def
                  apply (clarsimp simp add: List.map_filter_def enum_class.enum_UNIV split_beta c_pts_change_multiplicities split: option.splits prod.splits)
                  apply (rule exI[of _ nid'])
                  apply (intro disjI2)
                  using premm(3,4,5) apply -
                  apply (rule image_eqI[rotated])
                  apply auto
                  done
                subgoal
                  apply simp
                  using prems2(4,5) apply hypsubst_thin
                  apply (rule frontier_less_equal_ifrontier_trans_alt[of _ _ "Loc nid (Trg p)"])          
                  subgoal using prems(2) by assumption
                  subgoal
                    using prems(3) prems2(3,2) apply -
                    unfolding graph_summar_nt_def
                    apply auto
                    done
                  apply assumption
                  done
                done
              done
            done
          done
        done
      done
    subgoal premises prems
      apply auto
      subgoal  for nid'
        unfolding changes_above_impl_inv_def
        apply safe
        subgoal for l' t' m
          using prems(13) apply -
          apply (drule spec[of _ nid])
          apply (drule spec[of _ nid'])
          apply simp
          unfolding changes_above_impl_inv_def
          apply (drule bspec[of _ _ ])
          apply assumption
          apply simp
          subgoal premises temp
            apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc nid (Trg p)) +
                                 zmset (map snd (filter (\<lambda>(l', t, d). (Loc nid (Trg p)) = l') (extract_progress nid (nxt sg) (snd (obtain_progress (os nid))))))) t > 0 \<or>
   zcount (\<Sum>x\<in>UNIV - {nid}. zmset (List.map_filter (\<lambda> (p', t, d). case_option None (\<lambda> (nid'', p''). if nid'' = nid \<and> p'' = p then Some (t, d) else None) (nxt sg (x, p'))) (produ (os x)))) t > 0")
            defer
            subgoal premises prems2
              using prems(1,5,6) apply -
              unfolding Trg_caps_inv_def
              apply (drule spec[of _ nid])
              apply (drule spec[of _ p])
              unfolding c_pts_inv_def
              apply (drule spec[of _ "Loc nid (Trg p)"])
              apply (simp add: c_pts_change_multiplicities extract_prog_def filter_concat comp_def map_concat zmset_concat sum_list_distinct_conv_sum_set)
              apply (subst (asm) comm_monoid_add_class.sum.subset_diff[of "{nid}"])
              apply simp_all
              unfolding zmultiset_eq_iff
              apply (drule spec[of _ t])+
              apply (subgoal_tac  "zcount
       (c_pts (pt_tr sg) (Loc nid (Trg p)) +
        ((\<Sum>x\<in>UNIV - {nid}. zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_progress x (subgraph.nxt sg) (snd (obtain_progress (os x))))))) +
         zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_progress nid (subgraph.nxt sg) (snd (obtain_progress (os nid))))))))
       t > 0")
              subgoal premises prems3
                using prems3(4) 
                by (auto simp add: zmset_filter_Trg_not_nid)
              subgoal
                unfolding outputs_at_target_def BULK_BENQ_def
                apply (auto simp add: to_zmset_nenneg split: option.splits prod.splits)
                done
              done
            subgoal premises premst
              using temp apply -
              subgoal premises prems3
                apply (subgoal_tac "\<And> m' p'. nid \<noteq> nid' \<Longrightarrow>
    frontier_less_equal (ifrontier (summ sg) (-+-) (change_multiplicities (summ sg) (extract_progress nid (subgraph.nxt sg) (snd (obtain_progress (os nid)))) (pt_tr sg)) (Loc nid' (Src p'))) t' \<Longrightarrow>
    (p', t', m') \<in> set (operator_state.inter (os nid')) \<Longrightarrow>
    frontier_less_equal (ifrontier (summ sg) (-+-) (change_multiplicities (summ sg) (extract_progress nid (subgraph.nxt sg) (snd (obtain_progress (consumes (os nid) p t d)))) (pt_tr sg)) (Loc nid' (Src p'))) t'")
                defer
                subgoal for m' p'
                  apply (subst (asm) Propagate.dataflow_topology.implied_frontier_alt_def)
                  using prems(2) apply assumption
                  unfolding frontier_less_equal_iff2
                  apply clarsimp
                  subgoal for ft
                    apply (drule in_frontier_sumEx)
                    apply simp_all
                    subgoal
                      by (simp add: sum_nonneg zcount_sum)
                    apply clarsimp
                    apply (drule in_frontier_sumEx)
                    apply (simp_all flip: member_antichain.rep_eq)
                    apply clarsimp
                    subgoal for l s
                      apply (elim disjE rangeE)
                      subgoal for pa
                        apply (cases pa)
                        apply simp
                        apply hypsubst_thin
                        subgoal for nid3 p3
                          apply (cases "nid3 = nid \<and> p3 = p")
                          subgoal
                            apply clarsimp
                            apply hypsubst_thin
                            apply (subst (asm) in_frontier_zmset_image)
                            apply clarsimp+
                            subgoal for ft2
                              apply (simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                              apply hypsubst_thin
                              apply (cases "ft2 = t")
                              subgoal
                                apply hypsubst_thin
                                apply (clarsimp simp flip: member_antichain.rep_eq)
                                apply (subgoal_tac "\<exists> t p'' s'. t \<in> set (intsum (os nid) p p'') \<and> s' \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Src p'')) (Loc nid' (Src p')) \<and> s = t -+- s'")
                                subgoal
                                  apply clarsimp
                                  subgoal for t'' p'' s'
                                    apply (rule exI[of _ "t -+- t'' -+- s'"])
                                    apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
                                    using prems(2) apply assumption
                                    apply (intro conjI[rotated])
                                    apply (metis dataflow_topology_from_tree.followed_by_summary)
                                    apply (rule in_frontier_SumI[where a="Loc nid (Src p'')"])
                                    apply simp_all
                                    subgoal
                                      apply (rule in_frontier_SumI[where a="s'"])
                                      apply simp_all
                                      subgoal
                                        apply (simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes)
                                        apply (subst in_frontier_zmset_image)
                                        apply (clarsimp simp flip: add.assoc)+
                                        apply (rule in_frontier_sumI2)
                                        subgoal
                                          apply (simp add: to_zmset_map)
                                          apply (subgoal_tac "t'' \<in>\<^sub>A frontier (to_zmset (intsum (os nid) p p''))")
                                          subgoal
                                            using in_frontier_zmset_image
                                            by (smt (verit, ccfv_threshold) add_left_cancel canonically_ordered_monoid_add_class.lessE dataflow_topology_from_tree.followed_by_summary in_frontier_iff less_add_same_cancel1 pos_image_zmset_obtain_pre
                                                pos_zcount_image_zmset to_zmset_nenneg)
                                          find_theorems frontier image_zmset
                                          subgoal
                                            using prems(3) apply -
                                            unfolding graph_summar_nt_def
                                            apply clarsimp
                                            apply (meson in_frontier_iff zcount_to_zmset_gt_0)
                                            done
                                          done
                                        subgoal
                                          apply clarsimp
                                          subgoal for ft'
                                            apply (drule bspec[of _ _ "Loc nid (Src p'')"])
                                            apply fast
                                            apply (simp flip: zcount_union)
                                            apply (drule zcount_gt_0_in_frontierD)
                                            apply clarsimp
                                            subgoal for ft2
                                              apply (drule spec[of _ "ft2  -+- s'"])
                                              apply (simp add: zcount_sum)
                                              apply (drule mp)
                                              subgoal
                                                apply (rule dataflow_topology_from_tree.sum_pos)
                                                apply (simp_all flip: member_antichain.rep_eq)
                                                apply (rule pos_zcount_image_zmset)
                                                apply clarsimp
                                                apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                done
                                              subgoal
                                                by order
                                              done
                                            done
                                          done
                                        subgoal premises prems2
                                          using prems(4, 6) apply -
                                          unfolding Src_caps_inv_def
                                          apply (drule spec2[of _ nid p''])
                                          unfolding c_pts_inv_def
                                          apply (drule spec[of _ "Loc nid (Src p'')"])
                                          apply simp
                                          unfolding extract_prog_def
                                          apply (simp add: c_pts_change_multiplicities filter_concat comp_def map_concat zmset_concat sum_list_distinct_conv_sum_set)
                                          apply (subst (asm) comm_monoid_add_class.sum.subset_diff[of "{nid}"])
                                          apply simp_all
                                          apply (subst (asm) comm_monoid_add_class.sum.neutral)
                                          subgoal
                                            unfolding obtain_progress_def extract_progress_def
                                            apply (auto 0 0 simp add: List.map_filter_def filter_concat comp_def map_concat zmset_concat split_beta split: prod.splits option.splits)
                                            done
                                          apply simp
                                          unfolding zmultiset_eq_iff
                                          apply simp
                                          apply (meson to_zmset_nenneg)
                                          done
                                        subgoal
                                          apply clarsimp
                                          apply (meson to_zmset_nenneg)
                                          done
                                        done
                                      apply (simp flip: member_antichain.rep_eq)
                                      subgoal
                                        apply clarsimp
                                        subgoal for s'' t2
                                          apply hypsubst_thin
                                          apply (drule zcount_zimageD)
                                          apply clarsimp
                                          subgoal for t3
                                            apply (clarsimp simp add: zcount_sum c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes simp flip: member_antichain.rep_eq add.assoc)
                                            apply (drule in_frontier_addD[where t=t3])
                                            apply (elim exE conjE disjE)
                                            subgoal for t4
                                              apply (drule bspec[of _ _ "Loc nid (Src p'')"])
                                              apply fast
                                              apply (drule spec[of _ "t4 -+- s''"])
                                              apply (drule mp)
                                              subgoal
                                                apply (rule dataflow_topology_from_tree.sum_pos)
                                                apply simp
                                                apply (simp flip: member_antichain.rep_eq)
                                                unfolding member_antichain.rep_eq[symmetric]
                                                apply assumption
                                                back

                                                apply (rule pos_zcount_image_zmset)
                                                apply clarsimp
                                                apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                done
                                              subgoal
                                                by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                              done
                                            subgoal for t4
                                              apply clarsimp
                                              subgoal for t5
                                                apply hypsubst_thin
                                                  (* here! *)
                                                using premst apply -
                                                apply (elim disjE)
                                                subgoal
                                                  apply (drule zcount_gt_0_in_frontierD)
                                                  apply clarsimp
                                                  subgoal for ft'
(* here7 *)
                                                    apply (subgoal_tac "\<exists> t6\<le>t5. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p''))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t6
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s'' _ _ _ t6 "Loc nid (Trg p)"])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply simp
                                                    apply clarsimp
                                                    subgoal for u
                                                      apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                      apply (simp_all flip: member_antichain.rep_eq)
                                                      apply fast
                                                      apply (drule spec[of _ "ft' -+- u"])
                                                      apply (drule mp)
                                                      subgoal
                                                        apply (rule dataflow_topology_from_tree.sum_pos)
                                                        apply simp
                                                        apply (simp flip: member_antichain.rep_eq)
                                                        unfolding member_antichain.rep_eq[symmetric]
                                                        apply assumption
                                                        back
                                                        apply (rule pos_zcount_image_zmset)
                                                        apply clarsimp
                                                        apply (clarsimp simp flip: member_antichain.rep_eq)
                                                        done
                                                      subgoal 
                                                        using Groups.add_ac(2) add_less_imp_less_left add_mono_thms_linordered_field(4) group_cancel.add1
                                                        by (metis add_less_cancel_left basic_trans_rules(21) dataflow_topology_from_tree.results_in_mono(2))
                                                            done
                                                    done
                                                  done
                                                done
                                                subgoal
                                                  apply (simp add: zcount_sum)
                                                  apply (drule sum_pos_ex_elem_pos)
                                                  apply (elim bexE)
                                                  subgoal for nid''
                                                    apply simp
                                                    apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                                      (* here4 *)
                                                    apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                                    subgoal
                                                      apply (elim exE conjE)
                                                      using prems(13) apply -
                                                      apply (drule spec[of _ nid])
                                                      apply (drule spec[of _ nid''])
                                                      apply simp
                                                      unfolding changes_above_impl_inv_def
                                                      subgoal for p2 m'
                                                        apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                        subgoal
                                                          apply (subst obtain_progress_def)
                                                          apply (subst extract_progress_def)
                                                          apply (auto simp add: set_map_filter image_iff split_beta )
                                                          apply (rule bexI[rotated])
                                                          apply (clarsimp split: option.splits)
                                                          apply force
                                                          apply (clarsimp split: option.splits)
                                                          done
                                                        apply simp
                                                        apply (drule frontier_less_equal_ifrontierE)
                                                        using prems(2) apply assumption
                                                        apply clarsimp
                                                        unfolding frontier_less_equal_iff2
                                                        apply clarsimp
                                                        apply (subst (asm) (3) in_frontier_iff)
                                                        apply clarsimp
                                                        apply hypsubst_thin
                                                        subgoal for l  s''' t6 t6'
                                                          apply (drule bspec[of _ _ l])
                                                          subgoal
                                                            apply (cases l)
                                                            apply simp
                                                            subgoal for nn pp
                                                              apply (cases pp)
                                                              apply simp_all
                                                              apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                              done
                                                            done
(* here8 *)
                                                          apply (subgoal_tac "\<exists> t6\<le>t5. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p''))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s'' _ _ _ t9 "Loc nid (Trg p)"])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply simp
                                                    apply clarsimp
                                                    subgoal for u
                                                      apply (drule graph.path_weight_elem_trans[rotated, of _ _ l _ u ])
                                                      apply assumption
                                                            subgoal
                                                              apply (rule dataflow_topology.axioms(1))
                                                              apply (rule prems(2))
                                                              done
                                                            apply clarsimp
                                                            subgoal for u'
                                                              apply (drule zcount_gt_0_in_frontierD)
                                                              apply clarsimp
                                                              subgoal for ft7
                                                                apply (drule spec[of _ "ft7 -+- u'"])
                                                                back
                                                                apply (drule mp)
                                                                subgoal
                                                                  apply (rule dataflow_topology_from_tree.sum_pos)
                                                                  apply (simp_all flip: member_antichain.rep_eq)
                                                                  apply (rule pos_zcount_image_zmset)
                                                                  apply clarsimp
                                                                  apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                                  done
                                                                subgoal 
                                                                  by (smt (verit, ccfv_threshold) add_less_le_mono add_mono_thms_linordered_semiring(2) add_strict_right_mono antisym_conv2 dataflow_topology_from_tree.followed_by_summary dataflow_topology_from_tree.plus_mono dual_order.strict_trans2
                                                                      nless_le)
                                                                done
                                                              done
                                                            done
                                                          done
                                                        done
                                                      done
                                                    done
                                                    subgoal
                                                      (* here2! *)
                                                      apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                      apply (drule sum_list_pos_ex_elem_pos)
                                                      apply (elim bexE)
                                                      apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                      apply (metis not_Some_eq2)
                                                      apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                                      apply fast
                                                      apply blast
                                                      done
                                                    done
                                                  done
                                                done
                                              done
                                            done
                                          done
                                        done
                                      done
                                    apply fast
                                    subgoal
                                      apply clarsimp
                                      apply (metis dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)
                                      done
                                    subgoal
                                      apply clarsimp
                                      apply (simp add: zcount_sum)
                                      apply (drule sum_pos_ex_elem_pos)
                                      apply (elim bexE)
                                      subgoal for l t6 s'''
                                        apply (drule zcount_zimageD)
                                        apply clarsimp
                                        subgoal for ft''
                                          apply (simp flip: member_antichain.rep_eq)
                                          apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                          apply (cases l; clarsimp simp add: image_iff)
                                          apply (elim disjE exE)
                                          subgoal for nid2 _ p2
                                            apply hypsubst_thin
                                            apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                            apply (cases "nid2 = nid \<and> p2 = p")
                                            subgoal
                                              apply clarsimp
                                              apply hypsubst_thin
                                              apply (clarsimp simp add: add_diff_eq zmset_filter_extract_progress_Trg_consumes_alt c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                              apply (drule in_frontier_minusD)
                                              apply simp
                                              apply clarsimp
                                              subgoal for ft2
                                                apply (drule bspec[of _ _ s'''])
                                                apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                apply (drule spec[of _ "ft2 -+- s'''"])
                                                apply (drule mp)
                                                subgoal
                                                  apply (rule pos_zcount_image_zmset)
                                                  apply clarsimp
                                                  apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                  done
                                                subgoal
                                                  by (metis add_mono_thms_linordered_semiring(3) basic_trans_rules(21) group_cancel.add1)
                                                done
                                              done
                                            subgoal
                                              apply clarsimp
                                              apply (clarsimp simp add: zmset_filter_extract_progress_Trg_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                              apply (drule bspec[of _ _ "Loc nid2 (Trg p2)"])
                                              apply fast
                                              apply (drule spec[of _ "ft'' -+- s'''"])
                                              apply (drule mp)
                                              back
                                              subgoal
                                                apply (rule dataflow_topology_from_tree.sum_pos)
                                                apply (simp_all flip: member_antichain.rep_eq)
                                                apply (rule pos_zcount_image_zmset)
                                                apply clarsimp
                                                apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                done
                                              subgoal
                                                by (metis add.assoc)
                                              done
                                            done
                                          subgoal for nid2 _ p2
                                            apply hypsubst_thin
                                            apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                            apply (cases "nid2 = nid")
                                            subgoal
                                              apply hypsubst_thin
                                              apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes c_pts_change_multiplicities simp flip: add.assoc member_antichain.rep_eq)
                                              apply (drule in_frontier_addD[where t=ft''])
                                              apply (elim exE conjE disjE)
                                              subgoal for t4
                                                apply (drule bspec[of _ _ "Loc nid (Src p2)"])
                                                apply fast
                                                apply (drule spec[of _ "t4 -+- s'''"])
                                                apply (drule mp)
                                                subgoal
                                                  apply (rule dataflow_topology_from_tree.sum_pos)
                                                  apply simp
                                                  apply (simp flip: member_antichain.rep_eq)
                                                  unfolding member_antichain.rep_eq[symmetric]
                                                  apply assumption

                                                  apply (rule pos_zcount_image_zmset)
                                                  apply clarsimp
                                                  apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                  done
                                                subgoal
                                                  by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                                done
                                              subgoal for ft2
                                                apply clarsimp
                                                subgoal for ft3
                                                  apply hypsubst_thin
                                                  using premst apply -
                                                  apply (elim disjE)
                                                  subgoal
                                                    apply (drule zcount_gt_0_in_frontierD)
                                                    apply clarsimp
                                                    subgoal for ft'
                                                      apply (subgoal_tac "\<exists> t6\<le>ft3. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p2))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t6

                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of  s''' _ _  _ t6 _])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                     apply assumption
                                                    apply clarsimp
                                                    subgoal for u
                                                        apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                        apply (simp_all flip: member_antichain.rep_eq)
                                                        apply fast
                                                        apply (drule spec[of _ "ft' -+- u"])
                                                        apply (drule mp)
                                                        subgoal
                                                          apply (rule dataflow_topology_from_tree.sum_pos)
                                                          apply simp
                                                          apply (simp flip: member_antichain.rep_eq)
                                                          unfolding member_antichain.rep_eq[symmetric]
                                                          apply assumption
                                                          back
                                                          apply (rule pos_zcount_image_zmset)
                                                          apply clarsimp
                                                          apply (clarsimp simp flip: member_antichain.rep_eq)
                                                          done
                                                        subgoal
                                                          using Groups.add_ac(2) add_less_imp_less_left add_mono_thms_linordered_field(4) group_cancel.add1
                                                        by (metis add_less_cancel_left basic_trans_rules(21) dataflow_topology_from_tree.results_in_mono(2))
                                                        done
                                                      done
                                                    done
                                                  done
                                                  subgoal
                                                    apply (simp add: zcount_sum)
                                                    apply (drule sum_pos_ex_elem_pos)
                                                    apply (elim bexE)
                                                    subgoal for nid''
                                                      apply simp
                                                      apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                                      apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                                      subgoal
                                                        apply (elim exE conjE)
                                                        using prems(13) apply -
                                                        apply (drule spec[of _ nid])
                                                        apply (drule spec[of _ nid''])
                                                        apply simp
                                                        unfolding changes_above_impl_inv_def
                                                        subgoal for p3 m'
                                                          apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                          subgoal
                                                            apply (subst obtain_progress_def)
                                                            apply (subst extract_progress_def)
                                                            apply (auto simp add: set_map_filter image_iff split_beta )
                                                            apply (rule bexI[rotated])
                                                            apply (clarsimp split: option.splits)
                                                            apply force
                                                            apply (clarsimp split: option.splits)
                                                            done
                                                          apply simp
                                                          apply (drule frontier_less_equal_ifrontierE)
                                                          using prems(2) apply assumption
                                                          apply clarsimp
                                                          unfolding frontier_less_equal_iff2
                                                          apply clarsimp
                                                          apply hypsubst_thin
                                                          subgoal for l  s'''' t6 t6'
                                                            apply (drule bspec[of _ _ l])
                                                            subgoal
                                                              apply (cases l)
                                                              apply simp
                                                              subgoal for nn pp
                                                                apply (cases pp)
                                                                apply simp_all
                                                                apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                                done
                                                              done
                                                            apply (subgoal_tac "\<exists> t6\<le>ft3. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p2))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of t9 _ _ _  ])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply simp
                                                    apply clarsimp
                                                            subgoal for u
                                                              apply (drule graph.path_weight_elem_trans[rotated, of u  _ _ _ s''' "Loc nid' (Src p')"])
                                                              apply assumption
                                                              subgoal
                                                                apply (rule dataflow_topology.axioms(1))
                                                                apply (rule prems(2))
                                                                done
                                                              apply clarsimp
                                                              subgoal for u'
                                                                apply (drule spec[of _ "t6' -+- u'"])
                                                                apply (drule mp)
                                                                subgoal
                                                                  apply (rule dataflow_topology_from_tree.sum_pos)
                                                                  apply (simp_all flip: member_antichain.rep_eq)
                                                                  apply (rule pos_zcount_image_zmset)
                                                                  apply clarsimp
                                                                  apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                                  done
                                                                subgoal
                                                                  by (smt (verit, ccfv_threshold) add.commute add.left_commute add_le_cancel_left order_le_less_subst2)
                                                                done
                                                              done
                                                            done
                                                          done
                                                        done
                                                      done
                                                      subgoal
                                                        (* here2! *)
                                                        apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                        apply (drule sum_list_pos_ex_elem_pos)
                                                        apply (elim bexE)
                                                        apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                        apply (metis not_Some_eq2)
                                                        apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                                        apply fast
                                                        apply blast
                                                        done
                                                      done
                                                    done
                                                  done
                                                done
                                              done 
                                            subgoal
                                              apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: add.assoc member_antichain.rep_eq)
                                              apply (drule bspec[of _ _ "Loc nid2 (Src p2)"])
                                              apply fast
                                              apply (drule spec[of _ "ft'' -+- s'''"])
                                              apply (drule mp)
                                              subgoal
                                                apply (rule dataflow_topology_from_tree.sum_pos)
                                                apply (simp_all flip: member_antichain.rep_eq)
                                                apply (rule pos_zcount_image_zmset)
                                                apply clarsimp
                                                apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                done
                                              subgoal
                                                by auto
                                              done
                                            done
                                          done
                                        done
                                      done
                                    done
                                  done
                                subgoal
                                  using prems(3)[unfolded graph_summar_nt_def]
                                  by blast
                                done
                              subgoal
                                apply (rule exI[of _ "ft2 -+- s"])
                                apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
                                using prems(2) apply assumption
                                apply (intro conjI[rotated])
                                apply simp
                                apply (simp add: zmset_filter_extract_progress_Trg_consumes_alt)
                                apply (rule in_frontier_SumI[where a="Loc nid (Trg p)"])
                                apply simp_all
                                subgoal
                                  apply (rule in_frontier_SumI[where a=s])
                                  apply simp_all
                                  subgoal
                                    apply (subst in_frontier_zmset_image)
                                    apply clarsimp
                                    subgoal
                                      apply (simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt add_diff_eq)
                                      using in_frontier_minusI apply blast
                                      done
                                    done
                                  subgoal
                                    apply clarsimp
                                    subgoal for s' ft3
                                      apply (drule zcount_zimageD)
                                      apply clarsimp
                                      apply (simp flip: member_antichain.rep_eq)
                                      subgoal for ft4
                                        apply (simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt add_diff_eq)
                                        apply (drule in_frontier_minusD)
                                        apply simp
                                        apply clarsimp
                                        subgoal for ft5
                                          apply (drule bspec[of _ _ s'])
                                          apply (simp flip: member_antichain.rep_eq)
                                          apply (drule spec[of _ "ft5 -+- s'"])
                                          apply (drule mp)
                                          subgoal
                                            apply (rule pos_zcount_image_zmset)
                                            apply clarsimp
                                            apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                            done
                                          subgoal
                                            by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                          done
                                        done
                                      done
                                    done
                                  done
                                subgoal
                                  by fast
                                subgoal
                                  apply clarsimp
                                  apply (metis dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)
                                  done
                                subgoal
                                  apply clarsimp
                                  apply (simp add: zcount_sum c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt add_diff_eq)
                                  subgoal for l ft3
                                    apply (drule sum_pos_ex_elem_pos)
                                    apply clarsimp
                                    subgoal for s'
                                      apply (drule zcount_zimageD)
                                      apply (clarsimp simp add: image_iff simp flip: member_antichain.rep_eq)
                                      subgoal for ft4
                                        apply (cases l; clarsimp)
                                        apply (elim disjE exE)
                                        subgoal for nid2 _ p2 
                                          apply hypsubst_thin
                                          apply (simp add: zcount_sum c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff add_diff_eq)
                                          apply (drule bspec[of _ _ "Loc nid2 (Trg p2)"])
                                          apply fast
                                          apply (drule spec[of _ "ft4 -+- s'"])
                                          apply (drule mp)
                                          back
                                          subgoal
                                            apply (rule dataflow_topology_from_tree.sum_pos)
                                            apply (simp_all flip: member_antichain.rep_eq)
                                            apply (rule pos_zcount_image_zmset)
                                            apply clarsimp
                                            apply clarsimp
                                            apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                            done
                                          subgoal
                                            by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                          done
                                        subgoal for nid2 _ p2 
                                          apply hypsubst_thin
                                          apply (cases "nid2 = nid")
                                          subgoal
                                            apply simp
                                            apply hypsubst_thin
                                            apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes c_pts_change_multiplicities simp flip: add.assoc member_antichain.rep_eq)
                                            apply (drule in_frontier_addD[where t=ft4])
                                            apply (elim exE conjE disjE)
                                            subgoal for ft5
                                              apply (drule bspec[of _ _ "Loc nid (Src p2)"])
                                              apply fast
                                              apply (drule spec[of _ "ft5 -+- s'"])
                                              apply (drule mp)
                                              subgoal
                                                apply (rule dataflow_topology_from_tree.sum_pos)
                                                apply simp
                                                apply (simp flip: member_antichain.rep_eq)
                                                unfolding member_antichain.rep_eq[symmetric]
                                                apply assumption

                                                apply (rule pos_zcount_image_zmset)
                                                apply clarsimp
                                                apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                done
                                              subgoal
                                                by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                              done


                                            subgoal for ft2'
                                              apply clarsimp
                                              subgoal for ft3
                                                apply hypsubst_thin
                                                using premst apply -
                                                apply (elim disjE)
                                                subgoal
                                                  apply (drule zcount_gt_0_in_frontierD)
                                                  apply clarsimp
                                                  subgoal for ft'
                                                    apply (subgoal_tac "\<exists> t6\<le>ft3. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p2))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for u
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s' _ _ _ u "Loc nid (Trg p)"])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply simp
                                                    apply clarsimp
                                                    subgoal for u
                                                      apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                      apply (simp_all flip: member_antichain.rep_eq)
                                                      apply fast
                                                      apply (drule spec[of _ "ft' -+- u"])
                                                      apply (drule mp)
                                                      subgoal
                                                        apply (rule dataflow_topology_from_tree.sum_pos)
                                                        apply simp
                                                        apply (simp flip: member_antichain.rep_eq)
                                                        unfolding member_antichain.rep_eq[symmetric]
                                                        apply assumption
                                                        back
                                                        apply (rule pos_zcount_image_zmset)
                                                        apply clarsimp
                                                        apply (clarsimp simp flip: member_antichain.rep_eq)
                                                        done
                                                      subgoal 
      using Groups.add_ac(2) add_less_imp_less_left add_mono_thms_linordered_field(4) group_cancel.add1
                                                        by (metis add_less_cancel_left basic_trans_rules(21) dataflow_topology_from_tree.results_in_mono(2))
                                                      done
                                                    done
                                                  done
                                                done
                                                subgoal
                                                  apply (simp add: zcount_sum)
                                                  apply (drule sum_pos_ex_elem_pos)
                                                  apply (elim bexE)
                                                  subgoal for nid''
                                                    apply simp
                                                    apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                                    apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                                    subgoal
                                                      apply (elim exE conjE)
                                                      using prems(13) apply -
                                                      apply (drule spec[of _ nid])
                                                      apply (drule spec[of _ nid''])
                                                      apply simp
                                                      unfolding changes_above_impl_inv_def
                                                      subgoal for p2' m'
                                                        apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                        subgoal
                                                          apply (subst obtain_progress_def)
                                                          apply (subst extract_progress_def)
                                                          apply (auto simp add: set_map_filter image_iff split_beta )
                                                          apply (rule bexI[rotated])
                                                          apply (clarsimp split: option.splits)
                                                          apply force
                                                          apply (clarsimp split: option.splits)
                                                          done
                                                        apply simp
                                                        apply (drule frontier_less_equal_ifrontierE)
                                                        using prems(2) apply assumption
                                                        apply clarsimp
                                                        unfolding frontier_less_equal_iff2
                                                        apply clarsimp
                                                        apply hypsubst_thin
                                                        subgoal for l  s'''' t6 t6'
                                                          apply (drule bspec[of _ _ l])
                                                          subgoal
                                                            apply (cases l)
                                                            apply simp
                                                            subgoal for nn pp
                                                              apply (cases pp)
                                                              apply simp_all
                                                              apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                              done
                                                            done
(* here7b *)
                                                          apply (subgoal_tac "\<exists> t6\<le>ft3. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p2))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9
                                                    apply (drule graph.path_weight_elem_trans[rotated , of s''''  _ _ _ t9])
                                                    apply simp
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply clarsimp
                                                          subgoal for u
                                                            apply (drule graph.path_weight_elem_trans[rotated, of u  _ _ _ s' "Loc nid' (Src p')"])
                                                            apply assumption
                                                            subgoal
                                                              apply (rule dataflow_topology.axioms(1))
                                                              apply (rule prems(2))
                                                              done
                                                            apply clarsimp
                                                            subgoal for u'
                                                              apply (drule spec[of _ "t6' -+- u'"])
                                                              apply (drule mp)
                                                              subgoal
                                                                apply (rule dataflow_topology_from_tree.sum_pos)
                                                                apply (simp_all flip: member_antichain.rep_eq)
                                                                apply (rule pos_zcount_image_zmset)
                                                                apply clarsimp
                                                                apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                                done
                                                              subgoal 
                                                                by (smt (verit, ccfv_threshold) add.commute add.left_commute add_le_cancel_left order_le_less_subst2)
                                                              done
                                                            done
                                                          done
                                                        done
                                                      done
                                                    done
                                                    subgoal
                                                      apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                      apply (drule sum_list_pos_ex_elem_pos)
                                                      apply (elim bexE)
                                                      apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                      apply (metis not_Some_eq2)
                                                      apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                                      apply fast
                                                      apply blast
                                                      done
                                                    done
                                                  done
                                                done
                                              done 
                                            done
                                          subgoal
                                            apply simp
                                            apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes_diff simp flip: member_antichain.rep_eq)
                                            apply (drule bspec[of _ _ "Loc nid2 (Src p2)"])
                                            apply fast
                                            apply (drule spec[of _ "ft4 -+- s'"])
                                            apply (drule mp)
                                            subgoal
                                              apply (rule dataflow_topology_from_tree.sum_pos)
                                              apply (simp_all flip: member_antichain.rep_eq)
                                              apply (rule pos_zcount_image_zmset)
                                              apply clarsimp
                                              apply clarsimp
                                              apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes_diff simp flip: member_antichain.rep_eq)
                                              done
                                            subgoal
                                              by auto
                                            done
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          subgoal
                            apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff simp flip: member_antichain.rep_eq)
                            apply (subst (asm) in_frontier_zmset_image)
                            apply clarsimp+
                            subgoal for ft2
                              apply (rule exI[of _ "ft2 -+- s"])
                              apply simp
                              apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
                              using prems(2) apply assumption
                              apply simp
                              apply (rule in_frontier_SumI[where a="Loc nid3 (Trg p3)"])
                              apply simp_all
                              subgoal
                                apply (rule in_frontier_SumI[where a=s])
                                apply simp_all
                                subgoal
                                  apply (subst in_frontier_zmset_image)
                                  apply clarsimp
                                  apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff simp flip: member_antichain.rep_eq)
                                  done
                                subgoal
                                  by (simp flip: member_antichain.rep_eq)
                                subgoal
                                  apply clarsimp
                                  apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff simp flip: member_antichain.rep_eq)
                                  done
                                done
                              apply fast
                              subgoal
                                apply clarsimp
                                apply (metis AP_simp dataflow_topology.after_summary_nonneg prems(2) zmset_of_mset_set_ge_zero)
                                done
                              subgoal
                                apply (clarsimp simp add: zcount_sum image_iff)
                                apply (drule sum_pos_ex_elem_pos)
                                apply clarsimp
                                subgoal for l t2 s'
                                  apply (elim disjE conjE exE; simp)
                                  subgoal for nid4 p4
                                    apply hypsubst_thin
                                    apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff simp flip: member_antichain.rep_eq)
                                    apply (cases "nid4 = nid \<and> p4 = p")
                                    subgoal
                                      apply clarsimp
                                      apply hypsubst_thin
                                      apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt simp flip: member_antichain.rep_eq)
                                      apply (drule zcount_zimageD)
                                      apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt add_diff_eq simp flip: member_antichain.rep_eq)
                                      apply (drule in_frontier_minusD)
                                      apply simp
                                      apply clarsimp
                                      subgoal for ft4 ft5
                                        apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                        apply fast
                                        apply (drule spec[of _ "ft5 -+- s'"])
                                        apply (drule mp)
                                        back
                                        back
                                        subgoal
                                          apply (rule dataflow_topology_from_tree.sum_pos)

                                          apply (simp_all flip: member_antichain.rep_eq)
                                          apply (rule pos_zcount_image_zmset)
                                          apply clarsimp
                                          apply clarsimp

                                          apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff add_diff_eq simp flip: member_antichain.rep_eq)
                                          done
                                        subgoal
                                          by (metis add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                        done
                                      done
                                    subgoal
                                      apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff add_diff_eq simp flip: member_antichain.rep_eq)
                                      apply (drule zcount_zimageD)
                                      apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff add_diff_eq simp flip: member_antichain.rep_eq)
                                      subgoal for ft5
                                        apply hypsubst_thin
                                        apply (drule bspec[of _ _ "Loc nid4 (Trg p4)"])
                                        apply fast
                                        apply (drule spec[of _ "ft5 -+- s'"])
                                        apply (drule mp)
                                        back
                                        back
                                        back
                                        subgoal
                                          apply (rule dataflow_topology_from_tree.sum_pos)

                                          apply (simp_all flip: member_antichain.rep_eq)
                                          apply (rule pos_zcount_image_zmset)
                                          apply clarsimp
                                          apply clarsimp

                                          apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff add_diff_eq simp flip: member_antichain.rep_eq)
                                          done
                                        subgoal
                                          by auto
                                        done
                                      done
                                    done
                                  subgoal for nid4 p4
                                    apply hypsubst_thin
                                    apply (cases "nid4 = nid")
                                    subgoal
                                      apply hypsubst_thin
                                      apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes simp flip: member_antichain.rep_eq)
                                      apply (drule zcount_zimageD)
                                      apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes simp flip: add.assoc member_antichain.rep_eq)
                                      subgoal for ft3
                                        apply (drule in_frontier_addD)
                                        back
                                        apply (elim exE disjE; clarsimp)
                                        subgoal for ft5
                                          apply (drule bspec[of _ _ "Loc nid (Src p4)"])
                                          apply fast
                                          apply (drule spec[of _ "ft5 -+- s'"])
                                          apply (drule mp)
                                          back
                                          subgoal
                                            apply (rule dataflow_topology_from_tree.sum_pos)
                                            apply simp
                                            apply (simp flip: member_antichain.rep_eq)
                                            unfolding member_antichain.rep_eq[symmetric]
                                            apply assumption
                                            apply (rule pos_zcount_image_zmset)
                                            apply clarsimp
                                            apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                            done
                                          subgoal
                                            by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                          done
                                        subgoal for ft3 ft5
                                          apply hypsubst_thin
                                          using premst apply -
                                          apply (elim disjE)
                                          subgoal
                                            apply (drule zcount_gt_0_in_frontierD)
                                            apply clarsimp
                                            subgoal for ft'
                                              apply (subgoal_tac "\<exists> t6\<le>ft3. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p4))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                  apply clarsimp
                                                  subgoal for t7
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s' _ _ _ t7 "Loc nid (Trg p)"])
                                              subgoal
                                                apply (rule dataflow_topology.axioms(1))
                                                apply (rule prems(2))
                                                done
                                              subgoal 
                                                using prems(3)
                                                unfolding graph_summar_nt_def
                                                by metis
                                              apply clarsimp
                                              subgoal for u
                                                apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                apply (simp_all flip: member_antichain.rep_eq)
                                                apply fast
                                                apply (drule spec[of _ "ft' -+- u"])
                                                apply (drule mp)
                                                back
                                                subgoal
                                                  apply (rule dataflow_topology_from_tree.sum_pos)
                                                  apply simp
                                                  apply (simp flip: member_antichain.rep_eq)
                                                  unfolding member_antichain.rep_eq[symmetric]
                                                  apply assumption
                                                  apply (rule pos_zcount_image_zmset)
                                                  apply clarsimp
                                                  apply (clarsimp simp flip: member_antichain.rep_eq)
                                                  done
                                                subgoal 
                                                  by (smt (verit, ccfv_threshold) add.commute add.left_commute add_le_cancel_left order_le_less_subst2)
                                                done
                                              done
                                            done
                                          done
                                          subgoal
                                            apply (simp add: zcount_sum)
                                            apply (drule sum_pos_ex_elem_pos)
                                            apply (elim bexE)
                                            subgoal for nid''
                                              apply simp
                                              apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                              apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                              subgoal
                                                apply (elim exE conjE)
                                                using prems(13) apply -
                                                apply (drule spec[of _ nid])
                                                apply (drule spec[of _ nid''])
                                                apply simp
                                                unfolding changes_above_impl_inv_def
                                                subgoal for p3 m'
                                                  apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                  subgoal
                                                    (* here4b *)
                                                    apply (subst obtain_progress_def)
                                                    apply (subst extract_progress_def)
                                                    apply (auto simp add: set_map_filter image_iff split_beta )
                                                    apply (rule bexI[rotated])
                                                    apply (clarsimp split: option.splits)
                                                    apply force
                                                    apply (clarsimp split: option.splits)+
                                                    apply (rule bexI[rotated])
                                                    apply (clarsimp split: option.splits)+
                                                    apply force
                                                    apply (clarsimp split: option.splits)+
                                                    done
                                                  apply simp
                                                  apply (drule frontier_less_equal_ifrontierE)
                                                  using prems(2) apply assumption
                                                  apply clarsimp
                                                  unfolding frontier_less_equal_iff2
                                                  apply clarsimp
                                                  apply hypsubst_thin
                                                  subgoal for l  s'''' t6 t6'
                                                    apply (drule bspec[of _ _ l])
                                                    subgoal
                                                      apply (cases l)
                                                      apply simp
                                                      subgoal for nn pp
                                                        apply (cases pp)
                                                        apply simp_all
                                                        apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                        done
                                                      done
                                                    apply (subgoal_tac "\<exists> t6\<le>ft3. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p4))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9
                                                    apply (drule graph.path_weight_elem_trans[rotated , of s''''  _ _ _ t9])
                                                    apply simp
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply clarsimp
                                                    subgoal for u
                                                      apply (drule graph.path_weight_elem_trans[rotated, of u  _ _ _ s' "Loc nid' (Src p')"])
                                                      apply assumption
                                                      subgoal
                                                        apply (rule dataflow_topology.axioms(1))
                                                        apply (rule prems(2))
                                                        done
                                                      apply clarsimp
                                                      subgoal for u'
                                                        apply (drule spec[of _ "t6' -+- u'"])
                                                        apply (drule mp)
                                                        back
                                                        subgoal
                                                          apply (rule dataflow_topology_from_tree.sum_pos)
                                                          apply (simp_all flip: member_antichain.rep_eq)
                                                          apply (rule pos_zcount_image_zmset)
                                                          apply clarsimp
                                                          apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                          done
                                                        subgoal 
                                                          by (smt (verit, ccfv_threshold) add.commute add.left_commute add_le_cancel_left order_le_less_subst2)
                                                        done
                                                      done
                                                    done
                                                  done
                                                done
                                              done
                                              subgoal
                                                (* here2! *)
                                                apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                apply (drule sum_list_pos_ex_elem_pos)
                                                apply (elim bexE)
                                                apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                apply (metis not_Some_eq2)
                                                apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                                apply fast
                                                apply blast
                                                done
                                              done
                                            done
                                          done
                                        done
                                      done
                                    subgoal
                                      apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes_diff simp flip: member_antichain.rep_eq)
                                      apply (drule bspec[of _ _ "Loc nid4 (Src p4)"])
                                      apply fast
                                      apply (drule zcount_zimageD)
                                      apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes_diff simp flip: member_antichain.rep_eq)
                                      subgoal for ft5 
                                        apply (drule spec[of _ "ft5 -+- s'"])
                                        apply (drule mp)
                                        back
                                        subgoal
                                          apply (rule dataflow_topology_from_tree.sum_pos)
                                          apply simp
                                          apply (simp flip: member_antichain.rep_eq)
                                          unfolding member_antichain.rep_eq[symmetric]
                                          apply assumption
                                          apply (rule pos_zcount_image_zmset)
                                          apply clarsimp
                                          apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                          done
                                        apply auto
                                        done
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          done
                        done
                      subgoal for l
                        apply (cases l; clarsimp)
                        subgoal for nid3 p3
                          apply (cases "nid3 = nid")
                          subgoal
                            apply clarsimp
                            apply hypsubst_thin
                            apply (subst (asm) in_frontier_zmset_image)
                            apply clarsimp+
                            subgoal for ft2
                              apply (simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes)
                              apply hypsubst_thin
                              apply (cases "ft2 = t")
                              subgoal
                                apply hypsubst_thin
                                apply (rule exI[of _ "t -+- s"])
                                apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
                                using prems(2) apply assumption
                                apply (intro conjI[rotated])
                                apply simp
                                apply (rule in_frontier_SumI[where a="Loc nid (Src p3)"])
                                apply simp_all
                                subgoal
                                  apply (rule in_frontier_SumI[where a="s"])
                                  apply simp_all
                                  subgoal
                                    apply (simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes)
                                    apply (subst in_frontier_zmset_image)
                                    apply (clarsimp simp flip: add.assoc)+
                                    apply (rule in_frontier_sumI1)
                                    apply assumption
                                    apply clarsimp
                                    subgoal
                                      apply clarsimp
                                      subgoal premises prems2
                                        using prems(4, 6) apply -
                                        unfolding Src_caps_inv_def
                                        apply (drule spec2[of _ nid p3])
                                        unfolding c_pts_inv_def
                                        apply (drule spec[of _ "Loc nid (Src p3)"])
                                        apply simp
                                        unfolding extract_prog_def
                                        apply (simp add: c_pts_change_multiplicities filter_concat comp_def map_concat zmset_concat sum_list_distinct_conv_sum_set)
                                        apply (subst (asm) comm_monoid_add_class.sum.subset_diff[of "{nid}"])
                                        apply simp_all
                                        apply (subst (asm) comm_monoid_add_class.sum.neutral)
                                        subgoal
                                          unfolding obtain_progress_def extract_progress_def
                                          apply (auto 0 0 simp add: List.map_filter_def filter_concat comp_def map_concat zmset_concat split_beta split: option.splits)
                                          done
                                        apply simp
                                        unfolding zmultiset_eq_iff
                                        apply simp
                                        apply (meson to_zmset_nenneg)
                                        done
                                      done
                                    subgoal
                                      apply clarsimp
                                      apply (meson to_zmset_nenneg)
                                      done
                                    done
                                  subgoal
                                    apply clarsimp

                                    subgoal for s'' tt
                                      apply (drule zcount_zimageD)
                                      apply clarsimp
                                      subgoal for t3
                                        apply (clarsimp simp add: zcount_sum c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes simp flip: member_antichain.rep_eq add.assoc)
                                        apply (drule in_frontier_addD[where t=t3])
                                        apply (elim exE conjE disjE)
                                        subgoal for t4
                                          apply (drule bspec[of _ _ "Loc nid (Src p3)"])
                                          apply fast
                                          apply (drule spec[of _ "t4 -+- s''"])
                                          apply (drule mp)
                                          subgoal
                                            apply (rule dataflow_topology_from_tree.sum_pos)
                                            apply simp
                                            apply (simp flip: member_antichain.rep_eq)
                                            unfolding member_antichain.rep_eq[symmetric]
                                            apply assumption
                                            back

                                            apply (rule pos_zcount_image_zmset)
                                            apply clarsimp
                                            apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                            done
                                          subgoal
                                            by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                          done
                                        subgoal for t4
                                          apply clarsimp
                                          subgoal for t5
                                            apply hypsubst_thin
                                            using premst apply -
                                            apply (elim disjE)
                                            subgoal
                                              apply (drule zcount_gt_0_in_frontierD)
                                              apply clarsimp
                                              subgoal for ft'
                                                apply (subgoal_tac "\<exists> t6\<le>t5. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p3))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s''  _ _ _ t9])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply assumption
                                                    apply clarsimp
                                                          subgoal for u
                                                  apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                  apply (simp_all flip: member_antichain.rep_eq)
                                                  apply fast
                                                  apply (drule spec[of _ "ft' -+- u"])
                                                  apply (drule mp)
                                                  subgoal
                                                    apply (rule dataflow_topology_from_tree.sum_pos)
                                                    apply simp
                                                    apply (simp flip: member_antichain.rep_eq)
                                                    unfolding member_antichain.rep_eq[symmetric]
                                                    apply assumption
                                                    apply (rule pos_zcount_image_zmset)
                                                    apply clarsimp
                                                    apply (clarsimp simp flip: member_antichain.rep_eq)
                                                    done
                                                  subgoal
                                                    by (smt (verit, ccfv_threshold) add.commute add.left_commute add_le_cancel_left order_le_less_subst2)
                                                  done
                                                done
                                              done
                                            done
                                            subgoal
                                              apply (simp add: zcount_sum)
                                              apply (drule sum_pos_ex_elem_pos)
                                              apply (elim bexE)
                                              subgoal for nid''
                                                apply simp
                                                apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                                apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                                subgoal
                                                  apply (elim exE conjE)
                                                  using prems(13) apply -
                                                  apply (drule spec[of _ nid])
                                                  apply (drule spec[of _ nid''])
                                                  apply simp
                                                  unfolding changes_above_impl_inv_def
                                                  subgoal for p3' m'
                                                    apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                    subgoal
                                                      (* here4b *)
                                                      apply (subst obtain_progress_def)
                                                      apply (subst extract_progress_def)
                                                      apply (auto simp add: set_map_filter image_iff split_beta )
                                                      apply (rule bexI[rotated])
                                                      apply (clarsimp split: option.splits)
                                                      apply force
                                                      apply (clarsimp split: option.splits)+
                                                      done
                                                    apply simp
                                                    apply (drule frontier_less_equal_ifrontierE)
                                                    using prems(2) apply assumption
                                                    apply clarsimp
                                                    unfolding frontier_less_equal_iff2
                                                    apply clarsimp
                                                    apply (subst (asm) (3) in_frontier_iff)
                                                    apply clarsimp
                                                    apply hypsubst_thin
                                                    subgoal for l  s''' t6 t6'
                                                      apply (drule bspec[of _ _ l])
                                                      subgoal
                                                        apply (cases l)
                                                        apply simp
                                                        subgoal for nn pp
                                                          apply (cases pp)
                                                          apply simp_all
                                                          apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                          done
                                                        done
(* here7c *)
                                                      apply (subgoal_tac "\<exists> t6\<le>t5. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p3))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s''  _ _ _ t9])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply assumption
                                                    apply clarsimp
                                                    subgoal for u
                                                        apply (drule graph.path_weight_elem_trans[rotated, of s'''  _ _ _ u])
                                                        apply assumption
                                                        subgoal
                                                          apply (rule dataflow_topology.axioms(1))
                                                          apply (rule prems(2))
                                                          done
                                                        apply clarsimp
                                                        subgoal for u'
                                                          apply (drule zcount_gt_0_in_frontierD)
                                                          apply clarsimp
                                                          subgoal for ft7
                                                            apply (drule spec[of _ "ft7 -+- u'"])
                                                            back
                                                            apply (drule mp)
                                                            subgoal
                                                              apply (rule dataflow_topology_from_tree.sum_pos)
                                                              apply (simp_all flip: member_antichain.rep_eq)
                                                              apply (rule pos_zcount_image_zmset)
                                                              apply clarsimp
                                                              apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                              done
                                                            subgoal
                                                              by (smt (verit, ccfv_threshold) add_less_le_mono add_mono_thms_linordered_semiring(2) add_strict_right_mono antisym_conv2 dataflow_topology_from_tree.followed_by_summary dataflow_topology_from_tree.plus_mono dual_order.strict_trans2
                                                                  nless_le)
                                                            done
                                                          done
                                                        done
                                                      done
                                                    done
                                                  done
                                                done
                                                subgoal
                                                  (* here2! *)
                                                  apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                  apply (drule sum_list_pos_ex_elem_pos)
                                                  apply (elim bexE)
                                                  apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                  apply (metis not_Some_eq2)
                                                  apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                                  apply fast
                                                  apply blast
                                                  done
                                                done
                                              done
                                            done
                                          done
                                        done
                                      done
                                    done
                                  done
                                apply fast
                                subgoal
                                  apply clarsimp
                                  apply (metis dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)
                                  done
                                subgoal
                                  apply clarsimp

                                  subgoal for l ft3
                                    apply (simp add: zcount_sum)
                                    apply (drule sum_pos_ex_elem_pos)
                                    apply clarsimp
                                    subgoal for s'
                                      apply (drule zcount_zimageD)
                                      apply (clarsimp simp add: image_iff simp flip: member_antichain.rep_eq)
                                      subgoal for ft4
                                        apply (cases l; clarsimp)
                                        apply (elim disjE exE)
                                        subgoal for nid2 _ p2 
                                          apply hypsubst_thin
                                          apply (cases "nid2 = nid \<and> p2 = p")
                                          subgoal
                                            apply (simp add: zcount_sum c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt add_diff_eq )

                                            apply (drule in_frontier_minusD)
                                            apply simp
                                            apply clarsimp
                                            subgoal for ft5
                                              apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                              apply fast
                                              apply (drule spec[of _ "ft5 -+- s'"])
                                              apply (drule mp)
                                              subgoal
                                                apply (rule dataflow_topology_from_tree.sum_pos)

                                                apply (simp_all flip: member_antichain.rep_eq)
                                                apply (rule pos_zcount_image_zmset)
                                                apply clarsimp
                                                apply clarsimp

                                                apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff add_diff_eq simp flip: member_antichain.rep_eq)
                                                done
                                              subgoal
                                                by (metis add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                              done
                                            done
                                          subgoal
                                            apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff add_diff_eq simp flip: member_antichain.rep_eq)
                                            apply (drule bspec[of _ _ "Loc nid2 (Trg p2)"])
                                            apply fast
                                            apply (drule spec[of _ "ft4 -+- s'"])
                                            apply (drule mp)
                                            back
                                            subgoal
                                              apply (rule dataflow_topology_from_tree.sum_pos)

                                              apply (simp_all flip: member_antichain.rep_eq)
                                              apply (rule pos_zcount_image_zmset)
                                              apply clarsimp
                                              apply clarsimp

                                              apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff add_diff_eq simp flip: member_antichain.rep_eq)
                                              done
                                            subgoal
                                              by auto
                                            done
                                          done
                                        subgoal for nid2 _ p2 
                                          apply hypsubst_thin


                                          apply (cases "nid2 = nid")
                                          subgoal
                                            apply hypsubst_thin
                                            apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes c_pts_change_multiplicities simp flip: add.assoc member_antichain.rep_eq)
                                            apply (drule in_frontier_addD[where t=ft4])
                                            apply (elim exE conjE disjE)
                                            subgoal for t4
                                              apply (drule bspec[of _ _ "Loc nid (Src p2)"])
                                              apply fast
                                              apply (drule spec[of _ "t4 -+- s'"])
                                              apply (drule mp)
                                              subgoal
                                                apply (rule dataflow_topology_from_tree.sum_pos)
                                                apply simp
                                                apply (simp flip: member_antichain.rep_eq)
                                                unfolding member_antichain.rep_eq[symmetric]
                                                apply assumption

                                                apply (rule pos_zcount_image_zmset)
                                                apply clarsimp
                                                apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                done
                                              subgoal
                                                by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                              done
                                            subgoal for ft2
                                              apply clarsimp
                                              subgoal for ft3
                                                apply hypsubst_thin
                                                using premst apply -
                                                apply (elim disjE)
                                                subgoal
                                                  apply (drule zcount_gt_0_in_frontierD)
                                                  apply clarsimp
                                                  subgoal for ft'
                                                    apply (subgoal_tac "\<exists> t6\<le>ft3. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p2))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s'  _ _ _ t9])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply assumption
                                                    apply clarsimp
                                                    subgoal for u

                                                      apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                      apply (simp_all flip: member_antichain.rep_eq)
                                                      apply fast
                                                      apply (drule spec[of _ "ft' -+- u"])
                                                      apply (drule mp)
                                                      subgoal
                                                        apply (rule dataflow_topology_from_tree.sum_pos)
                                                        apply simp
                                                        apply (simp flip: member_antichain.rep_eq)
                                                        unfolding member_antichain.rep_eq[symmetric]
                                                        apply assumption
                                                        apply (rule pos_zcount_image_zmset)
                                                        apply clarsimp
                                                        apply (clarsimp simp flip: member_antichain.rep_eq)
                                                        done
                                                      subgoal 
                                                        by (smt (verit, ccfv_threshold) add.commute add.left_commute add_le_cancel_left order_le_less_subst2)
                                                      done
                                                    done
                                                  done
                                                done
                                                subgoal
                                                  apply (simp add: zcount_sum)
                                                  apply (drule sum_pos_ex_elem_pos)
                                                  apply (elim bexE)
                                                  subgoal for nid''
                                                    apply simp
                                                    apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                                    apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                                    subgoal
                                                      apply (elim exE conjE)
                                                      using prems(13) apply -
                                                      apply (drule spec[of _ nid])
                                                      apply (drule spec[of _ nid''])
                                                      apply simp
                                                      unfolding changes_above_impl_inv_def
                                                      subgoal for p3' m'
                                                        apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                        subgoal
                                                          (* here4b *)
                                                          apply (subst obtain_progress_def)
                                                          apply (subst extract_progress_def)
                                                          apply (auto simp add: set_map_filter image_iff split_beta )
                                                          apply (rule bexI[rotated])
                                                          apply (clarsimp split: option.splits)
                                                          apply force
                                                          apply (clarsimp split: option.splits)+
                                                          done
                                                        apply simp
                                                        apply (drule frontier_less_equal_ifrontierE)
                                                        using prems(2) apply assumption
                                                        apply clarsimp
                                                        unfolding frontier_less_equal_iff2
                                                        apply clarsimp
                                                        apply hypsubst_thin
                                                        subgoal for l  s'''' t6 t6'
                                                          apply (drule bspec[of _ _ l])
                                                          subgoal
                                                            apply (cases l)
                                                            apply simp
                                                            subgoal for nn pp
                                                              apply (cases pp)
                                                              apply simp_all
                                                              apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                              done
                                                            done
                                                          apply (subgoal_tac "\<exists> t6\<le>ft3. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p2))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9
                                                    apply (drule graph.path_weight_elem_trans[rotated , of s''''  _ _ _ t9])
                                                    apply assumption
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply clarsimp
                                                    subgoal for u'
                                                      apply (drule graph.path_weight_elem_trans[rotated 2, of s'  _ _ _ u'])
                                                          subgoal
                                                            apply (rule dataflow_topology.axioms(1))
                                                            apply (rule prems(2))
                                                            done
                                                          apply assumption
                                                          apply clarsimp
                                                          subgoal for u'
                                                              apply (drule spec[of _ "t6' -+- u'"])
                                                              apply (drule mp)
                                                              subgoal
                                                                apply (rule dataflow_topology_from_tree.sum_pos)
                                                                apply (simp_all flip: member_antichain.rep_eq)
                                                                apply (rule pos_zcount_image_zmset)
                                                                apply clarsimp
                                                                apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                                done
                                                              subgoal
                                                                by (smt (verit, ccfv_threshold) add.commute add.left_commute add_le_cancel_left order_le_less_subst2)
                                                              done
                                                            done
                                                          done
                                                        done
                                                      done
                                                    done
                                                    subgoal
                                                      (* here2! *)
                                                      apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                      apply (drule sum_list_pos_ex_elem_pos)
                                                      apply (elim bexE)
                                                      apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                      apply (metis not_Some_eq2)
                                                      apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                                      apply fast
                                                      apply blast
                                                      done
                                                    done
                                                  done
                                                done
                                              done
                                            done
                                          subgoal
                                            apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: add.assoc member_antichain.rep_eq)
                                            apply (drule bspec[of _ _ "Loc nid2 (Src p2)"])
                                            apply fast
                                            apply (drule spec[of _ "ft4 -+- s'"])
                                            apply (drule mp)
                                            subgoal
                                              apply (rule dataflow_topology_from_tree.sum_pos)
                                              apply (simp_all flip: member_antichain.rep_eq)
                                              apply (rule pos_zcount_image_zmset)
                                              apply clarsimp
                                              apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                              done
                                            subgoal
                                              by auto
                                            done
                                          done
                                        done
                                      done
                                    done
                                  done
                                done

                              subgoal
                                apply (drule in_frontier_addEx[where B="to_zmset (map ((-+-) t) (intsum (os nid) p p3))"])
                                apply clarsimp
                                apply (meson to_zmset_nenneg)
                                apply clarsimp
                                subgoal for ft3
                                  apply (rule exI[of _ "ft3 -+- s"])
                                  apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
                                  using prems(2) apply assumption
                                  apply (intro conjI[rotated])
                                  apply (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(23))
                                  apply simp
                                  apply (rule in_frontier_SumI[where a="Loc nid (Src p3)"])
                                  apply simp_all
                                  subgoal
                                    apply (rule in_frontier_SumI[where a=s])
                                    apply simp_all
                                    subgoal
                                      apply (subst in_frontier_zmset_image)
                                      apply clarsimp
                                      subgoal
                                        apply (simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes add_diff_eq flip: add.assoc)
                                        done
                                      done
                                    subgoal
                                      apply clarsimp
                                      subgoal for s' tt
                                        apply (drule zcount_zimageD)
                                        apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes add_diff_eq simp flip: add.assoc member_antichain.rep_eq)
                                        apply hypsubst_thin
                                        subgoal for t3
                                          apply (clarsimp simp add: zcount_sum c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes simp flip: member_antichain.rep_eq add.assoc)
                                          apply (drule in_frontier_addD[where t=t3])
                                          apply (elim exE conjE disjE)
                                          subgoal for t4
                                            apply (drule bspec[of _ _ "Loc nid (Src p3)"])
                                            apply fast
                                            apply (drule spec[of _ "t4 -+- s'"])
                                            apply (drule mp)
                                            subgoal
                                              apply (rule dataflow_topology_from_tree.sum_pos)
                                              apply simp
                                              apply (simp flip: member_antichain.rep_eq)
                                              unfolding member_antichain.rep_eq[symmetric]
                                              apply assumption
                                              back

                                              apply (rule pos_zcount_image_zmset)
                                              apply clarsimp
                                              apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                              done
                                            subgoal
                                              by (smt (verit) add_mono_thms_linordered_semiring(3) basic_trans_rules(18,19))
                                            done

                                          subgoal for t4
                                            apply clarsimp
                                            subgoal for t5
                                              apply hypsubst_thin
                                              using premst apply -
                                              apply (elim disjE)
                                              subgoal
                                                apply (drule zcount_gt_0_in_frontierD)
                                                apply clarsimp
                                                subgoal for ft'
                                                  apply (subgoal_tac "\<exists> t6\<le>t5. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p3))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9


                                                  apply (drule graph.path_weight_elem_trans[rotated 2, of s' _ _ _ t9 "Loc nid (Trg p)"])
                                                  subgoal
                                                    apply (rule dataflow_topology.axioms(1))
                                                    apply (rule prems(2))
                                                    done
                                                  subgoal 
                                                    using prems(3)
                                                    unfolding graph_summar_nt_def
                                                    by metis
                                                  apply clarsimp
                                                  subgoal for u
                                                    apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                    apply (simp_all flip: member_antichain.rep_eq)
                                                    apply fast
                                                    apply (drule spec[of _ "ft' -+- u"])
                                                    apply (drule mp)
                                                    subgoal
                                                      apply (rule dataflow_topology_from_tree.sum_pos)
                                                      apply simp
                                                      apply (simp flip: member_antichain.rep_eq)
                                                      unfolding member_antichain.rep_eq[symmetric]
                                                      apply assumption
                                                      apply (rule pos_zcount_image_zmset)
                                                      apply clarsimp
                                                      apply (clarsimp simp flip: member_antichain.rep_eq)
                                                      done
                                                    subgoal premises temp
                                                      using temp(3,6,7,9,10,12,14,16,19,20)
                                                     by (metis (mono_tags, lifting) add_mono_thms_linordered_semiring(2,3) dataflow_topology_from_tree.followed_by_summary dual_order.strict_trans1 dual_order.strict_trans2)
                                                      done
                                                  done
                                                done
                                              done
                                              subgoal
                                                apply (simp add: zcount_sum)
                                                apply (drule sum_pos_ex_elem_pos)
                                                apply (elim bexE)
                                                subgoal for nid''
                                                  apply simp
                                                  apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                                  apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                                  subgoal
                                                    apply (elim exE conjE)
                                                    using prems(13) apply -
                                                    apply (drule spec[of _ nid])
                                                    apply (drule spec[of _ nid''])
                                                    apply simp
                                                    unfolding changes_above_impl_inv_def
                                                    subgoal for p3' m'
                                                      apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                      subgoal
                                                        (* here4b *)
                                                        apply (subst obtain_progress_def)
                                                        apply (subst extract_progress_def)
                                                        apply (auto simp add: set_map_filter image_iff split_beta )
                                                        apply (rule bexI[rotated])
                                                        apply (clarsimp split: option.splits)
                                                        apply force
                                                        apply (clarsimp split: option.splits)+
                                                        done
                                                      apply simp
                                                      apply (drule frontier_less_equal_ifrontierE)
                                                      using prems(2) apply assumption
                                                      apply clarsimp
                                                      unfolding frontier_less_equal_iff2
                                                      apply clarsimp
                                                      apply (subst (asm) (3) in_frontier_iff)
                                                      apply clarsimp
                                                      apply hypsubst_thin
                                                      subgoal for l  s''' t6 t6'
                                                        apply (drule bspec[of _ _ l])
                                                        subgoal
                                                          apply (cases l)
                                                          apply simp
                                                          subgoal for nn pp
                                                            apply (cases pp)
                                                            apply simp_all
                                                            apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                            done
                                                          done
                                                   apply (subgoal_tac "\<exists> t6\<le>t5. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p3))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s'  _ _ _ t9])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply assumption
                                                    apply clarsimp

                                                        subgoal for u
                                                          apply (drule graph.path_weight_elem_trans[rotated, of s''' _ _ _ u])
                                                          apply assumption
                                                          subgoal
                                                            apply (rule dataflow_topology.axioms(1))
                                                            apply (rule prems(2))
                                                            done
                                                          apply clarsimp
                                                          subgoal for u'
                                                            apply (drule zcount_gt_0_in_frontierD)
                                                            apply clarsimp
                                                            subgoal for ft7
                                                              apply (drule spec[of _ "ft7 -+- u'"])
                                                              back
                                                              apply (drule mp)
                                                              subgoal
                                                                apply (rule dataflow_topology_from_tree.sum_pos)
                                                                apply (simp_all flip: member_antichain.rep_eq)
                                                                apply (rule pos_zcount_image_zmset)
                                                                apply clarsimp
                                                                apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                                done
                                                              subgoal
                                                                by (smt (verit, ccfv_threshold) add_less_le_mono add_mono_thms_linordered_semiring(2) add_strict_right_mono antisym_conv2 dataflow_topology_from_tree.followed_by_summary dataflow_topology_from_tree.plus_mono dual_order.strict_trans2
                                                                    nless_le)
                                                              done
                                                            done
                                                          done
                                                        done
                                                      done
                                                    done
                                                  done
                                                  subgoal
                                                    (* here2! *)
                                                    apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                    apply (drule sum_list_pos_ex_elem_pos)
                                                    apply (elim bexE)
                                                    apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                    apply (metis not_Some_eq2)
                                                    apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                                    apply fast
                                                    apply blast
                                                    done
                                                  done
                                                done

                                              done
                                            done
                                          done
                                        done
                                      done
                                    done
                                  apply fast
                                  subgoal
                                    apply clarsimp
                                    apply (metis dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)
                                    done
                                  subgoal
                                    apply clarsimp                       

                                    subgoal for l tt
                                      apply (simp add: zcount_sum)
                                      apply (drule sum_pos_ex_elem_pos)
                                      apply clarsimp
                                      subgoal for s'
                                        apply (drule zcount_zimageD)
                                        apply (clarsimp simp add: image_iff simp flip: member_antichain.rep_eq)
                                        subgoal for ft4
                                          apply (cases l; clarsimp)
                                          apply (elim disjE exE)
                                          subgoal for nid2 _ p2 
                                            apply hypsubst_thin
                                            apply (cases "nid2 = nid \<and> p2 = p")
                                            subgoal
                                              apply (simp add: zcount_sum c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt add_diff_eq )

                                              apply (drule in_frontier_minusD)
                                              apply simp
                                              apply clarsimp
                                              subgoal for ft5
                                                apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                apply fast
                                                apply (drule spec[of _ "ft5 -+- s'"])
                                                apply (drule mp)
                                                subgoal
                                                  apply (rule dataflow_topology_from_tree.sum_pos)

                                                  apply (simp_all flip: member_antichain.rep_eq)
                                                  apply (rule pos_zcount_image_zmset)
                                                  apply clarsimp
                                                  apply clarsimp

                                                  apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff add_diff_eq simp flip: member_antichain.rep_eq)
                                                  done
                                                subgoal
                                                  by (meson add_right_mono basic_trans_rules(21,22))
                                                done
                                              done
                                            subgoal
                                              apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff add_diff_eq simp flip: member_antichain.rep_eq)
                                              apply (drule bspec[of _ _ "Loc nid2 (Trg p2)"])
                                              apply fast
                                              apply (drule spec[of _ "ft4 -+- s'"])
                                              apply (drule mp)
                                              back
                                              subgoal
                                                apply (rule dataflow_topology_from_tree.sum_pos)

                                                apply (simp_all flip: member_antichain.rep_eq)
                                                apply (rule pos_zcount_image_zmset)
                                                apply clarsimp
                                                apply clarsimp

                                                apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff add_diff_eq simp flip: member_antichain.rep_eq)
                                                done
                                              subgoal
                                                by (meson add_le_cancel_right basic_trans_rules(22))
                                              done
                                            done
                                          subgoal for nid2 _ p2 
                                            apply hypsubst_thin


                                            apply (cases "nid2 = nid")
                                            subgoal
                                              apply hypsubst_thin
                                              apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes c_pts_change_multiplicities simp flip: add.assoc member_antichain.rep_eq)
                                              apply (drule in_frontier_addD[where t=ft4])
                                              apply (elim exE conjE disjE)
                                              subgoal for t4
                                                apply (drule bspec[of _ _ "Loc nid (Src p2)"])
                                                apply fast
                                                apply (drule spec[of _ "t4 -+- s'"])
                                                apply (drule mp)
                                                subgoal
                                                  apply (rule dataflow_topology_from_tree.sum_pos)
                                                  apply simp
                                                  apply (simp flip: member_antichain.rep_eq)
                                                  unfolding member_antichain.rep_eq[symmetric]
                                                  apply assumption

                                                  apply (rule pos_zcount_image_zmset)
                                                  apply clarsimp
                                                  apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                  done
                                                subgoal
                                                  by (meson add_right_mono basic_trans_rules(21,22))
                                                done
                                              subgoal for ft2
                                                apply clarsimp
                                                subgoal for ft3
                                                  apply hypsubst_thin
                                                  using premst apply -
                                                  apply (elim disjE)
                                                  subgoal
                                                    apply (drule zcount_gt_0_in_frontierD)
                                                    apply clarsimp
                                                    subgoal for ft'
                                                      apply (subgoal_tac "\<exists> t6\<le>ft3. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p2))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s'  _ _ _ t9])
                                               subgoal
                                                        apply (rule dataflow_topology.axioms(1))
                                                        apply (rule prems(2))
                                                 done
                                               apply assumption
                                                      apply clarsimp
                                                      subgoal for u
                                                        apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                        apply (simp_all flip: member_antichain.rep_eq)
                                                        apply fast
                                                        apply (drule spec[of _ "ft' -+- u"])
                                                        apply (drule mp)
                                                        subgoal
                                                          apply (rule dataflow_topology_from_tree.sum_pos)
                                                          apply simp
                                                          apply (simp flip: member_antichain.rep_eq)
                                                          unfolding member_antichain.rep_eq[symmetric]
                                                          apply assumption
                                                          apply (rule pos_zcount_image_zmset)
                                                          apply clarsimp
                                                          apply (clarsimp simp flip: member_antichain.rep_eq)
                                                          done
                                                        subgoal premises temp
                                                          using temp(3,6,7,10,12,14,16,20-)
                                                          by (smt (verit, ccfv_SIG) add_mono_thms_linordered_semiring(2,3) dataflow_topology_from_tree.followed_by_summary dual_order.strict_trans1 dual_order.strict_trans2 temp(19))
                                                        done
                                                      done
                                                    done
                                                  done
                                                  subgoal
                                                    apply (simp add: zcount_sum)
                                                    apply (drule sum_pos_ex_elem_pos)
                                                    apply (elim bexE)
                                                    subgoal for nid''
                                                      apply simp
                                                      apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                                      apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                                      subgoal
                                                    apply (elim exE conjE)
                                                    using prems(13) apply -
                                                    apply (drule spec[of _ nid])
                                                    apply (drule spec[of _ nid''])
                                                    apply simp
                                                    unfolding changes_above_impl_inv_def
                                                    subgoal for p3' m'
                                                      apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                      subgoal
                                                        (* here4b *)
                                                        apply (subst obtain_progress_def)
                                                        apply (subst extract_progress_def)
                                                        apply (auto simp add: set_map_filter image_iff split_beta )
                                                        apply (rule bexI[rotated])
                                                        apply (clarsimp split: option.splits)
                                                        apply force
                                                        apply (clarsimp split: option.splits)+
                                                        done
                                                      apply simp
                                                      apply (drule frontier_less_equal_ifrontierE)
                                                      using prems(2) apply assumption
                                                      apply clarsimp
                                                      unfolding frontier_less_equal_iff2
                                                      apply clarsimp
                                                      apply (subst (asm) (3) in_frontier_iff)
                                                      apply clarsimp
                                                      apply hypsubst_thin
                                                      subgoal for l  s''' t6 t6'
                                                        apply (drule bspec[of _ _ l])
                                                        subgoal
                                                          apply (cases l)
                                                          apply simp
                                                          subgoal for nn pp
                                                            apply (cases pp)
                                                            apply simp_all
                                                            apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                            done
                                                          done
                                                   apply (subgoal_tac "\<exists> t6\<le>ft3. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p2))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s'  _ _ _ t9])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply assumption
                                                    apply clarsimp

                                                        subgoal for u
                                                          apply (drule graph.path_weight_elem_trans[rotated, of s''' _ _ _ u])
                                                          apply assumption
                                                          subgoal
                                                            apply (rule dataflow_topology.axioms(1))
                                                            apply (rule prems(2))
                                                            done
                                                          apply clarsimp
                                                          subgoal for u'
                                                            apply (drule zcount_gt_0_in_frontierD)
                                                            apply clarsimp
                                                            subgoal for ft7
                                                              apply (drule spec[of _ "ft7 -+- u'"])
                                                              back
                                                              apply (drule mp)
                                                              subgoal
                                                                apply (rule dataflow_topology_from_tree.sum_pos)
                                                                apply (simp_all flip: member_antichain.rep_eq)
                                                                apply (rule pos_zcount_image_zmset)
                                                                apply clarsimp
                                                                apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                                done
                                                              subgoal
                                                                by (smt (verit, ccfv_threshold) add_less_le_mono add_mono_thms_linordered_semiring(2) add_strict_right_mono antisym_conv2 dataflow_topology_from_tree.followed_by_summary dataflow_topology_from_tree.plus_mono dual_order.strict_trans2
                                                                    nless_le)
                                                              done
                                                            done
                                                          done
                                                        done
                                                      done
                                                    done
                                                  done
                                                      subgoal
                                                        (* here2! *)
                                                        apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                        apply (drule sum_list_pos_ex_elem_pos)
                                                        apply (elim bexE)
                                                        apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                        apply (metis not_Some_eq2)
                                                        apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                                        apply fast
                                                        apply blast
                                                        done
                                                      done
                                                    done
                                                  done
                                                done
                                              done
                                            subgoal
                                              apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: add.assoc member_antichain.rep_eq)
                                              apply (drule bspec[of _ _ "Loc nid2 (Src p2)"])
                                              apply fast
                                              apply (drule spec[of _ "ft4 -+- s'"])
                                              apply (drule mp)
                                              subgoal
                                                apply (rule dataflow_topology_from_tree.sum_pos)
                                                apply (simp_all flip: member_antichain.rep_eq)
                                                apply (rule pos_zcount_image_zmset)
                                                apply clarsimp
                                                apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                done
                                              subgoal
                                                by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(22))
                                              done
                                            done
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          subgoal
                            apply hypsubst_thin
                            apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                            apply (subst (asm) in_frontier_zmset_image)
                            apply clarsimp+
                            apply (rule exI[of _ ft])
                            apply simp
                            subgoal for tt
                              apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
                              using prems(2) apply assumption
                              apply simp
                              apply (rule in_frontier_SumI[where a="Loc nid3 (Src p3)"])
                              apply simp_all
                              subgoal
                                apply (rule in_frontier_SumI[where a=s])
                                apply simp_all
                                subgoal
                                  apply (subst in_frontier_zmset_image)
                                  apply clarsimp
                                  subgoal
                                    apply (simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes_diff add_diff_eq flip: add.assoc)
                                    done
                                  done
                                apply (simp flip: member_antichain.rep_eq)
                                subgoal
                                  apply clarsimp
                                  subgoal for s' t''
                                    apply (drule zcount_zimageD)
                                    apply (simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes_diff add_diff_eq flip: add.assoc member_antichain.rep_eq)
                                    apply (drule bspec[of _ _ "Loc nid3 (Src p3)"])
                                    apply fast
                                    apply (clarsimp simp add: zcount_sum c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes_diff add_diff_eq simp flip: add.assoc member_antichain.rep_eq)
                                    subgoal for ft3
                                      apply (drule spec[of _ "ft3 -+- s'"])
                                      apply (drule mp)
                                      subgoal

                                        apply (rule dataflow_topology_from_tree.sum_pos)
                                        apply simp
                                        apply clarsimp
                                        unfolding member_antichain.rep_eq[symmetric]
                                        apply assumption
                                        back
                                        apply (rule pos_zcount_image_zmset)
                                        apply clarsimp
                                        apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                        done
                                      subgoal
                                        by auto
                                      done
                                    done
                                  done
                                done
                              apply fast
                              subgoal
                                apply clarsimp
                                apply (metis dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)
                                done
                              subgoal
                                apply clarsimp
                                subgoal l for l ft3
                                  apply (simp add: zcount_sum)
                                  apply (drule sum_pos_ex_elem_pos)
                                  apply clarsimp
                                  subgoal for s'
                                    apply (drule zcount_zimageD)
                                    apply (clarsimp simp add: image_iff simp flip: member_antichain.rep_eq)
                                    subgoal for ft4
                                      apply (cases l; clarsimp)
                                      apply (elim disjE exE)
                                      subgoal for nid2 _ p2 
                                        apply hypsubst_thin
                                        apply (cases "nid2 = nid \<and> p2 = p")
                                        subgoal
                                          apply (simp add: zcount_sum c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt add_diff_eq )

                                          apply (drule in_frontier_minusD)
                                          apply simp
                                          apply clarsimp
                                          subgoal for ft5
                                            apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                            apply fast
                                            apply (drule spec[of _ "ft5 -+- s'"])
                                            apply (drule mp)
                                            subgoal
                                              apply (rule dataflow_topology_from_tree.sum_pos)

                                              apply (simp_all flip: member_antichain.rep_eq)
                                              apply (rule pos_zcount_image_zmset)
                                              apply clarsimp
                                              apply clarsimp

                                              apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff add_diff_eq simp flip: member_antichain.rep_eq)
                                              done
                                            subgoal
                                              by (metis add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                            done
                                          done
                                        subgoal
                                          apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff add_diff_eq simp flip: member_antichain.rep_eq)
                                          apply (drule bspec[of _ _ "Loc nid2 (Trg p2)"])
                                          apply fast
                                          apply (drule spec[of _ "ft4 -+- s'"])
                                          apply (drule mp)
                                          back
                                          subgoal
                                            apply (rule dataflow_topology_from_tree.sum_pos)

                                            apply (simp_all flip: member_antichain.rep_eq)
                                            apply (rule pos_zcount_image_zmset)
                                            apply clarsimp
                                            apply clarsimp

                                            apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff add_diff_eq simp flip: member_antichain.rep_eq)
                                            done
                                          subgoal
                                            by auto
                                          done
                                        done
                                      subgoal for nid2 _ p2 
                                        apply hypsubst_thin


                                        apply (cases "nid2 = nid")
                                        subgoal
                                          apply hypsubst_thin
                                          apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes c_pts_change_multiplicities simp flip: add.assoc member_antichain.rep_eq)
                                          apply (drule in_frontier_addD[where t=ft4])
                                          apply (elim exE conjE disjE)
                                          subgoal for t4
                                            apply (drule bspec[of _ _ "Loc nid (Src p2)"])
                                            apply fast
                                            apply (drule spec[of _ "t4 -+- s'"])
                                            apply (drule mp)
                                            subgoal
                                              apply (rule dataflow_topology_from_tree.sum_pos)
                                              apply simp
                                              apply (simp flip: member_antichain.rep_eq)
                                              unfolding member_antichain.rep_eq[symmetric]
                                              apply assumption

                                              apply (rule pos_zcount_image_zmset)
                                              apply clarsimp
                                              apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                              done
                                            subgoal
                                              by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                            done
                                          subgoal for ft2
                                            apply clarsimp
                                            subgoal for ft3
                                              apply hypsubst_thin
                                              using premst apply -
                                              apply (elim disjE)
                                              subgoal
                                                apply (drule zcount_gt_0_in_frontierD)
                                                apply clarsimp
                                                subgoal for ft'
                                                  apply (subgoal_tac "\<exists> t6\<le>ft3. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p2))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t6
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s' _ _ _ t6 "Loc nid (Trg p)"])
                                                  subgoal
                                                    apply (rule dataflow_topology.axioms(1))
                                                    apply (rule prems(2))
                                                    done
                                                  subgoal 
                                                    using prems(3)
                                                    unfolding graph_summar_nt_def
                                                    by metis
                                                  apply clarsimp
                                                  subgoal for u
                                                    apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                    apply (simp_all flip: member_antichain.rep_eq)
                                                    apply fast
                                                    apply (drule spec[of _ "ft' -+- u"])
                                                    apply (drule mp)
                                                    subgoal
                                                      apply (rule dataflow_topology_from_tree.sum_pos)
                                                      apply simp
                                                      apply (simp flip: member_antichain.rep_eq)
                                                      unfolding member_antichain.rep_eq[symmetric]
                                                      apply assumption
                                                      apply (rule pos_zcount_image_zmset)
                                                      apply clarsimp
                                                      apply (clarsimp simp flip: member_antichain.rep_eq)
                                                      done
                                                    subgoal 
                                                                by (smt (verit, ccfv_threshold) add.commute add.left_commute add_le_cancel_left order_le_less_subst2)
                                                    done
                                                  done
                                                done
                                              done
                                              subgoal
                                                apply (simp add: zcount_sum)
                                                apply (drule sum_pos_ex_elem_pos)
                                                apply (elim bexE)
                                                subgoal for nid''
                                                  apply simp
                                                  apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                                  apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                                  subgoal
                                                    apply (elim exE conjE)
                                                    using prems(13) apply -
                                                    apply (drule spec[of _ nid])
                                                    apply (drule spec[of _ nid''])
                                                    apply simp
                                                    unfolding changes_above_impl_inv_def
                                                    subgoal for p3' m'
                                                      apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                      subgoal
                                                        (* here4b *)
                                                        apply (subst obtain_progress_def)
                                                        apply (subst extract_progress_def)
                                                        apply (auto simp add: set_map_filter image_iff split_beta )
                                                        apply (rule bexI[rotated])
                                                        apply (clarsimp split: option.splits)
                                                        apply force
                                                        apply (clarsimp split: option.splits)+
                                                        done
                                                      apply simp
                                                      apply (drule frontier_less_equal_ifrontierE)
                                                      using prems(2) apply assumption
                                                      apply clarsimp
                                                      unfolding frontier_less_equal_iff2
                                                      apply clarsimp
                                                      apply (subst (asm) (3) in_frontier_iff)
                                                      apply clarsimp
                                                      apply hypsubst_thin
                                                      subgoal for l  s''' t6 t6'
                                                        apply (drule bspec[of _ _ l])
                                                        subgoal
                                                          apply (cases l)
                                                          apply simp
                                                          subgoal for nn pp
                                                            apply (cases pp)
                                                            apply simp_all
                                                            apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                            done
                                                          done
                                                   apply (subgoal_tac "\<exists> t6\<le>ft3. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p2))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s'  _ _ _ t9])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply assumption
                                                    apply clarsimp

                                                        subgoal for u
                                                          apply (drule graph.path_weight_elem_trans[rotated, of s''' _ _ _ u])
                                                          apply assumption
                                                          subgoal
                                                            apply (rule dataflow_topology.axioms(1))
                                                            apply (rule prems(2))
                                                            done
                                                          apply clarsimp
                                                          subgoal for u'
                                                            apply (drule zcount_gt_0_in_frontierD)
                                                            apply clarsimp
                                                            subgoal for ft7
                                                              apply (drule spec[of _ "ft7 -+- u'"])
                                                              back
                                                              apply (drule mp)
                                                              subgoal
                                                                apply (rule dataflow_topology_from_tree.sum_pos)
                                                                apply (simp_all flip: member_antichain.rep_eq)
                                                                apply (rule pos_zcount_image_zmset)
                                                                apply clarsimp
                                                                apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                                done
                                                              subgoal
                                                                by (smt (verit, ccfv_threshold) add_less_le_mono add_mono_thms_linordered_semiring(2) add_strict_right_mono antisym_conv2 dataflow_topology_from_tree.followed_by_summary dataflow_topology_from_tree.plus_mono dual_order.strict_trans2
                                                                    nless_le)
                                                              done
                                                            done
                                                          done
                                                        done
                                                      done
                                                    done
                                                  done
                                                  subgoal
                                                    (* here2! *)
                                                    apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                    apply (drule sum_list_pos_ex_elem_pos)
                                                    apply (elim bexE)
                                                    apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                    apply (metis not_Some_eq2)
                                                    apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                                    apply fast
                                                    apply blast
                                                    done
                                                  done
                                                done
                                              done
                                            done
                                          done
                                        subgoal
                                          apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: add.assoc member_antichain.rep_eq)
                                          apply (drule bspec[of _ _ "Loc nid2 (Src p2)"])
                                          apply fast
                                          apply (drule spec[of _ "ft4 -+- s'"])
                                          apply (drule mp)
                                          back
                                          subgoal
                                            apply (rule dataflow_topology_from_tree.sum_pos)
                                            apply (simp_all flip: member_antichain.rep_eq)
                                            apply (rule pos_zcount_image_zmset)
                                            apply clarsimp
                                            apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                            done
                                          subgoal
                                            by auto
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          done
                        done
                      done
                    done
                  done
                subgoal premises prems4
                  using prems3 apply -
                  apply (subst (asm) extract_progress_def)
                  apply (subst (asm) (1 2 3) obtain_progress_def)
                  apply (clarsimp simp add: split_beta image_iff)
                  apply (elim disjE conjE bexE)
                    (* subgoal_consu *) 
                  subgoal for X
                    apply (cases X)
                    apply (clarsimp simp add: split_beta image_iff)
                    subgoal for  p' m
                      apply hypsubst_thin
                      apply (subst (asm) Propagate.dataflow_topology.implied_frontier_alt_def)
                      using prems(2) apply assumption
                      unfolding frontier_less_equal_iff2
                      apply clarsimp
                      subgoal for ft
                        apply (cases "\<exists> s p'' t''. t'' \<in> set (intsum (os nid) p p'') \<and>
                             s \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Src p'')) (Loc nid' (Trg p')) \<and> ft = t -+- t'' -+- s")
                        subgoal
                          apply clarsimp
                          subgoal for s p'' t''
                            apply (rule exI[of _ ft])
                            apply simp_all
                            apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
                            using prems(2) apply assumption
                            apply (rule in_frontier_SumI[where a="Loc nid (Src p'')"])
                            apply simp_all
                            subgoal
                              apply (simp add: c_pts_change_multiplicities)
                              apply (subst zmset_filter_extract_progress_Src_consumes)
                              apply (subst add.assoc[symmetric])
                              apply (rule in_frontier_SumI[where a=s])
                              apply (simp_all flip: member_antichain.rep_eq)
                              subgoal
                                apply (subst in_frontier_zmset_image)
                                apply clarsimp
                                apply simp
                                apply (rule in_frontier_sumI2)
                                apply simp_all
                                subgoal
                                  apply (simp add: to_zmset_map)
                                  apply (subgoal_tac "t'' \<in>\<^sub>A frontier (to_zmset (intsum (os nid) p p''))")
                                  subgoal
                                    using in_frontier_zmset_image
                                    by (smt (verit, ccfv_threshold) add_left_cancel canonically_ordered_monoid_add_class.lessE dataflow_topology_from_tree.followed_by_summary in_frontier_iff less_add_same_cancel1 pos_image_zmset_obtain_pre
                                        pos_zcount_image_zmset to_zmset_nenneg)
                                  find_theorems frontier image_zmset
                                  subgoal
                                    using prems(3) apply -
                                    unfolding graph_summar_nt_def
                                    apply clarsimp
                                    apply (meson in_frontier_iff zcount_to_zmset_gt_0)
                                    done
                                  done
                                subgoal
                                  apply safe
                                  subgoal for tt
                                    apply hypsubst_thin
                                    apply (simp flip: zcount_union)
                                    apply (drule zcount_gt_0_in_frontierD)
                                    apply clarsimp
                                    subgoal for tt'
                                      apply (drule in_frontier_Sum_all_not_lt)
                                      subgoal
                                        apply clarsimp
                                        apply (metis dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)
                                        done
                                      subgoal
                                        apply (drule bspec[of _ _ "Loc nid (Src p'')"])
                                        apply simp_all
                                        apply force
                                        apply (drule spec[of _ "tt' -+- s"])
                                        apply (drule mp)
                                        subgoal
                                          apply (simp add: zcount_sum)
                                          apply (rule Timely_Infrastructure.dataflow_topology_from_tree.sum_pos[of _ _ s])
                                          apply (simp_all flip: member_antichain.rep_eq)
                                          apply (rule pos_zcount_image_zmset)
                                          apply (simp_all flip: member_antichain.rep_eq)
                                          done
                                        subgoal by auto
                                        done
                                      done
                                    done
                                  done
                                subgoal premises prems2
                                  using prems(4, 6) apply -
                                  unfolding Src_caps_inv_def
                                  apply (drule spec2[of _ nid p''])
                                  unfolding c_pts_inv_def
                                  apply (drule spec[of _ "Loc nid (Src p'')"])
                                  apply simp
                                  unfolding extract_prog_def
                                  apply (simp add: c_pts_change_multiplicities filter_concat comp_def map_concat zmset_concat sum_list_distinct_conv_sum_set)
                                  apply (subst (asm) comm_monoid_add_class.sum.subset_diff[of "{nid}"])
                                  apply simp_all
                                  apply (subst (asm) comm_monoid_add_class.sum.neutral)
                                  subgoal
                                    unfolding obtain_progress_def extract_progress_def
                                    apply (auto 0 0 simp add: List.map_filter_def filter_concat comp_def map_concat zmset_concat split_beta split: option.splits)
                                    done
                                  apply simp
                                  unfolding zmultiset_eq_iff
                                  apply simp
                                  apply (meson to_zmset_nenneg)
                                  done
                                subgoal
                                  apply clarsimp
                                  apply (meson to_zmset_nenneg)
                                  done
                                done
                              subgoal
                                apply safe
                                subgoal for s' tt
                                  apply (simp flip: member_antichain.rep_eq)
                                  apply hypsubst_thin
                                  apply (drule zcount_zimageD)
                                  apply (clarsimp simp flip: member_antichain.rep_eq)
                                  subgoal for t2
                                    apply hypsubst_thin
                                    apply (drule in_frontier_addD)
                                    apply clarsimp
                                    apply (elim disjE conjE exE)
                                    subgoal for t2'
                                      apply (drule in_frontier_Sum_all_not_lt)
                                      subgoal
                                        apply (clarsimp simp add: image_iff)
                                        apply safe
                                        apply (metis dataflow_topology.after_summary_def dataflow_topology.after_summary_zmset_of_nonneg prems(2))+
                                        done
                                      subgoal
                                        apply (drule bspec[of _ _ "Loc nid (Src p'')"])
                                        apply simp
                                        apply force
                                        apply (drule spec[of _ "t2' -+- s'"])
                                        apply (drule mp)
                                        subgoal
                                          apply (simp add: zcount_sum)
                                          apply (rule Timely_Infrastructure.dataflow_topology_from_tree.sum_pos[of _ _ s'])
                                          apply (simp_all flip: member_antichain.rep_eq)
                                          apply (rule pos_zcount_image_zmset)
                                          apply (simp_all flip: member_antichain.rep_eq)
                                          done
                                        subgoal
                                          by (metis add.left_commute add_le_less_mono add_less_imp_less_left)
                                        done
                                      done
                                    subgoal for ta
                                      apply (clarsimp simp add: to_zmset_map)
                                      subgoal for t2'
                                        apply hypsubst_thin
                                        using premst apply -
                                        apply (elim disjE)
                                        subgoal
                                          apply (drule zcount_gt_0_in_frontierD)
                                          apply clarsimp
                                          subgoal for ft'
                                            apply (drule in_frontier_Sum_all_not_lt)
                                            subgoal
                                              apply (clarsimp simp add: image_iff)
                                              apply safe
                                              apply (metis dataflow_topology.after_summary_def dataflow_topology.after_summary_zmset_of_nonneg prems(2))+
                                              done
                                            apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                            apply simp
                                             apply fast
                                            apply (subgoal_tac "\<exists> t6\<le>t2'. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p''))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t6
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s' _ _ _ t6 "Loc nid (Trg p)"])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply simp
                                                    apply clarsimp
                                                    subgoal for u
                                              apply (drule spec[of _ "ft' + u"])
                                              apply (drule mp)
                                              subgoal
                                                apply (simp add: zcount_sum)
                                                apply (rule Timely_Infrastructure.dataflow_topology_from_tree.sum_pos[of _ _ "u"])
                                                apply (simp_all flip: member_antichain.rep_eq)
                                                apply (rule pos_zcount_image_zmset)
                                                apply (simp_all flip: member_antichain.rep_eq)
                                                done
                                              subgoal
                                                          by (smt (verit, ccfv_threshold) add.commute add.left_commute add_le_cancel_left order_le_less_subst2)
                                              done
                                            done
                                          done
done
                                        subgoal
                                          apply (simp add: zcount_sum)
                                          apply (drule sum_pos_ex_elem_pos)
                                          apply (elim bexE)
                                          subgoal for nid''
                                            apply simp
                                            apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                            apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                            subgoal
                                              apply (elim exE conjE)
                                              using prems(13) apply -
                                              apply (drule spec[of _ nid])
                                              apply (drule spec[of _ nid''])
                                              apply simp
                                              unfolding changes_above_impl_inv_def
                                              subgoal for p3' m'
                                                apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                subgoal
                                                  (* here4b *)
                                                  apply (subst obtain_progress_def)
                                                  apply (subst extract_progress_def)
                                                  apply (auto simp add: set_map_filter image_iff split_beta )
                                                  apply (rule bexI[rotated])
                                                  apply (clarsimp split: option.splits)
                                                  apply force
                                                  apply (clarsimp split: option.splits)+
                                                  done
                                                apply simp
                                                apply (drule frontier_less_equal_ifrontierE)
                                                using prems(2) apply assumption
                                                apply clarsimp
                                                unfolding frontier_less_equal_iff2
                                                apply clarsimp
                                                apply (subst (asm) (3) in_frontier_iff)
                                                apply clarsimp
                                                apply hypsubst_thin
                                                subgoal for l  s'' t4 t4'
                                                  apply (drule in_frontier_Sum_all_not_lt)
                                                  subgoal
                                                    apply (clarsimp simp add: image_iff)
                                                    apply safe
                                                    apply (metis (no_types) dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)+
                                                    done
                                                  apply (subgoal_tac "\<exists> t6\<le>t2'. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p''))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s'  _ _ _ t9])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                     apply assumption
                                                    apply clarsimp
                                                    subgoal for u
                                                      apply (drule graph.path_weight_elem_trans[rotated 1, of s'' _ _ _ u])
                                                    apply assumption
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply (elim conjE exE)
                                                    subgoal for u''
                                                      apply (clarsimp simp add: filter_concat comp_def filter_map map_concat zmset_concat sum_list_distinct_conv_sum_set split_beta c_pts_change_multiplicities split: prod.splits)
                                                      apply (drule bspec[of _ _ l])
                                                      apply simp
                                                      subgoal
                                                        apply (cases l)
                                                        apply simp
                                                        subgoal for nn pp
                                                          apply (cases pp)
                                                          apply simp_all
                                                          apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                          done
                                                        done
                                                      apply (simp flip: zcount_union)
                                                      apply (drule zcount_gt_0_in_frontierD[where t=t4'])
                                                      apply clarsimp
                                                      subgoal for ft'
                                                        apply (drule spec[of _ "ft' + u''"])
                                                        back
                                                        apply (drule mp)
                                                        subgoal
                                                          apply (simp add: zcount_sum)
                                                          apply (rule Timely_Infrastructure.dataflow_topology_from_tree.sum_pos[of _ _ "u''"])
                                                          apply (simp_all flip: member_antichain.rep_eq)
                                                          apply (rule pos_zcount_image_zmset)
                                                          apply (simp_all flip: member_antichain.rep_eq)
                                                          done
                                                        subgoal 
                                                          using  Groups.add_ac(2) add_le_cancel_left basic_trans_rules(21) dataflow_topology_from_tree.followed_by_summary
                                                            dataflow_topology_from_tree.plus_mono
                                                          by (smt (verit, ccfv_threshold) order_subst1)
                                                        done
                                                      done
                                                    done
                                                  done
                                                done
                                              done
                                            done
                                            subgoal
                                              (* here2! *)
                                              apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                              apply (drule sum_list_pos_ex_elem_pos)
                                              apply (elim bexE)
                                              apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                              apply (metis not_Some_eq2)
                                              apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                              apply fast
                                              apply blast
                                              done
                                            done
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              done
                            subgoal
                              by fast
                            subgoal
                              by (simp add: sum_nonneg zcount_sum)
                            subgoal
                              apply clarsimp
                              apply (elim disjE conjE exE)
                              subgoal for x ttt
                                apply clarsimp
                                subgoal for nid''' p'''
                                  apply hypsubst_thin
                                  apply (simp add: zcount_sum)
                                  apply (drule sum_pos_ex_elem_pos)
                                  apply clarsimp
                                  apply (drule zcount_zimageD)
                                  apply clarsimp
                                  apply hypsubst_thin
                                  subgoal for s' t4
                                    apply (simp add: c_pts_change_multiplicities)
                                    apply (cases "nid = nid''' \<and> p = p'''")
                                    subgoal
                                      apply clarsimp
                                      apply hypsubst_thin
                                      apply (subst (asm) zmset_filter_extract_progress_Trg_consumes_alt)
                                      apply (simp flip: member_antichain.rep_eq)
                                      apply (subst (asm) group_add_class.add_diff_eq)
                                      apply (drule in_frontier_minusD)
                                      apply simp
                                      apply clarsimp
                                      subgoal for t4'
                                        apply (drule in_frontier_Sum_all_not_lt)
                                        subgoal
                                          apply (clarsimp simp add: image_iff)
                                          apply safe
                                          apply (metis dataflow_topology.after_summary_def dataflow_topology.after_summary_zmset_of_nonneg prems(2))+
                                          done
                                        apply (drule bspec[of _ _ "Loc nid''' (Trg p''')"])
                                        apply simp
                                        apply force
                                        apply (drule spec[of _ "t4' -+- s'"])
                                        apply (drule mp)
                                        subgoal
                                          apply (simp add: zcount_sum)
                                          apply (rule Timely_Infrastructure.dataflow_topology_from_tree.sum_pos[of _ _ "s'"])
                                          apply (simp_all flip: member_antichain.rep_eq)
                                          apply (rule pos_zcount_image_zmset)
                                          apply (simp_all flip: member_antichain.rep_eq)
                                          done
                                        apply (meson basic_trans_rules(21) dataflow_topology.results_in_mono(1) prems(2))
                                        done
                                      done
                                    subgoal
                                      apply auto
                                      apply (simp_all flip: member_antichain.rep_eq)
                                      subgoal
                                        apply (drule in_frontier_Sum_all_not_lt)
                                        subgoal
                                          apply (clarsimp simp add: image_iff)
                                          apply safe
                                          apply (metis dataflow_topology.after_summary_def dataflow_topology.after_summary_zmset_of_nonneg prems(2))+
                                          done
                                        apply (drule bspec[of _ _ "Loc nid''' (Trg p''')"])
                                        apply simp
                                        apply force
                                        apply (drule spec[of _ "t4 -+- s'"])
                                        apply (drule mp)
                                        subgoal
                                          apply (simp add: zcount_sum)
                                          apply (rule Timely_Infrastructure.dataflow_topology_from_tree.sum_pos[of _ _ "s'"])
                                          apply (simp_all flip: member_antichain.rep_eq)
                                          apply (rule pos_zcount_image_zmset)
                                          apply (simp_all flip: member_antichain.rep_eq)
                                          unfolding obtain_progress_def extract_progress_def
                                          apply simp
                                          done
                                        apply auto
                                        done
                                      subgoal
                                        apply (drule in_frontier_Sum_all_not_lt)
                                        subgoal
                                          apply (clarsimp simp add: image_iff)
                                          apply safe
                                          apply (metis dataflow_topology.after_summary_def dataflow_topology.after_summary_zmset_of_nonneg prems(2))+
                                          done
                                        apply (drule bspec[of _ _ "Loc nid''' (Trg p''')"])
                                        apply simp
                                        apply force
                                        apply (drule spec[of _ "t4 -+- s'"])
                                        apply (drule mp)
                                        subgoal
                                          apply (simp add: zcount_sum)
                                          apply (rule Timely_Infrastructure.dataflow_topology_from_tree.sum_pos[of _ _ "s'"])
                                          apply (simp_all flip: member_antichain.rep_eq)
                                          apply (rule pos_zcount_image_zmset)
                                          apply (simp_all flip: member_antichain.rep_eq)
                                          unfolding obtain_progress_def extract_progress_def
                                          apply simp
                                          done
                                        apply auto
                                        done
                                      done
                                    done
                                  done
                                done
                              subgoal for x t4
                                apply clarsimp
                                apply(rule ccontr)
                                apply clarsimp
                                apply hypsubst_thin
                                subgoal for nid''' p'''
                                  apply (simp add: zcount_sum)
                                  apply (drule sum_pos_ex_elem_pos)
                                  apply clarsimp
                                  apply (drule zcount_zimageD)
                                  apply clarsimp
                                  apply hypsubst_thin
                                  subgoal for s' t4
                                    apply (simp add: c_pts_change_multiplicities)
                                    apply (cases "nid''' = nid")
                                    subgoal
                                      apply clarsimp
                                      apply hypsubst_thin
                                      apply (subst (asm) zmset_filter_extract_progress_Src_consumes)
                                      apply (simp flip: member_antichain.rep_eq)
                                      apply (subst (asm) add.assoc[symmetric])
                                      apply (drule in_frontier_addD)
                                      apply simp
                                      apply (elim disjE conjE exE)
                                      subgoal for t2'
                                        apply (drule in_frontier_Sum_all_not_lt)
                                        subgoal
                                          apply (clarsimp simp add: image_iff)
                                          apply safe
                                          apply (metis dataflow_topology.after_summary_def dataflow_topology.after_summary_zmset_of_nonneg prems(2))+
                                          done
                                        subgoal
                                          apply (drule bspec[of _ _ "Loc nid (Src p''')"])
                                          apply simp
                                          apply force
                                          apply (drule spec[of _ "t2' -+- s'"])
                                          apply (drule mp)
                                          subgoal
                                            apply (simp add: zcount_sum)
                                            apply (rule Timely_Infrastructure.dataflow_topology_from_tree.sum_pos[of _ _ s'])
                                            apply (simp_all flip: member_antichain.rep_eq)
                                            apply (rule pos_zcount_image_zmset)
                                            apply (simp_all flip: member_antichain.rep_eq)
                                            done
                                          subgoal
                                            by (metis add.left_commute add_le_less_mono add_less_imp_less_left)
                                          done
                                        done
                                      subgoal for t2
                                        apply clarsimp
                                        subgoal for t2'
                                          apply hypsubst_thin
                                          using premst apply -
                                          apply (elim disjE)
                                          subgoal
                                            apply (drule zcount_gt_0_in_frontierD)
                                            apply clarsimp
                                            subgoal for ft'
                                              apply (drule in_frontier_Sum_all_not_lt)
                                              subgoal
                                                apply (clarsimp simp add: image_iff)
                                                apply safe
                                                apply (metis dataflow_topology.after_summary_def dataflow_topology.after_summary_zmset_of_nonneg prems(2))+
                                                done
                                              apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                              apply simp
                                               apply fast
                                              apply (subgoal_tac "\<exists> t6\<le>t2'. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p'''))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t6
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s' _ _ _ t6 "Loc nid (Trg p)"])
                                              subgoal
                                                apply (rule dataflow_topology.axioms(1))
                                                apply (rule prems(2))
                                                done
                                              apply assumption
                                              apply clarsimp
                                              subgoal for u
                                                apply (drule spec[of _ "ft' + u"])
                                                apply (drule mp)
                                                subgoal
                                                  apply (simp add: zcount_sum)
                                                  apply (rule Timely_Infrastructure.dataflow_topology_from_tree.sum_pos[of _ _ "u"])
                                                  apply (simp_all flip: member_antichain.rep_eq)
                                                  apply (rule pos_zcount_image_zmset)
                                                  apply (simp_all flip: member_antichain.rep_eq)
                                                  done
                                                subgoal
                                                          by (smt (verit, ccfv_threshold) add.commute add.left_commute add_le_cancel_left order_le_less_subst2)
                                                        done
                                              done
                                            done
                                          done
                                          subgoal
                                            apply (simp add: zcount_sum)
                                            apply (drule sum_pos_ex_elem_pos)
                                            apply (elim bexE)
                                            subgoal for nid''
                                              apply simp
                                              apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                              apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                              subgoal
                                              apply (elim exE conjE)
                                              using prems(13) apply -
                                              apply (drule spec[of _ nid])
                                              apply (drule spec[of _ nid''])
                                              apply simp
                                              unfolding changes_above_impl_inv_def
                                              subgoal for p3' m'
                                                apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                subgoal
                                                  (* here4b *)
                                                  apply (subst obtain_progress_def)
                                                  apply (subst extract_progress_def)
                                                  apply (auto simp add: set_map_filter image_iff split_beta )
                                                  apply (rule bexI[rotated])
                                                  apply (clarsimp split: option.splits)
                                                  apply force
                                                  apply (clarsimp split: option.splits)+
                                                  done
                                                apply simp
                                                apply (drule frontier_less_equal_ifrontierE)
                                                using prems(2) apply assumption
                                                apply clarsimp
                                                unfolding frontier_less_equal_iff2
                                                apply clarsimp
                                                apply (subst (asm) (3) in_frontier_iff)
                                                apply clarsimp
                                                apply hypsubst_thin
                                                subgoal for l  s'' t4 t4'
                                                  apply (drule in_frontier_Sum_all_not_lt)
                                                  subgoal
                                                    apply (clarsimp simp add: image_iff)
                                                    apply safe
                                                    apply (metis (no_types) dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)+
                                                    done
                                                  apply (subgoal_tac "\<exists> t6\<le>t2'. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p'''))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t9
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s'  _ _ _ t9])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                     apply assumption
                                                    apply clarsimp
                                                    subgoal for u
                                                      apply (drule graph.path_weight_elem_trans[rotated 1, of s'' _ _ _ u])
                                                    apply assumption
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply (elim conjE exE)
                                                    subgoal for u''
                                                      apply (clarsimp simp add: filter_concat comp_def filter_map map_concat zmset_concat sum_list_distinct_conv_sum_set split_beta c_pts_change_multiplicities split: prod.splits)
                                                      apply (drule bspec[of _ _ l])
                                                      apply simp
                                                      subgoal
                                                        apply (cases l)
                                                        apply simp
                                                        subgoal for nn pp
                                                          apply (cases pp)
                                                          apply simp_all
                                                          apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                          done
                                                        done
                                                      apply (simp flip: zcount_union)
                                                      apply (drule zcount_gt_0_in_frontierD[where t=t4'])
                                                      apply clarsimp
                                                      subgoal for ft'
                                                        apply (drule spec[of _ "ft' + u''"])
                                                        back
                                                        apply (drule mp)
                                                        subgoal
                                                          apply (simp add: zcount_sum)
                                                          apply (rule Timely_Infrastructure.dataflow_topology_from_tree.sum_pos[of _ _ "u''"])
                                                          apply (simp_all flip: member_antichain.rep_eq)
                                                          apply (rule pos_zcount_image_zmset)
                                                          apply (simp_all flip: member_antichain.rep_eq)
                                                          done
                                                        subgoal 
                                                          using  Groups.add_ac(2) add_le_cancel_left basic_trans_rules(21) dataflow_topology_from_tree.followed_by_summary
                                                            dataflow_topology_from_tree.plus_mono
                                                          by (smt (verit, ccfv_threshold) order_subst1)
                                                        done
                                                      done
                                                    done
                                                  done
                                                done
                                              done
                                            done
                                              subgoal
                                                (* here2! *)
                                                apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                apply (drule sum_list_pos_ex_elem_pos)
                                                apply (elim bexE)
                                                apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                apply (metis not_Some_eq2)
                                                apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                                apply fast
                                                apply blast
                                                done
                                              done
                                            done
                                          done
                                        done
                                      done
                                    subgoal
                                      apply simp
                                      apply (subst (asm) zmset_filter_extract_progress_Src_consumes_diff)
                                      apply simp_all
                                      apply (drule in_frontier_Sum_all_not_lt)
                                      subgoal
                                        apply (clarsimp simp add: image_iff)
                                        apply safe
                                        apply (metis (no_types) dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)+
                                        done
                                      apply (drule bspec[of _ _ "Loc nid''' (Src p''')"])
                                      apply simp_all
                                      apply force
                                      apply (drule spec[of _ "t4 -+- s'"])
                                      apply (drule mp)
                                      subgoal
                                        apply (simp add: zcount_sum)
                                        apply (rule Timely_Infrastructure.dataflow_topology_from_tree.sum_pos[of _ _ "s'"])
                                        apply (simp_all flip: member_antichain.rep_eq)
                                        apply (rule pos_zcount_image_zmset)
                                        apply (simp_all flip: member_antichain.rep_eq)
                                        apply (subst zmset_filter_extract_progress_Src_consumes_diff)
                                        apply simp_all
                                        done
                                      subgoal
                                        by auto
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          done
                        subgoal
                          apply clarsimp
                          apply (drule in_frontier_sumEx)
                          apply simp_all
                          subgoal
                            by (simp add: sum_nonneg zcount_sum)
                          apply clarsimp
                          apply (drule in_frontier_sumEx)
                          apply (simp_all flip: member_antichain.rep_eq)
                          apply clarsimp
                          subgoal for l s
                            apply (elim disjE rangeE)
                              (* ****** *)
                            subgoal for pa
                              apply (clarsimp simp add: split: prod.splits)
                              subgoal for nid'' p''
                                apply hypsubst_thin
                                apply (cases "nid'' = nid \<and> p'' = p")
                                subgoal
                                  apply clarsimp
                                  apply hypsubst_thin
                                  apply (simp_all flip: member_antichain.rep_eq)
                                  apply (subgoal_tac "\<exists> t p'' s'. t \<in> set (intsum (os nid) p p'') \<and> s' \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Src p'')) (Loc nid' (Trg p')) \<and> s = t -+- s'")
                                  subgoal
                                    apply clarsimp
                                    subgoal for t'' p'' s'
                                      apply hypsubst_thin
                                      apply (drule spec[of _ s'])
                                      apply (drule spec[of _ p''])
                                      apply simp
                                      apply (drule spec[of _ t''])
                                      apply simp
                                      subgoal
                                        apply (subst (asm) in_frontier_zmset_image)
                                        apply clarsimp+
                                        subgoal for ft2
                                          apply (subgoal_tac "ft2 \<noteq> t")
                                          subgoal
                                            apply (rule exI[of _ "ft2 -+- (t'' -+- s')"])
                                            apply simp
                                            apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
                                            using prems(2) apply assumption
                                            apply (rule in_frontier_SumI[where a="Loc nid (Trg p)"])
                                            apply simp_all
                                            subgoal
                                              apply (rule in_frontier_SumI[where a="t'' -+- s'"])
                                              apply (simp_all flip: member_antichain.rep_eq)
                                              subgoal
                                                apply (subst in_frontier_zmset_image)
                                                apply simp
                                                apply (intro exI conjI)
                                                apply (rule refl)
                                                apply (simp add: in_frontier_iff c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt)
                                                done
                                              subgoal
                                                apply clarsimp
                                                apply (drule zcount_zimageD)
                                                apply (clarsimp simp flip: member_antichain.rep_eq)
                                                apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt split: if_splits)
                                                apply hypsubst_thin
                                                subgoal for s'' ft3
                                                  apply (subst (asm) add_diff_eq)
                                                  apply (drule bspec[of _ _ s''])
                                                  apply (clarsimp simp flip: member_antichain.rep_eq)
                                                  apply (drule in_frontier_minusD)
                                                  apply simp
                                                  apply clarsimp
                                                  subgoal for ft3'
                                                    apply (drule spec[of _ "ft3' -+- s''"])
                                                    apply (drule mp)
                                                    subgoal
                                                      apply (rule pos_zcount_image_zmset)
                                                      apply clarsimp
                                                      apply (clarsimp simp flip: member_antichain.rep_eq)
                                                      done
                                                    apply (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                                    done
                                                  done
                                                done
                                              done
                                            apply clarsimp
                                            apply fast
                                            apply clarsimp
                                            subgoal
                                              by (metis (no_types, lifting) ext AP_simp after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)
                                            subgoal
                                              apply (clarsimp simp add: zcount_sum image_iff)
                                              subgoal for l ft3
                                                apply (drule sum_pos_ex_elem_pos)
                                                apply (clarsimp simp flip: member_antichain.rep_eq)
                                                subgoal for s2'
                                                  apply (drule zcount_zimageD)
                                                  apply (clarsimp simp flip: member_antichain.rep_eq)
                                                  subgoal for ft3'
                                                    apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_alt split: if_splits)
                                                    apply hypsubst_thin
                                                    apply (cases l)
                                                    apply clarsimp
                                                    apply (elim disjE exE)
                                                    subgoal for nid4 _ p4
                                                      apply hypsubst_thin
                                                      apply (cases "nid4 = nid")
                                                      subgoal
                                                        apply (simp add: zmset_filter_extract_progress_Trg_consumes_diff_p)
                                                        apply hypsubst_thin
                                                        apply (drule bspec[of _ _ "Loc nid (Trg p4)"])
                                                        apply simp_all
                                                        apply fast
                                                        apply (drule spec[of _ "ft3' -+- s2'"])
                                                        apply (drule mp)
                                                        subgoal
                                                          apply (rule dataflow_topology_from_tree.sum_pos)
                                                          apply (simp_all flip: member_antichain.rep_eq)
                                                          apply (rule pos_zcount_image_zmset)
                                                          apply clarsimp
                                                          apply (clarsimp simp flip: member_antichain.rep_eq)
                                                          done
                                                        subgoal
                                                          by auto
                                                        done
                                                      subgoal
                                                        apply simp
                                                        apply (simp add: zmset_filter_extract_progress_Trg_consumes_diff_nid)
                                                        apply (drule bspec[of _ _ "Loc nid4 (Trg p4)"])
                                                        apply simp_all
                                                        apply fast
                                                        apply (drule spec[of _ "ft3' -+- s2'"])
                                                        apply (drule mp)
                                                        subgoal
                                                          apply (rule dataflow_topology_from_tree.sum_pos)
                                                          apply (simp_all flip: member_antichain.rep_eq)
                                                          apply (rule pos_zcount_image_zmset)
                                                          apply clarsimp
                                                          apply (clarsimp simp flip: member_antichain.rep_eq)
                                                          done
                                                        subgoal
                                                          by auto
                                                        done
                                                      done
                                                    subgoal for nid4 _ p4
                                                      apply hypsubst_thin
                                                      apply (cases "nid4 = nid")
                                                      subgoal
                                                        apply (simp add: zmset_filter_extract_progress_Src_consumes)
                                                        apply hypsubst_thin
                                                        apply (simp flip: add.assoc)
                                                        apply (drule in_frontier_addD)
                                                        back
                                                        apply (elim disjE exE conjE)
                                                        subgoal for ft3''
                                                          apply (drule bspec[of _ _ "Loc nid (Src p4)"])
                                                          apply simp_all
                                                          apply fast
                                                          apply (drule spec[of _ "ft3'' -+- s2'"])
                                                          apply (drule mp)
                                                          subgoal
                                                            apply (rule dataflow_topology_from_tree.sum_pos)
                                                            apply (simp_all flip: member_antichain.rep_eq)
                                                            apply (rule pos_zcount_image_zmset)
                                                            apply clarsimp
                                                            apply (clarsimp simp flip: member_antichain.rep_eq)
                                                            done
                                                          subgoal
                                                            by (meson add_mono_thms_linordered_semiring(3) dual_order.strict_trans2)
                                                          done
                                                        subgoal for ft3''
                                                          apply clarsimp
                                                          subgoal for t4
                                                            apply hypsubst_thin
                                                            using premst apply -
                                                            apply (elim disjE)
                                                            subgoal
                                                              apply (drule zcount_gt_0_in_frontierD)
                                                              apply clarsimp
                                                              subgoal for ft'

                                                                apply (subgoal_tac "\<exists> t6\<le>t4. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p4))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t6
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s2' _ _ _ t6 "Loc nid (Trg p)"])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply simp
                                                    apply clarsimp
                                                                subgoal for u
                                                                  apply (drule bspec[of _ _ "u"])
                                                                  apply (simp_all flip: member_antichain.rep_eq)
                                                                  apply (drule spec[of _ "ft' -+- u"])
                                                                  apply (drule mp)
                                                                  subgoal
                                                                    apply (rule pos_zcount_image_zmset)
                                                                    apply clarsimp
                                                                    apply (clarsimp simp flip: member_antichain.rep_eq)
                                                                    done
                                                                  subgoal
                                                          by (smt (verit, ccfv_threshold) add.commute add.left_commute add_le_cancel_left order_le_less_subst2)
                                                                  done
                                                                done
                                                              done
                                                            done
                                                            subgoal

                                                              apply (simp add: zcount_sum)
                                                              apply (drule sum_pos_ex_elem_pos)
                                                              apply (elim bexE)
                                                              subgoal for nid''
                                                                apply simp
                                                                apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                                                apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                                                subgoal
                                                                  apply (elim exE conjE)
                                                                  using prems(13) apply -
                                                                  apply (drule spec[of _ nid])
                                                                  apply (drule spec[of _ nid''])
                                                                  apply simp
                                                                  unfolding changes_above_impl_inv_def
                                                                  subgoal for p3' m'
                                                                    apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                                    subgoal
                                                                      (* here4b *)
                                                                      apply (subst obtain_progress_def)
                                                                      apply (subst extract_progress_def)
                                                                      apply (auto simp add: set_map_filter image_iff split_beta )
                                                                      apply (rule bexI[rotated])
                                                                      apply (clarsimp split: option.splits)
                                                                      apply force
                                                                      apply (clarsimp split: option.splits)+
                                                                      done
                                                                    apply simp
                                                                    apply (drule frontier_less_equal_ifrontierE)
                                                                    using prems(2) apply assumption
                                                                    apply clarsimp
                                                                    unfolding frontier_less_equal_iff2
                                                                    apply clarsimp
                                                                    apply (subst (asm) (3) in_frontier_iff)
                                                                    apply clarsimp
                                                                    apply hypsubst_thin
                                                                    subgoal for l  s'' t5 t5'
                                                                      apply (drule bspec[of _ _ l])
                                                                      subgoal
                                                                        apply (cases l)
                                                                        apply simp
                                                                        subgoal for nn pp
                                                                          apply (cases pp)
                                                                          apply simp_all
                                                                          apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                                          done
                                                                        done
                                                                      apply (subgoal_tac "\<exists> t6\<le>t4. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p4))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t6
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of t6 _ _ _ s'' ])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply simp
                                                    apply clarsimp
                                                    subgoal for u

                                                      apply (drule graph.path_weight_elem_trans[rotated, of u  _ _ _ s2'])
                                                                        apply assumption
                                                                        subgoal
                                                                          apply (rule dataflow_topology.axioms(1))
                                                                          apply (rule prems(2))
                                                                          done
                                                                        apply clarsimp
                                                                        subgoal for u'
                                                                          apply (drule zcount_gt_0_in_frontierD[where t=t5'])
                                                                          apply clarsimp
                                                                          subgoal for ft6
                                                                            apply (drule spec[of _ "ft6 -+- u'"])
                                                                            back
                                                                            apply (drule mp)
                                                                            subgoal
                                                                              apply (rule dataflow_topology_from_tree.sum_pos)
                                                                              apply (simp_all flip: member_antichain.rep_eq)
                                                                              apply (rule pos_zcount_image_zmset)
                                                                              apply clarsimp
                                                                              apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                                              done
                                                                            subgoal premises prems2
                                                                              using prems2(4,9,13,21,23,24,26,27,10,13,24,29) apply -
                                                                              by (smt (verit, ccfv_SIG) add_mono_thms_linordered_semiring(2,3) dataflow_topology_from_tree.followed_by_summary dual_order.strict_trans2 prems2(10,21,23,24,26,27,29))
                                                                            done
                                                                          done
                                                                        done
                                                                      done
                                                                    done
                                                                  done
                                                                done
                                                                subgoal
                                                                  (* here2! *)
                                                                  apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                                  apply (drule sum_list_pos_ex_elem_pos)
                                                                  apply (elim bexE)
                                                                  apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                                  apply (metis not_Some_eq2)
                                                                  apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                                                  apply fast
                                                                  apply blast
                                                                  done
                                                                done
                                                              done
                                                            done
                                                          done

                                                        done

                                                      subgoal
                                                        apply (simp add: zmset_filter_extract_progress_Src_consumes_diff)
                                                        apply (drule bspec[of _ _ "Loc nid4 (Src p4)"])
                                                        apply fast
                                                        apply (drule spec[of _ "ft3' -+- s2'"])
                                                        apply (drule mp)
                                                        apply (simp_all flip: member_antichain.rep_eq)
                                                        subgoal
                                                          apply (rule dataflow_topology_from_tree.sum_pos)
                                                          apply (simp_all flip: member_antichain.rep_eq)
                                                          apply (rule pos_zcount_image_zmset)
                                                          apply clarsimp
                                                          apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                          done
                                                        done
                                                      done
                                                    done
                                                  done
                                                done
                                              done
                                            done
                                          subgoal
                                            by (metis dataflow_topology_from_tree.followed_by_summary) 
                                          done
                                        done
                                      done
                                    done
                                  subgoal
                                  using prems(3)[unfolded graph_summar_nt_def]
                                  by blast
                                  done
                                subgoal
                                  apply (clarsimp simp add: c_pts_change_multiplicities)
                                  subgoal
                                    apply (cases "nid'' = nid")
                                    subgoal
                                      apply simp
                                      apply hypsubst_thin
                                      apply (rule exI[of _ "ft"])
                                      apply simp
                                      apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
                                      using prems(2) apply assumption
                                      apply (rule in_frontier_SumI[where a="Loc nid (Trg p'')"])
                                      apply simp_all
                                      apply (rule in_frontier_SumI[where a=s])
                                      apply (simp_all add: c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff_p)
                                      apply fast
                                      subgoal
                                        apply clarsimp
                                        by (metis (no_types) AP_simp after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)
                                      subgoal
                                        apply clarsimp
                                        subgoal for l ft'
                                          apply (cases l)
                                          apply (clarsimp simp add: image_iff c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff_nid zmset_filter_extract_progress_Trg_consumes_diff_p)
                                          apply (elim disjE exE)
                                          subgoal for nid''' a p'''
                                            apply (cases "nid''' = nid \<and> p''' = p")
                                            subgoal
                                              apply (clarsimp simp add: zcount_sum zmset_filter_extract_progress_Trg_consumes_alt image_iff c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff_nid zmset_filter_extract_progress_Trg_consumes_diff_p)
                                              apply hypsubst_thin
                                              apply (drule Auxiliary.sum_pos_ex_elem_pos)
                                              apply clarsimp
                                              subgoal for s'
                                                apply (drule zcount_zimageD)
                                                apply clarsimp
                                                subgoal for ft''
                                                  apply hypsubst_thin
                                                  apply (simp_all flip: member_antichain.rep_eq add: add_diff_eq)
                                                  apply (drule in_frontier_minusD)
                                                  apply simp
                                                  apply clarsimp
                                                  subgoal for ft'''
                                                    apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                    apply fast
                                                    apply (drule spec[of _ "ft''' -+- s'"])
                                                    back
                                                    apply (drule mp)
                                                    subgoal
                                                      apply (rule dataflow_topology_from_tree.sum_pos)
                                                      apply (simp_all flip: member_antichain.rep_eq)
                                                      apply (rule pos_zcount_image_zmset)
                                                      apply clarsimp
                                                      apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                      done
                                                    subgoal
                                                      by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                                    done
                                                  done
                                                done
                                              done
                                            subgoal
                                              apply (clarsimp simp add: zcount_sum zmset_filter_extract_progress_Trg_consumes_alt image_iff c_pts_change_multiplicities zmset_filter_extract_progress_Trg_consumes_diff)
                                              apply fast
                                              done
                                            done
                                          subgoal for nid3 a p'''
                                            apply simp
                                            apply (cases "nid3 = nid")
                                            apply (simp_all add: zcount_sum zmset_filter_extract_progress_Src_consumes zmset_filter_extract_progress_Src_consumes_diff image_iff c_pts_change_multiplicities)
                                            apply hypsubst_thin
                                            subgoal
                                              apply (drule Auxiliary.sum_pos_ex_elem_pos)
                                              apply clarsimp
                                              subgoal for s'
                                                apply (drule zcount_zimageD)
                                                apply clarsimp
                                                subgoal for ft''
                                                  apply hypsubst_thin
                                                  apply (simp_all flip: member_antichain.rep_eq add.assoc)
                                                  apply (drule in_frontier_addD)
                                                  apply (elim disjE exE conjE)
                                                  subgoal for ft'''
                                                    apply (drule bspec[of _ _ "Loc nid (Src p''')"])
                                                    apply fast
                                                    apply (drule spec[of _ "ft''' -+- s'"])
                                                    back
                                                    apply (drule mp)
                                                    subgoal
                                                      apply (rule dataflow_topology_from_tree.sum_pos)
                                                      apply (simp_all flip: member_antichain.rep_eq)
                                                      apply (rule pos_zcount_image_zmset)
                                                      apply clarsimp
                                                      apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                      done
                                                    subgoal
                                                      by (meson add_mono_thms_linordered_semiring(3) basic_trans_rules(21))
                                                    done
                                                  subgoal for t'''
                                                    apply clarsimp
                                                    apply hypsubst_thin
                                                    subgoal for ft5
                                                      apply (subgoal_tac "\<exists> t6\<le>ft5. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p'''))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t6
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of s' _ _ _ t6 "Loc nid (Trg p)"])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply simp
                                                    apply clarsimp
                                                    subgoal for u
                                                        using premst apply -
                                                        apply (elim disjE)
                                                        subgoal
                                                          apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                          apply fast
                                                          apply (drule zcount_gt_0_in_frontierD)
                                                          apply clarsimp
                                                          subgoal for ft'
                                                            apply (drule spec[of _ "ft' -+- u"])
                                                            back
                                                            apply (drule mp)
                                                            subgoal
                                                              apply (rule dataflow_topology_from_tree.sum_pos)
                                                              apply (simp_all flip: member_antichain.rep_eq)
                                                              apply (rule pos_zcount_image_zmset)
                                                              apply clarsimp
                                                              apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                              done
                                                            subgoal
                                                          by (smt (verit, ccfv_threshold) add.commute add.left_commute add_le_cancel_left order_le_less_subst2)
                                                            done
                                                          done

                                                        subgoal
                                                          apply (simp add: zcount_sum)
                                                          apply (drule sum_pos_ex_elem_pos)
                                                          apply (elim bexE)
                                                          subgoal for nid''
                                                            apply simp
                                                            apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                                            apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                                            subgoal
                                                              apply (elim exE conjE)
                                                              using prems(13) apply -
                                                              apply (drule spec[of _ nid])
                                                              apply (drule spec[of _ nid''])
                                                              apply simp
                                                              unfolding changes_above_impl_inv_def
                                                              subgoal for p3' m'
                                                                apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                                subgoal
                                                                  (* here4b *)
                                                                  apply (subst obtain_progress_def)
                                                                  apply (subst extract_progress_def)
                                                                  apply (auto simp add: set_map_filter image_iff split_beta )
                                                                  apply (rule bexI[rotated])
                                                                  apply (clarsimp split: option.splits)
                                                                  apply force
                                                                  apply (clarsimp split: option.splits)+
                                                                  done
                                                                apply simp
                                                                apply (drule frontier_less_equal_ifrontierE)
                                                                using prems(2) apply assumption
                                                                apply clarsimp
                                                                unfolding frontier_less_equal_iff2
                                                                apply clarsimp
                                                                subgoal for l s'' ft6 ft7
                                                                  apply hypsubst_thin
                                                                  apply (drule bspec[of _ _ l])
                                                                  apply simp
                                                                  subgoal
                                                                    apply (cases l)
                                                                    apply simp
                                                                    subgoal for nn pp
                                                                      apply (cases pp)
                                                                      apply simp_all
                                                                      apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                                      done
                                                                    done
                                                                  apply (drule graph.path_weight_elem_trans[rotated , of s'' _ _ _  u])
                                                                  apply assumption
  subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
    done
  apply clarsimp 

                                                                  subgoal for u'
                                                                    apply (clarsimp simp add: image_iff c_pts_change_multiplicities)
                                                                    apply (drule spec[of _ "ft7 -+- u'"])
                                                                    back
                                                                    apply (drule mp)
                                                                    subgoal
                                                                      apply (rule dataflow_topology_from_tree.sum_pos)
                                                                      apply (simp_all flip: member_antichain.rep_eq)
                                                                      apply (rule pos_zcount_image_zmset)
                                                                      apply clarsimp
                                                                      apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                                      done
                                                                    subgoal 
                                                                      by (smt (verit, ccfv_threshold) add.assoc add.commute add_mono_thms_linordered_field(2) less_le order_less_le_subst2)
                                                                    done
                                                                  done
                                                                done
                                                              done
                                                            subgoal
                                                              (* here2! *)
                                                              apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                              apply (drule sum_list_pos_ex_elem_pos)
                                                              apply (elim bexE)
                                                              apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                              apply (metis not_Some_eq2)
                                                              apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                                              apply fast
                                                              apply blast
                                                              done
                                                            done
                                                          done
                                                        done

                                                      done
                                                    done
                                                  done
                                                done
                                              done
                                            done
                                            subgoal
                                              apply (drule bspec[of _ _ "Loc nid3 (Src p''')"])
                                              apply fast
                                              apply (drule spec[of _ "ft'"])
                                              back
                                              apply (drule mp)
                                              subgoal
                                                by (simp_all add: zcount_sum zmset_filter_extract_progress_Src_consumes zmset_filter_extract_progress_Src_consumes_diff image_iff c_pts_change_multiplicities)
                                              subgoal
                                                by auto
                                              done
                                            done
                                          done
                                        done
                                      done
                                    subgoal
                                      apply (simp_all add: zcount_sum zmset_filter_extract_progress_Src_consumes zmset_filter_extract_progress_Src_consumes_diff image_iff c_pts_change_multiplicities)
                                      apply (rule exI[of _ ft])
                                      apply simp_all
                                      apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
                                      using prems(2) apply assumption
                                      apply (rule in_frontier_SumI[where a="Loc nid'' (Trg p'')"])
                                      apply (simp_all add: zcount_sum zmset_filter_extract_progress_Trg_consumes_diff_nid zmset_filter_extract_progress_Src_consumes_diff image_iff c_pts_change_multiplicities)
                                      subgoal
                                        apply (rule in_frontier_SumI[where a=s])
                                        apply (simp_all add: zcount_sum zmset_filter_extract_progress_Trg_consumes_diff_nid zmset_filter_extract_progress_Src_consumes_diff image_iff c_pts_change_multiplicities)
                                        done
                                      subgoal
                                        by (meson nonneg_zcount_image_zmset sum_nonneg zmset_of_mset_set_ge_zero)
                                      subgoal
                                        apply clarsimp
                                        subgoal for l ft'
                                          apply (cases l)
                                          apply simp
                                          subgoal for nid3 pp
                                            apply (cases pp)
                                            subgoal for p3
                                              apply (clarsimp split: prod.splits)
                                              apply hypsubst_thin
                                              apply (simp_all add: zcount_sum zmset_filter_extract_progress_Trg_consumes_diff zmset_filter_extract_progress_Src_consumes_diff image_iff c_pts_change_multiplicities)
                                              apply (cases "nid3 = nid \<and> p3 = p")
                                              subgoal
                                                apply (clarsimp simp add: zcount_sum zmset_filter_extract_progress_Trg_consumes_alt zmset_filter_extract_progress_Src_consumes_diff image_iff c_pts_change_multiplicities)
                                                apply hypsubst_thin
                                                apply (drule sum_pos_ex_elem_pos)
                                                apply clarsimp
                                                subgoal for s'
                                                  apply (drule zcount_zimageD)
                                                  apply clarsimp
                                                  subgoal for ft''
                                                    apply (simp add: add_diff_eq flip: member_antichain.rep_eq)
                                                    apply (drule in_frontier_minusD)
                                                    apply simp
                                                    apply clarsimp
                                                    subgoal for ft3
                                                      apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                      apply fast
                                                      apply (drule spec[of _ "ft3 -+- s'"])
                                                      back
                                                      apply (drule mp)
                                                      subgoal
                                                        apply (rule dataflow_topology_from_tree.sum_pos)
                                                        apply (simp_all flip: member_antichain.rep_eq)
                                                        apply (rule pos_zcount_image_zmset)
                                                        apply clarsimp
                                                        apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                        done
                                                      subgoal
                                                        by (meson add_le_cancel_right basic_trans_rules(21))
                                                      done
                                                    done
                                                  done
                                                done
                                              subgoal
                                                apply clarsimp
                                                apply (clarsimp simp add: zmset_filter_extract_progress_Trg_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                apply fast
                                                done
                                              done
                                            subgoal for p3
                                              apply (clarsimp simp add: image_iff)
                                              apply hypsubst_thin
                                              apply (cases "nid3 = nid")
                                              subgoal
                                                apply (simp add: zmset_filter_extract_progress_Src_consumes)
                                                apply (drule sum_pos_ex_elem_pos)
                                                apply clarsimp
                                                subgoal for s'
                                                  apply (drule zcount_zimageD)
                                                  apply clarsimp
                                                  subgoal for ft''
                                                    apply (simp add: add_diff_eq flip: member_antichain.rep_eq flip: add.assoc)
                                                    apply (drule in_frontier_addD)
                                                    apply (elim disjE exE conjE)
                                                    subgoal for ft5
                                                      apply (drule bspec[of _ _ "Loc nid (Src p3)"])
                                                      apply fast
                                                      apply (drule spec[of _ "ft5 -+- s'"])
                                                      back
                                                      apply (drule mp)
                                                      subgoal
                                                        apply (rule dataflow_topology_from_tree.sum_pos)
                                                        apply (simp_all flip: member_antichain.rep_eq)
                                                        apply (rule pos_zcount_image_zmset)
                                                        apply clarsimp
                                                        apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                        done
                                                      subgoal
                                                        by (meson add_le_cancel_right basic_trans_rules(21))
                                                      done
                                                    subgoal for ft6
                                                      apply clarsimp
                                                      subgoal for ft7
                                                        apply hypsubst_thin
                                                        using premst apply -
                                                        apply (elim disjE)
                                                        subgoal
                                                          apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                          apply fast
                                                          apply (drule zcount_gt_0_in_frontierD)
                                                          apply clarsimp
                                                          subgoal for ft'
                                                            apply (subgoal_tac "\<exists> t6\<le>ft7. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p3))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t6
                                                    apply (drule graph.path_weight_elem_trans[rotated , of t6 _ _ _ s'])
                                                    apply assumption
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply clarsimp
                                                    subgoal for u
                                                              apply (drule spec[of _ "ft' -+- u"])
                                                              back
                                                              apply (drule mp)
                                                              subgoal
                                                                apply (rule dataflow_topology_from_tree.sum_pos)
                                                                apply (simp_all flip: member_antichain.rep_eq)
                                                                apply (rule pos_zcount_image_zmset)
                                                                apply clarsimp
                                                                apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                                done
                                                              subgoal
                                                          by (smt (verit, ccfv_threshold) add.commute add.left_commute add_le_cancel_left order_le_less_subst2)
                                                              done
                                                            done
                                                          done
                                                        done
                                                        subgoal
                                                          apply (simp add: zcount_sum)
                                                          apply (drule sum_pos_ex_elem_pos)
                                                          apply (elim bexE)
                                                          subgoal for nid''
                                                            apply simp
                                                            apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                                            apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                                            subgoal
                                                              apply (elim exE conjE)
                                                              using prems(13) apply -
                                                              apply (drule spec[of _ nid])
                                                              apply (drule spec[of _ nid''])
                                                              apply simp
                                                              unfolding changes_above_impl_inv_def
                                                              subgoal for p3' m'
                                                                apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                                subgoal
                                                                  (* here4b *)
                                                                  apply (subst obtain_progress_def)
                                                                  apply (subst extract_progress_def)
                                                                  apply (auto simp add: set_map_filter image_iff split_beta )
                                                                  apply (rule bexI[rotated])
                                                                  apply (clarsimp split: option.splits)
                                                                  apply force
                                                                  apply (clarsimp split: option.splits)+
                                                                  done
                                                                apply simp
                                                                apply (drule frontier_less_equal_ifrontierE)
                                                                using prems(2) apply assumption
                                                                apply clarsimp
                                                                unfolding frontier_less_equal_iff2
                                                                apply clarsimp
                                                                subgoal for l s''' ft8 ft9
                                                                  apply hypsubst_thin
                                                                  apply (drule bspec[of _ _ l])
                                                                  apply simp
                                                                  subgoal
                                                                    apply (cases l)
                                                                    apply simp
                                                                    subgoal for nn pp
                                                                      apply (cases pp)
                                                                      apply simp_all
                                                                      apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                                      done
                                                                    done
                                                                  apply (subgoal_tac "\<exists> t6\<le>ft7. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p3))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t6
                                                    apply (drule graph.path_weight_elem_trans[rotated , of t6 _ _ _ s'])
                                                    apply assumption
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply clarsimp
                                                    subgoal for u
                                                                  apply (drule graph.path_weight_elem_trans[rotated, of s''' _ _ _ u])
                                                      apply assumption
                                                                  subgoal
                                                                    apply (rule dataflow_topology.axioms(1))
                                                                    apply (rule prems(2))
                                                                    done
                                                                  apply clarsimp
                                                                    subgoal for u'
                                                                      apply (clarsimp simp add: image_iff c_pts_change_multiplicities)
                                                                      apply (drule spec[of _ "ft9 -+- u'"])
                                                                      back
                                                                      apply (drule mp)
                                                                      subgoal
                                                                        apply (rule dataflow_topology_from_tree.sum_pos)
                                                                        apply (simp_all flip: member_antichain.rep_eq)
                                                                        apply (rule pos_zcount_image_zmset)
                                                                        apply clarsimp
                                                                        apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                                        done
                                                                      subgoal
                                                                        by (smt (verit, ccfv_threshold) add.commute add.left_commute add_le_cancel_left order_le_less_subst2)
                                                                      done
                                                                    done
                                                                  done
                                                                done
                                                              done
                                                            done
                                                            subgoal
                                                              (* here2! *)
                                                              apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                              apply (drule sum_list_pos_ex_elem_pos)
                                                              apply (elim bexE)
                                                              apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                              apply (metis not_Some_eq2)
                                                              apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                                              apply fast
                                                              apply blast
                                                              done
                                                            done
                                                          done
                                                        done
                                                      done
                                                    done
                                                  done
                                                done
                                              subgoal
                                                apply (simp add: zmset_filter_extract_progress_Src_consumes_diff)
                                                apply (drule bspec[of _ _ "Loc nid3 (Src p3)"])
                                                apply fast
                                                apply (simp add: zmset_filter_extract_progress_Src_consumes_diff)
                                                done
                                              done
                                            done
                                          done
                                        done
                                      done
                                    done
                                  done
                                done
                              done
                            subgoal for pa
                              apply (cases l; cases pa)
                              apply (clarsimp simp: prod.splits)
                              apply hypsubst_thin
                              subgoal for nid'' p''
                                apply (subst (asm) in_frontier_zmset_image)
                                apply clarsimp+
                                subgoal for ft2
                                  apply (cases "nid'' = nid")
                                  subgoal
                                    apply (drule in_frontier_addEx[where B="to_zmset (map ((-+-) t) (intsum (os nid) p p''))"])
                                    apply simp
                                    apply (meson to_zmset_nenneg)
                                    apply clarsimp
                                    subgoal for ft3

                                      apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
                                      using prems(2) apply assumption
                                      apply (rule in_frotier_sum_le_exI[where a="Loc nid'' (Src p'')", of _ _ "ft3 -+- s"])
                                      apply simp
                                      subgoal
                                        apply clarsimp
                                        by (metis dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)
                                      subgoal
                                        apply (simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes flip: add.assoc)
                                        apply (rule in_frontier_SumI[where a="s"])
                                        apply simp_all
                                        subgoal
                                          apply (subst in_frontier_zmset_image)
                                          apply clarsimp
                                          apply simp
                                          done
                                        subgoal
                                          apply clarsimp
                                          apply (drule zcount_zimageD)
                                          apply (clarsimp simp flip: member_antichain.rep_eq)
                                          subgoal for s' ft4
                                            apply (drule in_frontier_addD)
                                            back
                                            apply (elim disjE conjE exE)
                                            subgoal for ft5
                                              apply (drule bspec[of _ _ s'])
                                              apply (clarsimp simp flip: member_antichain.rep_eq)
                                              apply (drule spec[of _ "ft5 -+- s'"])
                                              back
                                              apply (drule mp)
                                              subgoal
                                                apply (rule pos_zcount_image_zmset)
                                                apply (simp_all flip: member_antichain.rep_eq)
                                                done
                                              subgoal premises prems2
                                                using prems2(3,9,11,12,16,17) apply -
                                                by (meson dataflow_topology.results_in_mono(1) dual_order.strict_trans1 dual_order.strict_trans2 prems(2) prems2(13))
                                              done
                                            subgoal for ft5
                                              apply clarsimp
                                              subgoal for ft6
                                                apply hypsubst_thin
                                                using premst apply -
                                                apply (elim disjE)
                                                subgoal
                                                  apply (drule zcount_gt_0_in_frontierD)
                                                  apply clarsimp
                                                  subgoal for ft'
                                                    apply (subgoal_tac "\<exists> t6\<le>ft6. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p''))")
                                                     defer
                                                    subgoal
                                                      subgoal 
                                                        using prems(3)
                                                        unfolding graph_summar_nt_def
                                                        by auto
                                                      done
                                                    apply clarsimp
                                                    subgoal for t6
                                                      apply (drule graph.path_weight_elem_trans[rotated 2, of s' _ _ _ t6])
                                                      subgoal
                                                        apply (rule dataflow_topology.axioms(1))
                                                        apply (rule prems(2))
                                                        done
                                                      apply simp
                                                      apply clarsimp
                                                      subgoal for u
                                                      apply (drule bspec[of _ _ "Loc nid (Trg p)"])
                                                      apply (simp_all flip: member_antichain.rep_eq)
                                                      apply fast
                                                      apply (drule spec[of _ "ft' -+- u"])
                                                      back
                                                      apply (drule mp)
                                                      subgoal
                                                        apply (simp add: zcount_sum)
                                                        apply (rule dataflow_topology_from_tree.sum_pos)
                                                        apply (simp_all flip: member_antichain.rep_eq)
                                                        apply (rule pos_zcount_image_zmset)
                                                        apply clarsimp
                                                        apply (clarsimp simp flip: member_antichain.rep_eq)
                                                        done
                                                      subgoal premises prems2
                                                        using prems2(16,3,7,9,10,12,14,19-)
                                                              by (smt (verit, ccfv_threshold) add_mono_thms_linordered_semiring(2,3) antisym_conv2 dataflow_topology_from_tree.followed_by_summary order.strict_trans)
                                                        done
                                                    done
                                                  done
                                                done
                                                subgoal
                                                  apply (simp add: zcount_sum)
                                                  apply (drule sum_pos_ex_elem_pos)
                                                  apply (elim bexE)
                                                  subgoal for nid''
                                                    apply simp
                                                    apply (simp add:  comp_def filter_map split_beta zcount_zmset)
                                                    apply (subgoal_tac "\<exists> p2. \<exists> m >0. (p2, t, m) \<in> set (produ (os nid'')) \<and> (nxt sg (nid'', p2) = Some (nid, p))")
                                                    subgoal
                                                      apply (elim exE conjE)
                                                      using prems(13) apply -
                                                      apply (drule spec[of _ nid])
                                                      apply (drule spec[of _ nid''])
                                                      apply simp
                                                      unfolding changes_above_impl_inv_def
                                                      subgoal for p3' m'
                                                        apply (drule bspec[of _ _ "(Loc nid (Trg p), t, m')"])
                                                        subgoal
                                                          (* here4b *)
                                                          apply (subst obtain_progress_def)
                                                          apply (subst extract_progress_def)
                                                          apply (auto simp add: set_map_filter image_iff split_beta )
                                                          apply (rule bexI[rotated])
                                                          apply (clarsimp split: option.splits)
                                                          apply force
                                                          apply (clarsimp split: option.splits)+
                                                          done
                                                        apply simp
                                                        apply (drule frontier_less_equal_ifrontierE)
                                                        using prems(2) apply assumption
                                                        apply clarsimp
                                                        unfolding frontier_less_equal_iff2
                                                        apply clarsimp
                                                        apply (subst (asm) (3) in_frontier_iff)
                                                        apply clarsimp
                                                        apply hypsubst_thin
                                                        subgoal for l  s'' t5 t5'
                                                          apply (drule bspec[of _ _ l])
                                                          subgoal
                                                            apply (cases l)
                                                            apply simp
                                                            subgoal for nn pp
                                                              apply (cases pp)
                                                              apply simp_all
                                                              apply (metis (no_types, lifting) UNIV_I image_eqI prod.sel(1,2))+
                                                              done
                                                            done

                                                          apply (subgoal_tac "\<exists> t6\<le>ft6. t6 \<in>\<^sub>A graph.path_weight (summ sg) (Loc nid (Trg p)) (Loc nid (Src p''))")
                                                    defer
                                                    subgoal
                                                      subgoal 
                                                      using prems(3)
                                                      unfolding graph_summar_nt_def
                                                      by auto
                                                    done
                                                    apply clarsimp
                                                  subgoal for t6
                                                    apply (drule graph.path_weight_elem_trans[rotated 2, of t6 _ _ _ s''])
                                                    subgoal
                                                      apply (rule dataflow_topology.axioms(1))
                                                      apply (rule prems(2))
                                                      done
                                                    apply simp
                                                    apply clarsimp
                                                    subgoal for u
                                                      apply (drule graph.path_weight_elem_trans[rotated, of u _ _ _ s'])
                                                      apply assumption
                                                          subgoal
                                                            apply (rule dataflow_topology.axioms(1))
                                                            apply (rule prems(2))
                                                            done
                                                          apply clarsimp
                                                            subgoal for u'
                                                              apply (drule spec[of _ "t5' -+- u'"])
                                                              back
                                                              back
                                                              apply (drule mp)
                                                              subgoal
                                                                apply (rule dataflow_topology_from_tree.sum_pos)
                                                                apply (simp_all flip: member_antichain.rep_eq)
                                                                apply (rule pos_zcount_image_zmset)
                                                                apply clarsimp
                                                                apply (clarsimp simp add: c_pts_change_multiplicities simp flip: member_antichain.rep_eq)
                                                                apply (metis (lifting) in_frontierI zcount_union)
                                                                done
                                                              subgoal premises temp
                                                                using temp(3,7,11,13,21,24,25,27-)
                                                                         by (smt (verit, ccfv_SIG) add_mono_thms_linordered_semiring(2,3) dataflow_topology_from_tree.followed_by_summary dual_order.strict_trans1 dual_order.strict_trans2)
                                                              done
                                                            done
                                                          done
                                                        done
                                                      done
                                                    done
                                                    subgoal
                                                      (* here2! *)
                                                      apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                      apply (drule sum_list_pos_ex_elem_pos)
                                                      apply (elim bexE)
                                                      apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits)
                                                      apply (metis not_Some_eq2)
                                                      apply (clarsimp simp add: List.map_filter_def comp_def split: option.splits prod.splits if_splits)
                                                      apply fast
                                                      apply blast
                                                      done
                                                    done
                                                  done
                                                done
                                              done
                                            done
                                          done
                                        done
                                      apply simp_all
                                      apply fast
                                      apply (meson add_le_cancel_right basic_trans_rules(23))
                                      done
                                    done
                                  subgoal
                                    apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes_diff)
                                    apply (subst Propagate.dataflow_topology.implied_frontier_alt_def)
                                    using prems(2) apply assumption
                                    apply (rule in_frotier_sum_le_exI[where a="Loc nid'' (Src p'')", of _ _ "ft2 -+- s"])
                                    apply simp_all
                                    subgoal
                                      apply clarsimp
                                      apply (metis dataflow_topology_from_tree.after_summary_def dataflow_topology_from_tree.after_summary_zmset_of_nonneg)
                                      done
                                    subgoal
                                      apply (rule in_frontier_SumI[where a=s])
                                      apply (simp_all add: in_frontier_zmset_image zcount_sum zmset_filter_extract_progress_Trg_consumes_diff_nid zmset_filter_extract_progress_Src_consumes_diff image_iff c_pts_change_multiplicities)
                                      done
                                    subgoal
                                      by fast
                                    done
                                  done
                                done
                              done
                            done
                          done
                        done
                      done
                    done
                      (* subgoal_inter *) 
                  subgoal for pa
                    apply (cases pa)
                    apply clarsimp
                    apply hypsubst_thin
                    subgoal for p'
                      using prems4 by auto
                    done
                      (* subgoal_produ *) 
                  subgoal
                    apply (clarsimp simp add: set_map_filter split: option.splits; hypsubst_thin?)
                    unfolding not_def
                    apply (drule mp)
                    apply simp_all
                    subgoal for p' nid2 p2
                      using prems(14) apply -
                      unfolding produ_supported_def
                      apply (drule spec2, drule spec2, drule mp, assumption)
                      apply (elim disjE)
                      subgoal
                        apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc nid' (Src p')", simplified])
                        using prems(2) apply assumption
                        subgoal
                          using prems(3) apply -
                          unfolding graph_summar_nt_def
                          by auto
                        subgoal
                          apply (clarsimp simp add: c_pts_change_multiplicities zmset_filter_extract_progress_Src_consumes_diff)
                          using frontier_less_equal_zcount_pos apply blast
                          done
                        done
                      subgoal
                        apply clarsimp
                        subgoal premises prems2 for m'
                          using prems2(2,5,6-) apply -
                          using prems(13) apply -
                          apply (drule spec[of _ nid])
                          apply (drule spec[of _ nid'])
                          apply simp
                          unfolding changes_above_impl_inv_def
                          apply (drule bspec)
                          apply (subst obtain_progress_def)
                          apply (subst extract_progress_def)
                          apply simp
                          apply force
                          apply simp
                          apply (rule frontier_less_equal_ifrontier_trans[of _ 0 "Loc nid' (Src p')", simplified])
                          using prems(2) apply assumption
                          subgoal
                            using prems(3) prems2(4) unfolding graph_summar_nt_def
                            by auto
                          subgoal
                            using prems4 by auto
                          done
                        done
                      done
                    done
                  done
                done
              done
            done
          done
        done
      subgoal for nid'
        subgoal premises temp
          apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc nid (Trg p)) +
                                 zmset (map snd (filter (\<lambda>(l', t, d). (Loc nid (Trg p)) = l') (extract_progress nid (nxt sg) (snd (obtain_progress (os nid))))))) t > 0 \<or>
   zcount (\<Sum>x\<in>UNIV - {nid}. zmset (List.map_filter (\<lambda> (p', t, d). case_option None (\<lambda> (nid'', p''). if nid'' = nid \<and> p'' = p then Some (t, d) else None) (nxt sg (x, p'))) (produ (os x)))) t > 0")
          defer
          subgoal premises prems2
            using prems(1,5,6) apply -
            unfolding Trg_caps_inv_def
            apply (drule spec[of _ nid])
            apply (drule spec[of _ p])
            unfolding c_pts_inv_def
            apply (drule spec[of _ "Loc nid (Trg p)"])
            apply (simp add: c_pts_change_multiplicities extract_prog_def filter_concat comp_def map_concat zmset_concat sum_list_distinct_conv_sum_set)
            apply (subst (asm) comm_monoid_add_class.sum.subset_diff[of "{nid}"])
            apply simp_all
            unfolding zmultiset_eq_iff
            apply (drule spec[of _ t])+
            apply (subgoal_tac  "zcount
       (c_pts (pt_tr sg) (Loc nid (Trg p)) +
        ((\<Sum>x\<in>UNIV - {nid}. zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_progress x (subgraph.nxt sg) (snd (obtain_progress (os x))))))) +
         zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (extract_progress nid (subgraph.nxt sg) (snd (obtain_progress (os nid))))))))
       t > 0")
            subgoal premises prems3
              using prems3(4) 
              by (auto simp add: zmset_filter_Trg_not_nid)
            subgoal
              unfolding outputs_at_target_def BULK_BENQ_def
              apply (auto simp add: to_zmset_nenneg split: option.splits prod.splits)
              done
            done
          subgoal premises premst
            using temp apply -
            unfolding changes_above_impl_inv_def
            apply clarsimp
            subgoal premises temp for l t' m
              apply (subgoal_tac "nid' \<noteq> nid \<Longrightarrow> frontier_less_equal (ifrontier (summ sg) (-+-) (change_multiplicities (summ sg) (extract_progress nid' (subgraph.nxt sg) (snd (obtain_progress (os nid')))) (pt_tr sg)) (Loc nid (Trg p))) t")
              defer
              subgoal
                apply (cases "\<exists> p'. nxt sg (nid', p') = Some (nid, p)")
                subgoal
                  apply (subgoal_tac "zcount (c_pts (pt_tr sg) (Loc nid (Trg p)) +
              zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (List.map_filter (\<lambda>(p, t, m). case subgraph.nxt sg (nid', p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) (produ (os nid')))))) t > 0")
                  subgoal
                    apply (drule zcount_gt_0_in_frontierD)
                    apply clarsimp
                    subgoal for ft
                      apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc nid (Trg p)", simplified])
                      using prems(2) apply assumption
                      subgoal
                        apply (rule Graph.graph.path_weight_refl)
                        apply (rule dataflow_topology.axioms(1))
                        using prems(2) apply assumption
                        done
                      subgoal
                        apply (clarsimp simp add: filter_concat comp_def map_concat zmset_concat c_pts_change_multiplicities extract_progress_def obtain_progress_def split_beta split: prod.splits)
                        using frontier_less_equal_iff2 apply blast
                        done
                      done
                    done
                  subgoal
                    using premst apply -
                    unfolding extract_progress_def obtain_progress_def
                    apply (clarsimp simp add: filter_map comp_def split: prod.splits)
                    subgoal for p2
                      apply (clarsimp simp add: filter_map comp_def split_beta split: option.splits prod.splits)
                      apply (subgoal_tac "zcount (zmset (map snd (filter (\<lambda>x. \<forall>x1. (\<forall>a b. x \<noteq> (x1, a, b)) \<or> p = x1) (consu (os nid))))) t \<ge> 0")
                      subgoal
                        apply (subgoal_tac "zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (List.map_filter (\<lambda>(p, t, m). case subgraph.nxt sg (nid, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) (produ (os nid))))) = {#}\<^sub>z")
                        subgoal
                          apply (subgoal_tac "zcount (zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (List.map_filter (\<lambda>(p, t, m). case subgraph.nxt sg (nid', p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) (produ (os nid')))))) t \<ge> 0")
                          subgoal
                            by simp
                          subgoal
                            apply (rule zcount_zmset_ge_0I)
                            apply (clarsimp simp add: set_map_filter split: option.splits)
                            using prems(10) apply -
                            unfolding change_deltas_inv_def
                            apply clarsimp
                            apply (smt (verit, best))
                            done
                          done
                        subgoal
                          apply (rule zmset_emptyI)
                          apply (clarsimp simp add: set_map_filter filter_empty_conv split: option.splits)
                          using prems(3) apply -
                          unfolding graph_summar_nt_def
                          apply clarsimp
                          apply (metis (mono_tags, lifting) Pair_inject domI inj_onD)
                          done
                        done
                      subgoal
                        apply (rule zcount_zmset_ge_0I)
                        apply (clarsimp simp add: set_map_filter split: option.splits)
                        using prems(10) apply -
                        unfolding change_deltas_inv_def
                        apply clarsimp
                        apply (smt (verit, best))
                        done
                      done
                    subgoal for p2
                      using prems(1,5,6) apply -
                      unfolding Trg_caps_inv_def
                      apply (drule spec[of _ nid])
                      apply (drule spec[of _ p])
                      unfolding c_pts_inv_def
                      apply (drule spec[of _ "Loc nid (Trg p)"])
                      apply (simp add: c_pts_change_multiplicities extract_prog_def filter_concat comp_def map_concat zmset_concat sum_list_distinct_conv_sum_set)
                      apply (subst (asm) obtain_progress_def)
                      apply (subst (asm) extract_progress_def)
                      apply (simp add: comm_monoid_add_class.sum.distrib split_beta c_pts_change_multiplicities extract_prog_def filter_concat comp_def map_concat zmset_concat sum_list_distinct_conv_sum_set)         
                      apply (subst (asm) (3) sum_eq_singleton[where a="nid'"])
                      apply simp_all
                      subgoal
                        using prems(3) apply -
                        unfolding graph_summar_nt_def
                        apply clarsimp
                        apply (subst filter_False)
                        subgoal
                          apply (clarsimp simp add: set_map_filter filter_empty_conv split: option.splits)
                          apply (metis (no_types, lifting) Pair_inject domI inj_onD)
                          done
                        subgoal
                          by simp
                        done
                      subgoal
                        apply (subgoal_tac "zcount (\<Sum>x\<in>UNIV. zmset (map snd (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l') (map (\<lambda>(p, t, m). (Loc x (Trg p), t, - m)) (consu (os x)))))) t \<le> 0")
                        subgoal
                          unfolding outputs_at_target_def Src_from_Trg_def BULK_BENQ_def zmultiset_eq_iff
                          apply (drule spec[of _ t])+
                          apply (clarsimp )
                          apply (smt (verit, ccfv_SIG) to_zmset_nenneg)
                          done
                        subgoal
                          apply (clarsimp simp add: zcount_sum)
                          apply (rule sum_le_0I)
                          apply simp_all
                          apply (clarsimp simp add: zcount_zmset filter_map comp_def split_beta split: prod.splits)
                          apply (rule sum_list_nonneg)
                          apply clarsimp
                          using prems(10) apply -
                          unfolding change_deltas_inv_def
                          apply clarsimp
                          apply (smt (verit, best))
                          done
                        done
                      done
                    done
                  done
                subgoal
                  using premst apply -
                  apply (elim disjE)
                  subgoal
                    apply clarsimp
                    apply (subst (asm) obtain_progress_def)
                    apply (subst (asm) extract_progress_def)
                    apply (clarsimp simp add: split_beta comp_def image_iff filter_map filter_concat split: prod.splits)
                      apply (cases "\<exists> m p'. (p', t, m) \<in> set (produ (os nid)) \<and> nxt sg (nid, p') = Some (nid, p)")
                    subgoal
                      apply clarsimp
                      subgoal for m' p'
                             using prems(14) apply -
                      unfolding produ_supported_def
                      apply (drule spec2, drule spec2, drule mp, assumption)
                      apply (elim disjE)
                      subgoal
       apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc nid (Src p')", simplified])
                        using prems(2) apply assumption
                        subgoal
                          using prems(3)
                          unfolding graph_summar_nt_def
                          by auto
                          apply (clarsimp simp add: filter_concat comp_def map_concat zmset_concat c_pts_change_multiplicities extract_progress_def obtain_progress_def split_beta split: prod.splits)
                        apply (subst filter_False)
                          subgoal
                            by (clarsimp simp add: set_map_filter split: option.splits)
                          apply simp
                          subgoal
                            using frontier_less_equal_zcount_pos by blast
                          done
                        subgoal
                          apply clarsimp
                          using prems(13) apply -
                          apply (drule spec[of _ nid'])
                          apply (drule spec[of _ nid])
                          unfolding changes_above_impl_inv_def
                          apply simp
                          subgoal for m''
                          apply (drule bspec[of _ _ "(Loc nid (Src p'), t, m'')"])
      subgoal
                            unfolding extract_progress_def obtain_progress_def
                            apply auto
                            done
                          apply simp
                          apply (rule frontier_less_equal_ifrontier_trans[of _ 0 "Loc nid (Src p')", simplified])
                          using prems(2) apply assumption
                          apply simp_all
                          subgoal
                            using prems(3)
                            unfolding graph_summar_nt_def
                            by clarsimp
                          done
                        done
                      done
                    done
                  subgoal
                    apply (subgoal_tac "zcount
          (zmset
            (map snd
              (filter (\<lambda>(l', t, d). Loc nid (Trg p) = l')
                (List.map_filter (\<lambda>(p, t, m). case subgraph.nxt sg (nid, p) of None \<Rightarrow> None | Some (nid', p') \<Rightarrow> Some (Loc nid' (Trg p'), t, m)) (produ (os nid))))))
          t = 0")
                    subgoal
                      apply (simp only: zcount_diff[symmetric] zcount_union[symmetric] zero_diff diff_0 right_minus add_uminus_conv_diff)
                      apply (drule zcount_gt_0_in_frontierD)
                      apply clarsimp
                      apply (drule in_frontier_minusD)
                      subgoal
                        apply clarsimp
                              using prems(10) apply -
                              unfolding change_deltas_inv_def
                              apply clarsimp
                              apply (rule zcount_zmset_ge_0I)
                              apply clarsimp
                              apply force
                              done
                            apply clarsimp
                      subgoal for ft ft'
                        apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc nid (Trg p)", simplified])
                        using prems(2) apply assumption
                        subgoal
                          apply (rule Graph.graph.path_weight_refl)
                          apply (rule dataflow_topology.axioms(1))
                          using prems(2) apply assumption
                          done
                        subgoal
                          apply (clarsimp simp add: filter_concat comp_def map_concat zmset_concat c_pts_change_multiplicities extract_progress_def obtain_progress_def split_beta split: prod.splits)
                          apply (subst filter_False)
                          subgoal
                            by (clarsimp simp add: set_map_filter split: option.splits)
                          apply simp
                          subgoal
                            using frontier_less_equal_iff2 frontier_less_equal_trans by blast
                          done
                        done
                      done
                    subgoal
                      apply (clarsimp simp add: zcount_zmset )
                      apply (subst filter_False)
                       apply simp_all
                      subgoal premises temp
                      apply (clarsimp simp add: set_map_filter split: option.splits)
                        using temp apply fast
                        done
                      done
                    done
                  done
                  subgoal
                    apply clarsimp
                    apply (subgoal_tac "\<exists> nid3 p3. nid3 \<noteq> nid \<and> nid3 \<noteq> nid' \<and> nxt sg (nid3, p3) = Some (nid, p) \<and> (\<exists> d. (p3, t, d) \<in> set (produ (os nid3)))")
                    defer
                    subgoal
                      apply (simp add: zcount_sum)
                      apply (drule sum_pos_ex_elem_pos)
                      apply clarsimp
                      apply (drule zcount_zmset_gt_0_set_Ex)
                      apply (auto 5 5 simp add: List.map_filter_def split: if_splits option.splits)
                      done
                    apply clarsimp
                    subgoal for nid3 p3 d
                      using prems(14) apply -
                      unfolding produ_supported_def
                      apply (drule spec2, drule spec2, drule mp, assumption)
                      apply (elim disjE)
                      subgoal
                        apply (rule frontier_less_equal_ifrontierI[of _ 0 "Loc nid3 (Src p3)", simplified])
                        using prems(2) apply assumption
                        subgoal
                          using prems(3)
                          unfolding graph_summar_nt_def
                          by clarsimp
                        subgoal
                          apply (clarsimp simp add: zmset_filter_extract_progress_Src_consumes_diff c_pts_change_multiplicities map_concat split_beta image_iff filter_map comp_def filter_concat split: prod.splits)
                          using frontier_less_equal_zcount_pos apply blast
                          done
                        done
                      subgoal
                        apply clarsimp
                        subgoal for m'
                          using prems(13) apply -
                          apply (drule spec[of _ nid'])
                          apply (drule spec[of _ nid3])
                          apply simp
                          unfolding changes_above_impl_inv_def
                          apply (drule bspec[of _ _ "(Loc nid3 (Src p3), t, m')"])
                          subgoal
                            unfolding extract_progress_def obtain_progress_def
                            apply auto
                            done
                          apply simp
                          apply (rule frontier_less_equal_ifrontier_trans[of _ 0 "Loc nid3 (Src p3)", simplified])
                          using prems(2) apply assumption
                          apply simp_all
                          subgoal
                            using prems(3)
                            unfolding graph_summar_nt_def
                            by clarsimp
                          done
                        done
                      done
                    done
                  done
                done
              subgoal premises temp2
                using temp apply -
                apply (drule set_extract_progressD)
                apply (elim disjE exE conjE)
                subgoal
                  using prems(13) apply -
                  apply (drule spec[of _ nid'])
                  apply (drule spec[of _ nid])
                  apply simp
                  unfolding changes_above_impl_inv_def
                  apply (drule bspec)
                  apply assumption
                  apply auto
                  done
                subgoal
                  using temp2 by auto
                subgoal for t'' s
                  apply hypsubst_thin
                  apply (rule frontier_less_equal_ifrontier_trans_alt[of _ _ "Loc nid (Trg p)"])
                  using prems(2) apply assumption
                  subgoal
                    using prems(3)
                    unfolding graph_summar_nt_def
                    apply clarsimp
                    done
                  subgoal
                    using temp2 by auto
                  done
                done
              done
            done
          done
        done
      done
    subgoal premises prems
      using prems(14) apply -
      unfolding produ_supported_def
      apply auto
      done
    done
  done
end