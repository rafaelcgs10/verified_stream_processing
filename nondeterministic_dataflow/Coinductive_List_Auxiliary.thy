theory Coinductive_List_Auxiliary

imports
    "HOL-Library.BNF_Corec"
    "Coinductive.Coinductive_List"
begin

fun lshift (infixr \<open>@@-\<close> 65) where
  "lshift [] lys = lys"
| "lshift (x # xs) lys = LCons x (lshift xs lys)"

friend_of_corec lshift where
  "lshift xs lys = (case xs of [] \<Rightarrow> (case lys of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons x xs)
    | x # xs \<Rightarrow> LCons x (lshift xs lys))"
  subgoal by (cases xs; cases lys; simp)
  subgoal by transfer_prover
  done

lemma lshift_simps[simp]:
  "lshift [] lxs = lxs"
  "lshift (x#xs) lxs = LCons x (lshift xs lxs)"
  by (subst lshift.code; auto split: llist.splits)+

lemma lset_lshift[simp]: "lset (lshift xs lxs) = set xs \<union> lset lxs"
  by (induct xs) auto

lemma lappend_llist_of: "lappend (llist_of xs) ys = xs @@- ys"
  by (induct xs) auto

lemma lshift_filter[simp]:
  "lfilter P (xs @@- lxs) = filter P xs @@- lfilter P lxs"
  by (metis lappend_llist_of lfilter_lappend_lfinite lfilter_llist_of lfinite_llist_of)

lemma snoc_shift[simp]: "(xs @ [x]) @@- ws = xs @@- LCons x ws"
  by (induct xs) auto

lemma shift_in_list: "xs @@- xxs = LCons x ys \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> x \<in> set xs"
  apply (induct xs)
   apply simp_all
  done

lemma shift_LNil[simp]:
  "xs @@- LNil = llist_of xs"
  apply (induct xs)
   apply simp_all
  done

lemma in_lset_shift_eq: "v \<in> lset (xs @@- lxs) \<longleftrightarrow> v \<in> set xs \<or> v \<in> lset lxs"
  apply safe
  subgoal
    apply (induct xs arbitrary: lxs)
     apply simp
    apply simp
    done
  subgoal
    apply (induct xs arbitrary: lxs)
     apply simp_all
    apply (elim disjE)
     apply simp_all
    done
  subgoal
    apply (induct xs arbitrary: lxs)
     apply simp_all
    done
  done

lemma lset_shift[simp]: "lset (xs @@- lxs) = set xs \<union> lset lxs"
  by (auto simp add: in_lset_shift_eq)

lemma LNil_eq_shift_iff:
  "LNil = xs @@- ys \<longleftrightarrow> xs = [] \<and> ys = LNil"
  apply (induct xs arbitrary: ys)
  by auto

lemma lshift_LNil_split:
  "xs @@- lxs = LNil \<longleftrightarrow> xs = [] \<and> lxs = LNil "
  by (metis LNil_eq_shift_iff)

lemma singleton_lshift:
  "[x] @@- lxs = LCons x lxs"
  apply simp
  done

lemma  shift_LCons_Cons:
  "(x1 # xs) @@- lxs = LCons x2 lxs' \<Longrightarrow> x1 = x2 \<and> (xs @@- lxs) = lxs'"
  by simp

lemma lnull_shift[simp]:
  "lnull (xs @@- lxs) = (List.null xs \<and> lnull lxs)"
   by (metis LNil_eq_shift_iff List.null_iff lnull_def)


corecursive lconcat where
  "lconcat xss = (if \<forall>xs \<in> lset xss. xs = [] then LNil else case xss of LNil \<Rightarrow> LNil
     | LCons [] xss' \<Rightarrow> lconcat xss'
     | LCons (x # xs) xss' \<Rightarrow> LCons x (lshift xs (lconcat xss')))"
  by (relation "measure (\<lambda>xss. LEAST i. lnth xss i \<noteq> [])")
    (auto simp: lset_conv_lnth Least_Suc)

lemma lconcat_unique:
  assumes "\<And>xss. f xss = (if \<forall>xs \<in> lset xss. xs = [] then LNil else case xss of LNil \<Rightarrow> LNil
     | LCons [] xss' \<Rightarrow> f xss'
     | LCons (x # xs) xss' \<Rightarrow> LCons x (lshift xs (f xss')))"
  shows "f = lconcat"
proof(rule ext)
  show "f xss = lconcat xss" for xss
  proof(coinduction arbitrary: xss rule: llist.coinduct_upto)
    case (Eq_llist xss)
    show ?case
      apply(induction xss rule: lconcat.inner_induct)
      apply(subst (1 2 3 5) assms)
      apply(subst (1 2 3 5) lconcat.code)
      apply (auto split: llist.splits list.splits intro: llist.cong_intros)
      done
  qed
qed

lemma lconcat_all_Nil: "\<forall>xs\<in>lset xss. xs = [] \<Longrightarrow> lconcat xss = LNil"
  by (subst lconcat.code) (auto)

lemma lconcat_code:
  "lconcat xss = (case xss of LNil \<Rightarrow> LNil | LCons xs xss' \<Rightarrow> lshift xs (lconcat xss'))"
  apply (rule lconcat_unique[THEN sym, THEN fun_cong])
  apply (subst lconcat.code)
  apply (auto simp: lconcat_all_Nil split: llist.splits list.splits)
  done

simps_of_case lconcat_simps[simp]: lconcat_code

lemma in_lset_lconcat_LNil_Nil:
  "xs \<in> lset xss \<Longrightarrow> lconcat xss = LNil \<Longrightarrow> xs = []"
  apply (induct xss arbitrary: rule: lset_induct)
   apply (subst (asm) lconcat_code)
   apply simp
   apply (subst (asm) lconcat_code)
  using lshift_LNil_split apply blast
  apply (metis LNil_eq_shift_iff lconcat_code llist.simps(5))
  done

lemma all_in_lset_lconcat_LNil_Nil: 
  "lconcat xss = LNil \<Longrightarrow> \<forall> xs \<in> lset xss. xs = []"
  using in_lset_lconcat_LNil_Nil apply auto
  done

lemma lconcat_not_all_Nil:
  "x \<in> lset (lconcat xss) \<Longrightarrow> \<not> (\<forall>xs\<in>lset xss. xs = [])"
  using lconcat_all_Nil by fastforce

lemma lconcat_eq_LNil[simp]: "lconcat xss = LNil \<longleftrightarrow> (\<forall>xs\<in>lset xss. xs = [])"
  using in_lset_lconcat_LNil_Nil lconcat_all_Nil by blast

lemma lconcat_LCons_ex:
  "lconcat lxs = LCons x lxs' \<Longrightarrow> \<exists>xa\<in>lset lxs. x \<in> set xa"
  apply (induct lxs rule: lconcat.corec.inner_induct)
  subgoal for xss
    apply (cases xss)
     apply (simp add: lconcat.code)
    subgoal for x xss'
      apply hypsubst_thin
      apply simp
      apply (metis lconcat_eq_LNil llist.distinct(1) lshift_simps(1) shift_in_list)
      done
    done
  done

lemma lconcat_remove_head:
  "lconcat lxs = LCons x xs \<Longrightarrow>
   lconcat (LCons (tl (lhd (ldropWhile (\<lambda>xs. xs = []) lxs))) (ltl (ldropWhile (\<lambda> xs. xs = []) lxs))) = xs"
  apply (induct lxs arbitrary: x rule: lconcat.corec.inner_induct)
  subgoal for xss
    apply (cases xss)
     apply (simp add: lconcat.code)
    subgoal for x xss'
      apply hypsubst_thin
      apply simp
      apply (intro impI conjI)
      apply (metis eq_LConsD lconcat.code lshift_simps(1))
      apply (metis list.exhaust_sel shift_LCons_Cons)
      done
    done
  done

lemma lconcat_inclusion:
  "x \<in> lset lys \<Longrightarrow> lys = lconcat lxs \<Longrightarrow> \<exists>xa\<in>lset lxs. x \<in> set xa"
  apply (induct lys arbitrary: lxs rule: lset_induct)
  using lconcat_LCons_ex apply metis
  subgoal for x' xs lxs
    apply (drule sym)
    apply (drule meta_spec[of _ "LCons (tl (lhd (ldropWhile (\<lambda> xs . xs = []) lxs))) (ltl (ldropWhile (\<lambda> xs . xs = []) lxs))"])
    apply (frule lconcat_LCons_ex)
    apply (smt (verit) empty_iff in_lset_ldropWhileD in_lset_ltlD lconcat_remove_head lhd_LCons lhd_ldropWhile lhd_ldropWhile_in_lset list.set(1) list.set_sel(2) lset_cases ltl_simps(2))
    done
  done

lemma inclusion_lconcat:
  "xs \<in> lset lxs \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<in> lset (lconcat lxs)"
  apply (induct lxs arbitrary: rule: lset_induct)
   apply (auto simp add: lconcat_code)
  done

lemma lset_lconcat:
  "lset (lconcat xss) = (\<Union>xs\<in>lset xss. set xs)"
  apply safe
  subgoal for x
    apply (induct "(lconcat xss)" arbitrary: rule: lset_induct)
     apply (metis UN_I lconcat_LCons_ex)
    using lconcat_inclusion 
    apply (metis UN_iff in_lset_ltlD ltl_simps(2))
    done
  subgoal for x xs
    using inclusion_lconcat apply fast
    done
  done

lemma lfinite_lconcat:
  "lfinite lxs \<Longrightarrow>
   lfinite (lconcat lxs)"
  apply (induct lxs rule: lfinite.induct)
   apply (simp add: lconcat_all_Nil)
  apply (subst lconcat.code)
  apply (auto split: list.splits)
  apply (metis lappend_llist_of lfinite_lappend lfinite_llist_of)
  done

lemma lconcat_lmap_LNil:
  "\<forall> x \<in> lset lxs . f x = LNil \<Longrightarrow>
   Coinductive_List.lconcat (lmap f lxs) = LNil"
  apply (auto simp add: Coinductive_List.lconcat_eq_LNil)
  done

lemma lconcat_correct:
  "lconcat lxs = Coinductive_List.lconcat (lmap llist_of lxs)"
  apply (rule lconcat_unique[THEN sym, THEN fun_cong])
  apply (simp add:   split: list.splits llist.splits)
  apply (simp add: lconcat_lmap_LNil )
  apply (intro allI impI)
  subgoal
    using lappend_llist_of
    by blast
  done

end