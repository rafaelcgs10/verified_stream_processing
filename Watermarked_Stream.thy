theory Watermarked_Stream
  imports
    "Coinductive.Coinductive_List"
    "Linear_Temporal_Logic_on_Llists"
    "HOL-Library.BNF_Corec"
    "HOL-Library.Multiset"
    "Utils"
begin

datatype ('t, 'd) event = Data (tmp: 't) (data: 'd) | Watermark (tmp: "'t::order")

fun wms where
  "wms [] = {}"
| "wms (Watermark wm#xs) = insert wm (wms xs)"
| "wms (Data t d#xs) = wms xs"

lemma wms_empty[simp]:
  "\<forall> x \<in> set xs . is_Data x \<Longrightarrow> wms xs = {}"
  apply (induct xs)
   apply simp
  subgoal for x xs
    apply (cases x)
     apply (auto split: event.splits)
    done
  done

lemma wms_correct:
  "wm \<in> wms xs \<longleftrightarrow> wm \<in> Watermark -` set xs"
  apply (induct xs)
  apply auto
  using insert_iff list.distinct(1) list.sel(3) wms.elims apply auto[1]
  subgoal for a xs
    apply (cases a)
    apply auto
    done
  done

fun tmps where
  "tmps [] = {}"
| "tmps (Watermark wm#xs) = tmps xs"
| "tmps (Data t d#xs) =  insert t (tmps xs)"

lemma tmps_tmps:
  "wms xs = {} \<Longrightarrow> tmps xs = tmp ` set xs"
  apply (induct xs)
   apply simp
  apply auto
    apply (metis (no_types, opaque_lifting) event.sel(1) insertE insert_not_empty list.inject neq_Nil_conv tmps.simps(3) wms.elims)
   apply (metis event.sel(1) insert_iff insert_not_empty list.distinct(1) list.inject tmps.simps(3) wms.elims)
  apply (smt (verit, best) imageI insert_iff insert_not_empty list.inject neq_Nil_conv tmps.simps(3) wms.elims)
  done

coinductive monotone :: "('t::order, 'd) event llist \<Rightarrow> 't set \<Rightarrow> bool" where
  LNil: "monotone LNil WM"
| LConsR: "\<lbrakk> monotone xs (insert wm WM)\<rbrakk> \<Longrightarrow> monotone (LCons (Watermark wm) xs) WM"
| LConsL: "\<lbrakk> \<forall> wm \<in> WM . \<not> wm \<ge> t; monotone xs WM \<rbrakk> \<Longrightarrow> monotone (LCons (Data t d) xs) WM"


lemma monotone_LCons_Watermark[simp]:
  "monotone (LCons (Watermark wm) lxs) WM = monotone lxs (insert wm WM)"
  apply safe
  using monotone.cases apply auto[1]
  using LConsR by blast

inductive monotone_prepend_cong for X where
  monotone_prepend_cong_base: "X xs S \<Longrightarrow> monotone_prepend_cong X xs S"
| monotone_prepend_cong_prepend: "monotone_prepend_cong X ys (wms xs \<union> S) \<Longrightarrow> monotone (llist_of xs) S \<Longrightarrow> monotone_prepend_cong X (xs @@- ys) S"

inductive_cases LNilE: "monotone LNil WM"
inductive_cases LConsWatermark: "monotone (LCons (Watermark wm) xs) WM"
inductive_cases LConsData: "monotone (LCons (Data t d) xs) WM"

lemma strict_monotone_coinduct_strict_monotone_prepend_cong1:
  assumes H1: "X lxs WM" 
    and H2:  "(\<And>x1 WM.
    X x1 WM \<Longrightarrow>
    (lnull x1) \<or>
    (\<exists>wm xs. x1 = LCons (Watermark wm) xs \<and> (monotone_prepend_cong X xs (insert wm WM) \<or> monotone xs (insert wm WM))) \<or>
    (\<exists>t xs d. x1 = LCons (Data t d) xs \<and> (\<forall>wm\<in>WM. \<not> t \<le> wm) \<and> (monotone_prepend_cong X xs WM \<or> monotone xs WM)))"  (is "\<And>x1 x2. X x1 x2 \<Longrightarrow> ?bisim x1 x2")
  shows "monotone lxs WM"
  using H1 apply -
  apply (erule monotone.coinduct[OF monotone_prepend_cong_base])
  subgoal for lxs WM
    apply (induct lxs WM rule: monotone_prepend_cong.induct) 
    subgoal for xs S
      apply (drule assms)
      apply auto
      done
    subgoal for ys xs S
      apply (cases xs)
       apply simp
      subgoal for a list
        apply (cases a)
         apply (metis LConsData llist_of.simps(2) monotone_prepend_cong_prepend lshift_simps(2) wms.simps(3))
        apply (smt (verit, best) LConsWatermark Un_insert_left Un_insert_right llist_of.simps(2) monotone_prepend_cong_prepend lshift_simps(2) wms.simps(2))
        done
      done
    done
  done



abbreviation good_example where
  "good_example \<equiv> LCons (Data 3 STR ''data2'') (LCons (Watermark 3) (LCons (Data 4 STR ''data'') (LCons (Watermark (14::nat)) LNil)))"

lemma strict_monotone_good_example: "monotone good_example {}"
  apply (rule LConsL)
   apply simp
  apply (rule LConsR)
  apply (rule LConsL)
   apply simp
  apply (rule LConsR)
  apply (rule LNil)
  done

lemma Data_tail_ahead_of_t:
  "x  \<in> lset xs \<Longrightarrow> x = Data t d \<Longrightarrow> monotone (LCons (Watermark wm) xs) WM \<Longrightarrow> \<not> t \<le> wm"
  apply (induct xs arbitrary: wm t d WM rule: Coinductive_List.lset_induct)
   apply (meson LConsData LConsWatermark insertI1)
  subgoal for x' xs wm t d
    apply hypsubst_thin
    apply (erule monotone.cases)
      apply simp_all
    apply hypsubst_thin
    apply (cases x')
     apply (meson LConsData LConsR)
    apply (smt (verit) LConsR insert_commute insert_iff llist.distinct(1) llist.inject order_trans monotone.simps)
    done
  done

lemma Data_set_strict_monotone_not_GE:
  "Data t d \<in> lset xs \<Longrightarrow> monotone xs WM \<Longrightarrow> \<forall> wm \<in> WM . \<not> t \<le> wm"
  apply (induct xs arbitrary: WM rule: Coinductive_List.lset_induct)
   apply (meson LConsData)
  by (metis LConsData LConsWatermark event.exhaust insert_iff)

lemma strict_monotone_with_smaller_initial_watermark_Watermark:
  "monotone xs (insert wm WM) \<Longrightarrow> \<forall> wm' \<in> WM . \<not> wm' \<ge> wm \<Longrightarrow> 
   monotone (LCons (Watermark wm) xs) WM"
  apply (rule LConsR)
   apply simp_all
  done

lemma strict_monotone_remove_wm[intro]:
  "monotone xs (insert wm WM) \<Longrightarrow> monotone xs WM"
  apply (coinduction arbitrary: xs wm WM rule: monotone.coinduct)
  apply (erule monotone.cases)
    apply simp
   apply (metis insert_commute)
  apply auto
  done

lemma strict_monotone_drop_head[intro]: "monotone (LCons x xs) WM \<Longrightarrow> monotone xs WM"
  apply (cases x)
   apply (metis LConsData)
  subgoal for wm
    apply (cases xs)
    using monotone.LNil apply blast
    subgoal for x' xs'
      apply simp
      apply hypsubst_thin
      using strict_monotone_remove_wm apply blast
      done
    done
  done

lemma strict_monotone_ltl: "monotone xs initial_watermark \<Longrightarrow> monotone (ltl xs) initial_watermark"
  using strict_monotone_drop_head by (metis llist.exhaust ltl_simps(1) ltl_simps(2))

lemma strict_monotone_ldrop_aux:
  "monotone xs initial_watermark \<Longrightarrow> ldrop (enat n) xs = xs' \<Longrightarrow> monotone xs' initial_watermark"
  apply (induct n arbitrary: xs xs')
   apply (subst (asm) enat_0)
   apply (subst (asm) ldrop_0)
   apply simp
  subgoal for n' xs1 xs2
    by (metis eSuc_enat ldrop_ltl strict_monotone_ltl)
  done

lemma strict_monotone_ldrop:
  "monotone xs initial_watermark \<Longrightarrow> ldrop n xs = xs' \<Longrightarrow> monotone xs' initial_watermark"
  apply (cases n)
   apply (simp add: strict_monotone_ldrop_aux)
  by (simp add: monotone.LNil)

lemma strict_monotone_LCons_Watermark_insert:
  "monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow> monotone lxs (insert wm WM)"
  apply (erule monotone.cases)
    apply simp_all
  done

lemma monotone_increases_set:
  " \<forall>wm\<in>WM. (\<forall>t\<in>tmps xs. \<not> t \<le> wm) \<Longrightarrow>
   monotone (llist_of xs) A \<Longrightarrow>
   monotone (llist_of xs) (A \<union> WM)"
  apply (induct xs arbitrary: WM A)
  using monotone.LNil apply auto[1]
  subgoal for a xs WM
    apply (cases a)
     apply simp_all
    apply (metis (no_types, lifting) Un_iff eq_LConsD event.distinct(1) event.sel(1) monotone.simps)
    apply (metis Un_insert_left)    
    done
  done

lemma strict_monotone_lfinite_lfilter_le_t_alt:
  "monotone lxs WM \<Longrightarrow>
   Watermark wm \<in> lset lxs \<Longrightarrow>
   wm \<ge> t \<Longrightarrow>
   lfinite (lfilter (\<lambda> x . case x of Data t' d \<Rightarrow> t' \<le> t | Watermark wm \<Rightarrow> False) lxs)"
  apply (cases "lfinite lxs")
  using lfinite_lfilterI apply blast
  subgoal
    apply (subst (asm) (1) in_lset_conv_lnth)
    apply (elim bexE exE conjE)
    subgoal for n
      apply (rule ldropn_lfinite_lfinter[where n=n])
       apply simp
      apply safe
      subgoal for x
        apply (induct n arbitrary: lxs WM)
        subgoal for lxs WM
          apply (cases lxs)
           apply simp_all
          apply (smt (verit, best) Data_set_strict_monotone_not_GE event.case_eq_if event.disc(2) event.exhaust_sel insertI1 order_trans)
          done
        subgoal for n lxs WM
          apply (cases lxs)
           apply simp_all
          using Suc_ile_eq strict_monotone_drop_head apply blast
          done
        done
      done
    done
  done

lemma strict_monotone_lfinite_lfilter_eq_t_alt:
  "monotone lxs WM \<Longrightarrow>
   Watermark wm \<in> lset lxs \<Longrightarrow>
   wm \<ge> t \<Longrightarrow>
   lfinite (lfilter (\<lambda> x . case x of Data t' d \<Rightarrow> t' = t | Watermark wm \<Rightarrow> False) lxs)"
  apply (cases "lfinite lxs")
  using lfinite_lfilterI apply blast
  subgoal
    apply (subst (asm) (1) in_lset_conv_lnth)
    apply (elim bexE exE conjE)
    subgoal for n
      apply (rule ldropn_lfinite_lfinter[where n=n])
       apply simp
      apply safe
      subgoal for x
        apply (induct n arbitrary: lxs WM)
        subgoal for lxs WM
          apply (cases lxs)
           apply simp_all
          apply (smt (verit, ccfv_SIG) Data_tail_ahead_of_t LConsR event.case_eq_if event.collapse(1) event.disc(2))
          done
        subgoal for n lxs WM
          apply (cases lxs)
           apply simp_all
          using Suc_ile_eq strict_monotone_drop_head apply blast
          done
        done
      done
    done
  done

lemma strict_monotone_LCons_Watermark_Data_not_ge:
  "monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   Data t batch \<in> lset lxs \<Longrightarrow> 
   \<not> t \<le> wm"
  apply (erule monotone.cases)
    apply (auto simp add: Data_set_strict_monotone_not_GE)
  done

lemma Watermark_in_lxs_in_sub:
  "t \<le> wm \<Longrightarrow>
   Watermark wm \<in> lset lxs \<Longrightarrow>
   lnth lxs n = Data t d  \<Longrightarrow>
   enat n < llength lxs \<Longrightarrow> 
   monotone lxs WM \<Longrightarrow>
   lfinite lxs \<Longrightarrow>
  \<forall>k\<in>{Suc n..<the_enat (llength lxs)}. \<forall>wm'\<ge>t. lnth lxs k \<noteq> Watermark wm' \<Longrightarrow>
  False"
  apply (induct "llength lxs")
  subgoal for n'
    apply (induct n' arbitrary: lxs n WM)
    using zero_enat_def apply force
    subgoal for n' lxs n WM
      apply (cases lxs)
       apply simp
      subgoal for x lxs'
        apply (drule meta_spec[of _ "lxs'"])
        apply simp
        apply (cases "Watermark wm = x")
         apply (metis event.simps(4) iless_Suc_eq in_lset_conv_lnth insertE llength_LCons lset_LCons strict_monotone_LCons_Watermark_Data_not_ge)
        apply (drule meta_spec[of _ "n - 1"])
        apply (drule meta_spec[of _ WM])
        apply (drule meta_mp)
         apply (metis co.enat.sel(2) eSuc_enat)
        apply (drule meta_mp)
         apply meson
        apply (drule meta_mp)
         apply (metis atLeastLessThan_iff co.enat.sel(2) eSuc_enat enat_ord_simps(2) image_Suc_atLeastLessThan image_eqI in_lset_conv_lnth lnth_LCons' lnth_Suc_LCons the_enat.simps zero_le)
        apply (drule meta_mp)
         apply (metis (no_types, lifting) Suc_ile_eq diff_is_0_eq in_lset_conv_lnth le_add_diff_inverse linorder_not_le order.strict_iff_order plus_1_eq_Suc zero_enat_def zero_le)
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply (drule meta_mp)
        subgoal
          apply auto
          apply (cases n)
           apply (metis atLeastLessThan_iff eSuc_enat eSuc_inject linorder_not_le lnth_Suc_LCons not_less_eq_eq the_enat.simps zero_less_Suc)
          apply auto
          apply (metis atLeastLessThan_iff eSuc_enat eSuc_inject less_Suc_eq_le linorder_not_le lnth_Suc_LCons the_enat.simps)
          done
        apply simp
        done
      done
    done
  apply (metis llength_eq_infty_conv_lfinite)
  done

definition stop_gathering_location :: "'t \<Rightarrow> ('t::order, 'b) event llist \<Rightarrow> nat" where
  "stop_gathering_location t xs = (if lfinite xs 
                                   then the_enat (llength xs)
                                   else LEAST x . (case lnth xs x of
                                                     Data _ _ \<Rightarrow> False 
                                                   | Watermark wm \<Rightarrow> t \<le> wm))"

lemma stop_gathering_location_finds_wm:
  "\<exists> wm \<ge> t. Watermark wm \<in> lset lxs \<Longrightarrow>
   \<not> lfinite lxs \<Longrightarrow>
   \<exists> n wm . stop_gathering_location t lxs = n \<and> lnth lxs n = Watermark wm \<and> wm \<ge> t"
  apply simp
  unfolding stop_gathering_location_def
  apply simp
  by (smt (verit) LeastI event.case_eq_if event.collapse(2) event.simps(6) lset_conv_lnth mem_Collect_eq)

lemma strict_monotone_lfinite_lfilter_le_t:
  "monotone lxs WM \<Longrightarrow>
   \<exists> wm \<ge> t. Watermark wm \<in> lset lxs \<Longrightarrow>
   lfinite (lfilter (\<lambda> x . case x of Data t' d \<Rightarrow> t' \<le> t | Watermark wm \<Rightarrow> False) lxs)"
  apply (cases "lfinite lxs")
  using lfinite_lfilterI apply blast
  subgoal
    apply (rule ldropn_lfinite_lfinter[where n="Suc (stop_gathering_location t lxs)"])
     apply (simp add: not_lfinite_llength)
    unfolding stop_gathering_location_def
    apply simp
    apply safe
    subgoal for x
      apply (cases x)
      subgoal for t' d'
        apply (subgoal_tac "\<exists>n wm. stop_gathering_location t lxs = n \<and> lnth lxs n = Watermark wm \<and> wm \<ge> t")
         defer
        using stop_gathering_location_finds_wm apply blast
        apply (cases x)
         apply auto
        apply (metis enat_ord_code(4) ldrop_enat ldropn_Suc_conv_ldropn not_lfinite_llength order_trans stop_gathering_location_def strict_monotone_LCons_Watermark_Data_not_ge strict_monotone_ldrop)
       done                 
      subgoal for wm'
        by simp
      done
    done
  done

definition productive where
  "productive s \<equiv> (\<forall> t . alwll ((holdsll (\<lambda> x . (\<exists> d . x = Data t d))) impll (evll (wholdsll (\<lambda> x . (\<exists> u \<ge> t . x = Watermark u))))) s)"

inductive productive_prepend_cong1 for X where
  productive_prepend_cong1_base: "X xs \<Longrightarrow> productive_prepend_cong1 X xs"
| productive_prepend_cong1_prepend_1: "productive_prepend_cong1 X ys \<Longrightarrow>
  \<forall> n < length xs . \<forall> t d . xs ! n = Data t d \<longrightarrow> (\<exists> wm .wm \<ge> t \<and> Watermark wm \<in> lset (drop (Suc n) xs @@- ys)) 
    \<Longrightarrow> productive_prepend_cong1 X (xs @@- ys)"


coinductive productive' where
  "lfinite xs \<Longrightarrow> productive' xs"
| "\<not> lfinite xs \<Longrightarrow> (\<exists>u \<in> Watermark -` lset xs. u \<ge> t) \<Longrightarrow> productive' xs \<Longrightarrow> productive' (LCons (Data t d) xs)"
| "\<not> lfinite xs \<Longrightarrow> productive' xs \<Longrightarrow> productive' (LCons (Watermark t) xs)"

lemma productive_productive': "productive ws \<Longrightarrow> productive' ws"
  apply (coinduction arbitrary: ws)
  subgoal for ws
    apply (cases ws)
     apply simp
    subgoal for x xs
      apply (cases x)
      subgoal for t d
        apply simp
        apply hypsubst_thin
        apply (simp only: productive_def alwll_LCons_iff  holdsll_LCons wholdsll_LCons
            productive_def[symmetric] sum.simps prod.simps simp_thms)
        apply (drule spec[of _ t])
        using evll_wholdsll_lfinite apply fastforce
        done 
      subgoal for wm
        apply simp
        apply (simp only: productive_def alwll_LCons_iff holdsll_LCons wholdsll_LCons
            productive_def[symmetric] sum.simps prod.simps simp_thms)
        done
      done
    done
  done


lemma productive'_productive: "productive' ws \<Longrightarrow> productive ws"
  unfolding productive_def
  apply (intro allI conjI)
  subgoal for t
    apply (coinduction arbitrary: ws)
    subgoal for ws
      apply (cases ws)
       apply simp
      subgoal for x xs
        apply (cases x)
        subgoal for u d
          apply (hypsubst_thin)
          apply (erule productive'.cases)
            apply (auto simp: lfinite_evll_wholdsll lset_induct)
          subgoal
            apply (induct xs rule: lfinite_induct)
             apply (auto simp: lnull_def) []
            subgoal for xs
              apply (cases xs)
               apply (auto simp: alwll_LCons_iff lfinite_evll_wholdsll productive'.intros)
              done
            done
          subgoal for wm
            apply (hypsubst_thin)
            apply (erule productive'.cases)
              apply (auto simp: base evll.step lfinite_evll_wholdsll lset_induct)
            done
          done
        subgoal for wm
          apply (hypsubst_thin)
          apply (erule productive'.cases)
            apply (auto simp: base evll.step lfinite_evll_wholdsll lset_induct)
          using productive'.intros(1) apply blast
          done
        done
      done
    done
  done

lemma productive_alt: "productive = productive'"
  unfolding fun_eq_iff using productive_productive' productive'_productive by blast

lemmas productive_intros = productive'.intros[folded productive_alt]
lemmas productive_cases = productive'.cases[folded productive_alt]
lemmas productive_coinduct[coinduct pred] = productive'.coinduct[folded productive_alt]

lemma productive_drop_head: "productive (LCons a xs) \<Longrightarrow> productive xs"
  unfolding productive_def
  apply safe
  subgoal for t
    apply (coinduction rule: alwll.coinduct)
    apply (metis (mono_tags) alwll.simps alwll_LConsD)
    done
  done

lemma productive_lappendD[rotated]: "lfinite xs \<Longrightarrow> productive (lappend xs ys) \<Longrightarrow> productive ys"
  by (induct xs rule: lfinite_induct)
    (auto simp add: lnull_def neq_LNil_conv dest!: productive_drop_head)

lemma productive'_coinduct_prepend_cong1:
  assumes H1: "X lxs" 
    and H2:  "(\<And>x1.
    X x1 \<Longrightarrow>
    (\<exists>xs. x1 = xs \<and> lfinite xs) \<or>
    (\<exists>xs t d. x1 = LCons (Data t d) xs \<and> \<not> lfinite xs \<and> Bex (Watermark -` lset xs) ((\<le>) t) \<and> (productive_prepend_cong1 X xs \<or> productive' xs)) \<or>
    (\<exists>xs wm. x1 = LCons (Watermark wm) xs \<and> \<not> lfinite xs \<and> (productive_prepend_cong1 X xs \<or> productive' xs)))" (is "\<And>x1 . X x1 \<Longrightarrow> ?bisim x1")
  shows "productive' lxs"
  using H1 apply -
proof (erule productive'.coinduct[OF productive_prepend_cong1_base])
  fix lxs
  assume  "productive_prepend_cong1 X lxs"
  then show "?bisim lxs"
    apply (induct lxs rule: productive_prepend_cong1.induct) 
    subgoal for xs
      apply (drule assms)
      apply auto
      done
    subgoal for ys xs
      apply (cases xs)
       apply simp
      subgoal for a list
        apply (cases a)
         apply hypsubst_thin
        subgoal for t' d'
          apply (elim exE disjE conjE)
              apply (rule disjI1)
              apply (metis lappend_llist_of lfinite_lappend lfinite_llist_of)
             apply (rule disjI2)
             apply (fastforce simp add: productive_prepend_cong1_prepend_1)+
          done
        apply hypsubst_thin
        subgoal for wm
          apply (elim exE disjE conjE)
              apply (rule disjI1)
              apply auto[1]
             apply (rule disjI2)+
             apply (fastforce simp add: productive_prepend_cong1_prepend_1)+
          done
        done
      done
    done
qed

lemmas productive_coinduct_prepend_cong1[coinduct pred] = productive'_coinduct_prepend_cong1[folded productive_alt]

lemma productive'_coinduct_prepend_cong1_shift:
  assumes H1: "X lxs" 
    and H2:  "(\<And>x1.
    X x1 \<Longrightarrow>
    (\<exists>lxs. x1 = lxs \<and> lfinite lxs) \<or>
    (\<exists>lxs t d wm. x1 = [Data t d, Watermark wm] @@- lxs \<and> t \<le> wm \<and> \<not> lfinite lxs \<and> productive_prepend_cong1 X lxs) \<or>
    (\<exists>lxs wm. x1 = LCons (Watermark wm) lxs \<and> \<not> lfinite lxs \<and> (productive_prepend_cong1 X lxs \<or> productive' lxs)))" (is "\<And>x1 . X x1 \<Longrightarrow> ?bisim x1") 
  shows "productive' lxs"
  using assms apply -
  apply (erule productive'_coinduct_prepend_cong1)
  subgoal for lxs
    apply (drule meta_spec)
    apply (drule meta_mp)
     apply assumption
    apply (elim exE conjE disjE)
     apply simp
    apply hypsubst_thin
    apply (rule disjI2)
    apply (rule disjI1)
    apply simp
    apply (rule conjI)
     apply blast
    apply (rule disjI1)
    subgoal for lxs t d wm
      using productive_prepend_cong1_prepend_1[where xs="[Watermark wm]"] apply simp
      apply assumption
      done
    apply auto
    done
  done

lemma productivity_good_example: "productive good_example"
  unfolding productive_def
  apply safe
  subgoal for t
    apply (rule alwll)
     apply simp
     apply safe
     apply (rule evll.step)
     apply (rule evll.base)
     apply simp_all
    apply (rule alwll)
     apply simp_all
    apply (rule alwll)
     apply simp_all
     apply safe
     apply (rule evll.step)
     apply (rule evll.base)
     apply simp_all
    apply (rule alwll)
     apply simp_all
    done
  done

lemma productive_ldrop: "productive xs \<Longrightarrow> productive (ldrop (enat n) xs)"
  apply (induct n)
   apply simp_all
  using zero_enat_def apply fastforce
  apply (metis ldrop_eSuc_ltl ldrop_enat ltl_ldropn ltl_simps(1) ltl_simps(2) neq_LNil_conv productive_drop_head)
  done

lemma productive_finds_data:
  "productive lxs \<Longrightarrow>
   lnth lxs n = Data t d \<Longrightarrow>
   \<not> lfinite lxs \<Longrightarrow>
   \<exists> m > n . \<exists> wm \<ge> t . lnth lxs m = Watermark wm"
  apply (subgoal_tac "evll (wholdsll (\<lambda>x. \<exists>u\<ge>t. x = Watermark u)) (ldrop (enat n) lxs)")
   apply (drule evll_wholdsll_finds_n_alt)
    apply simp
   apply safe
  subgoal for n' u
    apply (rule exI[of _ "n' + n"])
    apply simp
    apply safe
     apply (metis enat_ord_code(4) event.simps(4) ldrop_enat ldropn_Suc_conv_ldropn llength_eq_infty_conv_lfinite lnth_0 zero_less_iff_neq_zero)
    by (simp add: not_lfinite_llength)
  apply (drule productive_ldrop[where n=n])
  unfolding productive_def
  apply (drule spec[where x=t])
  apply (simp add: ldrop_enat)
  apply (subst ldropn_Suc_conv_ldropn[symmetric])
   apply (simp add: not_lfinite_llength)
  apply (simp add: not_lfinite_llength)
  apply (metis (mono_tags, lifting) alwll_headD enat_ord_code(4) holdsll.simps(2) ldropn_Suc_conv_ldropn llength_eq_infty_conv_lfinite)
  done

lemma strict_monotone_productive_lfinite_lfilter_eq_t:
  "monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   lfinite (lfilter (\<lambda> x . case x of Data t' d \<Rightarrow> t' = t | Watermark wm \<Rightarrow> False) lxs)"
  apply (cases "lfinite lxs")
  using lfinite_lfilterI apply blast
  apply (cases "\<exists> d . Data t d \<in> lset lxs")
  subgoal
    apply (subst (asm) in_lset_conv_lnth)
    apply (elim conjE exE)
    subgoal for d n
      apply (frule productive_finds_data[where t=t and d=d and n= n])
        apply assumption+
      apply (elim conjE exE bexE)
      subgoal for m wm
        apply (simp add: not_lfinite_llength)
        apply (metis enat_ord_code(4) in_lset_conv_lnth not_lfinite_llength strict_monotone_lfinite_lfilter_eq_t_alt)
        done
      done
    done
  subgoal
    apply (cases "\<exists> d . Watermark t \<in> lset lxs")
    subgoal
      apply (subst (asm) (2) in_lset_conv_lnth)
      apply (elim bexE exE conjE)
      subgoal for d m
        apply (metis dual_order.refl in_lset_conv_lnth strict_monotone_lfinite_lfilter_eq_t_alt)
        done
      done
    apply (rule ldropn_lfinite_lfinter[where n="0"])
     apply (simp add: not_lfinite_llength)
    apply simp
    apply (smt (verit, best) event.split_sel_asm inf_bool_def)
    done
  done

abbreviation "data_list_at lxs t \<equiv>
  List.map_filter (case_event (\<lambda>t d. Some d) Map.empty) (list_of (lfilter (\<lambda> x . case x of Data t' d \<Rightarrow> t' = t | Watermark wm \<Rightarrow> False) lxs))"

definition "coll WM lxs t = (
  if (\<exists> wm. Watermark wm \<in> lset lxs \<and> t \<le> wm) \<and> monotone lxs WM \<or> lfinite lxs
  then mset (data_list_at lxs t)
  else {#})"

lemma coll_LNil[simp]: "coll WM LNil t = {#}"
  unfolding coll_def
  by (simp add: map_filter_simps(2))

definition "ts lxs t = {t' . \<exists> d' . Data t' d' \<in> lset lxs \<and> t' \<le> t}"

lemma set_inv_llist_of_eq_lset:
  "lfinite lxs \<Longrightarrow>
   set (inv llist_of lxs) = lset lxs"
  apply (induct lxs rule: lfinite_rev_induct)
   apply (simp add: inv_f_eq)
  apply simp
  apply (smt (verit, best) Un_insert_right f_inv_into_f lappend_LNil2 lfinite_LConsI lfinite_eq_range_llist_of lfinite_lappend lset_LCons lset_lappend_conv lset_llist_of)
  done

lemma ts_LCons_Watermark[simp]:
  "ts (LCons (Watermark wm) lxs) t = ts lxs t"
  unfolding ts_def
  apply simp
  done

definition "ts' lxs t = tmp ` set (list_of (lfilter (\<lambda> x . case x of Data t' d \<Rightarrow> t' \<le> t | Watermark wm \<Rightarrow> False) lxs))"

lemma ts_eq_ts':
  "monotone lxs WM \<Longrightarrow>
   \<exists> wm\<ge>t. Watermark wm \<in> lset lxs \<Longrightarrow>
   ts lxs t = ts' lxs t"
  unfolding ts_def ts'_def list_of_def
  apply (subgoal_tac "lfinite (lfilter (case_event (\<lambda> t' d. t' \<le> t) (\<lambda>wm. False)) lxs)")
   defer
  using strict_monotone_lfinite_lfilter_le_t apply blast
  apply (simp only: if_True)
  apply (subst set_inv_llist_of_eq_lset)
  using strict_monotone_lfinite_lfilter_le_t apply blast
  apply auto
    apply (metis (no_types, lifting) event.sel(1) event.simps(5) imageI mem_Collect_eq)
   apply (metis event.case_eq_if event.collapse(1))
  apply (metis event.case_eq_if)
  done

lemma finite_ts[simp]:
  "monotone lxs WM \<Longrightarrow>
   \<exists> wm\<ge>t . Watermark wm \<in> lset lxs \<Longrightarrow>
   finite (ts lxs t)"
  apply (subst ts_eq_ts')
    apply assumption+
  unfolding ts'_def
  apply blast
  done

lemma ts_Data_in[simp]:
  "ts (LCons (Data t' d) lxs) t = (if t' \<le> t then insert t' (ts lxs t) else ts lxs t)"
  unfolding ts_def
  apply (cases "t' \<le> t")
   apply (simp only: if_True lset_LCons)
   apply blast
  apply auto
  done

lemma ts_shift_map_Data[simp]:
  "ts (map (\<lambda>(x, y). Data x y) buf @@- lxs) wm = {t \<in> fst ` set buf. t \<le> wm} \<union> ts lxs wm"
  unfolding ts_def
  apply (auto simp add: split_beta split: prod.splits)
  done

definition "ws lxs wm = {wm'. Watermark wm' \<in> lset (ltakeWhile ((\<noteq>) (Watermark wm)) lxs)}"

lemma ws_LCons_Watermark[simp]:
  "ws (LCons (Watermark wm') lxs) wm = (if wm = wm' then {} else insert wm' (ws lxs wm))"
  unfolding ws_def
  apply auto  
  done

lemma ws_LCons_Data[simp]:
  "ws (LCons (Data t d) lxs) wm = ws lxs wm"
  unfolding ws_def
  apply auto
  done

lemma ws_Data_map_shift[simp]:
  "ws (((map (\<lambda> (t, d). Data t d) xs)) @@- lxs) wm = ws lxs wm"
  apply (induct xs)
  subgoal
  apply auto
  done
  subgoal for x xs'
    apply (cases x)
    subgoal for t d
      apply auto
      done
    done
  done

lemma map_filter_empty:
  "List.map_filter P xs = [] \<longleftrightarrow> (\<forall> x \<in> set xs. P x = None)"
  by (smt (verit) emptyE empty_filter_conv empty_set imageI last_in_set list.map(1) list.set_map map_filter_def)




lemma coll_Data_eq_coll_ltl[simp]:
  "coll WM (LCons (Data t' d) lxs) t = (
   if (monotone (LCons (Data t' d) lxs) WM \<and> (\<exists> wm . Watermark wm \<in> lset lxs \<and> t \<le> wm)) \<or> lfinite lxs  
   then (if t' = t then add_mset d (coll WM lxs t) else coll WM lxs t)
   else {#})"
  apply (auto simp add: map_filter_simps coll_def split: if_splits event.splits)
  apply (subst list_of_LCons)
  subgoal for wm
    using strict_monotone_lfinite_lfilter_eq_t_alt[where wm=wm and WM=WM and lxs=lxs and t=t] apply simp
    by (smt (verit, best) event.case_eq_if event.collapse(1) event.distinct(1) event.sel(1) event.split_sel le_boolD lfilter_cong linorder_le_cases)
  apply (subst map_filter_simps)
  apply simp
  done


lemma coll_eq_coll_ltl_Watermark[simp]:
  "coll WM (LCons (Watermark wm) lxs) t = coll (insert wm WM) lxs t"
  apply (auto simp add: coll_def)
  by (smt (verit, best) Data_set_strict_monotone_not_GE event.split_sel insertI1 le_boolE lfilter_empty_conv list_of_LNil map_filter_simps(2) min_def)


lemma ts_all_not_le:
  "monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   \<exists>wm\<ge>t. Watermark wm \<in> lset lxs \<Longrightarrow>
   (\<forall>x\<in>ts lxs t. \<not> x \<le> wm)"
  apply (erule monotone.cases)
    apply simp_all
  unfolding ts_def
  apply safe
  apply (meson Data_set_strict_monotone_not_GE insertI1)
  done

fun ltaken_Data :: "nat \<Rightarrow> _ llist \<Rightarrow> _ list" where
  "ltaken_Data (Suc n) (LCons (Watermark _) lxs) = ltaken_Data n lxs"
| "ltaken_Data (Suc n) (LCons (Data t batch) lxs) = (t, batch) # ltaken_Data n lxs"
| "ltaken_Data _ _ = []"

lemma ltaken_Data_0[simp]:
  "ltaken_Data 0 lxs = []"
  apply (cases lxs)
   apply simp_all
  done

lemma ltaken_Data_LCons_Watermark:
  "ltaken_Data n (LCons (Watermark wm) lxs) = ltaken_Data (n - 1) lxs"
  apply (induct n arbitrary: lxs wm)
   apply simp_all
  done


definition coll_list :: "('t::order \<times> 'd) list \<Rightarrow> 't \<Rightarrow> _ list" where
  "coll_list xs t = map snd (filter (((=) t) \<circ> fst) xs)"

lemma coll_list_append[simp]:
  "coll_list (xs@ys) t = coll_list xs t @ coll_list ys t"
  unfolding coll_list_def
  apply force
  done

lemma coll_list_nil[simp]:
  "coll_list [] t = []"
  unfolding coll_list_def
  apply simp
  done

lemma t_in_ts[simp]:
  "t \<in> ts lxs wm \<longleftrightarrow> (\<exists> d. Data t d \<in> lset lxs) \<and> t \<le> wm"
  unfolding ts_def
  apply auto
  done
  
abbreviation
  "EV_LE_WM wm ev \<equiv> (case ev of Watermark wm' \<Rightarrow> False | Data t d \<Rightarrow> t \<le> wm)"

definition
  "incr_coll lxs wm = List.map_filter (\<lambda> e . case e of Watermark _ \<Rightarrow> None | Data t d \<Rightarrow> Some (t, d))
    (list_of (lfilter (EV_LE_WM wm)lxs))"

abbreviation
  "EV_EX_WS lxs wm e \<equiv> case e of Data t d \<Rightarrow> \<not> (\<exists> wm' \<in> ws lxs wm. t \<le> wm') | Watermark _ \<Rightarrow> False"

abbreviation
  "get_Data e \<equiv> case e of Data t d \<Rightarrow> Some d | Watermark _ \<Rightarrow> None"

lemma ltaken_Data_in_Suc:
  "x \<in> set (ltaken_Data n lxs) \<Longrightarrow>
   n \<le> m \<Longrightarrow>
   x \<in> set (ltaken_Data m lxs)"
  apply (induct n arbitrary: m lxs)
   apply auto
  subgoal for n m lxs
    apply (cases lxs)
     apply auto
    subgoal for x lxs'
      apply (cases x)
       apply auto
      using Suc_le_D apply fastforce
       apply (cases m)
        apply (auto simp add: ltaken_Data_LCons_Watermark)
      done
    done
  done

lemma in_ts_strict_monotone_False:
  "monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   t \<in> ts lxs wm \<Longrightarrow>
   False"
  unfolding ts_def
  using Data_tail_ahead_of_t apply fastforce
  done

lemma in_ts_LCons_Data_cases:
  "t \<in> ts (LCons (Data t' d) lxs) wm \<Longrightarrow>
   t \<in> ts lxs wm \<or> t = t'"
  unfolding ts_def
  apply auto
  done

lemma in_ts_transitive:
  "x \<in> ts lxs t \<Longrightarrow>
   t \<in> ts lxs wm \<Longrightarrow>
   x \<in> ts lxs wm"
  unfolding ts_def
  apply auto
  done

lemma ts_le:
  "t' \<in> ts lxs t \<Longrightarrow>
   t' \<le> t"
  unfolding ts_def
  apply auto
  done

lemma ldropn_LCons_ltaken_Data:
  "\<exists>n'\<le>n. ldropn n' lxs = LCons (Data wm batch) lxs' \<Longrightarrow> 
  (wm, batch) \<in> set (ltaken_Data (Suc n) lxs)"
  apply (induct "Suc n" lxs arbitrary: n rule: ltaken_Data.induct)
    apply auto
    apply (metis (no_types, lifting) diff_is_0_eq' diff_le_self event.distinct(1) gr0_conv_Suc ldropn_0 ldropn_Suc_LCons llist.inject not_less_eq_eq order.order_iff_strict)
   apply (metis (no_types, lifting) diff_is_0_eq' diff_le_self event.inject(1) gr0_conv_Suc ldropn_0 ldropn_Suc_LCons llist.inject not_less_eq_eq order.order_iff_strict)+
  done

lemma in_ltaken_Data_ldropn_LCons:
  "(wm, batch) \<in> set (ltaken_Data (Suc n) lxs) \<Longrightarrow> \<exists>n'\<le>n. \<exists>lxs'. ldropn n' lxs = LCons (Data wm batch) lxs'"
  apply (induct "Suc n" lxs arbitrary: n rule: ltaken_Data.induct)
    apply auto
   apply (metis (no_types, opaque_lifting) Suc_less_eq dual_order.strict_trans2 empty_iff empty_set gr0_conv_Suc ldropn_Suc_LCons lessI ltaken_Data_0 ltaken_Data_in_Suc not_less_eq_eq)
  apply (metis empty_iff empty_set ldropn_Suc_LCons ltaken_Data_0 not0_implies_Suc not_less_eq_eq)
  done

lemma timestamp_in_taken_Data_inversion_aux:
  "t \<in> fst ` (\<Union>a\<in>set (ltaken_Data n lxs). set (snd a)) \<Longrightarrow>
   \<exists> wm batch . (wm, batch) \<in> set (ltaken_Data n lxs) \<and> t \<in> fst ` set batch"
  apply (induct n arbitrary: lxs)
   apply auto
  subgoal for n lxs b aa ba
    apply (cases lxs)
     apply auto
    subgoal for x lxs'
      apply (cases x)
       apply auto
        apply (metis fst_conv imageI)+
      done
    done
  done

lemma ts_LCons:
  "t \<in> ts lxs wm \<Longrightarrow>
   t \<in> ts (LCons (Data t' d) lxs) wm"
  unfolding ts_def
  apply auto
  done

lemma in_ts_LCons_LE:
  "t \<le> wm \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<exists> wm' \<ge> wm . Watermark wm' \<in> lset lxs \<Longrightarrow>
   t \<in> ts (LCons (Data t d) lxs) wm"
  unfolding ts_def
  apply auto
  done

lemma coll_list_concat_ltaken_Data_Nil:
  "\<not> (\<exists> wm d . Data wm d \<in> lset lxs \<and> t \<in> fst ` set d) \<Longrightarrow>
   coll_list (concat (map snd (ltaken_Data n lxs))) t = []"
  apply (induct n arbitrary: lxs)
   apply simp
  subgoal for n lxs
    apply (cases lxs)
     apply auto
    subgoal for x lxs'
      apply (cases x)
      unfolding coll_list_def
       apply auto
      apply (smt (z3) comp_apply filter_False image_iff)
      done
    done
  done

lemma coll_empty:
  "\<not> (\<exists> d . Data t d \<in> lset lxs) \<Longrightarrow>
   coll WM lxs t = {#}"
  unfolding coll_def
  apply (smt (verit) dual_order.refl event.split_sel le_boolD lfilter_empty_conv list_of_LNil map_filter_simps(2) mset_zero_iff nless_le)
  done


lemma img_tmp_Lambda_Data:
  "finite A \<Longrightarrow> tmp ` (\<lambda>x. Data x (f x)) ` A = A"
  apply (induct A rule: finite_induct)
  apply auto
  done

lemma productive_Data_in_ge_Watermark_in:
  "Data t d \<in> lset lxs \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<not> lfinite lxs \<Longrightarrow>
   \<exists> wm. Watermark wm \<in> lset lxs \<and> t \<le> wm"
  by (metis enat_ord_code(4) in_lset_conv_lnth llength_eq_infty_conv_lfinite productive_finds_data)

lemma productive_find_bigger_watermark:
  "lnth lxs m = Data t d\<Longrightarrow>
   m < llength lxs \<Longrightarrow>
   \<not> lfinite lxs \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> n wm. m < n \<and> n < llength lxs \<and> lnth lxs n = Watermark wm \<and> t \<le> wm"
  apply (induct m arbitrary: lxs)
  subgoal for lxs
    apply (erule productive_cases)
    apply auto
    apply (metis Suc_ile_eq in_lset_conv_lnth lnth_Suc_LCons zero_less_Suc)
    done
  subgoal for m lxs
    apply (cases lxs)
    apply simp_all
    apply hypsubst_thin
    apply (metis Suc_ile_eq llist.disc(2) lnth_ltl ltl_simps(2) not_less_eq productive_drop_head)
    done
  done

lemma [simp]:
  "Watermark -` insert (Watermark wm) A = insert wm (Watermark -` A)"
  "Watermark -` insert (Data t d) A = Watermark -`A"
  unfolding vimage_def
  apply auto
  done

lemma map_case_sum_Watermark[simp]:
  "map (case_sum Watermark Watermark) xs \<noteq> Data t d#ys"
  by (smt (verit) event.distinct(1) map_eq_Cons_D sum.case_eq_if)

lemma monotone_all_Watermarks:
  "\<forall> x \<in> lset lxs. \<not> is_Data x \<Longrightarrow>
   monotone lxs WM"
  apply (coinduction arbitrary: lxs WM rule: monotone.coinduct)
  apply auto
  by (metis event.disc(1) event.exhaust llist.exhaust llist.set_intros(2) lset_intros(1))

lemma Inl_in_Inr_img[simp]:
  "Inl wm \<in> Inr ` WM \<Longrightarrow> False"
  by auto

lemma Inr_in_Inl_img[simp]:
  "Inr wm \<in> Inl ` WM \<Longrightarrow> False"
  by auto

lemma wms_map_case_sum[simp]:
  "wms (map (case_sum Watermark Watermark) xs) = Inl -` set xs \<union> Inr -` set xs"
  apply (induct xs)
  apply (auto split: sum.splits)
  done

end
