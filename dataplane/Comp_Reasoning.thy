theory Comp_Reasoning

imports
    "HOL-ex.Sketch_and_Explore" 
    Timely_Infrastructure_Dis
begin

lemma "dataflow_op sg op = dataflow_op sg' op' \<Longrightarrow> sg = sg' \<and> op = op'"
  apply(subst (asm) (2) dataflow_op.corec.code)
  apply(subst (asm) (1) dataflow_op.corec.code)
  apply(subgoal_tac "countable {y. \<exists>x. x \<in> rcset (choices op) \<and>
             nop sg x \<and>
             y =
             (case x of
              Read (Inl nid) f \<Rightarrow>
                case propagate_all (summ sg) (pt_tr sg) of
                Some conf' \<Rightarrow>
                  let sg' = sg\<lparr>pt_tr := conf', upfro := (upfro sg)(nid := False)\<rparr>;
                      imp_fron = \<lambda>p. c_imp (pt_tr sg') (Loc nid (Trg p))
                  in Silent (dataflow_op sg' (f (Inl (Inr (frontier \<circ> imp_fron)))))
              | Read (Inr (nid, p)) f \<Rightarrow> Read (nid, p) (\<lambda>x. dataflow_op sg (f (Inr x)))
              | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow>
                  Silent
                   (dataflow_op
                     (sg\<lparr>upfro := \<lambda>_. True,
                           pt_tr := change_multiplicities (summ sg) (extract_progress nid (edges sg) st) (pt_tr sg)\<rparr>)
                     op')
              | Write op' (Inl nid) (Inl (Inr b)) \<Rightarrow> Code.abort STR ''Operator in dataflow_op breaks contract'' (\<lambda>_. \<oslash>)
              | Write op' (Inl nid) (Inr b) \<Rightarrow> Code.abort STR ''Operator in dataflow_op breaks contract'' (\<lambda>_. \<oslash>)
              | Write op' (Inr (nid, p)) (Inl aa) \<Rightarrow> Code.abort STR ''Operator in dataflow_op breaks contract'' (\<lambda>_. \<oslash>)
              | Write op' (Inr (nid, p)) (Inr x) \<Rightarrow> Write (dataflow_op sg op') (nid, p) x | Choice cset \<Rightarrow> \<oslash>
              | Silent op' \<Rightarrow> Silent (dataflow_op sg op'))} \<and> 
      countable {y. \<exists>x. x \<in> rcset (choices op') \<and>
             nop sg' x \<and>
             y =
             (case x of
              Read (Inl nid) f \<Rightarrow>
                case propagate_all (summ sg') (pt_tr sg') of
                Some conf' \<Rightarrow>
                  let sg' = sg'\<lparr>pt_tr := conf', upfro := (upfro sg')(nid := False)\<rparr>;
                      imp_fron = \<lambda>p. c_imp (pt_tr sg') (Loc nid (Trg p))
                  in Silent (dataflow_op sg' (f (Inl (Inr (frontier \<circ> imp_fron)))))
              | Read (Inr (nid, p)) f \<Rightarrow> Read (nid, p) (\<lambda>x. dataflow_op sg' (f (Inr x)))
              | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow>
                  Silent
                   (dataflow_op
                     (sg'\<lparr>upfro := \<lambda>_. True,
                            pt_tr := change_multiplicities (summ sg') (extract_progress nid (edges sg') st) (pt_tr sg')\<rparr>)
                     op')
              | Write op' (Inl nid) (Inl (Inr b)) \<Rightarrow> Code.abort STR ''Operator in dataflow_op breaks contract'' (\<lambda>_. \<oslash>)
              | Write op' (Inl nid) (Inr b) \<Rightarrow> Code.abort STR ''Operator in dataflow_op breaks contract'' (\<lambda>_. \<oslash>)
              | Write op' (Inr (nid, p)) (Inl aa) \<Rightarrow> Code.abort STR ''Operator in dataflow_op breaks contract'' (\<lambda>_. \<oslash>)
              | Write op' (Inr (nid, p)) (Inr x) \<Rightarrow> Write (dataflow_op sg' op') (nid, p) x | Choice cset \<Rightarrow> \<oslash>
              | Silent op' \<Rightarrow> Silent (dataflow_op sg' op'))}")
  subgoal
    apply(auto dest!: Collect_inj simp add: cimage_def image_def cset.acset_inject Collect_inj)
    apply(erule thin_rl)
    subgoal
      apply(cases sg; cases sg'; simp)
      apply auto
      subgoal
        sorry
      sorry
    sorry
  sorry


lemma dataflow_tree_to_graph_aux_Comp: "dataflow_tree_to_graph_aux n dt1 = dataflow_tree_to_graph_aux n dt1' \<Longrightarrow>
       dataflow_tree_to_graph_aux (fst (dataflow_tree_to_graph_aux n dt1)) dt2 = dataflow_tree_to_graph_aux (fst (dataflow_tree_to_graph_aux n dt1)) dt2' \<Longrightarrow>
        dataflow_tree_to_graph_aux n (Comp buf dt1 dt2) = dataflow_tree_to_graph_aux n (Comp buf dt1' dt2')"
  apply auto
  by(cases "dataflow_tree_to_graph_aux n dt1'"; simp)

lemma dataflow_tree_to_graph_nodes_eq: "dataflow_tree_to_graph dt1 = dataflow_tree_to_graph dt1' \<Longrightarrow>
       nodes_count dt1 = nodes_count dt1'"
  unfolding dataflow_tree_to_graph_def
  sorry

lemma dataflow_tree_to_graph_alt_def:  "dataflow_tree_to_graph (df :: ('id :: {minus,one,plus,zero,ord,enum,hashable}, _, _, _, _) dataflow_tree) = (
  if \<not> has_zero_cyc (snd (dataflow_tree_to_graph_aux 0 df)) \<and>
     no_self_loop_checker (snd (dataflow_tree_to_graph_aux 0 df)) \<and>
     implementation_graph_checker (weights_to_graph_fun (remove_non_zero_weights (snd (dataflow_tree_to_graph_aux 0 df)))) \<and>
     CARD ('id) = nodes_count df
  then (snd (dataflow_tree_to_graph_aux 0 df))
  else Code.abort (STR ''Control plane could not be build'') (\<lambda> _. (\<lambda> _ _. frontier {#}\<^sub>z)))"
  unfolding dataflow_tree_to_graph_def
  by(cases "dataflow_tree_to_graph_aux 0 df"; simp)

lemma "remove_non_zero_weights s l1 l2 = remove_non_zero_weights s (f l1) (f l2)"
  apply(cases "s l1 l2"; simp)
  sorry

lemma "bij f \<Longrightarrow> has_zero_cyc s \<Longrightarrow>
       has_zero_cyc (\<lambda> x x'. s (f x) (f x'))"
  sorry

lemma "remove_non_zero_weights (snd (dataflow_tree_to_graph_aux n (Logic op su))) = remove_non_zero_weights (snd (dataflow_tree_to_graph_aux m (Logic op su)))"
  sorry

lemma "has_zero_cyc (snd (dataflow_tree_to_graph_aux n dt)) \<Longrightarrow>
       has_zero_cyc (snd (dataflow_tree_to_graph_aux m dt))"
  apply(induction dt)
  subgoal for op su
    unfolding cyc_checker_codeT_def
    sorry
  sorry

lemma "has_zero_cyc (snd (dataflow_tree_to_graph_aux 0 dt1)) \<Longrightarrow>
       has_zero_cyc (snd (dataflow_tree_to_graph_aux 0 (Comp buf dt1 dt2')))"
  apply auto
  apply(cases "dataflow_tree_to_graph_aux 0 dt1"; simp)
  subgoal for n summ
    apply(cases "dataflow_tree_to_graph_aux n dt2'"; simp)
    subgoal for n' summ'
      sorry
    done
  done

lemma "dataflow_tree_to_graph dt1 = dataflow_tree_to_graph dt1' \<Longrightarrow>
       dataflow_tree_to_graph dt2 = dataflow_tree_to_graph dt2' \<Longrightarrow>
       dataflow_tree_to_graph (Comp buf dt1 dt2') = dataflow_tree_to_graph (Comp buf dt1' dt2')"
  apply(subst dataflow_tree_to_graph_alt_def)
  apply(simp only: nodes_count.simps)
  apply auto
  sorry

lemma "dataflow_tree_to_graph_aux 0 dt1 = dataflow_tree_to_graph_aux 0 dt1' \<Longrightarrow>
        nodes_count dt1 = nodes_count dt1' \<Longrightarrow>
        dataflow_tree_to_graph (Comp buf dt1 dt2) = dataflow_tree_to_graph (Comp buf dt1' dt2)"
  unfolding dataflow_tree_to_graph_def
  sorry



fun nodes_height where
  "nodes_height (Logic op su) = (1 :: nat)"
| "nodes_height (Comp wire dt1 dt2) = 1 + nodes_height dt1 + nodes_height dt2"

definition chns_prop_temp where
  "chns_prop_temp _ _ _ _ _ = undefined"

primrec chns_prop where
"chns_prop _ (Logic _ _) _ _ _ = True" |
"chns_prop io (Comp buf dt1 dt2) dt' chns chns' = chns_prop_temp io (Comp buf dt1 dt2) dt' chns chns'"

lemma "to_nat (0 :: 'n :: {minus,one,semigroup_add,ord,countable,zero,equal}) = 0"
  apply code_simp
  apply simp
  using Hilbert_Choice.someI[of "\<lambda> f.  \<forall>x y. f x = f y \<longrightarrow> x = y" id, simplified]
  oops

lemma fst_dtoa_def: "fst (dataflow_tree_to_operator_aux (n :: 'n :: {minus,one,semigroup_add,ord,equal}) chns dt) = n + nodes_count dt"
proof (induction dt arbitrary: n)
  case (Logic x1 x2)
  then show ?case
    by simp
next
  fix x1 :: "'n \<times> 'a \<Rightarrow> ('n \<times> 'a) option"
    and dt1 :: "('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree"
    and dt2 :: "('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree"
    and n :: 'n
  assume ind1: "\<And>n. fst (dataflow_tree_to_operator_aux n chns (dt1::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree)) = n + nodes_count dt1"
    and ind2: "\<And>n. fst (dataflow_tree_to_operator_aux n chns (dt2::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree)) = n + nodes_count dt2"
  obtain n1 op1 where dtoa1: "dataflow_tree_to_operator_aux n chns dt1 = (n1, op1)"
    by fastforce
  obtain n2 op2 where dtoa2: "dataflow_tree_to_operator_aux n1 chns dt2 = (n2, op2)"
    by fastforce
  show "fst (dataflow_tree_to_operator_aux n chns (Comp x1 (dt1::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) dt2)) = n + nodes_count (Comp x1 dt1 dt2)"
    apply(simp add: dtoa1 dtoa2 )
    unfolding ind2[of n1, simplified dtoa2 fst_conv] ind1[of n, simplified dtoa1 fst_conv]
    by(simp add: Groups.add_ac(1))
qed

(*function convert_to_nat where                              
  "convert_to_nat (n :: 'a :: {minus,zero,enum,linorder,numeral,bot,top}) m = (if n = m then (0 :: nat) else Suc (convert_to_nat (n + 1) m))"
  by auto
termination
  apply(rule local.termination)
  apply(rule local.termination[of "{x. \<exists> n > \<bottom>. x = (n-1,n)}"]; simp?)
  subgoal
    apply(rule finite_acyclic_wf; simp?)
    apply(subst acyclic_converse[symmetric])
    apply(rule acyclicI_order[where f = id])
    apply simp
    sorry
  sorry
*)
(*
function convert_to_nat where
  "convert_to_nat (n :: 'a :: {minus,zero,ord,numeral}) = (if n \<le> 0 then (0 :: nat) else Suc (convert_to_nat (n - 1)))"
  by auto
termination
  apply(rule local.termination[of "{x. \<exists> n > 0. x = (n-1,n)}"]; simp?)
  subgoal
    apply(rule finite_acyclic_wf; simp?)
    apply(subst acyclic_converse[symmetric])
    apply(rule acyclicI_order[where f = id])
    apply simp
    apply(code_simp)
    sorry
  done
*)
print_classes

lemma Rep_bit0_0: "0 \<le> Rep_bit0 x"
  using bit0.Rep_bit0
  by auto

lemma Rep_bit1_1: "0 \<le> Rep_bit1 x"
  using bit1.Rep_bit1
  by auto

datatype dataflow_tree_cut = 
  "apply": LogicCut
  | CompCut "dataflow_tree_cut" "dataflow_tree_cut"

fun nodes_count_cut where
  "nodes_count_cut LogicCut = 1"
| "nodes_count_cut (CompCut dt1 dt2) = nodes_count_cut dt1 + nodes_count_cut dt2"

primrec tree_cut where
  "tree_cut (Logic _ _) = LogicCut"
| "tree_cut (Comp _ dt1 dt2) = (CompCut (tree_cut dt1) (tree_cut dt2))"

lemma nodes_count_cut: "nodes_count dt = nodes_count_cut (tree_cut dt)"
  by(induction dt; simp)

class tln = ord + one + plus +
  fixes to_nat :: "('a :: {one,plus,ord}) \<Rightarrow> nat"
  assumes ord_add: "CARD('a) > to_nat a + to_nat b \<Longrightarrow> (a :: 'a) \<le> a + b"
  assumes ord_add_leq: "to_nat ((a :: 'a) + b) \<le> to_nat a + to_nat b"
  assumes nodes_count_convert_aux: "CARD('a) > nodes_count_cut dt \<Longrightarrow> to_nat (nodes_count_cut dt :: 'a) = nodes_count_cut dt"
begin

lemma nodes_count_convert: "CARD('a) > nodes_count dt \<Longrightarrow> to_nat (nodes_count dt :: 'a) = nodes_count dt"
  by(simp add: nodes_count_cut nodes_count_convert_aux)

end

lemma Rep_bit0_add: "Rep_bit0 (n :: 'a bit0) + Rep_bit0 m < 2 * int CARD(('a :: finite)) \<Longrightarrow> Rep_bit0 n + Rep_bit0 m = Rep_bit0 (n + m)"
  by(cases n; cases m; simp add: bit0.of_int_eq Abs_bit0_inverse bit0.add_def)

lemma Rep_bit1_add: "Rep_bit1 (n :: 'a bit1) + Rep_bit1 m < 1 + 2 * int CARD(('a :: finite)) \<Longrightarrow> Rep_bit1 n + Rep_bit1 m = Rep_bit1 (n + m)"
  by(cases n; cases m; simp add: bit1.of_int_eq Abs_bit1_inverse bit1.add_def)

instantiation bit0 and bit1 :: (finite) tln begin

definition "tln_class.to_nat (P :: 'a bit0) = (nat o Rep_bit0) P"
definition "tln_class.to_nat (P :: 'a bit1) = (nat o Rep_bit1) P"

instance
   apply(intro_classes)
  unfolding to_nat_bit0_def to_nat_bit1_def
  subgoal for n m
    apply(simp add: nat_int_comparison Rep_bit0_0 mod_pos_pos_trivial less_eq_bit0_def)
    unfolding Rep_bit0_add[symmetric, of n m]
    apply(cases n; cases m; simp)
    by(simp add: bit0.of_int_eq Abs_bit0_inverse)
  subgoal for n m
    apply simp
    apply(cases n; cases m; simp add: bit0.of_int_eq Abs_bit0_inverse bit0.add_def nat_add_distrib[symmetric])
    by(simp add: zmod_le_nonneg_dividend nat_mono)
  subgoal for dt
    apply(induction dt; simp add: bit0.Rep_1 Rep_bit0_add)
    subgoal for dt1 dt2
      by(cases "nodes_count_cut dt1 :: 'a bit0"; cases "nodes_count_cut dt2 :: 'a bit0"; simp add: bit0.of_int_eq Abs_bit0_inverse bit0.add_def)
    done
  subgoal for n m
    apply(simp add: nat_int_comparison Rep_bit1_1 mod_pos_pos_trivial less_eq_bit1_def)
    unfolding Rep_bit1_add[symmetric, of n m]
    apply(cases n; cases m; simp)
    by(simp add: bit1.of_int_eq Abs_bit1_inverse)
  subgoal for n m
    apply simp
    apply(cases n; cases m; simp add: bit1.of_int_eq Abs_bit1_inverse bit1.add_def nat_add_distrib[symmetric])
    by(simp add: zmod_le_nonneg_dividend nat_mono)
  subgoal for dt
    apply(induction dt; simp add: bit1.Rep_1 Rep_bit0_add)
    subgoal for dt1 dt2
      by(cases "nodes_count_cut dt1 :: 'a bit1"; cases "nodes_count_cut dt2 :: 'a bit1"; simp add: bit1.of_int_eq Abs_bit1_inverse bit1.add_def)
    done
  done
end



lemma test: "(n :: _ :: {tln,preorder,group_add}) = undefined \<Longrightarrow> False"
  sorry

lemma "(n :: 4) = undefined \<Longrightarrow> False"
  by(rule test, simp)


(*

op = Silent (comp_op wire (BTL x11_ chns) op1 (x12_ (BHD x11_ chns)))
op = Read (Inr x11_) (\<lambda>x. comp_op wire chns op1 (x12_ x))
op = Write (comp_op wire chns op1 x21_) (Inr x22_) x23_
op = Silent (comp_op wire chns op1 x4_)

; auto?; fast?
*)
lemma comp_op_chns_inv_aux: "rel_fun (=)
        (\<lambda>op op'.
            \<exists>op1 op2 f f' f'' p p' p'' p''' x chns chns'.
               op = comp_op wire chns op1 op2 \<and> op' = comp_op wire chns' op1 op2 \<or>
               cases op op' op1 op2 f f' f'' p p' p'' p''' x chns chns')
        (\<lambda>x. comp_op wire chns (f'' x) (f' x)) (\<lambda>x. comp_op wire chns' (f'' x) (f' x))"
  unfolding rel_fun_def
  by fast

lemma comp_op_chns_inv_aux': "rel_fun (=)
        (\<lambda>op op'.
            \<exists>op1 op2 f f' f'' p p' p'' p''' x chns chns'.
               op = comp_op wire chns op1 op2 \<and> op' = comp_op wire chns' op1 op2 \<or>
               cases op op' op1 op2 f f' f'' p p' p'' p''' x chns chns')
        (\<lambda>x. comp_op wire chns (f'' x) (f' x)) (\<lambda>x. comp_op wire chns' (f'' x) (f' x))"
  unfolding rel_fun_def
  sorry

inductive port_unused where
  "(\<forall> f. \<not> (Read p f |\<in>| choices op)) \<Longrightarrow> 
   (\<forall> x op'. \<not> (Write op' p x |\<in>| choices op)) \<Longrightarrow> 
   (\<forall> io op'. step io op op' \<longrightarrow> port_unused p op') \<Longrightarrow> 
   port_unused p op"

abbreviation port_unused' where
  "port_unused' chns chns' op1 op2 \<equiv> (\<forall> p. \<not> (port_unused p op1) \<or> \<not> (port_unused p op2) \<longrightarrow> chns p = chns' p)"

lemma port_unused'_BENQ: "port_unused' chns chns' op1 op2 \<Longrightarrow> port_unused' (BENQ p x chns) (BENQ p x chns') op1 op2"
  unfolding BENQ_def
  by auto

lemma port_unused'_BTL: "port_unused' chns chns' op1 op2 \<Longrightarrow> port_unused' (BTL p chns) (BTL p chns') op1 op2"
  unfolding BTL_def
  by auto

lemma port_unused_Read1: "port_unused' chns chns' op1 op2 \<Longrightarrow> Read p f \<in> rcset (choices op1) \<Longrightarrow> \<forall>x p. (port_unused p (f x) \<longrightarrow> \<not> port_unused p op2) \<longrightarrow> chns p = chns' p"
  by (metis port_unused.cases cin.rep_eq Read_in_choices_step)

lemma port_unused_Write1: "port_unused' chns chns' op1 op2 \<Longrightarrow> Write op' p x \<in> rcset (choices op1) \<Longrightarrow> \<forall>p. (port_unused p op' \<longrightarrow> \<not> port_unused p op2) \<longrightarrow> chns p = chns' p"
  by (metis port_unused.cases cin.rep_eq Write_in_choices_step)

lemma comp_op_not_Silent[simp]:
  "\<not> is_Silent (comp_op wire buf op1 op2)"
  by (subst comp_op_code, simp)

lemma comp_op_chns_invar: "(\<forall> p. p \<in> outputs op1 \<and> wire p \<noteq> None \<or> p \<in> inputs op2 \<and> (\<exists>p'. wire p' = Some p ) \<longrightarrow> chns p = chns' p) \<Longrightarrow>
       comp_op wire chns op1 op2 =
       comp_op wire chns' op1 op2"
  apply(coinduction arbitrary: chns chns' op1 op2 rule: op.coinduct_upto)
  subgoal for chns chns' op1 op2
    apply clarsimp
    apply(subst (3 4) comp_op_code)
    apply simp
    apply(rule union_transfer[THEN rel_funD, THEN rel_funD])
    subgoal
      apply(rule image_transfer[THEN rel_funD, THEN rel_funD, of "eq_onp (\<lambda> x. x |\<in>| choices op1)"])
      subgoal
        apply(rule rel_funI)
        apply(auto simp add: eq_onp_def split: op.splits option.splits intro!: op.cong_Read op.cong_Write 
              op.cong_Silent rel_funI op.cong_base[of _ "comp_op _ _ _ _" "comp_op _ _ _ _"])
        subgoal
          apply(rule exI conjI refl)+
          by (meson Read_in_choices_step cin.rep_eq step_inputs_outputs subset_iff)
        subgoal
          apply(rule exI conjI refl)+
          by (meson Write_in_choices_step cin.rep_eq step_inputs_outputs subset_iff)
        subgoal
          apply(rule exI conjI refl allI impI)+
          apply(auto simp: BENQ_def)
          apply (meson Write_in_choices_step cin.rep_eq step_inputs_outputs subset_iff)+
          done
        subgoal
          apply(rule exI conjI refl)+
          by (meson Silent_in_choices_step cin.rep_eq step_inputs_outputs subset_iff)
        done
      by(auto intro!: rel_set_reflI simp add: eq_onp_def)
    subgoal
      apply(rule image_transfer[THEN rel_funD, THEN rel_funD, of "eq_onp (\<lambda> x. x |\<in>| choices op2)"])
      subgoal
        apply(rule rel_funI)
        apply(auto simp add: eq_onp_def split: op.splits option.splits intro!: op.cong_Read op.cong_Write 
              op.cong_Silent rel_funI op.cong_base[of _ "comp_op _ _ _ _" "comp_op _ _ _ _"])
        subgoal for p f
          apply(subgoal_tac "BHD p chns = BHD p chns'")
          subgoal
            apply simp
          apply(rule exI conjI refl allI impI)+
             apply(auto simp: BTL_def)
               apply (metis Read_choices_inputs cin.rep_eq)+
             apply (meson Read_in_choices_step cin.rep_eq step_inputs_outputs subset_iff)+
            done
          subgoal
            by (simp add: Read_choices_inputs BHD_def ran_def)
          done
        subgoal
          apply(rule exI conjI refl)+
          by (meson Read_in_choices_step cin.rep_eq step_inputs_outputs subset_iff)
        subgoal
          apply(rule exI conjI refl)+
          by (meson Write_in_choices_step cin.rep_eq step_inputs_outputs subset_iff)
        subgoal
          apply(rule exI conjI refl)+
          by (meson Silent_in_choices_step cin.rep_eq step_inputs_outputs subset_iff)
        done
      apply(subgoal_tac "{a \<in> rcset (choices op2). case a of Read p f \<Rightarrow> p \<in> ran wire \<longrightarrow> chns p \<noteq> [] | _ \<Rightarrow> True} =
     {a \<in> rcset (choices op2). case a of Read p f \<Rightarrow> p \<in> ran wire \<longrightarrow> chns' p \<noteq> [] | _ \<Rightarrow> True}")
      subgoal
        by(auto intro!: rel_set_reflI simp add: eq_onp_def)
      subgoal
        apply(auto split: op.splits simp add: Read_choices_inputs ran_def)
         apply (metis op.set_intros(1) cin.rep_eq inputs_after_choices)+
        done
      done
    done
  done

primrec used_ports where
  "used_ports _ _ (Logic op su) = {}"
| "used_ports n chns (Comp wire dt1 dt2) = 
   (image projr (outputs (snd (dataflow_tree_to_operator_aux n chns dt1))) \<inter> {(n',p). wire (n' - n,p) \<noteq> None}) \<union> 
   (image projr (inputs (snd (dataflow_tree_to_operator_aux (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2))) \<inter> {(n',p). \<exists>p'. wire p' = Some ((- fst (dataflow_tree_to_operator_aux n chns dt1)) + n' ,p)}) \<union> 
   used_ports n chns dt1 \<union> used_ports (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2"

(*
primrec used_ports where
  "used_ports n chns (Logic op su) = image projr (inputs (snd (dataflow_tree_to_operator_aux n chns (Logic op su))) \<union>
                                                  outputs (snd (dataflow_tree_to_operator_aux n chns (Logic op su))))"
| "used_ports n chns (Comp wire dt1 dt2) = used_ports n chns dt1 \<union> used_ports (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2"
lemma used_ports_out: "Inr x \<in> outputs (snd (dataflow_tree_to_operator_aux n chns dt)) \<Longrightarrow> x \<in> used_ports n chns dt"
  apply(induction dt arbitrary: x n)
  subgoal for op su x n
    by(auto simp add: image_def Bex_def)
  subgoal for wire dt1 dt2 x n
    apply(auto simp add: op.set_map split: prod.splits)
    by (metis prod.collapse prod.sel(2))
  done

lemma used_ports_in: "Inr x \<in> inputs (snd (dataflow_tree_to_operator_aux n chns dt)) \<Longrightarrow> x \<in> used_ports n chns dt"
  apply(induction dt arbitrary: x n)
  subgoal for op su x n
    by(auto simp add: image_def Bex_def)
  subgoal for wire dt1 dt2 x n
    apply(auto simp add: op.set_map split: prod.splits)
     apply (metis prod.sel(2) surj_pair)
    by (metis snd_conv surj_pair)
  done
*)



lemma dataflow_tree_to_operator_aux_chns_inv: "CARD('n) > nodes_count dt + tln_class.to_nat n \<Longrightarrow> \<forall> p. p \<in> used_ports n chns dt \<longrightarrow> 
  chns p = chns' p \<Longrightarrow> dataflow_tree_to_operator_aux (n :: 'n :: {one,semigroup_add,zero,ord,equal,tln,preorder,group_add}) chns dt = dataflow_tree_to_operator_aux n chns' dt"
proof (induction dt arbitrary: n)
  case (Logic x1 x2)
  then show ?case
    by simp
next
  fix wire :: "'n \<times> 'a \<Rightarrow> ('n \<times> 'a) option"
    and dt1 :: "('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree"
    and dt2 :: "('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree"
    and n :: 'n
  assume ind1: "\<And>n. nodes_count (dt1::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) -+- tln_class.to_nat n < CARD('n) \<Longrightarrow> \<forall> p. p \<in> used_ports n chns dt1 \<longrightarrow> chns p = chns' p \<Longrightarrow> dataflow_tree_to_operator_aux n chns dt1 = dataflow_tree_to_operator_aux n chns' dt1"
    and ind2: "\<And>n. nodes_count (dt2::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) -+- tln_class.to_nat n < CARD('n) \<Longrightarrow> \<forall> p. p \<in> used_ports n chns dt2 \<longrightarrow> chns p = chns' p \<Longrightarrow> dataflow_tree_to_operator_aux n chns dt2 = dataflow_tree_to_operator_aux n chns' dt2"
    and count: "nodes_count (Comp wire (dt1::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) dt2) -+- tln_class.to_nat n < CARD('n)"
    and eq: "\<forall> p. p \<in> used_ports n chns (Comp wire dt1 dt2) \<longrightarrow> chns p = chns' p"
  have eq: "\<And>p. p \<in> used_ports n chns (Comp wire dt1 dt2) \<Longrightarrow> chns p = chns' p"
    using eq
    by presburger
  obtain n1 op1 where dtoa1: "dataflow_tree_to_operator_aux n chns dt1 = (n1, op1)"
    by fastforce
  obtain n2 op2 where dtoa2: "dataflow_tree_to_operator_aux n1 chns dt2 = (n2, op2)"
    by fastforce
  have count1: "nodes_count dt1 -+- tln_class.to_nat n < CARD('n)"
    using count
    unfolding fst_dtoa_def
    by simp
  have count2: "nodes_count dt2 -+- tln_class.to_nat n1 < CARD('n)"
    using count dtoa1[THEN arg_cong[where f = fst], symmetric]
    apply(simp add: fst_dtoa_def)
    apply(rule dual_order.strict_trans2, assumption)
    apply(rule order.trans, rule add_left_mono, rule ord_add_leq)
    by(simp add: nodes_count_convert)
  have dtoa1_inv: "dataflow_tree_to_operator_aux n chns dt1 = dataflow_tree_to_operator_aux n chns' dt1"
    apply(rule ind1[of n, OF count1])
    apply safe
    apply(rule eq)
    by simp
  have dtoa2_inv: "dataflow_tree_to_operator_aux n1 chns dt2 = dataflow_tree_to_operator_aux n1 chns' dt2"
    apply(rule ind2[of n1, OF count2])
    apply safe
    apply(rule eq)
    by(simp add: dtoa1 dtoa2)
  show "dataflow_tree_to_operator_aux n chns (Comp wire (dt1::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) dt2) = dataflow_tree_to_operator_aux n chns' (Comp wire dt1 dt2)"
    apply simp
    apply(simp add: dtoa1_inv[symmetric] dtoa2_inv[symmetric] dtoa1 dtoa2)
    apply(rule arg_cong[where f = " map_op (case_sum id id) (case_sum id id)"])
    apply(rule comp_op_chns_invar)
    apply(auto intro!: eq simp add: dtoa1 dtoa2 image_def split: sum.splits)
         apply(fastforce intro!: eq simp add: dtoa1 dtoa2 image_def split: sum.splits)+
       apply force
    subgoal for a b p'
      apply(cases p'; simp)
      subgoal for p''
        apply(cases p''; simp)
        subgoal for aa bb
          apply(cases "wire (aa - n, bb)"; simp)
          subgoal for ab
            apply(cases ab; simp)
            apply(rule exI[where x = "aa - n"])
            apply(rule exI[where x = "bb"])
            by auto
          done
        done
      done
    apply force
    subgoal for a b p'
      apply(cases p'; simp)
      subgoal for p''
        apply(cases p''; simp)
        subgoal for aa bb
          apply(cases "wire (aa - n, bb)"; simp)
          subgoal for ab
            apply(cases ab; simp)
            apply(rule exI[where x = "aa - n"])
            apply(rule exI[where x = "bb"])
            by auto
          done
        done
      done
    done
qed

abbreviation chns_cut where
  "chns_cut n chns dt \<equiv> (\<lambda> p. if p \<in> used_ports n chns dt then chns p else [])"

lemma dataflow_tree_to_operator_aux_chns_cut: "CARD('n) > nodes_count dt + tln_class.to_nat n \<Longrightarrow>
  dataflow_tree_to_operator_aux (n :: 'n :: {one,semigroup_add,zero,ord,equal,tln,preorder,group_add}) chns dt = 
  dataflow_tree_to_operator_aux n (chns_cut n chns dt) dt"
  using dataflow_tree_to_operator_aux_chns_inv
  by fastforce

(*
primrec good_dt :: "('a \<times> 'b \<Rightarrow> ('a \<times> 'b) option) \<Rightarrow> ('a, 'b, 'c + 'd, 'e, 'f) dataflow_tree \<Rightarrow> bool" where
"good_dt _ (Logic op _) = (\<forall> io op'. step io op op' \<longrightarrow> ((\<exists> p x. io = Inp (Some p) (Inr x))) \<or> (\<exists> x. io = Inp None (Inl (Inr x))) \<or> (\<exists> p x. io = Out (Some p) (Inr x)) \<or> (\<exists> x. io = Out None (Inl (Inl x))))" |
"good_dt wire (Comp wire' dt1 dt2) = ((\<forall> x. wire x = None \<or> wire' x = None) \<and> (good_dt (wire ++ wire') dt1 \<and> good_dt (wire ++ wire') dt2))"
*)
primrec good_dt :: "('a, 'b, 'c + 'd, 'e, 'f) dataflow_tree \<Rightarrow> bool" where
"good_dt (Logic op _) = (\<forall> io op'. step io op op' \<longrightarrow> ((\<exists> p x. io = Inp (Some p) (Inr x))) \<or> (\<exists> x. io = Inp None (Inl (Inr x))) \<or> (\<exists> p x. io = Out (Some p) (Inr x)) \<or> (\<exists> x. io = Out None (Inl (Inl x))))" |
"good_dt (Comp _ dt1 dt2) = (good_dt dt1 \<and> good_dt dt2)"

lemma "step io' op op' \<Longrightarrow> map_IO (case_option (Inl n) (\<lambda>p. Inr (n, p))) (case_option (Inl n) (\<lambda>p. Inr (n, p))) id io' = io \<Longrightarrow>
       step io (snd (dataflow_tree_to_operator_aux (n :: 'a :: {minus,one,semigroup_add,zero,ord,equal,tln,preorder}) chns (Logic op su))) 
              (snd (dataflow_tree_to_operator_aux n chns' (Logic op' su')))"
  by simp

lemma "fst (dataflow_tree_to_operator_aux n chns dt1) = fst (dataflow_tree_to_operator_aux n chns' dt1) \<Longrightarrow>
      step Tau (snd (dataflow_tree_to_operator_aux (n :: 'a :: {minus,one,semigroup_add,zero,ord,equal,tln,preorder}) chns (Comp wire dt1 dt2))) 
              (snd (dataflow_tree_to_operator_aux n chns' (Comp wire dt1 dt2')))"
  apply simp
  apply(auto split: prod.splits)
  apply(rule step_comp_op_L_Tau)
  subgoal
    sorry
  subgoal
    sorry
sorry

inductive step_dt where                        
  SLogic: "step io (snd (dataflow_tree_to_operator_aux n chns (Logic op su))) (snd (dataflow_tree_to_operator_aux n chns (Logic op' su))) \<Longrightarrow> 
    step_dt io n chns (Logic op su) chns (Logic op' su)"
| SInpInl: "(step_dt (Inp (Inl p) x) n chns dt1 chns dt1' \<and> dt2 = dt2') \<or> (step_dt (Inp (Inl p) x) (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2 chns dt2' \<and> dt1 = dt1') \<Longrightarrow>
    step_dt (Inp (Inl p) x) n chns (Comp wire dt1 dt2) chns (Comp wire dt1' dt2')"
| SOutInl: "(step_dt (Out (Inl p) x) n chns dt1 chns dt1' \<and> dt2 = dt2') \<or> (step_dt (Out (Inl p) x) (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2 chns dt2' \<and> dt1 = dt1') \<Longrightarrow>
    step_dt (Out (Inl p) x) n chns (Comp wire dt1 dt2) chns (Comp wire dt1' dt2')"
| SInpInr: "(\<forall> p'. wire p' \<noteq> Some (n' - (fst (dataflow_tree_to_operator_aux n chns dt1)),p) \<and> step_dt (Inp (Inr (n',p)) x) (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2 chns dt2' \<and> dt1 = dt1') \<or>
    (step_dt (Inp (Inr (n',p)) x) n chns dt1 chns dt1' \<and> dt2 = dt2') \<Longrightarrow>
    step_dt (Inp (Inr (n',p)) x) n chns (Comp wire dt1 dt2) chns (Comp wire dt1' dt2')"
| SOutInr: "(wire (n',p) = None \<and> step_dt (Out (Inr (n',p)) x) n chns dt1 chns dt1' \<and> dt2 = dt2') \<or>
    (step_dt (Out (Inr (n',p)) x) n chns dt2 chns dt1' \<and> dt1 = dt1') \<Longrightarrow>
    step_dt (Out (Inr (n',p)) x) n chns (Comp wire dt1 dt2) chns (Comp wire dt1' dt2')"
| STau: "(step_dt Tau n chns dt1 chns' dt1' \<and> dt2 = dt2' ) \<or>
    (step_dt Tau (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2 chns' dt2' \<and> dt1 = dt1') \<or>
    (\<exists> p p' n' x. wire p' = Some (n' - (fst (dataflow_tree_to_operator_aux n chns dt1)),p) \<and> step_dt (Inp (Inr (n',p)) (Inr x)) (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2 chns dt2' \<and> dt1 = dt1' \<and> chns' = BTL (n',p) chns \<and> chns (n',p) \<noteq> [] \<and> x = BHD (n',p) chns) \<or>
    (\<exists> p p' n' n'' x. wire (n' - n,p) = Some (n'',p') \<and> step_dt (Out (Inr (n',p)) (Inr x)) n chns dt1 chns dt1' \<and> dt2 = dt2' \<and> chns' = BENQ (n'' + (fst (dataflow_tree_to_operator_aux n chns dt1)),p') x chns) \<Longrightarrow>
    step_dt Tau n chns (Comp wire dt1 dt2) chns' (Comp wire dt1' dt2')"


end
primrec chns_set where
  "chns_set io wire n chns (Logic op su) = (case io of
    Tau \<Rightarrow> {(chns, dt'). \<exists>dt' op'. step io op op' \<and> dt' = Logic op' su}
  | Inp (Some (n,p)) x \<Rightarrow> {(chns, dt'). undefined }
  | Inp None x \<Rightarrow> {(chns, dt'). undefined }
  | Out p x \<Rightarrow> undefined)"
| "chns_set io wire n chns (Comp _ op _) = undefined" 



lemma "step io (snd (dataflow_tree_to_operator_aux (n :: 'a :: {minus,one,semigroup_add,zero,ord,equal,tln,preorder}) chns (dt :: (_,_,_,_, 'g) dataflow_tree))) op' \<Longrightarrow> 
      good_dt dt \<Longrightarrow>
      nodes_count dt -+- tln_class.to_nat n < CARD('a) \<Longrightarrow>
      (\<exists> (dt' :: (_,_,_,_, 'g) dataflow_tree). dataflow_tree_to_operator_aux n chns dt' = (fst (dataflow_tree_to_operator_aux n chns dt), op')) \<and> 
      ((\<exists> p x. io = Inp (Inr p) (Inr x)) \<or> (\<exists> p x. io = Inp (Inl p) (Inl (Inr x))) \<or> (\<exists> p x. io = Out (Inr p) (Inr x)) \<or> (\<exists> p x. io = Out (Inl p) (Inl (Inl x))) \<or> (io = Tau))"
proof (induction dt arbitrary: io n chns op')
  case (Logic op su)
  assume step: "step io (snd (dataflow_tree_to_operator_aux n chns (Logic op (su::'b \<Rightarrow> 'b \<Rightarrow> 'g buf)))) op'"
    and dt_io: "good_dt (Logic op su::('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree)"
  show ?case
    using step apply -
    apply simp
    apply(elim step_map_op_elim conjE)
    apply(rule conjI)
    subgoal for io' op''
      apply(rule exI[where x = "Logic op'' su"])
      by simp
    subgoal for io' op''
      using dt_io
      unfolding good_dt.simps
      apply -
      apply(erule allE[where x = "io'"])
      apply(erule allE[where x = "op''"])
      by fastforce
    done
next
  fix x1 :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) option"
    and dt1 :: "('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree"
    and dt2 :: "('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree"
    and io :: "('a + 'a \<times> 'b, 'a + 'a \<times> 'b, ('c + 'd) + 'e \<times> 'f) IO"
    and n :: 'a
    and chns :: "'a \<times> 'b \<Rightarrow> ('e \<times> 'f) buf"
    and op' :: "('a + 'a \<times> 'b, 'a + 'a \<times> 'b, ('c + 'd) + 'e \<times> 'f) op"
  assume ind1: "\<And>io n chns op'. step io (snd (dataflow_tree_to_operator_aux n chns (dt1::('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree))) op' \<Longrightarrow> good_dt dt1 \<Longrightarrow> nodes_count dt1 -+- tln_class.to_nat n < CARD('a) \<Longrightarrow> (\<exists>dt'. dataflow_tree_to_operator_aux n chns (dt'::(_, _, _ + _, _ \<times> _, 'g) dataflow_tree) = (fst (dataflow_tree_to_operator_aux n chns dt1), op')) \<and> ((\<exists>p x. io = Inp (Inr p) (Inr x)) \<or> (\<exists>p x. io = Inp (Inl p) (Inl (Inr x))) \<or> (\<exists>p x. io = Out (Inr p) (Inr x)) \<or> (\<exists>p x. io = Out (Inl p) (Inl (Inl x))) \<or> io = Tau)"
    and ind2: "\<And>io n chns op'. step io (snd (dataflow_tree_to_operator_aux n chns (dt2::('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree))) op' \<Longrightarrow> good_dt dt2 \<Longrightarrow> nodes_count dt2 -+- tln_class.to_nat n < CARD('a) \<Longrightarrow> (\<exists>dt'. dataflow_tree_to_operator_aux n chns (dt'::(_, _, _ + _, _ \<times> _, 'g) dataflow_tree) = (fst (dataflow_tree_to_operator_aux n chns dt2), op')) \<and> ((\<exists>p x. io = Inp (Inr p) (Inr x)) \<or> (\<exists>p x. io = Inp (Inl p) (Inl (Inr x))) \<or> (\<exists>p x. io = Out (Inr p) (Inr x)) \<or> (\<exists>p x. io = Out (Inl p) (Inl (Inl x))) \<or> io = Tau)"
    and step: "step io (snd (dataflow_tree_to_operator_aux n chns (Comp x1 (dt1::('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree) dt2))) op'"
    and dt_prop: "good_dt (Comp x1 (dt1::('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree) dt2)"
    and card:"nodes_count (Comp x1 (dt1::('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree) dt2) -+- tln_class.to_nat n < CARD('a)"
  obtain n1 op1 where dtoa1: "dataflow_tree_to_operator_aux n chns dt1 = (n1, op1)"
    by force
  obtain n2 op2 where dtoa2: "\<And> chns. dataflow_tree_to_operator_aux n1 chns dt2 = (n2 chns, op2 chns)"
    apply atomize_elim
    apply(rule exI[where x = "\<lambda> chns. fst (dataflow_tree_to_operator_aux n1 chns dt2)"])
    apply(rule exI[where x = "\<lambda> chns. snd (dataflow_tree_to_operator_aux n1 chns dt2)"])
    by force
  have dt1_prop: "good_dt dt1" and dt2_prop: "good_dt dt2"
    using dt_prop
    unfolding good_dt.simps
    by auto
  have eq1': "nodes_count dt1 < CARD('a)"
    using card
    by simp
  have eq1: "nodes_count dt1 -+- tln_class.to_nat n < CARD('a)"
    using card
    by simp
  have eq2: "nodes_count dt2 -+- tln_class.to_nat n1 < CARD('a)"
    using card
    apply(simp add: dtoa1[symmetric, THEN arg_cong[where f = fst], simplified fst_dtoa_def, simplified])
    apply(rule dual_order.strict_trans2, assumption)
    apply(rule order.trans, rule add_left_mono, rule ord_add_leq)
    by(simp add: nodes_count_convert[OF eq1'])
  have eq_dtoa : "dataflow_tree_to_operator_aux n chns dt1 = dataflow_tree_to_operator_aux n (BENQ (n1 + ab, ba) x chns) dt1" for ab ba x
    apply(rule dataflow_tree_to_operator_aux_chns_inv, rule eq1)
    apply(auto simp add: BENQ_def dtoa1)
    sorry
  show "(\<exists>dt'. dataflow_tree_to_operator_aux n chns (dt'::('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree) = (fst (dataflow_tree_to_operator_aux n chns (Comp x1 (dt1::('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree) dt2)), op')) \<and> ((\<exists>p x. io = Inp (Inr p) (Inr x)) \<or> (\<exists>p x. io = Inp (Inl p) (Inl (Inr x))) \<or> (\<exists>p x. io = Out (Inr p) (Inr x)) \<or> (\<exists>p x. io = Out (Inl p) (Inl (Inl x))) \<or> io = Tau)"
    using step
    apply(simp add: dtoa1 dtoa2)
    apply(elim step_map_op_elim conjE step_comp_op_elim; simp add: eq_commute[of _ op'] eq_commute[of _ io])
    subgoal premises prems for io' op'' p x op1'
      using ind1[of "Inp p x" n chns op1', simplified dtoa1 snd_conv, OF prems(5) dt1_prop eq1]
      apply(elim conjE exE)?
      apply(rule conjI)
      subgoal for dt'
        apply(rule exI[where x = "Comp x1 dt' dt2"])
        using dataflow_tree_to_operator_aux_chns_inv
        by(simp add: dtoa2)
      by simp
    subgoal premises prems for io' op'' p x op2'
      using ind2[of "Out p x" n1 chns op2', simplified dtoa2[of chns] snd_conv, OF prems(5) dt2_prop eq2]
      apply(elim conjE exE)
      apply(rule conjI)
      subgoal for dt'
        apply(rule exI[where x = "Comp x1 dt1 dt'"])
        by(simp add: dtoa1)
      by simp
    subgoal premises prems for io' op'' p x op1'
      using ind1[of "Out p x" n chns op1', simplified dtoa1 snd_conv, OF prems(6) dt1_prop eq1]
      apply(elim conjE exE)
      apply(rule conjI)
      subgoal for dt'
        apply(rule exI[where x = "Comp x1 dt' dt2"])
        by(simp add: dtoa2)
      by simp
    subgoal premises prems for io' op'' p x op2'
      using ind2[of "Inp p x" n1 chns op2', simplified dtoa2[of chns] snd_conv, OF prems(6) dt2_prop eq2]
      apply(elim conjE exE)
      apply(rule conjI)
      subgoal for dt'
        apply(rule exI[where x = "Comp x1 dt1 dt'"])
        by(simp add: dtoa1)
      by simp
    subgoal premises prems for io' op'' p x op1' q
      using prems(5) prems(6)
      apply(clarsimp split: sum.splits option.splits)
      apply(subgoal_tac "\<exists> x'. x = Inr x'")
      subgoal for a b ba ab
        apply safe
        subgoal for x' x''
          using ind1[of "Out p x" n "BENQ (n1 + ab, ba) (x', x'') chns" op1', OF prems(6)[simplified dtoa1[symmetric, THEN arg_cong[where f = snd], simplified], simplified eq_dtoa[of ab ba "(x', x'')"]] dt1_prop eq1]
          sorry
        done
        sorry
    subgoal premises prems for io' op'' p x op2'
      using prems(5) prems(6) prems(7) prems(8)
      apply(clarsimp simp add: ran_def split: sum.splits option.splits prod.splits)
      subgoal for a aa b
        apply(cases a; simp)
      using ind2[of "Inp p x" n1 chns op2', simplified dtoa2[of chns] snd_conv, OF prems(6) dt2_prop] dtoa1 dtoa2
      apply auto
      subgoal for ab ba dt'
        apply(erule allE[where x = ab]; simp)
        apply(erule allE[where x = ba]; simp)
        apply auto

end
        apply(rule exI[where x = "Comp x1 dt1 dt'"])
        apply(simp only: dataflow_tree_to_operator_aux.simps)
        apply simp
        apply(rule arg_cong[where f = "map_op _ _"])
        apply(erule allE[where x = a])
        apply auto
        apply(rule comp_op_chns_invar)
        apply(auto split: sum.splits simp add: BTL_def)
      by simp
    subgoal premises prems for io' op'' p x op1' q
            sorry
          done
        done
      done
qed
next
  fix wire :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) option"
    and dt1 :: "('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree"
    and dt2 :: "('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree"
    and io :: "('a + 'a \<times> 'b, 'a + 'a \<times> 'b, ('c + 'd) + 'e \<times> 'f) IO"
    and n :: 'a
    and chns :: "'a \<times> 'b \<Rightarrow> ('e \<times> 'f) buf"
    and op' :: "('a + 'a \<times> 'b, 'a + 'a \<times> 'b, ('c + 'd) + 'e \<times> 'f) op"
  assume ind1: "\<And>io n chns op'. step io (snd (dataflow_tree_to_operator_aux n chns (dt1::('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree))) op' \<Longrightarrow> good_dt dt1 \<Longrightarrow> (\<exists>dt' chns'. dataflow_tree_to_operator_aux n chns' (dt'::('a, 'b, _ + _, 'e \<times> 'f, 'g) dataflow_tree) = (fst (dataflow_tree_to_operator_aux n chns dt1), op')) \<and> ((\<exists>p x. io = Inp (Inr p) (Inr x)) \<or> (\<exists>p x. io = Inp (Inl p) (Inl (Inr x))) \<or> (\<exists>p x. io = Out (Inr p) (Inr x)) \<or> (\<exists>p x. io = Out (Inl p) (Inl (Inl x))) \<or> io = Tau)"
    and ind2: "\<And>io n chns op'. step io (snd (dataflow_tree_to_operator_aux n chns (dt2::('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree))) op' \<Longrightarrow> good_dt dt2 \<Longrightarrow> (\<exists>dt' chns'. dataflow_tree_to_operator_aux n chns' (dt'::('a, 'b, _ + _, 'e \<times> 'f, 'g) dataflow_tree) = (fst (dataflow_tree_to_operator_aux n chns dt2), op')) \<and> ((\<exists>p x. io = Inp (Inr p) (Inr x)) \<or> (\<exists>p x. io = Inp (Inl p) (Inl (Inr x))) \<or> (\<exists>p x. io = Out (Inr p) (Inr x)) \<or> (\<exists>p x. io = Out (Inl p) (Inl (Inl x))) \<or> io = Tau)"
    and step: "step io (snd (dataflow_tree_to_operator_aux n chns (Comp wire (dt1::('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree) dt2))) op'"
    and dt_prop: "good_dt (Comp wire (dt1::('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree) dt2)"
  obtain n1 op1 where dtoa1: "dataflow_tree_to_operator_aux n chns dt1 = (n1, op1)"
    by force
  obtain n2 op2 where dtoa2: "\<And> chns. dataflow_tree_to_operator_aux n1 chns dt2 = (n2 chns, op2 chns)"
    apply atomize_elim
    apply(rule exI[where x = "\<lambda> chns. fst (dataflow_tree_to_operator_aux n1 chns dt2)"])
    apply(rule exI[where x = "\<lambda> chns. snd (dataflow_tree_to_operator_aux n1 chns dt2)"])
    by force
  have dt1_prop: "good_dt dt1" and dt2_prop: "good_dt dt2"
    using dt_prop
    unfolding good_dt.simps
    by auto
  show "(\<exists>dt' chns'. dataflow_tree_to_operator_aux n chns' (dt'::('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree) = (fst (dataflow_tree_to_operator_aux n chns (Comp wire (dt1::('a, 'b, 'c + 'd, 'e \<times> 'f, 'g) dataflow_tree) dt2)), op')) \<and> ((\<exists>p x. io = Inp (Inr p) (Inr x)) \<or> (\<exists>p x. io = Inp (Inl p) (Inl (Inr x))) \<or> (\<exists>p x. io = Out (Inr p) (Inr x)) \<or> (\<exists>p x. io = Out (Inl p) (Inl (Inl x))) \<or> io = Tau)"
    using step
    apply(simp add: dtoa1 dtoa2)
    apply(elim step_map_op_elim conjE step_comp_op_elim; simp add: eq_commute[of _ op'] eq_commute[of _ io])
    subgoal premises prems for io' op'' p x op1'
      using ind1[of "Inp p x" n chns op1', simplified dtoa1 snd_conv, OF prems(5) dt1_prop]
      apply(elim conjE exE)
      apply(rule conjI)
      subgoal for dt'
        apply(rule exI[where x = "Comp wire dt' dt2"])
        apply simp
        using dataflow_tree_to_operator_aux_chns_inv
        apply(simp add: dtoa2)

end
  by(simp add: chns_prop_inp dtoa2)
      by simp
    subgoal premises prems for io' op'' p x op2'
      using ind2[of "Out p x" n1 chns op2', simplified dtoa2[of chns] snd_conv, OF prems(5) dt2_prop]
      apply(elim conjE exE)
      apply(rule conjI)
      subgoal for dt'
        apply(rule exI[where x = "Comp wire dt1 dt'"])
        by(simp add: chns_prop_out dtoa1)
      by simp
    subgoal premises prems for io' op'' p x op1'
      using ind1[of "Out p x" n chns op1', simplified dtoa1 snd_conv, OF prems(6) dt1_prop]
      apply(elim conjE exE)
      apply(rule conjI)
      subgoal for dt'
        apply(rule exI[where x = "Comp wire dt' dt2"])
        by(simp add: chns_prop_out dtoa2)
      by simp
    subgoal premises prems for io' op'' p x op2'
      using ind2[of "Inp p x" n1 chns op2', simplified dtoa2[of chns] snd_conv, OF prems(6) dt2_prop]
      apply(elim conjE exE)
      apply(rule conjI)
      subgoal for dt'
        apply(rule exI[where x = "Comp wire dt1 dt'"])
        by(simp add: chns_prop_inp dtoa1)
      by simp
    subgoal premises prems for io' op'' p x op1' q
      using prems(5) prems(6)
      apply(clarsimp split: sum.splits option.splits)
      using ind1[of "Out p x" n chns op1', simplified dtoa1 snd_conv, OF prems(6) dt1_prop] dtoa1 dtoa2
      apply auto
      subgoal for a b ba ab dt' aa bb
        apply(rule exI[where x = "Comp wire dt' dt2"])
        apply simp
      sorry
    subgoal premises prems for io' op'' p x op2'
      using prems(6) prems(7) prems(8)
      apply(clarsimp simp add: ran_def split: sum.splits option.splits prod.splits)
      subgoal for a
        apply(cases a; simp)
        subgoal for b
          apply(cases b; simp)
          subgoal for x1 x2
            apply(erule allE[where x = x1]; simp)
            sorry
          done
        done
      done

end
            sorry
          subgoal
            sorry
        apply auto
        using prems(5)
        sorry
      subgoal for dt' chns'
        sorry

end
        apply(rule exI[where x = "Comp buf dt1' dt2"])
      sorry
    subgoal for io' op''
      sorry
    subgoal for io' op''
      sorry
    done
qed

*)

thm dataflow_tree_to_operator_aux_chns_cut


definition chns_combine where
  "chns_combine n dt1 dt2 buf chns1 chns2 p = (if p \<in> used_ports n chns1 dt1 then chns1 p else 
  (if p \<in> used_ports (fst (dataflow_tree_to_operator_aux n chns1 dt1)) chns2 dt2 then chns2 p else buf p))"

lemma chns_combine_dt1_simp: "nodes_count dt1 -+- tln_class.to_nat (n :: 'n :: {one,semigroup_add,zero,ord,equal,tln,preorder,group_add}) < CARD('n) \<Longrightarrow> 
  dataflow_tree_to_operator_aux n (chns_combine n dt1 dt2 buf chns1 chns2) dt1 = dataflow_tree_to_operator_aux n (chns_cut n chns1 dt1) dt1"
  unfolding chns_combine_def
  using dataflow_tree_to_operator_aux_chns_cut
  by (smt (verit) dataflow_tree_to_operator_aux_chns_inv)

lemma chns_combine_dt2_simp: "nodes_count dt2 -+- tln_class.to_nat (n1 :: 'n :: {one,semigroup_add,zero,ord,equal,tln,preorder,group_add}) < CARD('n) \<Longrightarrow> 
  n1 = n + nodes_count dt1 \<Longrightarrow>
  dataflow_tree_to_operator_aux n1 (chns_combine n dt1 dt2 buf chns1 chns2) dt2 = dataflow_tree_to_operator_aux n1 (chns_cut n1 chns2 dt2) dt2"
  unfolding chns_combine_def
  apply(subst dataflow_tree_to_operator_aux_chns_cut[of dt2 n1], assumption)
  apply auto
  sorry


lemma "nodes_count (Comp f dt1 dt2) -+- tln_class.to_nat n < CARD('a) \<Longrightarrow> 
    map_op projl projr (comp_op f buf (dataflow_op sg1 (snd (dataflow_tree_to_operator_aux n chns1 dt1))) (dataflow_op sg2 (snd (dataflow_tree_to_operator_aux (n + nodes_count dt1) chns2 dt2)))) \<approx>
   (dataflow_op (sg_f sg1 sg2) (snd (dataflow_tree_to_operator_aux n (chns_combine (n :: 'a :: {one,ab_semigroup_add,zero,ord,equal,tln,preorder,group_add,linorder,enum}) dt1 dt2 buf chns1 chns2) (Comp f dt1 dt2))))"
proof (coinduction arbitrary: buf chns1 chns2 sg1 sg2 dt1 dt2 f n)
  fix buf :: "'a \<times> 'b \<Rightarrow> ('f \<times> 'g) buf"
    and chns1 :: "'a \<times> 'b \<Rightarrow> ('f \<times> 'g) buf"
    and chns2 :: "'a \<times> 'b \<Rightarrow> ('f \<times> 'g) buf"
    and sg1 :: "('a, 'c, 'd, 'i) subgraph_scheme"
    and sg2 :: "('a, 'c, 'd, 'j) subgraph_scheme"
    and dt1 :: "('a, 'b, ('c, 'd, 'e) shared_state_scheme + ('c \<Rightarrow> 'd antichain), 'f \<times> 'g, 'h) dataflow_tree"
    and dt2 :: "('a, 'b, ('c, 'd, 'e) shared_state_scheme + ('c \<Rightarrow> 'd antichain), 'f \<times> 'g, 'h) dataflow_tree"
    and wire :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) option"
    and n :: 'a
  obtain n1 op1 where dtoa1: "dataflow_tree_to_operator_aux n (chns_cut n chns1 dt1) dt1 = (n1,op1)"
    by fastforce
  obtain n2 op2 where dtoa2: "dataflow_tree_to_operator_aux n1 (chns_cut n1 chns2 dt2) dt2 = (n2,op2)"
    by fastforce
  have n1_alt_def : "n1 = n + nodes_count dt1"
    using fst_dtoa_def[of n "(chns_cut n chns1 dt1)" dt1] 
    unfolding dtoa1
    by simp
  assume card: "nodes_count (Comp wire dt1 dt2) -+- tln_class.to_nat n < CARD('a)"
  have card1: "nodes_count dt1 -+- tln_class.to_nat n < CARD('a)"
    using card
    by simp
  have card2: "nodes_count dt2 -+- tln_class.to_nat n1 < CARD('a)"
    using card
    apply(simp add: n1_alt_def)
    using tln_class.ord_add_leq
    sorry
  let ?map_dt = "\<lambda> buf sg1 sg2 chns1 chns2 dt1 dt2 f n. map_op projl projr (comp_op f buf (dataflow_op sg1 (snd (dataflow_tree_to_operator_aux n chns1 dt1))) (dataflow_op sg2 (snd (dataflow_tree_to_operator_aux (n + nodes_count dt1) chns2 dt2))))"
  let ?map_dt' = "?map_dt buf sg1 sg2 chns1 chns2 dt1 dt2 wire n"
  let ?dt_map = "\<lambda> buf sg1 sg2 chns1 chns2 dt1 dt2 f n. dataflow_op (sg_f sg1 sg2) (snd (dataflow_tree_to_operator_aux n (chns_combine n dt1 dt2 buf chns1 chns2) (Comp f dt1 dt2)))"
  let ?dt_map' = "?dt_map buf sg1 sg2 chns1 chns2 dt1 dt2 wire n"
  let ?wsim' = "wsim (\<lambda>op1 op2. (\<exists>buf chns1 chns2 sg1 sg2 (dt1::(_, 'b, ('c, 'd, 'e) shared_state_scheme + ('c \<Rightarrow> 'd antichain), 'f \<times> 'g, 'h) dataflow_tree) dt2 wire n. op1 = ?map_dt buf sg1 sg2 chns1 chns2 dt1 dt2 wire n \<and>
                   op2 = ?dt_map buf sg1 sg2 chns1 chns2 dt1 dt2 wire n))"
  let ?wsim = "wsim (\<lambda>op1 op2. (\<exists>buf chns1 chns2 sg1 sg2 (dt1::(_, 'b, ('c, 'd, 'e) shared_state_scheme + ('c \<Rightarrow> 'd antichain), 'f \<times> 'g, 'h) dataflow_tree) dt2 wire n. op1 = ?map_dt buf sg1 sg2 chns1 chns2 dt1 dt2 wire n \<and>
                   op2 = ?dt_map buf sg1 sg2 chns1 chns2 dt1 dt2 wire n) \<or> op1 \<approx> op2)"
  have "?wsim' ?map_dt' ?dt_map'"

(* Maybe use the induction
  proof (induction "nodes_height (Comp f dt1 dt2)" arbitrary: buf dt1 dt2 f n1 n2 rule: nat_less_induct)
*)

    
    unfolding wsim_def dataflow_tree_to_operator_def
    apply safe
    apply(simp add: chns_combine_dt1_simp[OF card1] dtoa1 dataflow_tree_to_operator_aux_chns_cut[OF card1, of chns1]
        dataflow_tree_to_operator_aux_chns_cut[OF card2, of chns2, simplified n1_alt_def] dtoa2[simplified n1_alt_def]
        chns_combine_dt2_simp[OF card2 n1_alt_def] dtoa2)
    apply(auto elim!: step_map_op_elim step_comp_op_elim step_dataflow_op_elim dest!: map_IO_elim)
    subgoal for nid p op'' x1 x2
      apply(rule exI)
      apply(rule conjI, rule step_wstep)
      apply(rule step_Inp_dataflow_op_Inp_Inr_intro)
      apply(rule step_map_op[where io = "Inp (Inl (Inr (nid, p))) (Inr (x1, x2))"]; (rule map_IO_intros)?; simp?)
      apply(rule step_comp_op_L_Inp; simp?)
      apply(rule exI[where x = "buf"])
      apply(rule exI[where x = "chns1"])
      apply(rule exI[where x = "chns2"])
      apply(rule exI[where x = "sg1"])
      apply(rule exI[where x = "sg2"])
      apply(rule exI[where x = "undefined"])
      apply(rule exI[where x = "undefined"])
      apply(rule exI[where x = "wire"])
      apply(rule exI[where x = "n"])
      apply(intro conjI)
      subgoal
        sorry
      subgoal
        apply simp
      by simp
      using dtoa1
end
          apply((rule step_map_op, assumption); simp?)
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "chns1"])
          apply(rule exI[where x = "chns2"])
          apply(rule exI[where x = "sg1"])
          apply(rule exI[where x = "sg2"])
          apply(rule exI[where x = "Logic op'' su1"])
          apply(rule exI[where x = "Logic op2 su2"])
          apply(rule exI[where x = "Some"])
          apply(rule exI[where x = "n"])
          by simp

end
        subgoal for nid p ab bb op'' p'
          apply(cases p'; simp)
          apply(rule exI)
          apply(rule conjI, rule step_wstep)
          apply(rule step_Out_dataflow_op_Out_Inr_intro)
          apply(rule step_map_op[where io = "Out (Inr (Inr (n + 1, p))) (Inr (ab, bb))"]; (rule map_IO_intros)?; simp?)
          apply(rule step_comp_op_R_Out; simp?)
          apply((rule step_map_op, assumption); simp?)
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "chns1"])
          apply(rule exI[where x = "chns2"])
          apply(rule exI[where x = "sg1"])
          apply(rule exI[where x = "sg2"])
          apply(rule exI[where x = "Logic op1 su1"])
          apply(rule exI[where x = "Logic op'' su2"])
          apply(rule exI[where x = "Some"])
          apply(rule exI[where x = "n"])
          by simp
        subgoal for nid p ac bc op'' p'
          apply(cases p'; simp)
          apply(rule exI)
          apply(rule conjI, simp only: wstep_steps_Tau[symmetric],  rule step_wstep)
          apply(rule step_Tau_dataflow_op_Tau_intro)
          apply(rule step_map_op[where io = "Tau"]; (rule map_IO_intros)?; simp?)
          apply(rule step_Tau_comp_op_L_alt; simp?)
          apply((rule step_map_op, assumption); simp?)
          apply simp
          apply(rule exI[where x = "BENQ (nid, p) (ac, bc) buf"])
          apply(rule exI[where x = "chns1"])
          apply(rule exI[where x = "chns2"])
          apply(rule exI[where x = "sg1"])
          apply(rule exI[where x = "sg2"])
          apply(rule exI[where x = "Logic op'' su1"])
          apply(rule exI[where x = "Logic op2 su2"])
          apply(rule exI[where x = "Some"])
          apply(rule exI[where x = "n"])
          apply simp
(*The missing part is (Maybe nid should have the property that x - x = 0 *)
(*BENQ (nid + 1 + (nid - nid), p) (Inr (ac, bc)) (\<lambda>x. map Inr (chns_f buf chns1 chns2 x)) = 
  (\<lambda>x. map Inr (chns_f (BENQ (nid, p) (ac, bc) buf) chns1 chns2 x))*)
          sorry
        subgoal for nid p ab bb op'' p'
          apply(cases p'; simp)
          apply(rule exI)
          apply(rule conjI, simp only: wstep_steps_Tau[symmetric],  rule step_wstep)
          apply(rule step_Tau_dataflow_op_Tau_intro)
          apply(rule step_map_op[where io = "Tau"]; (rule map_IO_intros)?; simp?)
          apply(rule step_Tau_comp_op_R_alt; simp?)
             apply((rule step_map_op, assumption); simp?)
          sorry
        subgoal for op''
          apply(rule exI)
          apply(rule conjI, simp only: wstep_steps_Tau[symmetric],  rule step_wstep)
          apply(rule step_Tau_dataflow_op_Tau_intro)
          apply(rule step_map_op[where io = "Tau"]; (rule map_IO_intros)?; simp?)
          apply(rule step_comp_op_L_Tau; simp?)
          apply((rule step_map_op, assumption); simp?)
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "chns1"])
          apply(rule exI[where x = "chns2"])
          apply(rule exI[where x = "sg1"])
          apply(rule exI[where x = "sg2"])
          apply(rule exI[where x = "Logic op'' su1"])
          apply(rule exI[where x = "Logic op2 su2"])
          apply(rule exI[where x = "Some"])
          apply(rule exI[where x = "n"])
          by simp
        subgoal for nid st op'' p'
          apply(cases p'; simp)
          apply(rule exI)
          apply(rule conjI, simp only: wstep_steps_Tau[symmetric],  rule step_wstep)
          apply(rule step_Tau_dataflow_op_Out_Inl_intro)
          apply(rule step_map_op[where io = "Out (Inl (Inl n)) (Inl (Inl st))"]; (rule map_IO_intros)?; simp?)
          apply(rule step_comp_op_L_Out; simp?)
          apply((rule step_map_op, assumption); simp?)
          apply auto[1]
          apply simp
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "chns1"])
          apply(rule exI[where x = "chns2"])
          apply(rule exI[where x = "sg1\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg1) (extract_progress nid (edges sg1) st) (pt_tr sg1)\<rparr>"])
          apply(rule exI[where x = "sg2"])
          apply(rule exI[where x = "Logic op'' su1"])
          apply(rule exI[where x = "Logic op2 su2"])
          apply(rule exI[where x = "Some"])
          apply(rule exI[where x = "n"])
          sorry
        subgoal for nid op'' p'
          apply(cases p'; simp)
          apply(rule exI)
          apply(rule conjI, simp only: wstep_steps_Tau[symmetric], rule step_wstep)
          apply(rule step_Tau_dataflow_op_Inp_Inl_intro; simp?)
          apply(rule step_map_op[where io = "Inp (Inl (Inl n)) _"]; (rule map_IO_intros)?; simp?)
          apply(rule step_comp_op_L_Inp; simp?)
            apply((rule step_map_op, assumption); simp?)
          subgoal
            sorry
          subgoal
            sorry
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "chns1"])
          apply(rule exI[where x = "chns2"])
          apply(rule exI[where x = "case propagate_all (summ sg1) (pt_tr sg1) of Some conf' \<Rightarrow> sg1\<lparr>pt_tr := conf', upfro := (upfro sg1)(nid := False)\<rparr>"])
          apply(rule exI[where x = "sg2"])
          apply(rule exI[where x = "Logic op'' su1"])
          apply(rule exI[where x = "Logic op2 su2"])
          apply(rule exI[where x = "Some"])
          apply(rule exI[where x = "n"])
          apply simp
          sorry
        subgoal for op''
          apply(rule exI)
          apply(rule conjI, simp only: wstep_steps_Tau[symmetric],  rule step_wstep)
          apply(rule step_Tau_dataflow_op_Tau_intro)
          apply(rule step_map_op[where io = "Tau"]; (rule map_IO_intros)?; simp?)
          apply(rule step_comp_op_R_Tau; simp?)
          apply((rule step_map_op, assumption); simp?)
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "chns1"])
          apply(rule exI[where x = "chns2"])
          apply(rule exI[where x = "sg1"])
          apply(rule exI[where x = "sg2"])
          apply(rule exI[where x = "Logic op1 su1"])
          apply(rule exI[where x = "Logic op'' su2"])
          apply(rule exI[where x = "Some"])
          apply(rule exI[where x = "n"])
          by simp


end
      apply auto

end
        subgoal for nid p ab bb op'' p'
          apply(cases p'; simp)
          apply(rule exI)
          apply(rule conjI, rule step_wstep)
          apply(rule step_Inp_dataflow_op_Inp_Inr_intro)
          apply(rule step_map_op[where io = "Inp (Inl (Inr (n, p))) (Inr (ab, bb))"]; (rule map_IO_intros)?; simp?)
    
    
    
    
    
    
  proof -
    consider "\<exists> dt11 dt12 f1. dt1 = Comp f1 dt11 dt12" | "\<exists>op1 su1 dt21 dt22 f2. dt1 = Logic op1 su1 \<and> dt2 = Comp f2 dt21 dt22" | "\<exists>op1 su1 op2 su2. dt1 = Logic op1 su1 \<and> dt2 = Logic op2 su2"
      apply atomize_elim
      by(cases dt1; cases dt2; simp)
    then show "?wsim' ?map_dt' ?dt_map'"
    proof(cases, goal_cases "Comp" "Logic_Comp" "Logic_Logic")
      case Comp
      then obtain dt11 dt12 f1 where dt1_def: "dt1 = Comp f1 dt11 dt12"
        by blast
      show ?case 
        unfolding wsim_def
        apply auto
        sorry
    next
      case Logic_Comp
      then show ?case sorry
    next
      case Logic_Logic
      then obtain op1 su1 op2 su2 where dt1_def: "dt1 = Logic op1 su1" and dt2_def: "dt2 = Logic op2 su2"
        by blast
      have f_def: "f = Some"
        sorry
      show ?case
        unfolding wsim_def dt1_def dt2_def dataflow_tree_to_operator_def f_def
        apply safe
        apply(auto elim!: step_map_op_elim step_comp_op_elim step_dataflow_op_elim dest!: map_IO_elim)
        subgoal for nid p ab bb op'' p'
          apply(cases p'; simp)
          apply(rule exI)
          apply(rule conjI, rule step_wstep)
          apply(rule step_Inp_dataflow_op_Inp_Inr_intro)
          apply(rule step_map_op[where io = "Inp (Inl (Inr (n, p))) (Inr (ab, bb))"]; (rule map_IO_intros)?; simp?)
          apply(rule step_comp_op_L_Inp; simp?)
          apply((rule step_map_op, assumption); simp?)
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "chns1"])
          apply(rule exI[where x = "chns2"])
          apply(rule exI[where x = "sg1"])
          apply(rule exI[where x = "sg2"])
          apply(rule exI[where x = "Logic op'' su1"])
          apply(rule exI[where x = "Logic op2 su2"])
          apply(rule exI[where x = "Some"])
          apply(rule exI[where x = "n"])
          by simp
        subgoal for nid p ab bb op'' p'
          apply(cases p'; simp)
          apply(rule exI)
          apply(rule conjI, rule step_wstep)
          apply(rule step_Out_dataflow_op_Out_Inr_intro)
          apply(rule step_map_op[where io = "Out (Inr (Inr (n + 1, p))) (Inr (ab, bb))"]; (rule map_IO_intros)?; simp?)
          apply(rule step_comp_op_R_Out; simp?)
          apply((rule step_map_op, assumption); simp?)
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "chns1"])
          apply(rule exI[where x = "chns2"])
          apply(rule exI[where x = "sg1"])
          apply(rule exI[where x = "sg2"])
          apply(rule exI[where x = "Logic op1 su1"])
          apply(rule exI[where x = "Logic op'' su2"])
          apply(rule exI[where x = "Some"])
          apply(rule exI[where x = "n"])
          by simp
        subgoal for nid p ac bc op'' p'
          apply(cases p'; simp)
          apply(rule exI)
          apply(rule conjI, simp only: wstep_steps_Tau[symmetric],  rule step_wstep)
          apply(rule step_Tau_dataflow_op_Tau_intro)
          apply(rule step_map_op[where io = "Tau"]; (rule map_IO_intros)?; simp?)
          apply(rule step_Tau_comp_op_L_alt; simp?)
          apply((rule step_map_op, assumption); simp?)
          apply simp
          apply(rule exI[where x = "BENQ (nid, p) (ac, bc) buf"])
          apply(rule exI[where x = "chns1"])
          apply(rule exI[where x = "chns2"])
          apply(rule exI[where x = "sg1"])
          apply(rule exI[where x = "sg2"])
          apply(rule exI[where x = "Logic op'' su1"])
          apply(rule exI[where x = "Logic op2 su2"])
          apply(rule exI[where x = "Some"])
          apply(rule exI[where x = "n"])
          apply simp
(*The missing part is (Maybe nid should have the property that x - x = 0 *)
(*BENQ (nid + 1 + (nid - nid), p) (Inr (ac, bc)) (\<lambda>x. map Inr (chns_f buf chns1 chns2 x)) = 
  (\<lambda>x. map Inr (chns_f (BENQ (nid, p) (ac, bc) buf) chns1 chns2 x))*)
          sorry
        subgoal for nid p ab bb op'' p'
          apply(cases p'; simp)
          apply(rule exI)
          apply(rule conjI, simp only: wstep_steps_Tau[symmetric],  rule step_wstep)
          apply(rule step_Tau_dataflow_op_Tau_intro)
          apply(rule step_map_op[where io = "Tau"]; (rule map_IO_intros)?; simp?)
          apply(rule step_Tau_comp_op_R_alt; simp?)
             apply((rule step_map_op, assumption); simp?)
          sorry
        subgoal for op''
          apply(rule exI)
          apply(rule conjI, simp only: wstep_steps_Tau[symmetric],  rule step_wstep)
          apply(rule step_Tau_dataflow_op_Tau_intro)
          apply(rule step_map_op[where io = "Tau"]; (rule map_IO_intros)?; simp?)
          apply(rule step_comp_op_L_Tau; simp?)
          apply((rule step_map_op, assumption); simp?)
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "chns1"])
          apply(rule exI[where x = "chns2"])
          apply(rule exI[where x = "sg1"])
          apply(rule exI[where x = "sg2"])
          apply(rule exI[where x = "Logic op'' su1"])
          apply(rule exI[where x = "Logic op2 su2"])
          apply(rule exI[where x = "Some"])
          apply(rule exI[where x = "n"])
          by simp
        subgoal for nid st op'' p'
          apply(cases p'; simp)
          apply(rule exI)
          apply(rule conjI, simp only: wstep_steps_Tau[symmetric],  rule step_wstep)
          apply(rule step_Tau_dataflow_op_Out_Inl_intro)
          apply(rule step_map_op[where io = "Out (Inl (Inl n)) (Inl (Inl st))"]; (rule map_IO_intros)?; simp?)
          apply(rule step_comp_op_L_Out; simp?)
          apply((rule step_map_op, assumption); simp?)
          apply auto[1]
          apply simp
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "chns1"])
          apply(rule exI[where x = "chns2"])
          apply(rule exI[where x = "sg1\<lparr>upfro := \<lambda>_. True, pt_tr := change_multiplicities (summ sg1) (extract_progress nid (edges sg1) st) (pt_tr sg1)\<rparr>"])
          apply(rule exI[where x = "sg2"])
          apply(rule exI[where x = "Logic op'' su1"])
          apply(rule exI[where x = "Logic op2 su2"])
          apply(rule exI[where x = "Some"])
          apply(rule exI[where x = "n"])
          sorry
        subgoal for nid op'' p'
          apply(cases p'; simp)
          apply(rule exI)
          apply(rule conjI, simp only: wstep_steps_Tau[symmetric], rule step_wstep)
          apply(rule step_Tau_dataflow_op_Inp_Inl_intro; simp?)
          apply(rule step_map_op[where io = "Inp (Inl (Inl n)) _"]; (rule map_IO_intros)?; simp?)
          apply(rule step_comp_op_L_Inp; simp?)
            apply((rule step_map_op, assumption); simp?)
          subgoal
            sorry
          subgoal
            sorry
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "chns1"])
          apply(rule exI[where x = "chns2"])
          apply(rule exI[where x = "case propagate_all (summ sg1) (pt_tr sg1) of Some conf' \<Rightarrow> sg1\<lparr>pt_tr := conf', upfro := (upfro sg1)(nid := False)\<rparr>"])
          apply(rule exI[where x = "sg2"])
          apply(rule exI[where x = "Logic op'' su1"])
          apply(rule exI[where x = "Logic op2 su2"])
          apply(rule exI[where x = "Some"])
          apply(rule exI[where x = "n"])
          apply simp
          sorry
        subgoal for op''
          apply(rule exI)
          apply(rule conjI, simp only: wstep_steps_Tau[symmetric],  rule step_wstep)
          apply(rule step_Tau_dataflow_op_Tau_intro)
          apply(rule step_map_op[where io = "Tau"]; (rule map_IO_intros)?; simp?)
          apply(rule step_comp_op_R_Tau; simp?)
          apply((rule step_map_op, assumption); simp?)
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "chns1"])
          apply(rule exI[where x = "chns2"])
          apply(rule exI[where x = "sg1"])
          apply(rule exI[where x = "sg2"])
          apply(rule exI[where x = "Logic op1 su1"])
          apply(rule exI[where x = "Logic op'' su2"])
          apply(rule exI[where x = "Some"])
          apply(rule exI[where x = "n"])
          by simp
        sorry
    qed
  qed
  next
    fix x1 :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) option"
      and dt11 :: "('a, 'b, ('e, 'f, 'h) shared_state_scheme + ('e \<Rightarrow> 'f antichain), 'c \<times> 'd, 'i) dataflow_tree"
      and dt12 :: "('a, 'b, ('e, 'f, 'h) shared_state_scheme + ('e \<Rightarrow> 'f antichain), 'c \<times> 'd, 'i) dataflow_tree"
    assume ind1: "wsim (\<lambda>op1 op2. \<exists>buf chns1 chns2 sg1 sg2 dt1 dt2. op1 = map_op projl projr (comp_op Some buf (dataflow_op sg1 (dataflow_tree_to_operator chns1 (dt1::('a, 'b, ('e, 'f, 'h) shared_state_scheme + ('e \<Rightarrow> 'f antichain), 'c \<times> 'd, 'i) dataflow_tree))) (dataflow_op sg2 (dataflow_tree_to_operator chns2 dt2))) \<and> op2 = dataflow_op (sg_f sg1 sg2) (dataflow_tree_to_operator (chns_f buf chns1 chns2) (Comp Some dt1 dt2))) (map_op projl projr (comp_op Some buf (dataflow_op sg1 (dataflow_tree_to_operator chns1 dt11)) (dataflow_op sg2 (dataflow_tree_to_operator chns2 dt2)))) (dataflow_op (sg_f sg1 sg2) (dataflow_tree_to_operator (chns_f buf chns1 chns2) (Comp Some dt11 dt2)))"
      and "wsim (\<lambda>op1 op2. \<exists>buf chns1 chns2 sg1 sg2 dt1 dt2. op1 = map_op projl projr (comp_op Some buf (dataflow_op sg1 (dataflow_tree_to_operator chns1 (dt1::('a, 'b, ('e, 'f, 'h) shared_state_scheme + ('e \<Rightarrow> 'f antichain), 'c \<times> 'd, 'i) dataflow_tree))) (dataflow_op sg2 (dataflow_tree_to_operator chns2 dt2))) \<and> op2 = dataflow_op (sg_f sg1 sg2) (dataflow_tree_to_operator (chns_f buf chns1 chns2) (Comp Some dt1 dt2))) (map_op projl projr (comp_op Some buf (dataflow_op sg1 (dataflow_tree_to_operator chns1 dt12)) (dataflow_op sg2 (dataflow_tree_to_operator chns2 dt2)))) (dataflow_op (sg_f sg1 sg2) (dataflow_tree_to_operator (chns_f buf chns1 chns2) (Comp Some dt12 dt2)))"
    show "wsim (\<lambda>op1 op2. \<exists>buf chns1 chns2 sg1 sg2 dt1 dt2. op1 = map_op projl projr (comp_op Some buf (dataflow_op sg1 (dataflow_tree_to_operator chns1 (dt1::('a, 'b, ('e, 'f, 'h) shared_state_scheme + ('e \<Rightarrow> 'f antichain), 'c \<times> 'd, 'i) dataflow_tree))) (dataflow_op sg2 (dataflow_tree_to_operator chns2 dt2))) \<and> op2 = dataflow_op (sg_f sg1 sg2) (dataflow_tree_to_operator (chns_f buf chns1 chns2) (Comp Some dt1 dt2))) (map_op projl projr (comp_op Some buf (dataflow_op sg1 (dataflow_tree_to_operator chns1 (Comp x1 dt11 dt12))) (dataflow_op sg2 (dataflow_tree_to_operator chns2 dt2)))) (dataflow_op (sg_f sg1 sg2) (dataflow_tree_to_operator (chns_f buf chns1 chns2) (Comp Some (Comp x1 dt11 dt12) dt2)))"
      unfolding wsim_def dataflow_tree_to_operator_def
      apply safe
      apply(erule step_map_op_elim)
      apply (auto elim!: step_comp_op_elim step_dataflow_op_elim step_map_op_elim dest!: map_IO_elim split: )
      subgoal for nid p op'' ab bb

      sorry
  qed
  then have H1: "?wsim ?map_dt' ?dt_map'"
    unfolding wsim_def
    by fast
  have "?wsim ?dt_map' ?map_dt'"
    sorry
  then have H2: "?wsim ?dt_map' ?map_dt'"
    unfolding wsim_def
    by fast
  show "\<exists>op1 op2. ?map_dt' = op1 \<and> ?dt_map' = op2 \<and> ?wsim op1 op2 \<and> ?wsim op2 op1"
    using H1 H2
    by simp

    apply auto
    subgoal
      unfolding wsim_def
      apply safe
      apply(erule step_map_op_elim)
      apply (auto elim!: step_comp_op_elim)
      apply (auto elim!: step_comp_op_elim step_dataflow_op_elim)

      
      
      
      subgoal for io op
        apply(erule step_comp_op_elim; simp)
        subgoal premises prems for p x op'
          using prems(3) apply -
          apply(erule step_dataflow_op_elim; simp)
          unfolding dataflow_tree_to_operator_def
          sorry
      subgoal for p x op2'
        apply(erule step_dataflow_op_elim; simp)
          unfolding dataflow_tree_to_operator_def
          sorry
      subgoal for io op
        apply(erule step_comp_op_elim; simp)
        subgoal premises prems for p x op'
          using prems(3) apply -
          apply(erule step_dataflow_op_elim; simp)
          unfolding dataflow_tree_to_operator_def
          sorry
      subgoal for io op
        apply(erule step_comp_op_elim; simp)
        subgoal premises prems for p x op'
          using prems(3) apply -
          apply(erule step_dataflow_op_elim; simp)
          unfolding dataflow_tree_to_operator_def
          sorry
      subgoal for io op
        apply(erule step_comp_op_elim; simp)
        subgoal premises prems for p x op'
          using prems(3) apply -
          apply(erule step_dataflow_op_elim; simp)
          unfolding dataflow_tree_to_operator_def
          sorry
      subgoal for io op
        apply(erule step_comp_op_elim; simp)
        subgoal premises prems for p x op'
          using prems(3) apply -
          apply(erule step_dataflow_op_elim; simp)
          unfolding dataflow_tree_to_operator_def
          sorry
        sorry
      done
    subgoal
      sorry
    done
qed


lemma "invar_scomp buf chns1 chns2 pt_tr'1 pt_tr'2 upfro'1 upfro'2 \<Longrightarrow>
        map_op projl projr (comp_op Some buf (compile_dataflow_ext chns1 pt_tr'1 upfro'1 dt1) (compile_dataflow_ext chns2 pt_tr'2 upfro'2 dt2)) \<approx>
        (compile_dataflow_ext (chns_f buf chns1 chns2) (pt_tr'_f pt_tr'1 pt_tr'2) (upfro'_f upfro'1 upfro'2) (Comp Some dt1 dt2))"
proof (coinduction arbitrary: buf chns1 chns2 pt_tr'1 pt_tr'2 upfro'1 upfro'2 dt1 dt2)
  fix buf :: "'a \<times> 'b \<Rightarrow> ('c \<times> 'd) buf"
    and chns1 :: "'a \<times> 'b \<Rightarrow> ('c \<times> 'd) buf"
    and chns2 :: "'a \<times> 'b \<Rightarrow> ('c \<times> 'd) buf"
    and pt_tr'1 :: "(('a, 'b) location, 'e) configuration"
    and pt_tr'2 :: "(('a, 'b) location, 'e) configuration"
    and upfro'1 :: "'a \<Rightarrow> bool"
    and upfro'2 :: "'a \<Rightarrow> bool"
    and dt1 :: "('a, 'b, ('b, 'e, 'f) shared_state_scheme + ('b \<Rightarrow> 'e antichain), 'c \<times> 'd, 'e) dataflow_tree"
    and dt2 :: "('a, 'b, ('b, 'e, 'f) shared_state_scheme + ('b \<Rightarrow> 'e antichain), 'c \<times> 'd, 'e) dataflow_tree"
  assume invar: "invar_scomp buf chns1 chns2 pt_tr'1 pt_tr'2 upfro'1 upfro'2"
  show "\<exists>op1 op2. map_op projl projr (comp_op Some buf (compile_dataflow_ext chns1 pt_tr'1 upfro'1 dt1) (compile_dataflow_ext chns2 pt_tr'2 upfro'2 dt2)) = op1 \<and>
    compile_dataflow_ext (chns_f buf chns1 chns2) (pt_tr'_f pt_tr'1 pt_tr'2) (upfro'_f upfro'1 upfro'2) (Comp Some dt1 dt2) = op2 \<and> 
    wsim (\<lambda>op op'. (\<exists>buf chns1 chns2 pt_tr'1 pt_tr'2 upfro'1 upfro'2 dt1 dt2. op = map_op projl projr (comp_op Some buf (compile_dataflow_ext chns1 pt_tr'1 upfro'1 (dt1::('a, 'b, ('b, 'e, 'f) shared_state_scheme + ('b \<Rightarrow> _ antichain), 'c \<times> 'd, _) dataflow_tree)) 
    (compile_dataflow_ext chns2 pt_tr'2 upfro'2 dt2)) \<and> op' = compile_dataflow_ext (chns_f buf chns1 chns2) (pt_tr'_f pt_tr'1 pt_tr'2) (upfro'_f upfro'1 upfro'2) (Comp Some dt1 dt2) \<and> 
    invar_scomp buf chns1 chns2 pt_tr'1 pt_tr'2 upfro'1 upfro'2) \<or> op \<approx> op') op1 op2 \<and> 
    wsim (\<lambda>op op'. (\<exists>buf chns1 chns2 pt_tr'1 pt_tr'2 upfro'1 upfro'2 dt1 dt2. op = map_op projl projr (comp_op Some buf (compile_dataflow_ext chns1 pt_tr'1 upfro'1 (dt1::('a, 'b, ('b, 'e, 'f) shared_state_scheme + ('b \<Rightarrow> _ antichain), 'c \<times> 'd, _) dataflow_tree)) (compile_dataflow_ext chns2 pt_tr'2 upfro'2 dt2)) \<and> 
    op' = compile_dataflow_ext (chns_f buf chns1 chns2) (pt_tr'_f pt_tr'1 pt_tr'2) (upfro'_f upfro'1 upfro'2) (Comp Some dt1 dt2) \<and> 
    invar_scomp buf chns1 chns2 pt_tr'1 pt_tr'2 upfro'1 upfro'2) \<or> op \<approx> op') op2 op1"
    apply auto
    subgoal
      unfolding wsim_def
      apply safe
      apply(erule step_map_op_elim)
      apply auto
      subgoal for io op
        apply(erule step_comp_op_elim; simp)
        subgoal premises prems for p x op'
          using prems(3)
          apply(subst (asm) compile_dataflow_ext_def)
          apply simp
          apply(erule step_dataflow_op_elim; simp)
          subgoal premises prems for nid p' op''
            using prems(3)
            apply -
            apply(simp add: dataflow_tree_to_operator_def)
            sorry
          done
        sorry
      done
    subgoal
      sorry
    done
qed





end