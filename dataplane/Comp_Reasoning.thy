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
        oops


lemma dataflow_tree_to_graph_aux_Comp: "dataflow_tree_to_graph_aux n dt1 = dataflow_tree_to_graph_aux n dt1' \<Longrightarrow>
       dataflow_tree_to_graph_aux (fst (dataflow_tree_to_graph_aux n dt1)) dt2 = dataflow_tree_to_graph_aux (fst (dataflow_tree_to_graph_aux n dt1)) dt2' \<Longrightarrow>
        dataflow_tree_to_graph_aux n (Comp buf dt1 dt2) = dataflow_tree_to_graph_aux n (Comp buf dt1' dt2')"
  apply auto
  by(cases "dataflow_tree_to_graph_aux n dt1'"; simp)




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
  assumes ord_add_le: "CARD('a) > to_nat a + to_nat b \<Longrightarrow> 0 < to_nat b \<Longrightarrow> (a :: 'a) < a + b"
  assumes ord_add_leq: "to_nat ((a :: 'a) + b) \<le> to_nat a + to_nat b"
  assumes nodes_count_convert_aux: "CARD('a) > nodes_count_cut dt \<Longrightarrow> to_nat (nodes_count_cut dt :: 'a) = nodes_count_cut dt"
  assumes one_def: "to_nat 1 = 1"
  assumes to_nat_le: "x < y \<Longrightarrow> to_nat x < to_nat y"
  assumes add_strict_right_mono: "CARD('a) > to_nat x' + to_nat y \<Longrightarrow> x < x' \<Longrightarrow> x + y < x' + y"
begin

lemma nodes_count_convert: "CARD('a) > nodes_count dt \<Longrightarrow> to_nat (nodes_count dt :: 'a) = nodes_count dt"
  by(simp add: nodes_count_cut nodes_count_convert_aux)

lemma ord_add_le_nodes: "CARD('a) > to_nat n + nodes_count dt \<Longrightarrow> (n :: 'a) < n + nodes_count dt"
  apply(rule ord_add_le)
  subgoal
    by (simp add: nodes_count_convert)
  subgoal
    apply(simp add: nodes_count_convert)
    by(induction dt; simp)
  done

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
    apply(simp add: nat_int_comparison Rep_bit0_0 mod_pos_pos_trivial less_bit0_def)
    unfolding Rep_bit0_add[symmetric, of n m]
    by(cases n; cases m; simp)
  subgoal for n m
    apply simp
    apply(cases n; cases m; simp add: bit0.of_int_eq Abs_bit0_inverse bit0.add_def nat_add_distrib[symmetric])
    by(simp add: zmod_le_nonneg_dividend nat_mono)
  subgoal for dt
    apply(induction dt; simp add: bit0.Rep_1 Rep_bit0_add)
    subgoal for dt1 dt2
      by(cases "nodes_count_cut dt1 :: 'a bit0"; cases "nodes_count_cut dt2 :: 'a bit0"; simp add: bit0.of_int_eq Abs_bit0_inverse bit0.add_def)
    done
  subgoal
    by(simp add: bit0.Rep_1)
  subgoal for x y
    apply(auto simp add: less_bit0_def)
    by (metis Rep_bit0_0 order_le_imp_less_or_eq order_trans_rules(20))
  subgoal for x' y x
    by(auto simp add: less_bit0_def Rep_bit0_add[symmetric])
  subgoal for n m
    apply(simp add: nat_int_comparison Rep_bit1_1 mod_pos_pos_trivial less_eq_bit1_def)
    unfolding Rep_bit1_add[symmetric, of n m]
    apply(cases n; cases m; simp)
    by(simp add: bit1.of_int_eq Abs_bit1_inverse)
  subgoal for n m
    apply(simp add: nat_int_comparison Rep_bit1_1 mod_pos_pos_trivial less_bit1_def)
    unfolding Rep_bit1_add[symmetric, of n m]
    by(cases n; cases m; simp)
  subgoal for n m
    apply simp
    apply(cases n; cases m; simp add: bit1.of_int_eq Abs_bit1_inverse bit1.add_def nat_add_distrib[symmetric])
    by(simp add: zmod_le_nonneg_dividend nat_mono)
  subgoal for dt
    apply(induction dt; simp add: bit1.Rep_1 Rep_bit0_add)
    subgoal for dt1 dt2
      by(cases "nodes_count_cut dt1 :: 'a bit1"; cases "nodes_count_cut dt2 :: 'a bit1"; simp add: bit1.of_int_eq Abs_bit1_inverse bit1.add_def)
    done
  subgoal
    by(simp add: bit1.Rep_1)
  subgoal for x y
    apply(auto simp add: less_bit1_def)
    by (metis Rep_bit1_1 order_le_imp_less_or_eq order_trans_rules(20))
  subgoal for x' y x
    by(auto simp add: less_bit1_def Rep_bit1_add[symmetric])
  done
end



lemma test: "(n :: _ :: {tln,preorder,group_add, ab_semigroup_add,preorder,linorder}) = undefined \<Longrightarrow> False"
  sorry

lemma "(n :: 4) = undefined \<Longrightarrow> False"
  by(rule test, simp)



lemma comp_op_chns_inv_aux: "rel_fun (=)
        (\<lambda>op op'.
            \<exists>op1 op2 f f' f'' p p' p'' p''' x chns chns'.
               op = comp_op wire chns op1 op2 \<and> op' = comp_op wire chns' op1 op2 \<or>
               cases op op' op1 op2 f f' f'' p p' p'' p''' x chns chns')
        (\<lambda>x. comp_op wire chns (f'' x) (f' x)) (\<lambda>x. comp_op wire chns' (f'' x) (f' x))"
  unfolding rel_fun_def
  by fast


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


lemma comp_op_chns_invar: "(\<forall> p. p \<in> inputs op2 \<and> (\<exists>p'. wire p' = Some p ) \<longrightarrow> chns p = chns' p) \<Longrightarrow>
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
          apply(intro allI impI)
          apply(drule spec, drule mp, assumption)
          unfolding BENQ_def
          by auto
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
   (image projr (Set.filter is_Inr (outputs (snd (dataflow_tree_to_operator_aux n chns dt1)))) \<inter> {(n',p). wire (n' - n,p) \<noteq> None}) \<union> 
   (image projr (Set.filter is_Inr (inputs (snd (dataflow_tree_to_operator_aux (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2)))) \<inter> {(n',p). \<exists> n'' p'. wire (n'' - n,p') = Some ((- fst (dataflow_tree_to_operator_aux n chns dt1)) + n' ,p)}) \<union> 
   used_ports n chns dt1 \<union> used_ports (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2"

primrec used_ports' where
  "used_ports' _ (Logic op su) = {}"
| "used_ports' n (Comp wire dt1 dt2) = 
   {(n',p). wire (n' - n,p) \<noteq> None} \<union> {(n',p). \<exists> n'' p'. wire (n'' - n,p') = Some ((- fst (dataflow_tree_to_operator_aux n (\<lambda>_. []) dt1)) + n' ,p)} \<union> 
   used_ports' n dt1 \<union> used_ports' (fst (dataflow_tree_to_operator_aux n (\<lambda>_. []) dt1)) dt2"

lemma used_ports_sub: "used_ports (n :: 'n :: {minus,one,semigroup_add,ord,equal,uminus}) chns dt \<subseteq> used_ports' n dt"
  apply(induction dt arbitrary: n)
  subgoal
    by simp
  subgoal for wire dt1 dt2 n
    by (fastforce simp add: fst_dtoa_def)
  done



lemma card_leq_nodes_count_help: "nodes_count dt1 -+- nodes_count dt2 -+- tln_class.to_nat (n :: 'a :: {tln,ab_semigroup_add}) < CARD('a) \<Longrightarrow> nodes_count dt2 -+- tln_class.to_nat (n + nodes_count dt1) < CARD('a)"
  apply(rule dual_order.strict_trans2, assumption)
  apply(rule order.trans, rule add_left_mono, rule tln_class.ord_add_leq)
  using tln_class.nodes_count_convert
  by (metis add.commute add.left_commute add_lessD1 eq_imp_le)

lemma dtoa_outputs: "CARD('n) > nodes_count dt + tln_class.to_nat n \<Longrightarrow> Inr (n',p) \<in> outputs (snd (dataflow_tree_to_operator_aux (n :: 'n :: {one,ab_semigroup_add,zero,ord,equal,tln,preorder,group_add}) chns dt)) \<Longrightarrow> n' < (fst (dataflow_tree_to_operator_aux n chns dt))"
proof (induction dt arbitrary: n)
  case (Logic x1 x2)
  then show ?case 
    by(auto simp add: op.set_map tln_class.one_def intro!: tln_class.ord_add_le split: option.splits)
next
  fix wire :: "'n \<times> 'a \<Rightarrow> ('n \<times> 'a) option"
    and dt1 :: "('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree"
    and dt2 :: "('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree"
    and n :: 'n
  assume ind1: "\<And>n. nodes_count (dt1::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) -+- tln_class.to_nat n < CARD('n) \<Longrightarrow> Inr (n', p) \<in> outputs (snd (dataflow_tree_to_operator_aux n chns dt1)) \<Longrightarrow> n' < fst (dataflow_tree_to_operator_aux n chns dt1)"
    and ind2: "\<And>n. nodes_count (dt2::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) -+- tln_class.to_nat n < CARD('n) \<Longrightarrow> Inr (n', p) \<in> outputs (snd (dataflow_tree_to_operator_aux n chns dt2)) \<Longrightarrow> n' < fst (dataflow_tree_to_operator_aux n chns dt2)"
    and card: "nodes_count (Comp wire (dt1::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) dt2) -+- tln_class.to_nat n < CARD('n)"
    and outputs: "Inr (n', p) \<in> outputs (snd (dataflow_tree_to_operator_aux n chns (Comp wire (dt1::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) dt2)))"
  have H: "dataflow_tree_to_operator_aux n chns dt1 = (n1, op1) \<Longrightarrow> dataflow_tree_to_operator_aux n1 chns dt2 = (n2, op2) \<Longrightarrow> 
        Inr (n', p) \<in> outputs op2 \<Longrightarrow> n' < fst (dataflow_tree_to_operator_aux (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2)" for n1 n2 op1 op2
    apply(rule ind2)
    subgoal
      unfolding fst_dtoa_def
      by(rule card_leq_nodes_count_help[OF card[simplified]])
    by auto
  have card1: "nodes_count dt1 -+- tln_class.to_nat n < CARD('n)"
    using card
    by simp
  show "n' < fst (dataflow_tree_to_operator_aux n chns (Comp wire (dt1::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) dt2))"
    using outputs
    apply(auto simp add: op.set_map fst_dtoa_def dest!: card_leq_nodes_count_help split: option.splits prod.splits)
    subgoal for x1 x2 x1a x2a
      apply(subgoal_tac "x1 \<le> x1a")
      subgoal
        using ind1[OF card1] order_trans_rules(22) by fastforce
      subgoal
        using card
        apply simp
        apply(drule arg_cong[where f = fst])+
        apply(simp add: fst_dtoa_def)
        using tln_class.ord_add[of "n + nodes_count dt1" "nodes_count dt2"] card_leq_nodes_count_help
        by (metis add.commute add_lessD1 nodes_count_convert)
      done
    subgoal for x1 x2 x1a x2a
      apply(frule H; assumption?)
      by simp
    done
qed

lemma dtoa_inputs: "CARD('n) > nodes_count dt + tln_class.to_nat n \<Longrightarrow> 
      Inr (n',p) \<in> inputs (snd (dataflow_tree_to_operator_aux (n :: 'n :: {one,ab_semigroup_add,zero,ord,equal,tln,preorder,group_add}) chns dt)) \<Longrightarrow> n' < (fst (dataflow_tree_to_operator_aux n chns dt))"
proof (induction dt arbitrary: n)
  case (Logic x1 x2)
  then show ?case 
    by(auto simp add: op.set_map tln_class.one_def intro!: tln_class.ord_add_le split: option.splits)
next
  fix wire :: "'n \<times> 'a \<Rightarrow> ('n \<times> 'a) option"
    and dt1 :: "('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree"
    and dt2 :: "('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree"
    and n :: 'n
  assume ind1: "\<And>n. nodes_count (dt1::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) -+- tln_class.to_nat n < CARD('n) \<Longrightarrow> Inr (n', p) \<in> inputs (snd (dataflow_tree_to_operator_aux n chns dt1)) \<Longrightarrow> n' < fst (dataflow_tree_to_operator_aux n chns dt1)"
    and ind2: "\<And>n. nodes_count (dt2::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) -+- tln_class.to_nat n < CARD('n) \<Longrightarrow> Inr (n', p) \<in> inputs (snd (dataflow_tree_to_operator_aux n chns dt2)) \<Longrightarrow> n' < fst (dataflow_tree_to_operator_aux n chns dt2)"
    and card: "nodes_count (Comp wire (dt1::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) dt2) -+- tln_class.to_nat n < CARD('n)"
    and inputs: "Inr (n', p) \<in> inputs (snd (dataflow_tree_to_operator_aux n chns (Comp wire (dt1::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) dt2)))"
  have H: "dataflow_tree_to_operator_aux n chns dt1 = (n1, op1) \<Longrightarrow> dataflow_tree_to_operator_aux n1 chns dt2 = (n2, op2) \<Longrightarrow> 
        Inr (n', p) \<in> inputs op2 \<Longrightarrow> n' < fst (dataflow_tree_to_operator_aux (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2)" for n1 n2 op1 op2
    apply(rule ind2)
    subgoal
      unfolding fst_dtoa_def
      by(rule card_leq_nodes_count_help[OF card[simplified]])
    by auto
  have card1: "nodes_count dt1 -+- tln_class.to_nat n < CARD('n)"
    using card
    by simp
  show "n' < fst (dataflow_tree_to_operator_aux n chns (Comp wire (dt1::('n, 'a, 'b, 'c \<times> 'd, 'e) dataflow_tree) dt2))"
    using inputs
    apply(auto simp add: op.set_map fst_dtoa_def dest!: card_leq_nodes_count_help split: option.splits prod.splits)
    subgoal for x1 x2 x1a x2a
      apply(subgoal_tac "x1 \<le> x1a")
      subgoal
        using ind1[OF card1] order_trans_rules(22) by fastforce
      subgoal
        using card
        apply simp
        apply(drule arg_cong[where f = fst])+
        apply(simp add: fst_dtoa_def)
        using tln_class.ord_add[of "n + nodes_count dt1" "nodes_count dt2"] card_leq_nodes_count_help
        by (metis add.commute add_lessD1 nodes_count_convert)
      done
    subgoal for x1 x2 x1a x2a
      apply(frule H; assumption?)
      by simp
    done
qed


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
    apply(auto intro!: eq simp add: dtoa1 dtoa2 image_def split: sum.splits; clarsimp split: option.splits)
     apply force
    subgoal for a b p'
      apply(cases p'; simp)
      subgoal for p''
        apply(cases p''; simp)
        subgoal for aa bb
          apply(erule allE[where x = aa])
          apply(erule allE[where x = bb]; simp)
          apply(rule exI[where x = "aa"])
          apply(rule exI[where x = "bb"])
          by auto
        done
      done
    apply force
    subgoal for a b p'
      apply(cases p'; simp)
      subgoal for p''
        apply(cases p''; simp)
        subgoal for aa bb
          apply(erule allE[where x = aa])
          apply(erule allE[where x = bb]; simp)
          apply(rule exI[where x = "aa"])
          apply(rule exI[where x = "bb"])
          by auto
        done
      done
    done
qed

lemma dataflow_tree_to_operator_aux_chns_inv': "CARD('n) > nodes_count dt + tln_class.to_nat n \<Longrightarrow> \<forall> p. p \<in> used_ports' n dt \<longrightarrow> 
  chns p = chns' p \<Longrightarrow> dataflow_tree_to_operator_aux (n :: 'n :: {one,semigroup_add,zero,ord,equal,tln,preorder,group_add}) chns dt = dataflow_tree_to_operator_aux n chns' dt"
  using dataflow_tree_to_operator_aux_chns_inv used_ports_sub
  by blast

abbreviation chns_cut where
  "chns_cut n chns dt \<equiv> (\<lambda> p. if p \<in> used_ports' n dt then chns p else [])"

lemma dataflow_tree_to_operator_aux_chns_cut: "CARD('n) > nodes_count dt + tln_class.to_nat n \<Longrightarrow>
  dataflow_tree_to_operator_aux (n :: 'n :: {one,semigroup_add,zero,ord,equal,tln,preorder,group_add}) chns dt = 
  dataflow_tree_to_operator_aux n (chns_cut n chns dt) dt"
  using dataflow_tree_to_operator_aux_chns_inv'
  by fastforce

lemma nodes_count_less_help: "nodes_count dt1 -+- nodes_count dt2 -+- tln_class.to_nat n < CARD('n) \<Longrightarrow> n' < nodes_count dt1 + (n :: 'n :: {one,semigroup_add,zero,ord,equal,tln,preorder,group_add,ab_semigroup_add}) \<Longrightarrow> n' <nodes_count dt1 + nodes_count dt2 + n"
  apply(rule order.strict_trans2, assumption)
  apply(drule card_leq_nodes_count_help)
  apply(subgoal_tac "n + nodes_count dt1 \<le> n + nodes_count dt1 + nodes_count dt2")
  defer
  subgoal
    apply(rule tln_class.ord_add)
    by(simp add: nodes_count_convert)
  by (simp add: add.commute add.left_commute)


lemma nodes_count_less_help': "nodes_count dt1 -+- nodes_count dt2 -+- tln_class.to_nat n < CARD('n) \<Longrightarrow> nodes_count dt1 + (n :: 'n :: {one,semigroup_add,zero,ord,equal,tln,preorder,group_add,ab_semigroup_add}) < nodes_count dt1 + nodes_count dt2 + n"
  apply(subgoal_tac " nodes_count dt1 + n < nodes_count dt1 + n + nodes_count dt2")
  subgoal
    by (simp add: Groups.add_ac(2,3))
  subgoal
    apply(rule ord_add_le_nodes)
    by (simp add: Groups.add_ac(2) card_leq_nodes_count_help)
  done

lemma dtoa_outputs_leq: "CARD('n) > nodes_count dt + tln_class.to_nat n \<Longrightarrow> Inr (n', p) \<in> outputs (snd (dataflow_tree_to_operator_aux (n :: 'n :: {preorder,minus,one,plus,tln,semigroup_add,equal,ab_semigroup_add}) chns dt)) \<Longrightarrow> n \<le> n'"
  apply(induction dt arbitrary: n)
  subgoal for op su n
    by(auto simp add: op.set_map refl split: option.splits)
  subgoal premises prems for wire dt1 dt2 n
    using prems(3,4)
    apply(auto simp add: op.set_map split: prod.splits)
    subgoal for n1 p1 n2 p2
      using prems(1)
      by auto
    subgoal for n1 p1 n2 p2
      apply(rule order.trans[of _ n1])
      subgoal
        apply(drule arg_cong[where f = fst])+
        apply(simp add: fst_dtoa_def)
        by(auto intro!: tln_class.ord_add simp add: tln_class.nodes_count_convert)
      subgoal
        apply(rule prems(2))
        apply(drule arg_cong[where f = fst])+
        by(auto dest!: card_leq_nodes_count_help simp add: fst_dtoa_def)
      done
    done
  done

lemma dtoa_outputs_le: "CARD('n) > nodes_count dt + tln_class.to_nat n \<Longrightarrow> Inr (n', p) \<in> outputs (snd (dataflow_tree_to_operator_aux (n :: 'n :: {preorder,minus,one,plus,tln,semigroup_add,equal,ab_semigroup_add,group_add}) chns dt)) \<Longrightarrow> n' < nodes_count dt + n"
  apply(induction dt arbitrary: n)
  subgoal for op su n
    apply(auto simp add: op.set_map refl split: option.splits)
    by (metis One_nat_def add.commute less_add_one one_def ord_add_le plus_1_eq_Suc)
  subgoal premises prems for wire dt1 dt2 n
    using prems(3,4)
    apply(auto simp add: op.set_map split: prod.splits option.splits)
    subgoal premises premss for n1 p1 n2 p2
      using prems(1)[of n, simplified premss(2) snd_conv] premss(1,4,5) prems(3)
      by(auto dest!: nodes_count_less_help[rotated])
    subgoal premises premss for n1 p1 n2 p2
      apply(subgoal_tac "nodes_count dt2 -+- tln_class.to_nat n1 < CARD('n)")
      defer
      subgoal
        using prems(3) premss(2)[symmetric,THEN arg_cong[where f = fst]]
        by(auto intro: card_leq_nodes_count_help simp add: fst_dtoa_def)
      using prems(2)[of n1, simplified premss(3) snd_conv] premss(1,4) 
      apply auto
      apply(rule order.strict_trans2, assumption)
      using premss(2)[symmetric,THEN arg_cong[where f = fst]]
      apply(simp add: fst_dtoa_def)
      by (simp add: add.commute add.left_commute)
    done
  done


lemma dtoa_inputs_leq: "CARD('n) > nodes_count dt + tln_class.to_nat n \<Longrightarrow> Inr (n', p) \<in> inputs (snd (dataflow_tree_to_operator_aux (n :: 'n :: {preorder,minus,one,plus,tln,semigroup_add,equal,ab_semigroup_add,group_add}) chns dt)) \<Longrightarrow> n \<le> n'"
  apply(induction dt arbitrary: n)
  subgoal for op su n
    by(auto simp add: op.set_map refl split: option.splits)
  subgoal premises prems for wire dt1 dt2 n
    using prems(3,4)
    apply(auto simp add: op.set_map split: prod.splits)
    subgoal for n1 p1 n2 p2
      using prems(1)
      by auto
    subgoal for n1 p1 n2 p2
      apply(rule order.trans[of _ n1])
      subgoal
        apply(drule arg_cong[where f = fst])+
        apply(simp add: fst_dtoa_def)
        by(auto intro!: tln_class.ord_add simp add: tln_class.nodes_count_convert)
      subgoal
        apply(rule prems(2))
        apply(drule arg_cong[where f = fst])+
        by(auto dest!: card_leq_nodes_count_help simp add: fst_dtoa_def)
      done
    done
  done



lemma dtoa_inputs_le: "CARD('n) > nodes_count dt + tln_class.to_nat n \<Longrightarrow> Inr (n', p) \<in> inputs (snd (dataflow_tree_to_operator_aux (n :: 'n :: {preorder,minus,one,plus,tln,semigroup_add,equal,ab_semigroup_add,group_add}) chns dt)) \<Longrightarrow> n' < nodes_count dt + n"
  apply(induction dt arbitrary: n)
  subgoal for op su n
    apply(auto simp add: op.set_map refl split: option.splits)
    by (metis One_nat_def add.commute less_add_one one_def ord_add_le plus_1_eq_Suc)
  subgoal premises prems for wire dt1 dt2 n
    using prems(3,4)
    apply(auto simp add: op.set_map split: prod.splits option.splits)
    subgoal premises premss for n1 p1 n2 p2
      using prems(1)[of n, simplified premss(2) snd_conv] premss(1,4) prems(3)
      by(auto dest!: nodes_count_less_help[rotated])
    subgoal premises premss for n1 p1 n2 p2
      apply(subgoal_tac "nodes_count dt2 -+- tln_class.to_nat n1 < CARD('n)")
      defer
      subgoal
        using prems(3) premss(2)[symmetric,THEN arg_cong[where f = fst]]
        by(auto intro: card_leq_nodes_count_help simp add: fst_dtoa_def)
      using prems(2)[of n1, simplified premss(3) snd_conv] premss(1,4) 
      apply auto
      apply(rule order.strict_trans2, assumption)
      using premss(2)[symmetric,THEN arg_cong[where f = fst]]
      apply(simp add: fst_dtoa_def)
      by (simp add: add.commute add.left_commute)
    done
  done


lemma dataflow_tree_to_operator_aux_chns_eq_larger: "CARD('n) > nodes_count dt + tln_class.to_nat n \<Longrightarrow> 
  \<forall> n' p. n' \<ge> n \<longrightarrow> chns (n',p) = chns' (n',p) \<Longrightarrow>
  dataflow_tree_to_operator_aux (n :: 'n :: {one,semigroup_add,zero,ord,equal,tln,preorder,group_add,ab_semigroup_add}) chns dt = 
  dataflow_tree_to_operator_aux n chns' dt"
  apply(rule dataflow_tree_to_operator_aux_chns_inv, assumption)
  apply(safe)
  subgoal for n' p
    apply(induction dt arbitrary: n)
    subgoal
      by simp
    subgoal premises prems for wire dt1 dt2 n
      using prems(3,4,5)
      apply auto
      subgoal for x n'' p'
        apply(cases x; simp)
        apply hypsubst_thin
        by(auto dest!: dtoa_outputs_leq[rotated])
      subgoal for x n'' p'
        apply(cases x; simp)
        apply hypsubst_thin
        apply(erule allE[where x = n'])+
        apply(frule card_leq_nodes_count_help)
        apply(auto simp add: fst_dtoa_def dest!: dtoa_inputs_leq[rotated])
        apply(subgoal_tac "n \<le> n + nodes_count dt1"; simp?)
        subgoal
          by (meson dual_order.trans)
        by(auto simp add: tln_class.nodes_count_convert intro: tln_class.ord_add)
      subgoal
        using prems(1)
        by force
      subgoal
        apply(rule prems(2)[of "fst (dataflow_tree_to_operator_aux n chns dt1)"])
        apply(auto simp add: fst_dtoa_def intro: card_leq_nodes_count_help)
        subgoal for n'' p''
          apply(erule allE[where x = n''])
          apply(subgoal_tac "n \<le> n''"; simp?)
          apply(subgoal_tac "n \<le> n + nodes_count dt1"; simp?)
          subgoal
            by (meson dual_order.trans)
          by(auto simp add: tln_class.nodes_count_convert intro: tln_class.ord_add)
        done
      done
    done
  done



lemma dataflow_tree_to_operator_aux_chns_eq_smaller: "CARD('n) > nodes_count dt + tln_class.to_nat n \<Longrightarrow> 
  \<forall> n' p. n' < nodes_count dt + n \<longrightarrow> chns (n',p) = chns' (n',p) \<Longrightarrow>
  dataflow_tree_to_operator_aux (n :: 'n :: {one,semigroup_add,zero,ord,equal,tln,preorder,group_add,ab_semigroup_add}) chns dt = 
  dataflow_tree_to_operator_aux n chns' dt"
  apply(rule dataflow_tree_to_operator_aux_chns_inv, assumption)
  apply(safe)
  subgoal for n' p
    apply(induction dt arbitrary: n)
    subgoal
      by simp
    subgoal premises prems for wire dt1 dt2 n
      using prems(3,4,5) nodes_count_less_help[of dt1 dt2 n]
      apply auto
      subgoal for x n'' p'
        apply(cases x; simp)
        apply hypsubst_thin
        by(drule dtoa_outputs_le[rotated]; simp?)
      subgoal for x n'' p'
        apply(cases x; simp)
        apply hypsubst_thin
        apply(erule allE[where x = n'])+
        apply(frule card_leq_nodes_count_help)
        apply(auto simp add: fst_dtoa_def dest!: dtoa_inputs_le[rotated])
        apply(rule FalseE)
        unfolding Metis.not_atomize
        apply(subgoal_tac "n \<le> n + nodes_count dt1"; simp?)
        subgoal
          by (metis add.left_commute add.commute)
        by(auto simp add: tln_class.nodes_count_convert intro: tln_class.ord_add)
      subgoal
        by(rule prems(1); simp)
      subgoal
        apply(rule prems(2)[of "fst (dataflow_tree_to_operator_aux n chns dt1)"])
        apply(auto simp add: fst_dtoa_def intro: card_leq_nodes_count_help)
        subgoal for n'' p''
          apply(erule allE[where x = n''])
          apply(erule impE; simp?)
          by (simp add: add.commute add.left_commute)
        done
      done
    done
  done



lemma "step io' op op' \<Longrightarrow> map_IO (case_option (Inl n) (\<lambda>p. Inr (n, p))) (case_option (Inl n) (\<lambda>p. Inr (n, p))) id io' = io \<Longrightarrow>
       step io (snd (dataflow_tree_to_operator_aux (n :: 'a :: {minus,one,semigroup_add,zero,ord,equal,tln,preorder}) chns (Logic op su))) 
              (snd (dataflow_tree_to_operator_aux n chns' (Logic op' su')))"
  by simp



inductive step_dt where                        
  SLogic[intro]: "step io (snd (dataflow_tree_to_operator_aux n chns (Logic op su))) (snd (dataflow_tree_to_operator_aux n chns (Logic op' su))) \<Longrightarrow> 
    step_dt io n chns (Logic op su) chns (Logic op' su)"
| SInpInl[intro]: "(step_dt (Inp (Inl p) x) n chns dt1 chns dt1' \<and> dt2 = dt2') \<or> (step_dt (Inp (Inl p) x) (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2 chns dt2' \<and> dt1 = dt1') \<Longrightarrow>
    step_dt (Inp (Inl p) x) n chns (Comp wire dt1 dt2) chns (Comp wire dt1' dt2')"
| SOutInl[intro]: "(step_dt (Out (Inl p) x) n chns dt1 chns dt1' \<and> dt2 = dt2') \<or> (step_dt (Out (Inl p) x) (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2 chns dt2' \<and> dt1 = dt1') \<Longrightarrow>
    step_dt (Out (Inl p) x) n chns (Comp wire dt1 dt2) chns (Comp wire dt1' dt2')"
| SInpInr[intro]: "(\<forall> p' n''. wire (n'' - n,p') \<noteq> Some (n' - (fst (dataflow_tree_to_operator_aux n chns dt1)),p) \<and> step_dt (Inp (Inr (n',p)) x) (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2 chns dt2' \<and> dt1 = dt1') \<or>
    (step_dt (Inp (Inr (n',p)) x) n chns dt1 chns dt1' \<and> dt2 = dt2') \<Longrightarrow>
    step_dt (Inp (Inr (n',p)) x) n chns (Comp wire dt1 dt2) chns (Comp wire dt1' dt2')"
| SOutInr[intro]: "(wire (n' - n,p) = None \<and> step_dt (Out (Inr (n',p)) x) n chns dt1 chns dt1' \<and> dt2 = dt2') \<or>
    (step_dt (Out (Inr (n',p)) x) (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2 chns dt2' \<and> dt1 = dt1') \<Longrightarrow>
    step_dt (Out (Inr (n',p)) x) n chns (Comp wire dt1 dt2) chns (Comp wire dt1' dt2')"
| STau[intro]: "(step_dt Tau n chns dt1 chns' dt1' \<and> dt2 = dt2' ) \<or>
    (step_dt Tau (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2 chns' dt2' \<and> dt1 = dt1') \<or>
    (\<exists> p p' n' n'' x. wire (n'' - n, p') = Some (n' - (fst (dataflow_tree_to_operator_aux n chns dt1)),p) \<and> step_dt (Inp (Inr (n',p)) (Inr x)) (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2 chns dt2' \<and> dt1 = dt1' \<and> chns' = BTL (n',p) chns \<and> chns (n',p) \<noteq> [] \<and> x = BHD (n',p) chns) \<or>
    (\<exists> p p' n' n'' x. wire (n' - n,p) = Some (n'',p') \<and> step_dt (Out (Inr (n',p)) (Inr x)) n chns dt1 chns dt1' \<and> dt2 = dt2' \<and> chns' = BENQ (n'' + (fst (dataflow_tree_to_operator_aux n chns dt1)),p') x chns) \<Longrightarrow>
    step_dt Tau n chns (Comp wire dt1 dt2) chns' (Comp wire dt1' dt2')"

lemma step_dt_same_chns_Inp: "step_dt (Inp p x) n chns dt chns' dt' \<Longrightarrow> chns = chns'"
  apply(drule step_dt.cases)
  by auto

lemma step_dt_same_chns_Out: "step_dt (Out p x) n chns dt chns' dt' \<Longrightarrow> chns = chns'"
  apply(drule step_dt.cases)
  by auto

primrec chns_set where
  "chns_set io wire n chns (Logic op su) = (case io of
    Tau \<Rightarrow> {(chns, dt'). \<exists>dt' op'. step io op op' \<and> dt' = Logic op' su}
  | Inp (Some (n,p)) x \<Rightarrow> {(chns, dt'). undefined }
  | Inp None x \<Rightarrow> {(chns, dt'). undefined }
  | Out p x \<Rightarrow> undefined)"
| "chns_set io wire n chns (Comp _ op _) = undefined" 

lemma dtoa_fst_chns_inv: "fst (dataflow_tree_to_operator_aux n chns dt) = fst (dataflow_tree_to_operator_aux n chns' dt)"
  apply(induction dt arbitrary: n; simp)
  apply(auto split: prod.splits)
  by (metis eq_fst_iff)



lemma used_ports_less: "CARD('a) > nodes_count dt + tln_class.to_nat n \<Longrightarrow> 
      (n',p) \<in> used_ports (n :: 'a :: {minus,one,semigroup_add,zero,ord,equal,tln,preorder,group_add,ab_semigroup_add}) chns dt \<Longrightarrow> 
      n' < fst (dataflow_tree_to_operator_aux n chns dt)"
proof (induction dt arbitrary: n n')
  case (Logic x1 x2)
  then show ?case
    by simp
next
  fix wire :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) option"
    and dt1 :: "('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree"
    and dt2 :: "('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree"
    and n :: 'a
    and n' :: 'a
  assume ind1: "\<And>n n'. nodes_count (dt1::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree) -+- tln_class.to_nat n < CARD('a) \<Longrightarrow> (n', p) \<in> used_ports n chns dt1 \<Longrightarrow> n' < fst (dataflow_tree_to_operator_aux n chns dt1)"
    and ind2: "\<And>n n'. nodes_count (dt2::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree) -+- tln_class.to_nat n < CARD('a) \<Longrightarrow> (n', p) \<in> used_ports n chns dt2 \<Longrightarrow> n' < fst (dataflow_tree_to_operator_aux n chns dt2)"
    and card: "nodes_count (Comp wire (dt1::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree) dt2) -+- tln_class.to_nat n < CARD('a)"
    and port: "(n', p) \<in> used_ports n chns (Comp wire (dt1::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree) dt2)"
  have card1: "nodes_count dt1 -+- tln_class.to_nat n < CARD('a)"
    using card
    by simp
  have card2: "nodes_count dt2 -+- tln_class.to_nat (fst (dataflow_tree_to_operator_aux n chns dt1)) < CARD('a)"
    using card 
    by(simp add: fst_dtoa_def card_leq_nodes_count_help)
  consider "\<exists>x a b. (n', p) = projr x \<and> x \<in> outputs (snd (dataflow_tree_to_operator_aux n chns dt1)) \<and> wire (n' - n, p) = Some (a, b) \<and> is_Inr x" |
           "\<exists>x a b. (n', p) = projr x \<and> x \<in> inputs (snd (dataflow_tree_to_operator_aux (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2)) \<and> wire (a, b) = Some (- fst (dataflow_tree_to_operator_aux n chns dt1) + n', p) \<and> is_Inr x" |
           "(n', p) \<in> used_ports n chns dt1" |
           "(n', p) \<in> used_ports (fst (dataflow_tree_to_operator_aux n chns dt1)) chns dt2"
    using port
    by fastforce
  then show "n' < fst (dataflow_tree_to_operator_aux n chns (Comp wire (dt1::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree) dt2))"
  proof(cases)
    case 1
    show ?thesis
      using 1 
      apply(auto split: prod.splits)
      subgoal for x x1 x2 x1a a b x2a
        apply(cases x; simp)
        using dtoa_outputs[of dt1 n n' p chns] card2[simplified]
        apply simp
        apply(drule arg_cong[where f = fst])+
        apply(simp add: fst_dtoa_def)
        apply auto
        by (metis add.commute add_lessD1 card1 nodes_count_convert ord_add order_less_le_trans)
      done
  next
    case 2
    then show ?thesis
      apply(auto split: prod.splits)
      subgoal for x x1 x2 x1a a b x2a
        apply(cases x; simp)
        using dtoa_inputs[of dt2 "fst (dataflow_tree_to_operator_aux n chns dt1)" n' p chns,OF card2[simplified]]
        by simp
      done
  next
    case 3
    show ?thesis
      using ind1[OF card1 3]
      apply(auto split: prod.splits simp add: fst_dtoa_def dest!: arg_cong[where f = fst])
      using card
      by (smt (verit) add.commute add_lessD1 int_ops(5) nat_int_comparison(2,3) nodes_count.simps(2) nodes_count_convert ord_add ord_add_leq order_less_le_trans)
  next
    case 4
    show ?thesis
      using ind2[OF card2 4]
      by(auto split: prod.splits)
  qed
qed

(*
primrec good_dt :: "('a \<times> 'b \<Rightarrow> ('a \<times> 'b) option) \<Rightarrow> ('a, 'b, 'c + 'd, 'e, 'f) dataflow_tree \<Rightarrow> bool" where
"good_dt wire (Comp wire' dt1 dt2) = ((\<forall> x. wire x = None \<or> wire' x = None) \<and> (good_dt (wire ++ wire') dt1 \<and> good_dt (wire ++ wire') dt2))"

maybe add this  (\<forall>p n' p'. wire p = Some (n', p') \<longrightarrow> tln_class.to_nat(fst (dataflow_tree_to_operator_aux n (\<lambda>_. []) dt1)) + tln_class.to_nat(n') < CARD('a))
*)
primrec good_dt where
"good_dt _ (Logic op _) = (\<forall> io op'. step io op op' \<longrightarrow> ((\<exists> p x. io = Inp (Some p) (Inr x))) \<or> (\<exists> x. io = Inp None (Inl x)) \<or> (\<exists> p x. io = Out (Some p) (Inr x)) \<or> (\<exists> x. io = Out None (Inl x)))" |
"good_dt (n :: 'a :: {tln,minus,one,plus,uminus}) (Comp wire dt1 dt2) = 
  ((\<forall> n' p n'' p'. wire (n' - n,p) = Some (n'', p') \<longrightarrow> ((n',p) \<notin> used_ports' n dt1 \<and> n \<le> n' \<and> n' < nodes_count dt1 + n \<and> n'' < nodes_count dt2)) \<and>
  (\<forall> n'' n' p p'. wire (n'' - n, p') = Some (- fst (dataflow_tree_to_operator_aux n (\<lambda>_. []) dt1) + n',p) \<longrightarrow> (n',p) \<notin> used_ports' (fst (dataflow_tree_to_operator_aux n (\<lambda>_ . []) dt1)) dt2 \<and> nodes_count dt1 + n \<le> n' \<and> n' < nodes_count (Comp wire dt1 dt2) + n \<and> (\<forall> chns. Inr (n', p) \<notin> outputs (snd (dataflow_tree_to_operator_aux (fst (dataflow_tree_to_operator_aux n (\<lambda>_. []) dt1)) chns dt2)))) \<and> 
    good_dt n dt1 \<and> good_dt (fst (dataflow_tree_to_operator_aux n (\<lambda>_. []) dt1)) dt2)"

coinductive good_dt' where                        
  good_dt'I[intro]: "good_dt n dt \<Longrightarrow> (\<And> io chns chns' dt'. step_dt io n chns dt chns' dt' \<Longrightarrow> good_dt' n dt') \<Longrightarrow> good_dt' n dt"

lemma 
  "good_dt' n (Comp wire dt1 dt2) \<Longrightarrow> good_dt' n dt1"
proof(coinduction arbitrary: dt1)
  case good_dt'
  then show ?case
    apply auto
    subgoal
      apply(subst (asm) good_dt'.simps)
      by auto
    subgoal for io chns chns' dt'
      apply(subgoal_tac "\<exists> io'. step_dt io' n chns (Comp wire dt1 dt2) chns' (Comp wire dt' dt2)")
       defer
      subgoal premises prems
        using prems(2) apply -
        apply(rule exI)
        sorry
      subgoal
      apply(subst (asm) good_dt'.simps)
      by auto

    qed

end
proof(rule good_dt'.coinduct[of "\<lambda> n dt1. \<exists> dt2. good_dt' n (Comp wire dt1 dt2)"])
  case good_dt'
  then show ?case
    apply auto
    sorry
qed

end
  have "good_dt' n (Comp wire dt1 dt2) \<longrightarrow> good_dt' n dt1"
    apply(coinduction)
  apply(subst (asm) good_dt'.simps)
  apply simp

end
lemma used_ports'_less: "CARD('n) > nodes_count dt + tln_class.to_nat (n :: 'n :: {one,semigroup_add,zero,ord,equal,tln,preorder,group_add,ab_semigroup_add}) \<Longrightarrow> 
        good_dt n dt \<Longrightarrow> (n',p) \<in> used_ports' n dt \<Longrightarrow> n' < nodes_count dt + n"
  apply(induction dt arbitrary: n n')
  subgoal for op su n n'
    by simp
  subgoal premises prems for wire dt1 dt2 n n'
    using prems(3,4,5)
    apply auto
    subgoal for a b
      using nodes_count_less_help
      by blast
    subgoal for a b
      by blast
    subgoal
      by(auto intro: nodes_count_less_help dest!: prems(1)[rotated 2])
    subgoal
      by(auto dest!: prems(2)[rotated 2] simp add: fst_dtoa_def card_leq_nodes_count_help add.commute add.left_commute)
    done
  done

lemma used_ports'_gt: "CARD('n) > nodes_count dt + tln_class.to_nat (n :: 'n :: {one,semigroup_add,zero,ord,equal,tln,preorder,group_add,ab_semigroup_add}) \<Longrightarrow> 
        good_dt n dt \<Longrightarrow> (n',p) \<in> used_ports' n dt \<Longrightarrow> n \<le> n'"
  apply(induction dt arbitrary: n n')
  subgoal for op su n n'
    by simp
  subgoal premises prems for wire dt1 dt2 n n'
    using prems(3,4,5)
    apply auto
    subgoal for n'' p'
      by (meson order_le_less_trans order_less_imp_le order_less_le_trans)
    subgoal
      by(auto intro: nodes_count_less_help dest!: prems(1)[rotated 2])
    subgoal
      apply(auto dest!: prems(2)[rotated 2] simp add: fst_dtoa_def card_leq_nodes_count_help add.commute add.left_commute)
      by (metis (no_types, lifting) add.assoc add_diff_cancel_left' add_diff_cancel_right' dual_order.trans
          less_imp_diff_less nodes_count_convert ord_add)
    done
  done

lemma good_dt_Inr_output: "good_dt (n :: 'a :: {tln,minus,minus,one,semigroup_add,equal,ord,uminus}) dt \<Longrightarrow> step (Out (Inr p) x) (snd (dataflow_tree_to_operator_aux n chns dt)) op \<Longrightarrow> is_Inr x"
proof (induction dt arbitrary: n op)
  fix x1 :: "('b option, 'b option, 'c + 'd \<times> 'e) op"
    and x2 :: "'b \<Rightarrow> 'b \<Rightarrow> 'f buf"
    and n :: 'a
    and op :: "('a + 'a \<times> 'b, 'a + 'a \<times> 'b, 'c + 'd \<times> 'e) op"
  assume good_dt: "good_dt n (Logic x1 x2::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree)"
    and step: "step (Out (Inr p) x) (snd (dataflow_tree_to_operator_aux n chns (Logic x1 (x2::'b \<Rightarrow> 'b \<Rightarrow> 'f buf)))) op"
  show "is_Inr x"
    using step good_dt
    by(auto dest!: step_map_op_inv map_IO_elim )
next
  fix x1 :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) option"
    and dt1 :: "('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree"
    and dt2 :: "('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree"
    and n :: 'a
    and op :: "('a + 'a \<times> 'b, 'a + 'a \<times> 'b, 'c + 'd \<times> 'e) op"
    and wire :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) option"
  assume ind1: "\<And>n op. good_dt n (dt1::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree) \<Longrightarrow> step (Out (Inr p) x) (snd (dataflow_tree_to_operator_aux n chns dt1)) op \<Longrightarrow> is_Inr x"
    and ind2: "\<And>n op. good_dt n (dt2::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree) \<Longrightarrow> step (Out (Inr p) x) (snd (dataflow_tree_to_operator_aux n chns dt2)) op \<Longrightarrow> is_Inr x"
    and good_dt: "good_dt n (Comp x1 (dt1::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree) dt2)"
    and step: "step (Out (Inr p) x) (snd (dataflow_tree_to_operator_aux n chns (Comp x1 (dt1::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree) dt2))) op"
  show "is_Inr x"
    using step
    apply(auto dest!: step_map_op_inv map_IO_elim elim!: step_comp_op_elim split: prod.splits)
    subgoal for n1 op1 n2 op2 op'
      apply(rule ind2[of n1 op'])
      subgoal
        apply(drule arg_cong[where f = fst])+
        using good_dt
        apply simp
        by(simp add: fst_dtoa_def)
      by simp
    subgoal for n1 op1 n2 op2 op'
      apply(rule ind1[of n op'])
      subgoal
        apply(drule arg_cong[where f = fst])+
        using good_dt
        by(simp add: fst_dtoa_def)
      by simp
    done
qed

lemma good_dt_Inr_input: "good_dt (n :: 'a :: {tln,minus,minus,one,semigroup_add,equal,ord,uminus}) dt \<Longrightarrow> step (Inp (Inr p) x) (snd (dataflow_tree_to_operator_aux n chns dt)) op \<Longrightarrow> is_Inr x"
proof (induction dt arbitrary: n op)
  fix x1 :: "('b option, 'b option, 'c + 'd \<times> 'e) op"
    and x2 :: "'b \<Rightarrow> 'b \<Rightarrow> 'f buf"
    and n :: 'a
    and op :: "('a + 'a \<times> 'b, 'a + 'a \<times> 'b, 'c + 'd \<times> 'e) op"
  assume good_dt: "good_dt n (Logic x1 x2::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree)"
    and step: "step (Inp (Inr p) x) (snd (dataflow_tree_to_operator_aux n chns (Logic x1 (x2::'b \<Rightarrow> 'b \<Rightarrow> 'f buf)))) op"
  show "is_Inr x"
    using step good_dt
    by(auto dest!: step_map_op_inv map_IO_elim )
next
  fix x1 :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) option"
    and dt1 :: "('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree"
    and dt2 :: "('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree"
    and n :: 'a
    and op :: "('a + 'a \<times> 'b, 'a + 'a \<times> 'b, 'c + 'd \<times> 'e) op"
    and wire :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) option"
  assume ind1: "\<And>n op. good_dt n (dt1::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree) \<Longrightarrow> step (Inp (Inr p) x) (snd (dataflow_tree_to_operator_aux n chns dt1)) op \<Longrightarrow> is_Inr x"
    and ind2: "\<And>n op. good_dt n (dt2::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree) \<Longrightarrow> step (Inp (Inr p) x) (snd (dataflow_tree_to_operator_aux n chns dt2)) op \<Longrightarrow> is_Inr x"
    and good_dt: "good_dt n (Comp x1 (dt1::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree) dt2)"
    and step: "step (Inp (Inr p) x) (snd (dataflow_tree_to_operator_aux n chns (Comp x1 (dt1::('a, 'b, 'c, 'd \<times> 'e, 'f) dataflow_tree) dt2))) op"
  show "is_Inr x"
    using step
    apply(auto dest!: step_map_op_inv map_IO_elim elim!: step_comp_op_elim split: prod.splits)
    subgoal for n1 op1 n2 op2 op'
      apply(rule ind1[of  n op'])
      subgoal
        apply(drule arg_cong[where f = fst])+
        using good_dt
        by(simp add: fst_dtoa_def)
      by simp
    subgoal for n1 op1 n2 op2 op'
      apply(rule ind2[of n1 op'])
      subgoal
        apply(drule arg_cong[where f = fst])+
        using good_dt
        by(simp add: fst_dtoa_def)
      by simp
    done
qed

lemma step_dt_eq_nodes_count:  "step_dt io n chns dt chns' dt' \<Longrightarrow> nodes_count dt = nodes_count dt'"
  apply(induction dt arbitrary: io n dt' chns chns')
  subgoal for op su io n dt' chns chns'
    by(drule step_dt.cases; simp)
  subgoal for wire dt1 dt2 io n dt' chns chns'
    apply(drule step_dt.cases; simp)
    by auto
  done

lemma step_dt_used_port_inv: "step_dt io (n :: 'n :: {minus,one,plus,uminus,semigroup_add,equal,ord}) chns dt chns' dt' \<Longrightarrow> used_ports' n' dt = used_ports' n' dt'"
  apply(induction dt arbitrary: n n' dt' chns chns' io)
  subgoal for op su n n' dt' chns chns' io
    apply(subst (asm) step_dt.simps)
    by auto
  subgoal premises prems for wire dt1 dt2 n n' dt' chns chns' io
    using prems(3)
    apply(subst (asm) step_dt.simps)
    apply(elim disjE exE conjE; simp; hypsubst_thin)
    by(auto dest: prems(1) prems(2) simp add: fst_dtoa_def step_dt_eq_nodes_count)
  done

lemma step_dt_Inp_ord: " nodes_count dt -+- tln_class.to_nat n < CARD('n) \<Longrightarrow> 
      step_dt (Inp (Inr (n', p)) x) (n :: 'n :: {minus,one,plus,uminus,group_add,equal,ord,tln,preorder,ab_semigroup_add}) chns dt chns' dt' \<Longrightarrow> 
      n \<le> n' \<and> n' < nodes_count dt + n"
  apply(induction dt arbitrary: n chns chns' dt')
  subgoal for op su n chns chns' dt'
    apply(subst (asm) step_dt.simps)
    apply(auto dest!: map_IO_elim elim!: step_map_op_elim split: option.splits)
    by (metis Groups.add_ac(2) less_numeral_extra(1) one_def ord_add_le plus_1_eq_Suc)
  subgoal premises prems for wire dt1 dt2 n chns chns' dt'
    using prems(3,4)
    apply(subst (asm) step_dt.simps)
    apply auto
    subgoal for dt2'
      apply(drule prems(2)[rotated])
      subgoal
        by (metis fst_dtoa_def card_leq_nodes_count_help)
      apply(simp add: fst_dtoa_def)
      apply(subgoal_tac "n < n + nodes_count dt1")
      subgoal
        by (meson dual_order.trans order_less_imp_le)
      by(rule ord_add_le_nodes; simp)
    subgoal for dt2'
      apply(drule prems(2)[rotated])
      subgoal
        by (metis fst_dtoa_def card_leq_nodes_count_help)
      by (simp add: add.commute add.left_commute fst_dtoa_def)
    subgoal for dt1'
      apply(drule prems(1)[rotated])
      by(simp add: fst_dtoa_def)+
    subgoal for dt1'
      apply(drule prems(1)[rotated], simp)
      apply(subgoal_tac "n + nodes_count dt1 < n + nodes_count dt1 + nodes_count dt2")
      subgoal
        by (metis nodes_count_less_help)
      apply(rule tln_class.ord_add_le_nodes)
      using card_leq_nodes_count_help by fastforce
    done
  done

lemma step_dt_Out_ord: " nodes_count dt -+- tln_class.to_nat n < CARD('n) \<Longrightarrow> 
      step_dt (Out (Inr (n', p)) x) (n :: 'n :: {minus,one,plus,uminus,group_add,equal,ord,tln,preorder,ab_semigroup_add}) chns dt chns' dt' \<Longrightarrow> 
      n \<le> n' \<and> n' < nodes_count dt + n"
  apply(induction dt arbitrary: n chns chns' dt')
  subgoal for op su n chns chns' dt'
    apply(subst (asm) step_dt.simps)
    apply(auto dest!: map_IO_elim elim!: step_map_op_elim split: option.splits)
    by (metis Groups.add_ac(2) less_numeral_extra(1) one_def ord_add_le plus_1_eq_Suc)
  subgoal premises prems for wire dt1 dt2 n chns chns' dt'
    using prems(3,4)
    apply(subst (asm) step_dt.simps)
    apply auto
    subgoal for dt1'
      apply(drule prems(1)[rotated])
      by(simp add: fst_dtoa_def)+
    subgoal for dt1'
      apply(drule prems(1)[rotated], simp)
      apply(subgoal_tac "n + nodes_count dt1 < n + nodes_count dt1 + nodes_count dt2")
      subgoal
        by (metis nodes_count_less_help)
      apply(rule tln_class.ord_add_le_nodes)
      using card_leq_nodes_count_help by fastforce
    subgoal for dt2'
      apply(drule prems(2)[rotated])
      subgoal
        by (metis fst_dtoa_def card_leq_nodes_count_help)
      apply(simp add: fst_dtoa_def)
      apply(subgoal_tac "n < n + nodes_count dt1")
      subgoal
        by (meson dual_order.trans order_less_imp_le)
      by(rule ord_add_le_nodes; simp)
    subgoal for dt2'
      apply(drule prems(2)[rotated])
      subgoal
        by (metis fst_dtoa_def card_leq_nodes_count_help)
      by (simp add: add.commute add.left_commute fst_dtoa_def)
    done
  done

lemma step_dt_chns_inv: " nodes_count dt -+- tln_class.to_nat n < CARD('n) \<Longrightarrow> good_dt n dt \<Longrightarrow>
      step_dt io (n :: 'n :: {minus,one,plus,uminus,group_add,equal,ord,tln,preorder,ab_semigroup_add}) chns dt chns' dt' \<Longrightarrow> 
      \<forall>n' p. n' < n \<or> n' \<ge> nodes_count dt + n \<longrightarrow> chns (n',p) = chns'(n',p)"
  apply(induction dt arbitrary: n dt' chns chns' io)
  subgoal for op su n dt' chns chns' io
    apply(subst (asm) step_dt.simps)
    by auto
  subgoal premises prems for wire dt1 dt2 n dt' chns chns' io
    using prems(3,4,5)
    apply(subst (asm) step_dt.simps)
    apply(elim disjE exE conjE; simp; hypsubst_thin; frule step_dt_eq_nodes_count[symmetric])
    subgoal for n' chns'' dt1a chns''' dt1' dt2a
      apply(drule prems(1)[rotated 2]; simp?)
      apply(drule nodes_count_less_help')
      by (meson less_imp_le order_trans_rules(22))
    subgoal for n' chns'' dt1a chns''' dt1' dt2a
      apply(drule prems(2)[rotated 2]; (simp add: fst_dtoa_def)?)
      subgoal
        by(auto dest!: card_leq_nodes_count_help simp add: fst_dtoa_def)
      apply safe
      subgoal for n'' p
        apply(subgoal_tac "n < n + nodes_count dt1")
        subgoal
          by (metis (no_types, lifting) fst_dtoa_def order_less_trans ord_add_le_nodes)
        by(simp add: ord_add_le_nodes)
      subgoal for n'' p
        by (simp add: add.commute add.left_commute fst_dtoa_def)
      done
    subgoal for n1 chns1 dt1a chns1' dt1' dt2' p p' n' n'' x
      apply(drule step_dt_Inp_ord[rotated])
      subgoal
        by (metis fst_dtoa_def card_leq_nodes_count_help)
      apply safe
      subgoal for n''' p'
        apply(subgoal_tac "n' \<noteq> n'''")
        subgoal
          by(auto simp add: BTL_def)
        apply(auto simp add: fst_dtoa_def)
        apply(subgoal_tac "n < n + nodes_count dt1")
         defer
        subgoal
          apply(rule tln_class.ord_add_le_nodes)
          using card_leq_nodes_count_help by fastforce
        apply(subgoal_tac "n + nodes_count dt1 < n + nodes_count dt1 + nodes_count dt2")
         defer
        subgoal
          apply(rule tln_class.ord_add_le_nodes)
          using card_leq_nodes_count_help by fastforce
        by (metis basic_trans_rules(20,22))
      subgoal for n''' p'
        apply(subgoal_tac "n' \<noteq> n'''")
        subgoal
          by(auto simp add: BTL_def)
        apply(auto simp add: fst_dtoa_def)
        by (metis add.commute add.left_commute basic_trans_rules(22) less_irrefl)
      done
    subgoal for n1 chns1 dt1a chns1' dt1' dt2' p p' n' n'' x
      apply(drule step_dt_Out_ord[rotated], simp)
      apply safe
      subgoal for n''' p''
        apply(simp add: fst_dtoa_def)
        apply(subgoal_tac "n'' + (n + nodes_count dt1) \<noteq> n'''")
        subgoal
          by(auto simp add: BENQ_def)
        apply(auto simp add: fst_dtoa_def)
        by (smt (verit) add.left_commute add_0_right add_eq_0_iff2 order.strict_trans1
            order_less_asym)
      subgoal for n''' p''
        apply(simp add: fst_dtoa_def)
        apply(subgoal_tac "n'' + (n + nodes_count dt1) \<noteq> n'''")
        subgoal
          by(auto simp add: BENQ_def)
        apply(auto simp add: fst_dtoa_def)
        by (smt (verit) add.left_commute add_0_right add_eq_0_iff2 order.strict_trans1
            order_less_asym)
      done
    done
  done

(*These are almost copies of dtoa_inputs_le*)
lemma inputs_dtoa_le: "nodes_count dt -+- tln_class.to_nat n < CARD('n) \<Longrightarrow>
      n' < (n :: 'n :: {minus,one,plus,uminus,group_add,equal,ord,tln,preorder,ab_semigroup_add}) \<Longrightarrow> 
      Inr (n', p) \<in> inputs (snd (dataflow_tree_to_operator_aux n chns dt)) \<Longrightarrow> False"
  apply(induction dt arbitrary: n chns)
  subgoal for op' su n chns
    by(auto simp add: op.set_map split: option.splits)
  subgoal premises prems for wire dt1 dt2 n chns
    using prems(5)
    apply(auto simp add: op.set_map split: prod.splits)
    subgoal premises prems2 for n1 p1 n2 p2
      using prems(1)[of n chns, simplified prems2(1) snd_conv] prems(3)[simplified] prems(4) prems2(3)
      by simp
    subgoal premises prems2 for n1 p1 n2 p2
      using prems(2)[of n1 chns, simplified prems2(2) snd_conv] prems(3,4) prems2(1,3)
      by (meson dtoa_inputs_leq less_le_not_le prems(5))
    done
  done

lemma inputs_dtoa_leq: "nodes_count dt -+- tln_class.to_nat n < CARD('n) \<Longrightarrow>
      n' \<ge> nodes_count dt + (n :: 'n :: {minus,one,plus,uminus,group_add,equal,ord,tln,preorder,ab_semigroup_add}) \<Longrightarrow> 
      Inr (n', p) \<in> inputs (snd (dataflow_tree_to_operator_aux n chns dt)) \<Longrightarrow> False"
  apply(induction dt arbitrary: n chns)
  subgoal for op' su n chns
    apply(auto simp add: op.set_map split: option.splits)
    by (metis Suc_eq_plus1 add.commute less_le_not_le one_def ord_add_le semiring_norm(135))
  subgoal premises prems for wire dt1 dt2 n chns
    using prems(5)
    apply(auto simp add: op.set_map split: prod.splits)
    subgoal premises prems2 for n1 p1 n2 p2
      using prems(1)[of n chns, simplified prems2(1) snd_conv] prems(3)[simplified] prems(4) prems2(3)
      by (meson dtoa_inputs_le dual_order.strict_iff_not prems(3,5))
    subgoal premises prems2 for n1 p1 n2 p2
      using prems(2)[of n1 chns, simplified prems2(2) snd_conv] prems(3,4) prems2(1,3)
      by (metis add.commute dtoa_inputs fst_dtoa_def less_le_not_le prems(5))
    done
  done



lemma step_dt_inputs_chns_inv: "nodes_count dt -+- tln_class.to_nat n < CARD('n) \<Longrightarrow> step_dt Tau n chns dt chns' dt' \<Longrightarrow> good_dt n dt \<Longrightarrow>
    Inr ((n' :: 'n :: {minus,one,plus,uminus,group_add,equal,ord,tln,preorder,ab_semigroup_add,linorder}), p) \<in> inputs (snd (dataflow_tree_to_operator_aux n chns' dt')) \<Longrightarrow> 
    chns' (n', p) = chns (n', p)"
  apply(induction dt arbitrary: n n' chns chns' dt')
  subgoal for op' su n chns chns' dt'
    apply(subst (asm) step_dt.simps)
    by simp
  subgoal premises prems for wire dt1 dt2 n n' chns chns' dt'
    using prems(4)
    apply(subst (asm) step_dt.simps)
    apply auto
    subgoal for dt''
      apply(cases "n' \<ge> n \<and> nodes_count dt1 + n > n'")
       defer
      subgoal
        apply(frule step_dt_chns_inv[rotated 2])
        using prems(3,5) apply simp
        using prems(3,5) apply simp
        apply(erule allE[where x = n'])
        apply(erule allE[where x = p])
        by fastforce
      apply(rule prems(1); simp?)
      using prems(3) apply simp
      using prems(5) apply simp
      using prems(6)
      apply(auto simp add: op.set_map split: prod.splits)
      apply(auto simp add: ran_def split: sum.splits option.splits)
      subgoal for n1 p1 n2 p2
        using inputs_dtoa_le[of dt2 n1 n' p chns'] prems(3) fst_dtoa_def prems(5)
        by (smt (verit) add.assoc add.commute add.left_commute add_lessD1 card_leq_nodes_count_help fst_conv inputs_dtoa_le
            nodes_count.simps(2) ord_add_le_nodes snd_conv step_dt_eq_nodes_count)
      done
    subgoal for dt''
      apply(cases "n' \<ge> nodes_count dt1 + n \<and> nodes_count dt1 + nodes_count dt2 + n > n'")
       defer
      subgoal
        apply(frule step_dt_chns_inv[rotated 2])
        using prems(3,5) apply (simp add: fst_dtoa_def card_leq_nodes_count_help)
        using prems(3,5) apply (simp add: fst_dtoa_def)
        apply(erule allE[where x = n'])
        apply(erule allE[where x = p])
        apply(simp add: fst_dtoa_def)
        by (metis add.commute add.left_commute linorder_le_less_linear)
      apply(rule prems(2); simp?)
      using prems(3,5) apply (simp add: fst_dtoa_def card_leq_nodes_count_help)
      using prems(3,5) apply (simp add: fst_dtoa_def)
      using prems(6)
      apply(auto simp add: op.set_map split: prod.splits)
      apply(auto simp add: ran_def split: sum.splits option.splits)
      subgoal for n1 p1 n2 p2
        using inputs_dtoa_leq[of dt2 n1 n' p chns'] prems(3) fst_dtoa_def prems(5)
        by (smt (verit) dataflow_topology_from_tree.followed_by_summary ex_least_nat_le inputs_dtoa_leq le_antisym
            le_simps(1) linorder_neqE_nat nat_arith.add2 nodes_count.simps(2) snd_conv trans_less_add2)
      using fst_dtoa_def
      by (metis fst_conv snd_conv)
    subgoal for dt2' pa p' n'' n''' a b
      apply(cases "n'' = n' \<and> pa = p"; simp?)
      defer
      subgoal
        by(auto simp add: BTL_def)
      using prems(6)
      apply(auto simp add: op.set_map ran_def split: sum.splits option.splits prod.splits)
      subgoal for n1 p1 n2 p2
        using prems(5)
        apply auto
        apply(erule allE[where x = n'''])
        apply(erule allE[where x = n'''])
        apply(erule allE[where x = n'])
        apply(erule allE[where x = pa])
        apply(erule allE[where x = pa])
        apply(erule impE)
        subgoal
          unfolding fst_dtoa_def
          by (metis add.commute add_uminus_conv_diff)
        using inputs_dtoa_leq[of dt1 n n' p "(BTL (n', pa) chns)"] prems(3) fst_dtoa_def
        by simp
      subgoal for n1 p1 n2 p2
        apply(erule allE[where x = "n'''"])
        apply(erule allE[where x = p'])
        apply(erule allE[where x = "n' - fst (dataflow_tree_to_operator_aux n chns dt1)"])
        apply(erule allE[where x = pa])
        apply(auto simp add: fst_dtoa_def)
        by (metis add.commute diff_add_cancel fst_dtoa_def prod.sel(1))
      done
    subgoal for dt1' pa p' n'' n''' a b
      apply(simp add: fst_dtoa_def)
      apply(cases "n''' + (n + nodes_count dt1) = n' \<and> p' = p"; simp?)
      defer
      subgoal
        by(auto simp add: BENQ_def)
      using prems(6)
      apply(auto simp add: op.set_map ran_def split: sum.splits option.splits prod.splits)
      subgoal for n1 p1 n2 p2
        apply(subgoal_tac "n''' + (n + nodes_count dt1) < nodes_count dt1 + n")
        defer
        subgoal
          using dtoa_inputs_le[of dt1' n "n''' + (n + nodes_count dt1)" p "\<lambda>_ . []"] fst_dtoa_def prems(3)
          apply -
          apply(auto simp add: fst_dtoa_def step_dt_eq_nodes_count[symmetric])
          by (smt (verit, best) Groups.add_ac(2) Nat.add_diff_assoc2 dataflow_topology_from_tree.le_plus(2) diff_add_inverse2
              dtoa_inputs fst_dtoa_def less_imp_diff_less prod.sel(2) step_dt_eq_nodes_count)
        apply(subgoal_tac "n + nodes_count dt1 \<le> n + nodes_count dt1 + n'''")
         defer
        subgoal
          apply(rule tln_class.ord_add)
          using prems(3,5)
          apply auto
          apply(erule allE[where x = n''])
          apply(erule allE[where x = pa])
          apply(erule allE[where x = n'''])
          apply(erule allE[where x = n'''])
          apply(erule impE)
           apply auto[1]
          by (smt (verit) Groups.add_ac(2) add_diff_inverse_nat card_leq_nodes_count_help le_antisym less_or_eq_imp_le
              nat_add_left_cancel_le nat_neq_iff nodes_count_convert to_nat_le trans_le_add2)
        by (simp add: add.commute)
      subgoal for n1 p1 n2 p2
        apply(erule allE[where x = "n''"])
        apply(erule allE[where x = pa])
        apply(erule allE[where x = "n'''"])
        apply(erule allE[where x = p])
        by (metis add.commute fst_dtoa_def prod.sel(1) step_dt_eq_nodes_count)
      done
    done
  done


lemma step_dtoa_elim: "step io (snd (dataflow_tree_to_operator_aux (n :: 'a :: {minus,one,semigroup_add,zero,ord,equal,tln,preorder,group_add,ab_semigroup_add,linorder}) chns (dt :: (_,_,_,_, 'g) dataflow_tree))) op' \<Longrightarrow>
      nodes_count dt -+- tln_class.to_nat n < CARD('a) \<Longrightarrow>
      good_dt n dt \<Longrightarrow>
      \<exists> (dt' :: (_,_,_,_, 'g) dataflow_tree) chns'. step_dt io n chns dt chns' dt' \<and>
       dataflow_tree_to_operator_aux n chns' dt' = (fst (dataflow_tree_to_operator_aux n chns dt), op')"
proof (induction dt arbitrary: io n chns op')
  case (Logic op su)
  assume step: "step io (snd (dataflow_tree_to_operator_aux n chns (Logic op (su::'b \<Rightarrow> 'b \<Rightarrow> 'g buf)))) op'"
    and dt_io: "nodes_count (Logic op su) -+- tln_class.to_nat n < CARD('a)"
  show ?case
    using step apply -
    apply simp
    apply(elim step_map_op_elim conjE)
    by fastforce
next
  fix wire :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) option"
    and dt1 :: "('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree"
    and dt2 :: "('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree"
    and io :: "('a + 'a \<times> 'b, 'a + 'a \<times> 'b, 'c + 'd \<times> 'e) IO"
    and n :: 'a
    and chns :: "'a \<times> 'b \<Rightarrow> ('d \<times> 'e) buf"
    and op' :: "('a + 'a \<times> 'b, 'a + 'a \<times> 'b, 'c + 'd \<times> 'e) op"
  assume ind1:"\<And>io n chns op'. step io (snd (dataflow_tree_to_operator_aux n chns (dt1::('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree))) op' \<Longrightarrow> nodes_count dt1 -+- tln_class.to_nat n < CARD('a) \<Longrightarrow> good_dt n dt1 \<Longrightarrow> \<exists>dt' chns'. step_dt io n chns dt1 chns' dt' \<and> dataflow_tree_to_operator_aux n chns' dt' = (fst (dataflow_tree_to_operator_aux n chns dt1), op')"
    and ind2: "\<And>io n chns op'. step io (snd (dataflow_tree_to_operator_aux n chns (dt2::('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree))) op' \<Longrightarrow> nodes_count dt2 -+- tln_class.to_nat n < CARD('a) \<Longrightarrow> good_dt n dt2 \<Longrightarrow> \<exists>dt' chns'. step_dt io n chns dt2 chns' dt' \<and> dataflow_tree_to_operator_aux n chns' dt' = (fst (dataflow_tree_to_operator_aux n chns dt2), op')"
    and step: "step io (snd (dataflow_tree_to_operator_aux n chns (Comp wire (dt1::('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree) dt2))) op'"
    and card: "nodes_count (Comp wire (dt1::('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree) dt2) -+- tln_class.to_nat n < CARD('a)"
    and good_dt: "good_dt n (Comp wire dt1 dt2)"
  obtain n1 op1 where dtoa1: "dataflow_tree_to_operator_aux n chns dt1 = (n1, op1)"
    by force
  have n1_def: "n1 = n + nodes_count dt1"
    using dtoa1 fst_dtoa_def[of n chns dt1]
    by auto
  obtain n2 op2 where dtoa2: "\<And> chns. dataflow_tree_to_operator_aux n1 chns dt2 = (n2 chns, op2 chns)"
    apply atomize_elim
    apply(rule exI[where x = "\<lambda> chns. fst (dataflow_tree_to_operator_aux n1 chns dt2)"])
    apply(rule exI[where x = "\<lambda> chns. snd (dataflow_tree_to_operator_aux n1 chns dt2)"])
    by force
  have good_dt1: "good_dt n dt1"
    using good_dt
    by simp
  have good_dt2: "good_dt n1 dt2"
    using good_dt dtoa1[THEN arg_cong[where f = fst], symmetric]
    by(simp add: fst_dtoa_def)
  have card1': "nodes_count dt1 < CARD('a)"
    using card
    by simp
  have card1: "nodes_count dt1 -+- tln_class.to_nat n < CARD('a)"
    using card
    by simp
  have card2: "nodes_count dt2 -+- tln_class.to_nat n1 < CARD('a)"
    using card
    apply(simp add: dtoa1[symmetric, THEN arg_cong[where f = fst], simplified fst_dtoa_def, simplified])
    apply(rule dual_order.strict_trans2, assumption)
    apply(rule order.trans, rule add_left_mono, rule ord_add_leq)
    by(simp add: nodes_count_convert[OF card1'])
  have BENQ_map: "(\<lambda>x. map Inr (BENQ p x' chns x)) = BENQ p (Inr x') (\<lambda>x. map Inr (chns x))" for p chns x'
    apply(rule ext)
    subgoal for x
      unfolding BENQ_def
      by simp
    done
  show "\<exists>dt' chns'. step_dt io n chns (Comp wire (dt1::('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree) dt2) chns' dt' \<and> dataflow_tree_to_operator_aux n chns' dt' = (fst (dataflow_tree_to_operator_aux n chns (Comp wire dt1 dt2)), op')"
    using step
    apply(simp add: dtoa1 dtoa2)
    apply(elim step_map_op_elim conjE step_comp_op_elim; simp add: eq_commute[of _ op'] eq_commute[of _ io])
    subgoal premises prems for io' op'' p x op1'
      using ind1[of "Inp p x" n chns op1', simplified dtoa1 snd_conv, OF prems(5) card1 good_dt1]
      apply(elim conjE exE)?
      subgoal for dt' chns'
        apply(rule exI[where x = "Comp wire dt' dt2"])
        apply(rule exI[where x = "chns"])
        apply(frule step_dt_same_chns_Inp; simp)
        apply(rule conjI)
        subgoal
          by(cases p; auto)
        by(simp add: dtoa2)
      done
    subgoal premises prems for io' op'' p x op2'
      using ind2[of "Out p x" n1 chns op2', simplified dtoa2[of chns] snd_conv, OF prems(5) card2 good_dt2]
      apply(elim conjE exE)
      apply(frule step_dt_same_chns_Out; simp)
      apply(drule sym[of chns])
      subgoal for dt' chns'
        apply(rule exI[where x = "Comp wire dt1 dt'"])
        apply(rule exI[where x = "chns"])
        by(cases p; auto simp add: dtoa1)
      done
    subgoal premises prems for io' op'' p x op1'
      using ind1[of "Out p x" n chns op1', simplified dtoa1 snd_conv, OF prems(6) card1 good_dt1]
      apply(elim conjE exE)
      apply(frule step_dt_same_chns_Out; simp)
      apply(drule sym[of chns])
      subgoal for dt' chns'
        apply(rule exI[where x = "Comp wire dt' dt2"])
        apply(rule exI[where x = "chns"])
        using prems(5)
        apply(auto simp add: dtoa2 split: sum.splits)
        apply(rule SOutInr)
        apply auto
        done
      done
    subgoal premises prems for io' op'' p x op2'
      using ind2[of "Inp p x" n1 chns op2', simplified dtoa2[of chns] snd_conv, OF prems(6) card2 good_dt2]
      apply(elim conjE exE)
      apply(frule step_dt_same_chns_Inp; simp)
      apply(drule sym[of chns])
      subgoal for dt' chns'
        apply(rule exI[where x = "Comp wire dt1 dt'"])
        apply(rule exI[where x = "chns"])
        using prems(5)
        apply(cases p; auto simp add: dtoa1 ran_def split: sum.splits)
        apply(rule SInpInr)
        apply(rule disjI1)
        apply(simp add: dtoa1)
        apply safe
        subgoal for a b p' n''
          apply(erule allE[where x = n''])
          apply(erule allE[where x = p'])
          apply(auto split: option.splits)
          by(simp add: group_add_class.add_diff_eq ab_semigroup_add_class.add.commute[of n1])
        done
      done
    subgoal premises prems for io' op'' p x op1' q
      using prems(5) prems(6)
      apply(clarsimp split: sum.splits option.splits)
      apply(subgoal_tac "\<exists> x'. x = Inr x'")
      subgoal for a b ba ab
        apply safe
        subgoal for x' x''
          using ind1[of "Out p x" n chns op1', OF prems(6)[simplified dtoa1[symmetric, THEN arg_cong[where f = snd], simplified]] card1 good_dt1]
          apply safe
          apply(frule step_dt_same_chns_Out; simp)
          apply(drule sym[of chns])
          subgoal for dt' chns'
            apply(rule exI[where x = "Comp wire dt' dt2"])
            apply(rule exI[where x = "BENQ (n1 + ab, ba) (x', x'') chns"])
            apply(auto simp add: dtoa1 ran_def split: sum.splits)
            subgoal
              apply(rule STau)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule exI[where x = b])
              apply(rule exI[where x = ba])
              apply(rule exI[where x = a])
              apply(rule exI[where x = ab])
              apply auto
              apply(rule exI[where x = x'])
              apply(rule exI[where x = x''])
              by(auto simp add: dtoa1 ab_semigroup_add_class.add.commute)
            apply(subgoal_tac "dataflow_tree_to_operator_aux n (BENQ (n1 + ab, ba) (x', x'') chns) dt' = dataflow_tree_to_operator_aux n chns dt'")
            subgoal
              apply(subgoal_tac "dataflow_tree_to_operator_aux n1 (BENQ (n1 + ab, ba) (x', x'') chns) dt2 = dataflow_tree_to_operator_aux n1 chns dt2")
              subgoal
                by(simp add: dtoa2 BENQ_map)
              subgoal
                apply(rule dataflow_tree_to_operator_aux_chns_inv'; (simp add: card2)?)
                apply safe
                subgoal for aa bb
                  apply(cases "(aa,bb) = (n1 + ab, ba)")
                  subgoal
                    apply(safe)
                    apply hypsubst_thin
                    apply simp
                    using good_dt
                    apply simp
                    apply safe
                    apply(drule arg_cong[where f = fst])+
                    apply simp
                    apply(erule allE[where x = a])
                    apply(erule allE[where x = a])
                    apply(erule allE[where x = "n1 + ab"])
                    apply(erule allE[where x = ba])+
                    by(auto simp add: fst_dtoa_def n1_def)
                  subgoal
                    by(auto simp add: BENQ_def)
                  done
                done
              done
            subgoal
              apply(subgoal_tac "nodes_count dt' -+- tln_class.to_nat n < CARD('a)")
              subgoal
                apply(rule dataflow_tree_to_operator_aux_chns_inv; simp?)
                apply safe
                apply(frule used_ports_less, assumption)
                apply(drule arg_cong[where f = fst])
                apply(simp add: fst_dtoa_def)
                subgoal for aa bb
                  apply(subgoal_tac "aa < n1 + ab")
                  subgoal
                    by (metis BENQ_diff_access less_imp_not_less prod.inject)
                  apply(rule order.strict_trans2, assumption)
                  apply(rule tln_class.ord_add)
                  using card_leq_nodes_count_help[OF card[simplified]] apply -
                  unfolding n1_def
                  apply(subgoal_tac "ab < nodes_count dt2")
                  defer
                  subgoal
                    using good_dt
                    by auto
                  apply(drule to_nat_le[of ab])
                  by(simp add: tln_class.nodes_count_convert)
                done
              subgoal
                by(simp add: step_dt_eq_nodes_count[symmetric] card1)
              done
            done
          done
        done
      subgoal for n2 p2 p3 n3
        apply(drule good_dt_Inr_output[OF good_dt1, of "(n2, p2)" x chns, simplified dtoa1 snd_conv])
        by(auto simp add: is_Inr_def split: sum.splits)
      done
    subgoal premises prems for io' op'' p x op2'
      using prems(5) prems(6) prems(7) prems(8)
      apply(clarsimp simp add: ran_def split: sum.splits option.splits prod.splits)
      subgoal for a aa b
        apply(cases a; simp)
        using ind2[of "Inp p x" n1 chns op2', simplified dtoa2[of chns] snd_conv, OF prems(6) card2 good_dt2] dtoa1 dtoa2
        apply safe
        subgoal for ab ba dt' chns'
          apply(rule exI[where x = "Comp wire dt1 dt'"])
          apply(rule exI[where x = "BTL (aa, b) chns"])
          apply(rule conjI)
          subgoal
            apply(rule STau)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI1)
            apply(frule step_dt_same_chns_Inp; simp)
            apply(drule sym[of chns])
            apply(erule allE[where x = "ab"]; simp)
            apply(erule allE[where x = "ba"]; simp)
            apply safe
            subgoal for ac bb
            apply(rule exI[where x = b])
            apply(rule exI[where x = ba])
            apply(rule exI[where x = aa])
            apply(rule conjI)
            subgoal
              apply(erule allE[where x = ac])
              apply(erule allE[where x = bb]; simp)
              apply(rule exI[where x = ab]; simp)
              apply auto
              by(simp add: group_add_class.add_diff_eq ab_semigroup_add_class.add.commute[of n1])
            subgoal
              apply(cases x; simp)
              subgoal for x'
                apply(cases x')
                subgoal for x1 x2
                  apply(rule exI[where x = x1])
                  apply(rule exI[where x = x2])
                  by auto
                done
              done
            done
          done
        apply(frule step_dt_same_chns_Inp[symmetric])
        apply simp
        apply hypsubst_thin
        apply(subgoal_tac "dataflow_tree_to_operator_aux n (BTL (aa, b) chns) dt1 = dataflow_tree_to_operator_aux n chns dt1")
         defer
        subgoal
          apply(rule dataflow_tree_to_operator_aux_chns_inv', rule card1)
          apply(erule allE[where x = ab]; simp)
          apply(erule allE[where x = ba]; simp)
          unfolding BTL_def
          apply auto
          apply hypsubst_thin
          subgoal for a
            apply(frule used_ports'_less[rotated 2])
              apply(simp add: card1 good_dt1 n1_def)+
            apply(drule used_ports'_gt[rotated 2])
              apply(rule card1)
             apply(rule good_dt1)
            apply(subgoal_tac "a < nodes_count dt2")
             defer
            subgoal
              using good_dt
              by fastforce
            by (metis add.commute card2 dual_order.strict_iff_not n1_def step_dt_Inp_ord)
          done
        apply(subgoal_tac "dataflow_tree_to_operator_aux n1 (BTL (aa, b) chns) dt' = dataflow_tree_to_operator_aux n1 chns dt'")
         defer
        subgoal
          apply(rule dataflow_tree_to_operator_aux_chns_inv')
          subgoal
            using card2 step_dt_eq_nodes_count
            by metis
          apply(erule allE[where x = ab]; simp)
          apply(erule allE[where x = ba]; simp)
          unfolding BTL_def
          apply auto
          apply hypsubst_thin
          subgoal for a
            using good_dt
          apply simp
            apply safe
            apply(erule allE[where x = ab])
            apply(erule allE[where x = ab])
            apply(erule allE[where x = "fst (dataflow_tree_to_operator_aux n (\<lambda>_. []) dt1) + a"])
            apply(erule allE[where x = b])
            apply(erule allE[where x = b])
            by(simp add: step_dt_used_port_inv fst_dtoa_def n1_def)
          done
        apply simp
        unfolding BTL_def
        by (metis (mono_tags, lifting) fun_upd_def map_tl)
      done
    done
    subgoal premises prems for io' op'' op1'
      using prems(5) ind1[of Tau n chns op1', simplified dtoa1 snd_conv, OF prems(5) card1 good_dt1]
      apply(elim conjE exE)
      subgoal for dt' chns'
        apply(rule exI[where x = "Comp wire dt' dt2"])
        apply(rule exI[where x = "chns'"])
        apply(rule conjI)
        subgoal
          apply(rule STau)
          by(rule disjI1; simp)
        apply auto
        apply(subgoal_tac "dataflow_tree_to_operator_aux n1 chns' dt2 = dataflow_tree_to_operator_aux n1 chns dt2")
         defer
        subgoal
          apply(auto dest!: step_dt_chns_inv[rotated 2] intro!: dataflow_tree_to_operator_aux_chns_eq_larger simp add: card1 card2 good_dt1)
          by (metis n1_def add.commute)
        apply(simp add: dtoa2[of chns])
        apply(rule arg_cong[where f = "map_op _ _"])
        apply(cases "chns = chns'"; simp?)
        apply(rule comp_op_chns_invar)
        apply(auto split: sum.splits)
        subgoal for n' p y
          apply(auto split: option.splits)
          apply(drule step_dt_chns_inv[rotated 2])
          apply(rule card1)
          apply(rule good_dt1)
          apply(erule allE[where x = n'])
          apply(erule allE[where x = p])
          using dtoa_inputs_leq[of dt2 n1 n' p chns', OF card2]
          by (simp add: add.commute n1_def)
        done
      done
    subgoal premises prems for io' op'' op2'
      using prems(5) ind2[of Tau n1 chns op2', simplified dtoa2[of chns] snd_conv, OF prems(5) card2 good_dt2]
      apply(elim conjE exE)
      subgoal for dt' chns'
        apply(rule exI[where x = "Comp wire dt1 dt'"])
        apply(rule exI[where x = "chns'"])
        apply(rule conjI)
        subgoal
          apply(rule STau)
          apply(rule disjI2)
          by(rule disjI1; simp add: dtoa1)
        apply(auto simp add: dtoa2)
        apply(subgoal_tac "dataflow_tree_to_operator_aux n chns' dt1 = dataflow_tree_to_operator_aux n chns dt1"; simp?)
        subgoal premises prems
          using prems
          apply(simp add: dtoa1)
          apply(rule arg_cong[where f = "map_op _ _"])
          apply(cases "chns = chns'"; simp?)
          apply(rule comp_op_chns_invar)
          apply(auto split: sum.splits)
          subgoal for n' p y
            by(rule step_dt_inputs_chns_inv[of dt2 n1 chns chns' dt' _ p]; (simp add: card2 good_dt2)?)
          done
        subgoal
          apply(rule dataflow_tree_to_operator_aux_chns_eq_smaller, rule card1)
          apply(drule step_dt_chns_inv[rotated 2])
          subgoal
            using card
            by(auto intro: card_leq_nodes_count_help simp add: n1_def)
           apply(rule good_dt2)
          by(auto simp add: n1_def add.commute)
        done
      done
    done
qed


lemma step_comp_op_R_Inp':
  "step (Inp p x) op2 op2' \<Longrightarrow> p \<notin> ran wire \<Longrightarrow> buf = buf' \<Longrightarrow> op1 = op1' \<Longrightarrow> io = (Inp (Inr p) x) \<Longrightarrow> step io (comp_op wire buf op1 op2) (comp_op wire buf' op1' op2')"
  using step_comp_op_R by force


lemma step_dtoa_intro: "nodes_count dt -+- tln_class.to_nat n < CARD('a) \<Longrightarrow>
      good_dt n dt \<Longrightarrow>
      step_dt io n chns dt chns' dt' \<Longrightarrow>
  step io (snd (dataflow_tree_to_operator_aux (n :: 'a :: {tln,ab_semigroup_add,group_add,equal,linorder}) chns (dt :: (_,_,_,_, 'g) dataflow_tree))) 
  (snd (dataflow_tree_to_operator_aux n chns' dt'))"
proof (induction dt arbitrary: io n chns chns' dt')
  case (Logic op su)
  then show ?case
    apply(subst (asm) step_dt.simps)
    by auto
next
  fix wire :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) option"
    and dt1 :: "('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree"
    and dt2 :: "('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree"
    and io :: "('a + 'a \<times> 'b, 'a + 'a \<times> 'b, 'c + 'd \<times> 'e) IO"
    and n :: 'a
    and chns :: "'a \<times> 'b \<Rightarrow> ('d \<times> 'e) buf"
    and chns' :: "'a \<times> 'b \<Rightarrow> ('d \<times> 'e) buf"
    and dt' :: "('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree"
  assume ind1:  "\<And>io n chns chns' dt'. nodes_count (dt1::('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree) -+- tln_class.to_nat n < CARD('a) \<Longrightarrow> good_dt n dt1 \<Longrightarrow> step_dt io n chns dt1 chns' dt' \<Longrightarrow> step io (snd (dataflow_tree_to_operator_aux n chns dt1)) (snd (dataflow_tree_to_operator_aux n chns' dt'))"
    and ind2:  "\<And>io n chns chns' dt'. nodes_count (dt2::('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree) -+- tln_class.to_nat n < CARD('a) \<Longrightarrow> good_dt n dt2 \<Longrightarrow> step_dt io n chns dt2 chns' dt' \<Longrightarrow> step io (snd (dataflow_tree_to_operator_aux n chns dt2)) (snd (dataflow_tree_to_operator_aux n chns' dt'))"
    and card: "nodes_count (Comp wire (dt1::('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree) dt2) -+- tln_class.to_nat n < CARD('a)"
    and good_dt: "good_dt n (Comp wire (dt1::('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree) dt2)"
    and step: "step_dt io n chns (Comp wire dt1 dt2) chns' dt'"
  obtain n1 op1 where dtoa1: "dataflow_tree_to_operator_aux n chns dt1 = (n1, op1)"
    by force
  have n1_def: "n1 = n + nodes_count dt1"
    using dtoa1 fst_dtoa_def[of n chns dt1]
    by auto
  obtain n2 op2 where dtoa2: "\<And> chns. dataflow_tree_to_operator_aux n1 chns dt2 = (n2, op2 chns)"
    apply atomize_elim
    apply(rule exI[where x = "fst (dataflow_tree_to_operator_aux n1 chns dt2)"])
    apply(rule exI[where x = "\<lambda> chns. snd (dataflow_tree_to_operator_aux n1 chns dt2)"])
    by (metis dtoa_fst_chns_inv split_pairs)
  have n2_def: "n2 = n + nodes_count dt1 + nodes_count dt2" for chns
    using n1_def dtoa2 fst_dtoa_def[of n1 _ dt2]
    by auto
  have good_dt1: "good_dt n dt1"
    using good_dt
    by simp
  have good_dt2: "good_dt n1 dt2"
    using good_dt dtoa1[THEN arg_cong[where f = fst], symmetric]
    by(simp add: fst_dtoa_def)
  have card1': "nodes_count dt1 < CARD('a)"
    using card
    by simp
  have card1: "nodes_count dt1 -+- tln_class.to_nat n < CARD('a)"
    using card
    by simp
  have card2: "nodes_count dt2 -+- tln_class.to_nat n1 < CARD('a)"
    using card
    apply(simp add: dtoa1[symmetric, THEN arg_cong[where f = fst], simplified fst_dtoa_def, simplified])
    apply(rule dual_order.strict_trans2, assumption)
    apply(rule order.trans, rule add_left_mono, rule ord_add_leq)
    by(simp add: nodes_count_convert[OF card1'])
  have BENQ_map: "(\<lambda>x. map Inr (BENQ p x' chns x)) = BENQ p (Inr x') (\<lambda>x. map Inr (chns x))" for p chns x'
    apply(rule ext)
    subgoal for x
      unfolding BENQ_def
      by simp
    done
  have step1: "step_dt io n chns dt1 chns' dt1' \<Longrightarrow> \<exists> op1'. dataflow_tree_to_operator_aux n chns dt1' = (n1, op1')" for dt1' io chns'
    by (metis (no_types, lifting) eq_fst_iff n1_def step_dt_eq_nodes_count fst_dtoa_def)
  have step2: "step_dt io n1 chns dt2 chns' dt2' \<Longrightarrow> \<exists> op2'. dataflow_tree_to_operator_aux n1 chns dt2' = (n2, op2')" for dt2' io chns'
    by(auto simp add: eq_fst_iff[symmetric] fst_dtoa_def n2_def n1_def dest!: step_dt_eq_nodes_count)
  show "step io (snd (dataflow_tree_to_operator_aux n chns (Comp wire (dt1::('a, 'b, 'c, 'd \<times> 'e, 'g) dataflow_tree) dt2))) (snd (dataflow_tree_to_operator_aux n chns' dt'))"
    using step
    apply(subst (asm) step_dt.simps)
    apply(simp)
    apply(elim conjE disjE exE; auto)
    subgoal premises prems for p x dt1'
      using step1[OF prems(4)] ind1[OF card1 good_dt1 prems(4)]
      by(auto simp add: dtoa1 dtoa2)
    subgoal premises prems for p x dt2'
      using step2[simplified n1_def, OF prems(4)[simplified fst_dtoa_def]] ind2[OF card2 good_dt2, simplified n1_def, OF prems(4)[simplified fst_dtoa_def]]
      apply(auto intro!: step_comp_op_R_Inp simp add: dtoa1 dtoa2[simplified n1_def] n1_def ran_def)
       apply(rule step_comp_op_R_Inp; (auto intro!: map_IO_intros simp add: ran_def split: sum.splits option.splits))
      by simp
    subgoal premises prems for p x dt1'
      using step1[OF prems(4)] ind1[OF card1 good_dt1 prems(4)]
      apply(auto simp add: dtoa1 dtoa2)
       apply(rule step_comp_op_L_Out; (auto intro!: map_IO_intros simp add: ran_def split: sum.splits option.splits))
      by simp
    subgoal premises prems for p x dt2'
      using step2[simplified n1_def, OF prems(4)[simplified fst_dtoa_def]] ind2[OF card2 good_dt2, simplified n1_def, OF prems(4)[simplified fst_dtoa_def]]
      by(auto simp add: dtoa1 dtoa2[simplified n1_def] n1_def)
    subgoal premises prems for n' p x dt2'
      using step2[simplified n1_def, OF prems(5)[simplified fst_dtoa_def]] ind2[OF card2 good_dt2, simplified n1_def, OF prems(5)[simplified fst_dtoa_def]]
      apply(auto intro!: step_comp_op_R_Inp simp add: dtoa1 dtoa2[simplified n1_def] n1_def)
       apply(rule step_comp_op_R_Inp; (auto simp add: ran_def prems(4)[simplified fst_dtoa_def] split: sum.splits)?)
      apply(auto simp add: prems(4)[simplified fst_dtoa_def] add.commute split: option.splits)
      using prems(4)[simplified fst_dtoa_def]
      by (simp add: add.commute)
    subgoal premises prems for n' p x dt1'
      using step1[OF prems(4)] ind1[OF card1 good_dt1 prems(4)]
      by(auto simp add: dtoa1 dtoa2)
    subgoal premises prems for n' p x dt1'
      using step1[OF prems(5)] ind1[OF card1 good_dt1 prems(5)]
      apply(auto simp add: dtoa1 dtoa2)
       apply(rule step_comp_op_L_Out, assumption; (auto simp add: prems(4) split: option.splits)?)
      by simp
    subgoal premises prems for n' p x dt2'
      using step2[simplified n1_def, OF prems(4)[simplified fst_dtoa_def]] ind2[OF card2 good_dt2, simplified n1_def, OF prems(4)[simplified fst_dtoa_def]]
      by(auto simp add: dtoa1 dtoa2[simplified n1_def] n1_def)
    subgoal premises prems for dt1'
      apply(auto simp add: dtoa1 dtoa2 split: prod.splits)
      subgoal premises prems' for n1' op1' n2' op2'
        apply(subgoal_tac "n1' = n1")
         defer
        subgoal
          using prems'
          by (metis fst_conv prems(3) step_dt_eq_nodes_count dtoa1 fst_dtoa_def)
        apply auto
        apply(subgoal_tac "comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case wire (nid - n, p) of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (n1' + offset, q)))) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (chns' x))) op1' op2' =
            comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case wire (nid - n, p) of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (n1' + offset, q)))) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (chns x))) op1' op2'")
         defer
        subgoal
          apply(rule comp_op_chns_invar)
          apply(auto split: sum.splits)
          unfolding prems'(1)[symmetric, THEN arg_cong[where f = snd], simplified snd_conv]
          apply(drule dtoa_inputs_leq[rotated]; simp add: card2)
          using step_dt_chns_inv[rotated 2, OF prems(3) card1 good_dt1] n1_def add.commute
          by metis
        apply auto
        apply(rule step_comp_op_L_Tau; (simp add: ind1[OF card1 good_dt1 prems(3), simplified dtoa1 snd_conv prems'])?)
        apply(erule thin_rl)
        using prems(3) prems'(1) dtoa2 dataflow_tree_to_operator_aux_chns_eq_larger[OF card2, of chns chns',THEN arg_cong[where f = snd] , simplified prems'(1) snd_conv]
        using step_dt_chns_inv[rotated 2, OF prems(3) card1 good_dt1] n1_def add.commute
        by (metis prod.sel(2))
      done
    subgoal premises prems for dt2'
      apply(auto simp add: dtoa1 dtoa2 split: prod.splits)
      subgoal premises prems' for n1' op1' n2' op2'
        apply(subgoal_tac "n1' = n1")
         defer
        subgoal
          using prems'
          by (metis fst_conv prems(3) step_dt_eq_nodes_count dtoa1 fst_dtoa_def)
        apply auto
        apply(subgoal_tac "comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case wire (nid - n, p) of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (n1' + offset, q)))) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (chns' x))) op1' op2' =
            comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case wire (nid - n, p) of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (n1' + offset, q)))) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (chns x))) op1' op2'")
         defer
        subgoal
          apply(rule comp_op_chns_invar)
          apply(auto split: sum.splits)
          apply(rule step_dt_inputs_chns_inv[rotated, OF prems(3)[simplified fst_dtoa_def] good_dt2[simplified n1_def]])
          using prems' n1_def
          apply simp
          using n1_def card2
          by simp
        apply auto
        apply(erule thin_rl)
        apply(rule step_comp_op_R_Tau)
        subgoal
          using ind2[OF card2[simplified n1_def] good_dt2[simplified n1_def] prems(3)[simplified fst_dtoa_def]] prems'(1) dtoa2 n1_def
          by simp
        subgoal
          by simp
        using prems(3) prems'(2) dtoa1 dataflow_tree_to_operator_aux_chns_eq_smaller[OF card1, of chns chns',THEN arg_cong[where f = snd] , simplified prems'(1) snd_conv]
        using step_dt_chns_inv[rotated 2, OF prems(3)[simplified fst_dtoa_def n1_def[symmetric]]  card2 good_dt2] n1_def add.commute
        by (metis split_pairs2)
      done
    subgoal premises prems for dt2' p p' n' n'' a b
      apply(auto simp add: dtoa1 dtoa2 split: prod.splits)
      subgoal premises prems' for n1' op1' n2' op2'
        apply(subgoal_tac "n1' = n1")
         defer
        subgoal
          using prems'
          by (metis fst_conv prems(3) step_dt_eq_nodes_count dtoa1 fst_dtoa_def)
        apply auto
        apply(subgoal_tac "(n1', op1') = (n1,op1)")
        defer
        subgoal
          apply(rule dataflow_tree_to_operator_aux_chns_eq_smaller[OF card1, of "BTL (n', p) chns" chns, simplified dtoa1 prems'(2)])
          apply(auto simp add: BTL_def)
          using  step_dt_Inp_ord[OF card2 prems(4)[simplified fst_dtoa_def n1_def[symmetric]]] n1_def add.commute
          by (metis leD)
        apply simp
        apply(subgoal_tac "step Tau
     (comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case wire (nid - n, p) of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (n1 + offset, q))))
       (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (chns x))) op1 (op2 chns))
     (comp_op (case_sum (\<lambda>_. None) ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod) (\<lambda>nid p. case wire (nid - n, p) of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (n1 + offset, q))))
       (BTL (Inr (n', p)) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (chns x)))) op1 op2')")
         defer
        subgoal
          apply(rule step_Tau_comp_op_R_alt)
          subgoal
            apply(subgoal_tac "dataflow_tree_to_operator_aux n1 chns dt2' = dataflow_tree_to_operator_aux n1' (BTL (n', p) chns) dt2'")
             defer
            subgoal
              apply simp
              apply(rule dataflow_tree_to_operator_aux_chns_inv'; (simp add: card2[simplified prems(4)[THEN step_dt_eq_nodes_count]])?)
              apply(auto simp add: BTL_def)
              using prems(3) good_dt
              apply auto
              apply(erule allE[where x = "n''"])
              apply(erule allE[where x = "n''"])
              apply(erule allE[where x = "n'"])
              apply(erule allE[where x = "p"])
              apply(erule allE[where x = "p"])
              by(auto simp add: fst_dtoa_def add.commute n1_def step_dt_used_port_inv[OF prems(4)])
            using ind2[OF card2 good_dt2 prems(4)[simplified fst_dtoa_def n1_def[symmetric]], simplified dtoa2 snd_conv] prems'(1)
            by (simp add: prems(6))
          subgoal
            using prems(3)
            apply(auto simp add: ran_def split: sum.splits)
            apply(rule exI[where x = "Inr (n'',p')"])
            apply(auto simp add: n1_def fst_dtoa_def)
            by (metis diff_eq_eq add.commute)
          subgoal
            by(auto simp add: prems(6))
          done
        apply(rule HOL.subst[where P = "\<lambda> chns. step _ _ (comp_op _ chns _ _)"]; assumption?)
        apply(erule thin_rl)+
        by(auto simp add: BTL_def map_tl)
      done
    subgoal premises prems for dt1' p p' n' n'' a b
      apply(auto simp add: dtoa1 dtoa2 split: prod.splits)
      subgoal premises prems' for n1' op1' n2' op2'
        apply(subgoal_tac "n1' = n1")
         defer
        subgoal
          using prems'
          by (metis fst_conv prems(4) step_dt_eq_nodes_count dtoa1 fst_dtoa_def)
        apply auto
        apply(subgoal_tac "(n2', op2') = (n2,op2 chns)")
        defer
        subgoal premises n1_alt
          apply(rule dataflow_tree_to_operator_aux_chns_inv'[OF card2, of "BENQ (n'' + n1, p') (a, b) chns" chns, simplified prems'(1)[simplified n1_alt[symmetric]] dtoa2[of chns,simplified n1_alt[symmetric]] n1_alt[symmetric]])
          apply(auto simp add: BENQ_def n1_alt n1_def)
          using good_dt prems(3)
          apply auto
          apply(erule allE[where x = "n'"])
          apply(erule allE[where x = "n'"])
          apply(erule allE[where x = "n'' + n1"])
          apply(erule allE[where x = "p'"])
          apply(erule allE[where x = "p'"])
          by(auto simp add: fst_dtoa_def n1_def add.commute[of "- (n + nodes_count dt1)"])
        apply simp
        apply(subgoal_tac "step Tau
     (comp_op
       (case_sum (\<lambda>_. None)
         ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod)
           (\<lambda>nid p. case wire (nid - n, p) of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (n1 + offset, q))))
       (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (chns x))) op1 (op2 chns))
     (comp_op
       (case_sum (\<lambda>_. None)
         ((case_option None (Some \<circ> Inr) \<circ>\<circ> case_prod)
           (\<lambda>nid p. case wire (nid - n, p) of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (n1 + offset, q))))
       (BENQ (Inr (n'' + n1, p')) (Inr (a, b)) (case_sum (\<lambda>x. []) (\<lambda>x. map Inr (chns x)))) op1' (op2 chns))")
         defer
        subgoal
          apply(rule step_Tau_comp_op_L_alt)
          using ind1[OF card1 good_dt1 prems(4), simplified dtoa1] prems'
          apply(subgoal_tac "dataflow_tree_to_operator_aux n chns dt1' = dataflow_tree_to_operator_aux n (BENQ (n'' + n1, p') (a, b) chns) dt1'")
           defer
          subgoal
            apply(rule dataflow_tree_to_operator_aux_chns_eq_smaller; (simp add: card1[simplified prems(4)[THEN step_dt_eq_nodes_count]])?)
            apply(auto simp add: BENQ_def n1_def prems(4)[THEN step_dt_eq_nodes_count, symmetric])
            apply(subgoal_tac "nodes_count dt1 + n \<le> (nodes_count dt1 + n) + n''")
            defer
            subgoal
              apply(rule tln_class.ord_add)
              apply(subgoal_tac "tln_class.to_nat n'' \<le> nodes_count dt2")
               defer
              subgoal
                apply(erule thin_rl)+
                using prems(3) good_dt
                apply auto
                apply(erule allE[where x = "n'"])
                apply(erule allE[where x = "p"])
                apply(erule allE[where x = "n''"])
                apply(erule allE[where x = "n''"])
                apply(auto)
                by (metis add_lessD1 card2 nless_le nodes_count_convert to_nat_le)
              using card
              by (metis add.commute add_mono_thms_linordered_semiring(2) card2 dual_order.strict_trans2 n1_def)
            by(auto simp add: add.commute)
          by(auto simp add: prems(3) add.commute split: sum.splits option.splits)
        by (simp add: BENQ_map)
      done
    done
qed



definition chns_combine where
  "chns_combine n dt1 dt2 buf chns1 chns2 p = (if p \<in> used_ports' n dt1 then chns1 p else 
  (if p \<in> used_ports' (fst (dataflow_tree_to_operator_aux n chns1 dt1)) dt2 then chns2 p else buf p))"

lemma chns_combine_dt1_simp: "nodes_count dt1 -+- tln_class.to_nat (n :: 'n :: {one,semigroup_add,zero,ord,equal,tln,preorder,group_add}) < CARD('n) \<Longrightarrow> 
  dataflow_tree_to_operator_aux n (chns_combine n dt1 dt2 buf chns1 chns2) dt1 = dataflow_tree_to_operator_aux n (chns_cut n chns1 dt1) dt1"
  unfolding chns_combine_def
  using dataflow_tree_to_operator_aux_chns_cut 
  by (smt (verit) dataflow_tree_to_operator_aux_chns_inv')

lemma chns_combine_dt2_simp: "nodes_count dt1 -+- nodes_count dt2 -+- tln_class.to_nat n < CARD('n) \<Longrightarrow> 
  (n1 :: 'n :: {one,semigroup_add,zero,ord,equal,tln,preorder,group_add,ab_semigroup_add}) = n + nodes_count dt1 \<Longrightarrow> good_dt n1 dt2 \<Longrightarrow> good_dt n dt1 \<Longrightarrow>
  dataflow_tree_to_operator_aux n1 (chns_combine n dt1 dt2 buf chns1 chns2) dt2 = dataflow_tree_to_operator_aux n1 (chns_cut n1 chns2 dt2) dt2"
  unfolding chns_combine_def
  apply(subst dataflow_tree_to_operator_aux_chns_cut[of dt2 n1])
  subgoal
    by (metis card_leq_nodes_count_help)
  apply(rule dataflow_tree_to_operator_aux_chns_inv')
  subgoal
    by (metis card_leq_nodes_count_help)
  apply(simp add: fst_dtoa_def)
  apply auto
  subgoal for n' p'
    apply(subgoal_tac "n' < nodes_count dt1 + n")
     defer
    subgoal
      by(rule used_ports'_less; simp?)
    apply(subgoal_tac "nodes_count dt1 + n \<le> n'")
     defer
    subgoal
      apply(rule used_ports'_gt; (simp add: add.commute)?)
      by (metis card_leq_nodes_count_help add.commute)
    using less_le_not_le by blast
  done


lemma "nodes_count (Comp wire dt1 dt2) -+- tln_class.to_nat n < CARD('a) \<Longrightarrow> good_dt' n (Comp wire dt1 dt2) \<Longrightarrow>
    map_op projl projr (comp_op wire buf (dataflow_op sg1 (snd (dataflow_tree_to_operator_aux n chns1 dt1))) (dataflow_op sg2 (snd (dataflow_tree_to_operator_aux (n + nodes_count dt1) chns2 dt2)))) \<approx>
   (dataflow_op (sg_f sg1 sg2) (snd (dataflow_tree_to_operator_aux n (chns_combine (n :: 'a :: {one,ab_semigroup_add,zero,ord,equal,tln,preorder,group_add,linorder,enum}) dt1 dt2 buf chns1 chns2) (Comp wire dt1 dt2))))"
proof (coinduction arbitrary: buf chns1 chns2 sg1 sg2 dt1 dt2 wire n)
  fix buf :: "'a \<times> 'b \<Rightarrow> ('f \<times> 'g) buf"
    and chns1 :: "'a \<times> 'b \<Rightarrow> ('f \<times> 'g) buf"
    and chns2 :: "'a \<times> 'b \<Rightarrow> ('f \<times> 'g) buf"
    and sg1 :: "('a, 'c, 'd, 'i) subgraph_scheme"
    and sg2 :: "('a, 'c, 'd, 'j) subgraph_scheme"
    and dt1 :: "('a, 'b, ('c, 'd, 'e) shared_state_scheme + ('c \<Rightarrow> 'd antichain), 'f \<times> 'g, 'h) dataflow_tree"
    and dt2 :: "('a, 'b, ('c, 'd, 'e) shared_state_scheme + ('c \<Rightarrow> 'd antichain), 'f \<times> 'g, 'h) dataflow_tree"
    and wire :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) option"
    and n :: 'a
  obtain n1 op1 where dtoa1: "dataflow_tree_to_operator_aux n chns1 dt1 = (n1,op1)"
    by fastforce
  obtain n2 op2 where dtoa2: "dataflow_tree_to_operator_aux n1 chns2 dt2 = (n2,op2)"
    by fastforce
  have n1_def : "n1 = n + nodes_count dt1"
    using fst_dtoa_def[of n "chns1" dt1] 
    unfolding dtoa1
    by simp
  have n2_def : "n2 = n1 + nodes_count dt2"
    using fst_dtoa_def[of n1 "chns2" dt2] 
    unfolding dtoa2
    by simp
  assume card: "nodes_count (Comp wire dt1 dt2) -+- tln_class.to_nat n < CARD('a)"
    and good_dt': "good_dt' n (Comp wire dt1 dt2)"
  have good_dt: "good_dt n (Comp wire dt1 dt2)"
    using good_dt'
    by(simp add: good_dt'_def)
  have good_dt1: "good_dt n dt1"
    using good_dt
    by simp
  have good_dt2: "good_dt n1 dt2"
    using good_dt dtoa1[THEN arg_cong[where f = fst], symmetric]
    by(simp add: fst_dtoa_def)
  have card1: "nodes_count dt1 -+- tln_class.to_nat n < CARD('a)"
    using card
    by simp
  have card2: "nodes_count dt2 -+- tln_class.to_nat n1 < CARD('a)"
    using card n1_def
    by(simp add: fst_dtoa_def card_leq_nodes_count_help)
  have dtoa1': "dataflow_tree_to_operator_aux n (chns_cut n chns1 dt1) dt1 = (n1,op1)"
    using dataflow_tree_to_operator_aux_chns_cut[OF card1] card1 dtoa1[symmetric]
    by presburger
  have dtoa2': "dataflow_tree_to_operator_aux n1 (chns_cut n1 chns2 dt2) dt2 = (n2,op2)"
    using dataflow_tree_to_operator_aux_chns_cut[OF card2] card2 dtoa2[symmetric]
    by presburger
  have "step_dt io n chns1 dt1 chns' dt' \<Longrightarrow> good_dt' n (Comp wire dt' dt2)" for io chns' dt'
    using good_dt'
    apply(subst (asm) good_dt'.simps)
    by auto

end
end
  have chns_combine_simp1: "step_dt io n chns1 dt1 chns' dt' \<Longrightarrow>
     dataflow_tree_to_operator_aux n (chns_combine n dt' dt2 buf chns' chns2) dt' = (n1, snd (dataflow_tree_to_operator_aux n chns' dt'))" for io chns' dt'
    using chns_combine_dt1_simp card1 n1_def step_dt_eq_nodes_count
    by (metis (no_types, lifting) dataflow_tree_to_operator_aux_chns_cut fst_dtoa_def prod.exhaust_sel)
  let ?map_dt = "\<lambda> buf sg1 sg2 chns1 chns2 dt1 dt2 wire n. map_op projl projr (comp_op wire buf (dataflow_op sg1 (snd (dataflow_tree_to_operator_aux n chns1 dt1))) (dataflow_op sg2 (snd (dataflow_tree_to_operator_aux (n + nodes_count dt1) chns2 dt2))))"
  let ?map_dt' = "?map_dt buf sg1 sg2 chns1 chns2 dt1 dt2 wire n"
  let ?dt_map = "\<lambda> buf sg1 sg2 chns1 chns2 dt1 dt2 wire n. dataflow_op (sg_f sg1 sg2) (snd (dataflow_tree_to_operator_aux n (chns_combine n dt1 dt2 buf chns1 chns2) (Comp wire dt1 dt2)))"
  let ?dt_map' = "?dt_map buf sg1 sg2 chns1 chns2 dt1 dt2 wire n"
  let ?wsim' = "wsim (\<lambda>op1 op2. (\<exists>buf chns1 chns2 sg1 sg2 (dt1::(_, 'b, ('c, 'd, 'e) shared_state_scheme + ('c \<Rightarrow> 'd antichain), 'f \<times> 'g, 'h) dataflow_tree) dt2 wire n. op1 = ?map_dt buf sg1 sg2 chns1 chns2 dt1 dt2 wire n \<and>
                   op2 = ?dt_map buf sg1 sg2 chns1 chns2 dt1 dt2 wire n \<and> nodes_count (Comp wire dt1 dt2) -+- tln_class.to_nat n < CARD('a) \<and> good_dt' n (Comp wire dt1 dt2)))"
  let ?wsim = "wsim (\<lambda>op1 op2. (\<exists>buf chns1 chns2 sg1 sg2 (dt1::(_, 'b, ('c, 'd, 'e) shared_state_scheme + ('c \<Rightarrow> 'd antichain), 'f \<times> 'g, 'h) dataflow_tree) dt2 wire n. op1 = ?map_dt buf sg1 sg2 chns1 chns2 dt1 dt2 wire n \<and>
                   op2 = ?dt_map buf sg1 sg2 chns1 chns2 dt1 dt2 wire n \<and> nodes_count (Comp wire dt1 dt2) -+- tln_class.to_nat n < CARD('a) \<and> good_dt' n (Comp wire dt1 dt2)) \<or> op1 \<approx> op2)"
  have "?wsim' ?map_dt' ?dt_map'"
    unfolding wsim_def dataflow_tree_to_operator_def
    apply safe
    apply(simp add: chns_combine_dt1_simp[OF card1] dtoa1 dataflow_tree_to_operator_aux_chns_cut[OF card1, of chns1]
        dataflow_tree_to_operator_aux_chns_cut[OF card2, of chns2, simplified n1_def] dtoa2[simplified n1_def]
        chns_combine_dt2_simp[OF card[simplified] n1_def good_dt2 good_dt1] dtoa2 dtoa1' dtoa2')
    apply(auto elim!: step_map_op_elim step_comp_op_elim step_dataflow_op_elim simp add: dtoa1[THEN arg_cong[where f = snd], symmetric, simplified snd_conv]; drule step_dtoa_elim; 
          (simp add: card1 card2[simplified n1_def] good_dt1 good_dt2[simplified n1_def] | elim exE conjE)?)
    subgoal premises prems for nid p op'' x1 x2 dt' chns'
      using prems apply -
      apply(rule exI)
      apply(rule conjI, rule step_wstep)
      apply(rule step_Inp_dataflow_op_Inp_Inr_intro)
      apply(rule step_map_op[where io = "Inp (Inl (Inr (nid, p))) (Inr (x1, x2))"]; (rule map_IO_intros)?; simp?)
      apply(rule step_comp_op_L_Inp; simp?)
      apply(rule step_dtoa_intro; (simp add: card1 good_dt1)?)
      apply(rule exI[where x = "buf"])
      apply(rule exI[where x = "chns'"])
      apply(rule exI[where x = "chns2"])
      apply(rule exI[where x = "sg1"])
      apply(rule exI[where x = "sg2"])
      apply(rule exI[where x = "dt'"])
      apply(rule exI[where x = "dt2"])
      apply(rule exI[where x = "wire"])
      apply(rule exI[where x = "n"])
      apply(intro conjI)
      subgoal
        by(simp add: dtoa2[simplified n1_def] dataflow_tree_to_operator_aux_chns_cut[OF card2, symmetric, simplified n1_def, of chns2, symmetric] dtoa1 dtoa2 fst_dtoa_def split_pairs2 dtoa2'[simplified n1_def] )
      subgoal
        apply(simp add: chns_combine_simp1)

end
    sorry
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

end


      using prems apply -
      apply(rule exI)
      apply(rule conjI, rule step_wstep)
      apply(rule step_Inp_dataflow_op_Inp_Inr_intro)
      apply(rule step_map_op[where io = "Inp (Inl (Inr (nid, p))) (Inr (x1, x2))"]; (rule map_IO_intros)?; simp?)
      apply(rule step_comp_op_L_Inp; simp?)
      apply(rule step_dtoa_intro; (simp add: card1 good_dt1)?)
      apply(rule exI[where x = "buf"])
      apply(rule exI[where x = "chns'"])
      apply(rule exI[where x = "chns2"])
      apply(rule exI[where x = "sg1"])
      apply(rule exI[where x = "sg2"])
      apply(rule exI[where x = "dt'"])
      apply(rule exI[where x = "dt2"])
      apply(rule exI[where x = "wire"])
      apply(rule exI[where x = "n"])
      apply(intro conjI)
      subgoal
        by(simp add: dtoa2[simplified n1_def] dataflow_tree_to_operator_aux_chns_cut[OF card2, symmetric, simplified n1_def, of chns2, symmetric] dtoa1 dtoa2 fst_dtoa_def split_pairs2 dtoa2'[simplified n1_def] )
      subgoal
        apply(simp add: chns_combine_simp1)
        using chns_combine_dt2_simp[OF card[simplified, simplified step_dt_eq_nodes_count[OF prems(1)]] n1_def[simplified step_dt_eq_nodes_count[OF prems(1)]] good_dt2] dtoa2'

end 
        apply(rule arg_cong[where f = "\<lambda> x. dataflow_op _ (map_op _ _ x)"])
        apply(rule comp_op_chns_invar)
        apply(auto simp add: split: sum.splits)
        unfolding chns_combine_def

end
end
        apply(simp add: chns_combine_dt1_simp chns_combine_dt2_simp[OF card2] card1[simplified step_dt_eq_nodes_count[OF prems(1)]] dataflow_tree_to_operator_aux_chns_cut[symmetric] dtoa1 n1_def[simplified step_dt_eq_nodes_count[OF prems(1)]]
              chns_combine_dt2_simp[OF card2 n1_def[simplified step_dt_eq_nodes_count[OF prems(1)]], simplified n1_def step_dt_eq_nodes_count[OF prems(1)]]
              dtoa2'[simplified n1_def step_dt_eq_nodes_count[OF prems(1)]] n1_def step_dt_eq_nodes_count[OF prems(1)])
        using n1_def
        apply(auto simp add: n1_def)

end
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
*)

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