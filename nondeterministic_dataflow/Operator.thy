text \<open>Operators, trace model, history model, cleaned predicate, and welltyped predicate\<close>

theory Operator

imports
  Linear_Temporal_Logic_on_Llists
  "HOL-Library.BNF_Corec"
  "HOL-Library.Code_Lazy"
  "HOL-Library.Numeral_Type"
  "HOL-Library.Code_Cardinality"
  "HOL-Library.Simps_Case_Conv"
  "HOL-Library.FSet"
begin

section\<open>Channels\<close>

code_lazy_type llist

datatype (discs_sels) 'd observation = Observed (obs: 'd) | EOS
codatatype (dinputs: 'i, doutputs: 'o, dead 'd) dop =
    Read 'i "'d observation \<Rightarrow> ('i, 'o, 'd) nop"
  | Write "('i, 'o, 'd) nop" 'o 'd
and (ninputs: 'i, noutputs: 'o, dead 'd) nop = Choice "('i, 'o, 'd) dop fset"

codatatype (dinputs': 'i, doutputs': 'o, dead 'd, 'nop) dop_nested =
    Read' 'i "'d observation \<Rightarrow> 'nop"
    | Write' 'nop 'o 'd
codatatype (ninputs': 'i, noutputs': 'o, dead 'd) nop' =
    Choice' "('i, 'o, 'd, ('i, 'o, 'd) nop') dop_nested fset"
type_synonym ('i, 'o, 'd) dop' = "('i, 'o, 'd, ('i, 'o, 'd) nop') dop_nested"

primcorec to_dop :: "('i, 'o, 'd) dop' \<Rightarrow> ('i, 'o, 'd) dop" and to_nop :: "('i, 'o, 'd) nop' \<Rightarrow> ('i, 'o, 'd) nop" where
  "to_dop dop = (case dop of Read' i f \<Rightarrow> Read i (to_nop \<circ> f) | Write' op i x \<Rightarrow> Write (to_nop op) i x)"
| "to_nop nop = (case nop of Choice' ops \<Rightarrow> Choice (fimage to_dop ops))"

definition to_dop' :: "(('i, 'o, 'd) nop \<Rightarrow> 'nop) \<Rightarrow> ('i, 'o, 'd) dop \<Rightarrow> ('i, 'o, 'd, 'nop) dop_nested" where
  "to_dop' to_nop' dop = (case dop of Read i f \<Rightarrow> Read' i (to_nop' \<circ> f) | Write op i x \<Rightarrow> Write' (to_nop' op) i x)"

primcorec to_nop' where
  "to_nop' nop = (case nop of Choice ops \<Rightarrow> Choice' (fimage (map_dop_nested id id to_nop') (fimage (to_dop' id) ops)))"


lemma map_dop_nested_to_nop'[simp]:
  "map_dop_nested id id to_nop' (to_dop' id x) = to_dop' to_nop' x"
  unfolding to_dop'_def
  apply (cases x)
   apply auto
  done

lemma map_dop_nested_to_nop'_to_dop'[simp]:
  "map_dop_nested id id to_nop' \<circ> to_dop' id = to_dop' to_nop'"
  apply (rule ext)
  subgoal for x
    unfolding to_dop'_def
    apply (cases x)
     apply auto
    done
  done

lemma to_nop'_code:
  "to_nop' nop = (case nop of Choice ops \<Rightarrow> Choice' (fimage (to_dop' to_nop') ops))"
  apply (subst to_nop'.code)
  apply (simp only: map_dop_nested_to_nop'_to_dop' fset.map_comp)
  done

lemma to_nop'_Choice_simp[simp]:
  "to_nop' (Choice x) = Choice' (fimage (to_dop' to_nop') x)"
  apply (subst to_nop'.code)
  apply simp
  done

lemma to_dop_to_dop'_and_to_nop_to_nop'_aux:
  fixes dop :: "('i, 'o, 'd) dop" and nop :: "('i, 'o, 'd) nop"
  assumes "\<And>l r. R l r = (\<exists> dop. l = to_dop (to_dop' to_nop' dop) \<and> r = dop)"
      and "\<And>l r. S l r = (\<exists> nop. l = to_nop (to_nop' nop) \<and> r = nop)"
  shows  "(R (to_dop (to_dop' to_nop' dop)) dop \<longrightarrow> to_dop (to_dop' to_nop' dop) = dop) \<and> (S (to_nop (to_nop' nop)) nop \<longrightarrow> to_nop (to_nop' nop) = nop)"
  apply (rule dop_nop.coinduct)
  subgoal for dop dop'
    apply (cases dop; cases dop'; (simp add: assms(1) assms(2) rel_funI to_dop'_def))
    done
  subgoal for nop nop'
    apply (cases nop; cases nop'; (simp add: assms(2)))
    apply (simp add: assms(1) fset.rel_map(1) fset.rel_refl)
    done
  done

lemma to_dop_to_dop'_and_to_nop_to_nop':
  fixes dop :: "('i, 'o, 'd) dop" and nop :: "('i, 'o, 'd) nop"
  shows "to_dop (to_dop' to_nop' dop) = dop \<and> to_nop (to_nop' nop) = nop"
  using to_dop_to_dop'_and_to_nop_to_nop'_aux
 [where dop=dop and nop=nop and R="\<lambda> l r. (\<exists>dop. l = to_dop (to_dop' to_nop' dop) \<and> r = dop)" and
  S="\<lambda> l r. (\<exists>nop. l = to_nop (to_nop' nop) \<and> r = nop)"]
  apply simp
  done
     
abbreviation "End \<equiv> Choice {||}"
abbreviation "Det op \<equiv> Choice {|op|}"
abbreviation "ARead i f op \<equiv> Choice {|Read i f, op|}"

type_synonym 'd channel = "'d llist"

code_lazy_type dop
code_lazy_type nop

fun chd where
  "chd LNil = EOS"
| "chd (LCons x lxs) = Observed x"

abbreviation ctl :: "'d channel \<Rightarrow> 'd channel" where "ctl \<equiv> ltl"

abbreviation CHD :: "'a \<Rightarrow> ('a \<Rightarrow> 'd channel) \<Rightarrow> 'd observation" where "CHD p lxs \<equiv> chd (lxs p)"
abbreviation CTL :: "'a \<Rightarrow> ('a \<Rightarrow> 'd channel) \<Rightarrow> ('a \<Rightarrow> 'd channel)" where "CTL p lxs \<equiv> lxs(p := ctl (lxs p))"

section \<open>Sub operators\<close>

inductive sub_ddop :: \<open>('ip, 'op, 'd) dop \<Rightarrow> ('ip, 'op, 'd) dop \<Rightarrow> nat \<Rightarrow> bool\<close>
      and sub_dnop :: \<open>('ip, 'op, 'd) dop \<Rightarrow> ('ip, 'op, 'd) nop \<Rightarrow> nat \<Rightarrow> bool\<close> for op where
  sub_op_Refl: \<open>sub_ddop op op 0\<close>
| sub_op_Read: \<open>sub_dnop op (f x) n \<Longrightarrow> sub_ddop op (Read p f) (Suc n)\<close>
| sub_op_Write: \<open>sub_dnop op op' n \<Longrightarrow> sub_ddop op (Write op' p x) (Suc n)\<close>
| sub_op_Choice: \<open>op' |\<in>| ops \<Longrightarrow> sub_ddop op op' n \<Longrightarrow> sub_dnop op (Choice ops) (Suc n)\<close>

inductive_cases sub_ddop_ReflE [elim!]: \<open>sub_ddop op op n\<close>
inductive_cases sub_ddop_ReadE [elim!]: \<open>sub_ddop op (Read p f) n\<close>
inductive_cases sub_ddop_WriteE [elim!]: \<open>sub_ddop op (Write op' p x) n\<close>   
inductive_cases sub_dnop_ChoiceE [elim!]: \<open>sub_dnop op (Choice ops) n\<close>

inductive sub_ndop :: \<open>('ip, 'op, 'd) nop \<Rightarrow> ('ip, 'op, 'd) dop \<Rightarrow> nat \<Rightarrow> bool\<close>
      and sub_nnop :: \<open>('ip, 'op, 'd) nop \<Rightarrow> ('ip, 'op, 'd) nop \<Rightarrow> nat \<Rightarrow> bool\<close> for op where
  sub_op_Refl: \<open>sub_nnop op op 0\<close>
| sub_op_Read: \<open>sub_nnop op (f x) n \<Longrightarrow> sub_ndop op (Read p f) (Suc n)\<close>
| sub_op_Write: \<open>sub_nnop op op' n \<Longrightarrow> sub_ndop op (Write op' p x) (Suc n)\<close>
| sub_op_Choice: \<open>op' |\<in>| ops \<Longrightarrow> sub_ndop op op' n \<Longrightarrow> sub_nnop op (Choice ops) (Suc n)\<close>

inductive_cases sub_nnop_ReflE [elim!]: \<open>sub_nnop op op n\<close>
inductive_cases sub_ndop_ReadE [elim!]: \<open>sub_ndop op (Read p f) n\<close>
inductive_cases sub_ndop_WriteE [elim!]: \<open>sub_ndop op (Write op' p x) n\<close>   
inductive_cases sub_nnop_ChoiceE [elim!]: \<open>sub_nnop op (Choice ops) n\<close>

lemmas inputs_set_induct =
  dop_nop.set_induct(1)[THEN conjunct1, rule_format, rotated -1, consumes 1, case_names Read Write Choice, induct set: dinputs]
  dop_nop.set_induct(1)[THEN conjunct2, rule_format, rotated -1, consumes 1, case_names Read Write Choice, induct set: ninputs]
lemmas outputs_set_induct =
  dop_nop.set_induct(2)[THEN conjunct1, rule_format, rotated -1, consumes 1, case_names Read Write Choice, induct set: doutputs]
  dop_nop.set_induct(2)[THEN conjunct2, rule_format, rotated -1, consumes 1, case_names Read Write Choice, induct set: noutputs]

lemma inputs_sub_op_Read:
  fixes dop :: "('i, 'o, 'd) dop" and nop :: "('i, 'o, 'd) nop"
  shows \<open>p \<in> dinputs dop \<Longrightarrow> \<exists>f n. sub_ddop (Read p f) dop n\<close>
   \<open>p \<in> ninputs nop \<Longrightarrow> \<exists>f n. sub_dnop (Read p f) nop n\<close>
  by (induct dop and nop set: dinputs ninputs) (auto intro: sub_ddop_sub_dnop.intros)

lemma sub_op_Read_inputs:
  fixes dop :: "('i, 'o, 'd) dop" and nop :: "('i, 'o, 'd) nop"
  shows \<open>sub_ddop (Read p f) dop n \<Longrightarrow> p \<in> dinputs dop\<close>
  \<open>sub_dnop (Read p f) nop n \<Longrightarrow> p \<in> ninputs nop\<close>
  by (induct dop n and nop n pred: sub_ddop sub_dnop) auto

lemma outputs_sub_op_Write:
  fixes dop :: "('i, 'o, 'd) dop" and nop :: "('i, 'o, 'd) nop"
  shows \<open>p \<in> doutputs dop \<Longrightarrow> \<exists>op' x n. sub_ddop (Write op' p x) dop n\<close>
   \<open>p \<in> noutputs nop \<Longrightarrow> \<exists>op' x n. sub_dnop (Write op' p x) nop n\<close>
  by (induct dop and nop set: doutputs noutputs) (auto intro: sub_ddop_sub_dnop.intros)

lemma sub_op_Write_outputs:
  fixes dop :: "('i, 'o, 'd) dop" and nop :: "('i, 'o, 'd) nop"
  shows \<open>sub_ddop (Write op' p x) dop n \<Longrightarrow> p \<in> doutputs dop\<close>
  \<open>sub_dnop (Write op' p x) nop n \<Longrightarrow> p \<in> noutputs nop\<close>
  by (induct dop n and nop n pred: sub_ddop sub_dnop) auto

(*
lemma sub_op_Read_induct [consumes 1, case_names Read1 Read2 Write]:
  assumes \<open>sub_op (Read p g) op d\<close>
    and read1: \<open>\<And>f p. P p (Read p f)\<close>
    and read2: \<open>\<And>p p' f x d g. sub_op (Read p g) (f x) d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Read p g) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Read p' f)\<close>
    and writ: \<open>\<And>p p' op' x d g. sub_op (Read p g) op' d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Read p g) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Write op' p' x)\<close>
    and choic: \<open>\<And>p p' ops x d g. \<exists> op' |\<in>| ops. sub_op (Read p g) op' d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Read p g) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Choice ops)\<close>
  shows \<open>P p op\<close>
  using assms(1)
proof (induct d arbitrary: op p rule: less_induct)
  case (less m)
  from this(2,1) show ?case
    by (induct op m pred: sub_op) (meson assms(2-) le_imp_less_Suc)+
qed

lemma sub_op_Write_induct [consumes 1, case_names Read Write1 Write2]:
  assumes \<open>sub_op (Write op2 p y) op d\<close>
    and read: \<open>\<And>p p' f x op2 y d. sub_op (Write op2 p y) (f x) d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Write op2 p y) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Read p' f)\<close>
    and write1: \<open>\<And>p p' op' x op2 y d. sub_op (Write op2 p y) op' d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Write op2 p y) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Write op' p' x)\<close>
    and write1: \<open>\<And>p op' op2 y d ops.  \<exists> op' |\<in>| ops.  sub_op (Write op2 p y) op' d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Write op2 p y) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Choice ops)\<close>
    and write2: \<open>\<And>p op' x. P p (Write op' p x)\<close>
  shows \<open>P p op\<close>
  using assms(1)
proof (induct d arbitrary: op p rule: less_induct)
  case (less m)
  from this(2,1) show ?case
    by (induct op m pred: sub_op) (meson assms(2-) le_imp_less_Suc)+
qed
*)
(*
section\<open>Inputs measure\<close>

inductive input_at where
  "input_at p (Read p f) n"
| "p \<noteq> p' \<Longrightarrow> input_at p (f x) n \<Longrightarrow> input_at p (Read p' f) (Suc n)"
| "input_at p op' n \<Longrightarrow> input_at p (Write op' p' x) (Suc n)"
| "\<exists> op' |\<in>| ops. input_at p op' n \<Longrightarrow> input_at p (Choice ops) (Suc n)"


lemma inputs_input_at: "p \<in> inputs op \<Longrightarrow> \<exists>n. input_at p op n"
  by (induct p op rule: op.set_induct(1)) (auto intro: input_at.intros)

lemma input_at_inputs: "input_at p op n \<Longrightarrow> p \<in> inputs op"
  by (induct p op n rule: input_at.induct) auto

lemma inputs_alt: "p \<in> inputs op \<longleftrightarrow> (\<exists>n. input_at p op n)"
  by (metis input_at_inputs inputs_input_at)

definition "input_depth p op = (LEAST n. input_at p op n)"

lemma input_depth_Read: "p \<in> inputs op \<Longrightarrow> input_depth p op = 0 \<longleftrightarrow> (\<exists>f. op = Read p f)"
  unfolding input_depth_def
  apply (cases op)
    apply (auto intro: input_at.intros Least_eq_0)
   apply (metis LeastI_ex Zero_not_Suc input_at.simps inputs_input_at op.inject(1))
   apply (metis input_at.simps inputs_input_at op.simps(4) wellorder_Least_lemma(1) zero_less_Suc)
  apply (metis LeastI input_at.simps inputs_alt nat.discI op.simps(6) zero_less_iff_neq_zero)
  done

lemma input_depth_Write[simp]:
  "p \<in> inputs op' \<Longrightarrow> input_depth p (Write op' p' x) = Suc (input_depth p op')"
  unfolding input_depth_def
  apply (drule inputs_input_at)
  apply (erule exE)
  apply (rule Least_Suc2)
     apply (auto elim: input_at.cases intro: input_at.intros)
  done

lemma input_at_mono: "input_at p op n \<Longrightarrow> n \<le> m \<Longrightarrow> input_at p op m"
  by (induct p op n arbitrary: m rule: input_at.induct)
    (auto intro: input_at.intros simp: less_eq_nat.simps split: nat.splits)

lemma input_depth_Read_diff: 
  "p \<noteq> p' \<Longrightarrow> \<exists>x. p \<in> inputs (f x) \<Longrightarrow>
   input_depth p (Read p' f) = Suc (input_depth p (f (arg_min (input_depth p o f) (\<lambda>x. p \<in> inputs (f x)))))"
  unfolding input_depth_def inputs_alt
  apply (erule exE)
  apply (frule arg_min_natI[of "\<lambda>x. \<exists>n. input_at p (f x) n" _ "input_depth p o f"])
  unfolding input_depth_def
  apply (erule exE)+
  apply (rule Least_Suc2)
     apply (erule input_at.intros)
     apply assumption
    apply assumption
   apply (auto elim: input_at.cases intro: input_at.intros)
  apply (erule input_at.cases[of _ "Read p' f"])
    apply auto
  apply (smt (verit, del_insts) LeastI Least_le arg_min_nat_le comp_eq_dest_lhs input_at_mono)
  done

lemma input_depth_arg_min_le[simp]:
  "p \<in> inputs (f x) \<Longrightarrow>
   input_depth p (f (ARG_MIN (input_depth p o f) x. p \<in> inputs (f x))) \<le> input_depth p (f x)"
  by (metis arg_min_nat_le comp_apply)

lemma input_depth_Read_diff'[simp]: 
  "p \<noteq> p' \<Longrightarrow> p \<in> inputs (f x) \<Longrightarrow>
   input_depth p (Read p' f) = Suc (input_depth p (f (arg_min (input_depth p o f) (\<lambda>x. p \<in> inputs (f x)))))"
  by (metis input_depth_Read_diff)

lemma input_depth_Read_diff_le[simp]: 
  "p \<noteq> p' \<Longrightarrow> \<exists>x. p \<in> inputs (f x) \<Longrightarrow>
   (input_depth p (f (arg_min (input_depth p o f) (\<lambda>x. p \<in> inputs (f x))))) \<le> input_depth p (Read p' f)"
  by force

section\<open>Outputs measure\<close>

inductive output_at where
  "output_at p (Write op' p x) n"
| "p \<noteq> p' \<Longrightarrow> output_at p op' n \<Longrightarrow> output_at p (Write op' p' x) (Suc n)"
| "output_at p op' n \<Longrightarrow> op' \<in> range f \<Longrightarrow> output_at p (Read p' f) (Suc n)"
| "\<exists> op' |\<in>| ops. output_at p op' n \<Longrightarrow> output_at p (Choice ops) (Suc n)"

lemma outputs_output_at: "p \<in> outputs op \<Longrightarrow> \<exists>n. output_at p op n"
  by (induct p op rule: op.set_induct(2)) (auto intro: output_at.intros)

lemma output_at_outputs: "output_at p op n \<Longrightarrow> p \<in> outputs op"
  by (induct p op n rule: output_at.induct) auto

lemma outputs_alt: "p \<in> outputs op \<longleftrightarrow> (\<exists>n. output_at p op n)"
  by (metis output_at_outputs outputs_output_at)

definition "output_depth p op = (LEAST n. output_at p op n)"

lemma output_depth_Write_simp_eq[simp]:
  "output_depth p (Write op p x) = 0"
  by (simp add: output_depth_def output_at.intros(1))

lemma input_depth_Write_0: 
  "p \<in> outputs op \<Longrightarrow>
   output_depth p op = 0 \<longleftrightarrow> (\<exists>x op'. op = Write op' p x)"
  unfolding output_depth_def
  apply (auto elim: output_at.cases intro: output_at.intros)
  apply (smt (verit) LeastI_ex Zero_neq_Suc output_at.cases outputs_alt)
  apply (simp add: output_at.intros(1))
  done

lemma output_at_mono: "output_at p op n \<Longrightarrow> n \<le> m \<Longrightarrow> output_at p op m"
  by (induct p op n arbitrary: m rule: output_at.induct)
    (auto intro: output_at.intros simp: less_eq_nat.simps split: nat.splits)

lemma output_depth_Read[simp]:
  "\<exists>x. p \<in> outputs (f x) \<Longrightarrow>
   output_depth p (Read p' f) = Suc (output_depth p (f (arg_min (output_depth p o f) (\<lambda>x. p \<in> outputs (f x)))))"
  unfolding output_depth_def outputs_alt
  apply (erule exE)
  subgoal for  d
    apply (frule arg_min_natI[of "\<lambda>x. \<exists>n. output_at p (f x) n" _ "output_depth p o f"])
    unfolding output_depth_def
    apply (erule exE)+
    apply (rule Least_Suc2)
       apply (erule output_at.intros)
       apply simp_all
     apply (meson Zero_neq_Suc op.distinct(1) output_at.cases)
    apply (auto elim: output_at.cases intro: output_at.intros)
    apply (erule output_at.cases[of _ "Read p' f"])
      apply auto
    using output_at_mono 
    apply (smt (verit, ccfv_SIG) LeastI Least_le arg_min_nat_le comp_eq_dest_lhs)
    done
  done

lemma output_depth_Write_simp_diff[simp]:
  "\<exists>x. p \<in> outputs op \<Longrightarrow>
   p \<noteq> p' \<Longrightarrow>
   output_depth p (Write op p' x) = Suc (output_depth p op)"
  unfolding output_depth_def outputs_alt
  apply (elim exE)
  subgoal for x n
    apply (rule Least_Suc2[where n="Suc n"])
       defer
       apply assumption
    using output_at.cases apply force
    subgoal
      by (smt (verit, del_insts) diff_Suc_1' op.distinct(1) op.inject(2) op.simps(9) output_at.cases output_at.intros(2))
    subgoal
      using output_at.simps by fastforce
    done
  done
*)

section\<open>Trace model basics\<close>
datatype ('a, 'b, 'd) IO = Inp (proji: 'a) "'d observation" | Out (projo: 'b) (data: 'd)
  where "data (Inp p x) = obs x"

coinductive dtraced and ntraced where
  Read: "ntraced (f x) lxs \<Longrightarrow> dtraced (Read p f) (LCons (Inp p x) lxs)"
| Write: "ntraced op lxs \<Longrightarrow> dtraced (Write op p x) (LCons (Out p x) lxs)"
| Choice: "op |\<in>| ops \<Longrightarrow> dtraced op lxs \<Longrightarrow>  ntraced (Choice ops) lxs"

inductive_cases dtraced_WriteE[elim!]: "dtraced (Write op p' x) lxs"
inductive_cases dtraced_ReadE[elim!]: "dtraced (Read p' f) lxs"
inductive_cases ntraced_ChoiceE[elim!]: "ntraced (Choice ops) lxs"
(*
inductive traced_cong for R where
  tc_base: "R op lxs \<Longrightarrow> traced_cong R op lxs"
| tc_traced: "traced op lxs \<Longrightarrow> traced_cong R op lxs"
| tc_read: "traced_cong R (f x) lxs \<Longrightarrow> traced_cong R (Read p f) (LCons (Inp p x) lxs)"
| tc_write: "traced_cong R op lxs \<Longrightarrow> traced_cong R (Write op q x) (LCons (Out q x) lxs)"
| tc_choice: "\<exists> op |\<in>| ops. traced_cong R op lxs \<Longrightarrow> traced_cong R (Choice ops) lxs"

lemma traced_cong_disj[simp]:
  "(traced_cong R op lxs \<or> traced op lxs) = traced_cong R op lxs"
  by (auto intro: traced_cong.intros)

lemma traced_coinduct_upto:
  assumes "X op lxs"
    "(\<And>x1 x2.
     X x1 x2 \<Longrightarrow>
    (\<exists>f x lxs p. x1 = Read p f \<and> x2 = LCons (Inp p x) lxs \<and> traced_cong X (f x) lxs) \<or>
    (\<exists>op lxs p x. x1 = Write op p x \<and> x2 = LCons (Out p x) lxs \<and> traced_cong X op lxs) \<or>
    (\<exists>ops. x1 = Choice ops \<and> (\<exists>op|\<in>|ops. traced_cong X op x2)) \<or>
     x1 = Choice {||} \<and> x2 = LNil)"
  shows "traced op lxs"
  apply (rule traced.coinduct[where X = "traced_cong X"])
   apply (rule tc_base, rule assms(1))
  subgoal for op lxs
    apply (induct op lxs rule: traced_cong.induct)
    subgoal for op lxs
      by (drule assms(2)) (auto simp del: fun_upd_apply)
    subgoal for op lxs
      by (erule traced.cases)
        (auto 10 10 simp add: tc_traced simp del: fun_upd_apply)
    subgoal for p f x lxs
      by (auto simp del: fun_upd_apply)
    subgoal for p n f 
      by (auto simp del: fun_upd_apply)
    subgoal 
      by (auto simp del: fun_upd_apply)
    done
  done

definition "traces op = {lxs. traced op lxs}"

(* lemma traces_Read[simp]:
  "traces (Read p f) = (\<Union>x. LCons (Inp p (Observed x)) ` traces (f (Observed x))) \<union>
                       LCons (Inp p EOB) ` traces (f EOB) \<union>
                       LCons (Inp p EOS) ` traces (f EOS)"
  apply (auto simp: traces_def image_iff intro: traced.intros split: nat.splits)
     apply (metis observation.exhaust)+
  done
 *)
lemma traces_Write[simp]:
  "traces (Write op p x) = LCons (Out p x) ` traces op"
  by (auto simp: traces_def intro: traced.intros)

lemma traces_End[simp]:
  "traces End = {LNil}"
  by (auto simp: traces_def intro: traced.intros)

corec traced_wit where
  "traced_wit op = (case op of
    Read p f \<Rightarrow> LCons (Inp p EOS) (traced_wit (f EOS))
  | Write op' p' x \<Rightarrow> LCons (Out p' x) (traced_wit op')
  | End \<Rightarrow> LNil)"

lemma lset_traced_wit: "t \<in> lset (traced_wit op) \<Longrightarrow> (\<exists>p \<in> inputs op. t = (Inp p EOS)) \<or> (\<exists>q \<in> outputs op. \<exists>x. t = (Out q x))"
  apply (induction t "traced_wit op" arbitrary: op rule: llist.set_induct)
   apply (subst (asm) traced_wit.code)
   apply (auto split: op.splits) []
  apply (subst (asm) (2) traced_wit.code)
  apply (fastforce split: op.splits) []
  done

definition agree :: "('l \<Rightarrow> 'l' \<Rightarrow> bool) \<Rightarrow> ('l \<times> 'c) llist \<Rightarrow> ('l' \<times> 'c) llist \<Rightarrow> bool" where
  "agree R lxs lys = llist_all2 (rel_prod R (=)) (lfilter (Domainp R o fst) lxs) (lfilter (Rangep R o fst) lys)"


definition "lproject R S ios = (\<lambda>p. lmap data (lfilter (\<lambda>qx. case qx of Inp q (Observed x) \<Rightarrow> R p q | Out q x \<Rightarrow> S p q | _ \<Rightarrow> False) ios))"

lemma lproject_LNil[simp]: "lproject R S LNil = (\<lambda>p. LNil)"
  by (simp add: lproject_def)

lemma lproject_LCons[simp]: "lproject R S (LCons (Inp q (Observed x)) lxs) =
  (\<lambda>p. if R p q then LCons x (lproject R S lxs p) else lproject R S lxs p)"
  "lproject R S (LCons (Out q' x) lxs) =
  (\<lambda>p. if S p q' then LCons x (lproject R S lxs p) else lproject R S lxs p)"
  "lproject R S (LCons (Inp q EOS) lxs) = lproject R S lxs"
  "lproject R S (LCons (Inp q EOB) lxs) = lproject R S lxs"
  by (auto simp add: lproject_def)

lemma lproject_LCons_False[simp]:
  "\<not> R p p' \<Longrightarrow>
   lproject R S (LCons (Inp p' x) lxs) p = lproject R S lxs p"
  apply (cases x)
    apply auto
  done

lemma lproject_LCons_True[simp]:
  "R p p' \<Longrightarrow>
   is_Observed x \<Longrightarrow>
   lproject R S (LCons (Inp p' x) lxs) p = LCons (obs x) (lproject R S lxs p)"
  apply (cases x)
    apply auto
  done

lemma lproject_empty_conv:
  "lproject R S lxs p = LNil \<longleftrightarrow> (\<forall>q x. Inp q (Observed x) \<in> lset lxs \<longrightarrow> \<not> R p q) \<and> (\<forall>q x. Out q x \<in> lset lxs \<longrightarrow> \<not> S p q)"
  "LNil = lproject R S lxs p \<longleftrightarrow> (\<forall>q x. Inp q (Observed x) \<in> lset lxs \<longrightarrow> \<not> R p q) \<and> (\<forall>q x. Out q x \<in> lset lxs \<longrightarrow> \<not> S p q)"
  by (auto simp: lproject_def lmap_eq_LNil LNil_eq_lmap lfilter_empty_conv
      split: observation.splits IO.splits)

lemma lproject_False: 
  "(\<And>q x. Inp q (Observed x) \<in> lset lxs \<Longrightarrow> \<not> R p q) \<Longrightarrow> (\<And>q x. Out q x \<in> lset lxs \<Longrightarrow> \<not> S p q) \<Longrightarrow> lproject R S lxs p = LNil"
  by (simp add: lproject_empty_conv)

lemma lproject_False_weak: 
  "(\<And>qx. qx \<in> lset lxs \<Longrightarrow> case_IO (\<lambda> q _. \<not> R p q) (\<lambda> q _. \<not> S p q) qx) \<Longrightarrow> lproject R S lxs p = LNil"
  by (force simp add: lproject_empty_conv)

(*
lemma traced_not_forever_EOB:
  "traced m op lxs \<Longrightarrow> ldropn i (lfilter (\<lambda>x. is_Inp x \<and> proji x = p) lxs) \<noteq> repeat (Inp p EOB)"
  apply (induct "m p" arbitrary: op lxs)
  oops

lemma TRACES_not_forever_EOB:
  "lxs \<in> TRACES op \<Longrightarrow> ldropn i (lfilter (\<lambda>x. is_Inp x \<and> proji x = p) lxs) \<noteq> repeat (Inp p EOB)"
  unfolding TRACES_def traces_def
  by (auto dest: traced_not_forever_EOB)
*)
*)

section\<open>Cleaned predicate\<close>

coinductive dcleaned and ncleaned where
  cleaned_Read[intro]: "p \<notin> inputs (f EOS) \<Longrightarrow> (\<And>x. ncleaned (f x)) \<Longrightarrow> dcleaned (Read p f)"
| cleaned_Write[intro]: "ncleaned op \<Longrightarrow> dcleaned (Write op q x)"
| cleaned_End[iff]: "(\<forall>op |\<in>| ops. dcleaned op) \<Longrightarrow> ncleaned (Choice ops)"

inductive_cases dcleaned_ReadE[elim!]: "dcleaned (Read p f)"
inductive_cases dcleaned_WriteE[elim!]: "dcleaned (Write op q x)"
inductive_cases ncleaned_ChoiceE[elim!]: "ncleaned (Choice ops)"

(*
inductive cleaned_cong for R where
  cc_base: "R op \<Longrightarrow> cleaned_cong R op"
| cc_cleaned: "cleaned op \<Longrightarrow> cleaned_cong R op"
| cc_read: "p \<notin> inputs (f EOS) \<Longrightarrow> (\<And>x. cleaned_cong R (f x)) \<Longrightarrow> cleaned_cong R (Read p f)"
| cc_write: "cleaned_cong R op \<Longrightarrow> cleaned_cong R (Write op q x)"

lemma cleaned_coinduct_upto: "X op \<Longrightarrow>
  (\<And>op. X op \<Longrightarrow> (\<exists>p f. op = Read p f \<and> p \<notin> inputs (f EOS) \<and> (\<forall>x. cleaned_cong X (f x))) \<or> (\<exists>op' q x. op = Write op' q x \<and> (cleaned_cong X op')) \<or> op = End) \<Longrightarrow>
  cleaned op"
  apply (rule cleaned.coinduct[where X="cleaned_cong X"])
   apply (erule cleaned_cong.intros)
  apply (erule thin_rl)
  subgoal premises prems for op
    using prems(2)
    apply (induct op rule: cleaned_cong.induct)
    subgoal for op
      by (auto dest: prems(1))
    subgoal for op
      by (cases op) auto
    subgoal for f p
      by auto
    subgoal for f p
      by auto
    done
  done

lemma ldropn_LConsD: "ldropn n xs = LCons x ys \<Longrightarrow> x \<in> lset xs"
  by (metis in_lset_ldropnD lset_intros(1))

l(* emma non_input_traces: "t \<in> lset lxs \<Longrightarrow> t = Inp p y \<Longrightarrow> p \<notin> inputs op \<Longrightarrow> lxs \<in> traces op \<Longrightarrow> False"
  apply (induct t lxs arbitrary: op rule: llist.set_induct)
  subgoal for t lxs op
    apply (cases op; auto)
    done
  subgoal for t lxs x op
    apply (cases op; auto split: nat.splits)
    done
  done
 *)
lemma cleaned_traced_gen:
  "cleaned op \<Longrightarrow> traced op (rev ps @@- lxs) \<Longrightarrow> alw (now ((=) (Inp p EOS)) imp nxt (alw (wow (\<lambda>t. \<forall>x. t \<noteq> Inp p x)))) ps lxs"
  apply (coinduction arbitrary: op ps lxs)
  subgoal for op ps lxs
    apply (cases lxs)
     apply simp_all
    subgoal for x lxs'
      apply (intro conjI impI disjI1; blast?)
      apply (induct ps arbitrary: op rule: rev_induct)
       apply simp
       apply (erule traced.cases; simp)
       apply (erule cleaned.cases; simp)
       apply (auto simp: alw_iff_ldropn wow_alt dest!: ldropn_LConsD dest: non_input_traces[unfolded traces_def] split: llist.splits) []
       apply simp
      apply (erule traced.cases; simp)
         apply (erule cleaned.cases; auto simp add: alw_iff_ldropn wow_alt)+
      done
    done
  done

lemma cleaned_traced:
  "cleaned op \<Longrightarrow> traced op lxs \<Longrightarrow> alw (now ((=) (Inp p EOS)) imp nxt (alw (wow (\<lambda>t. \<forall>x. t \<noteq> Inp p x)))) [] lxs"
  using cleaned_traced_gen[where ps = "[]"] by simp

section\<open>Trace model full abstraction\<close>

lemma traced_traced_wit: "traced op (traced_wit op)"
  apply (coinduction arbitrary: op)
  apply (subst (1 3 5) traced_wit.code)
  apply (auto split: op.splits dest: lset_traced_wit simp: traced_wit.code[where op=End])
  done

lemma traced_wit_traces: "traced_wit op \<in> traces op"
  by (auto simp add: traced_traced_wit traces_def)

lemma traces_nonempty: "traces op \<noteq> {}"
  by (auto simp: traces_def intro!: traced_traced_wit)
(* 
lemma traces_op_eqI: "traces op = traces op' \<Longrightarrow> op = op'"
  apply (coinduction arbitrary: op op')
  subgoal for op op'
    apply (cases op; cases op')
            apply (simp_all add: rel_fun_def set_eq_iff split: nat.splits)
    subgoal for p f p' f'
      apply (rule context_conjI)
      subgoal
        apply (drule spec[of _ "LCons (Inp p EOS) (traced_wit (f EOS))"])
        apply simp
        apply (drule iffD1)
         apply (rule disjI2)
         apply (auto dest: lset_traced_wit simp: traces_def traced_traced_wit image_iff) []
        apply (erule exE disjE conjE)+
         apply (simp_all add: gr0_conv_Suc image_iff)
        done
      subgoal
        apply safe
        subgoal for x lxs
          apply (drule spec[of _ "LCons (Inp p x) lxs"])
          apply (drule iffD1)
           apply (cases x; auto simp: image_iff dest: non_input_traces) []
          apply (erule exE conjE disjE)+
           apply (auto simp add: gr0_conv_Suc image_iff)
          done
        subgoal for x lxs
          apply (drule spec[of _ "LCons (Inp p' x) lxs"])
          apply (drule iffD2)
           apply (cases x; auto simp: image_iff dest: non_input_traces) []
           apply (auto simp add: gr0_conv_Suc image_iff)
          done
        done
      done
    subgoal
      apply (auto simp: set_eq_iff image_iff)
      apply (metis IO.distinct(1) llist.inject traced_wit_traces)
      done
    subgoal
      apply (auto dest!: spec[of _ LNil] simp: gr0_conv_Suc)
      done
    subgoal
      apply (auto simp: set_eq_iff image_iff)
      apply (metis IO.distinct(1) llist.inject traced_wit_traces)
      done
    subgoal for op1 p1 x1 op2 p2 x2
      apply (auto simp: set_eq_iff image_iff)
      apply (metis IO.inject(2) llist.inject traced_wit_traces)
      apply (metis IO.inject(2) llist.inject traced_wit_traces)
      done
    subgoal
      apply (auto simp: set_eq_iff image_iff)
      done
    subgoal
      apply (auto dest!: spec[of _ LNil] simp: gr0_conv_Suc)
      done
    subgoal
      apply (auto simp: set_eq_iff image_iff)
      done
    done
  done *)

section\<open>Produce function\<close>
(* 
inductive producing for p where
  "producing p End lxs 0"
| "producing p (Write _ p _) lxs 0"
| "producing p (f (CHD p' lxs)) (CTL p' lxs) i \<Longrightarrow> producing p (Read p' f) lxs (Suc i)"
| "p \<noteq> p' \<Longrightarrow> producing p op lxs i \<Longrightarrow> producing p (Write op p' x) lxs (Suc i)"

inductive_cases producing_EndE[elim!]: "producing p End lxs n"
inductive_cases producing_WriteE[elim!]: "producing p (Write op p' x) lxs n"
inductive_cases producing_ReadE[elim!]: "producing p (Read p' f) lxs n"

lemma producing_inject: "producing p op lxs i \<Longrightarrow> producing p op lxs j \<Longrightarrow> i = j"
  by (induct op lxs i arbitrary: j rule: producing.induct) fastforce+

lemma The_producing: "producing p op lxs i \<Longrightarrow> The (producing p op lxs) = i"
  using producing_inject by fast

corecursive produce where
  "produce op lxs p = (let produce' = (\<lambda>op' lxs'. if \<exists>i. producing p op lxs i then produce op' lxs' p else LNil) in case op of
    Read p' f \<Rightarrow> (produce' (f (CHD p' lxs)) (CTL p' lxs))
  | Write op' p' x \<Rightarrow> (if p = p' then LCons x (produce op' lxs p) else produce' op' lxs)
  | End \<Rightarrow> LNil)"
  by (relation "measure (\<lambda>(op, lxs, p). THE i. producing p op lxs i)")
    (auto 0 3 simp: The_producing del: producing_ReadE producing_WriteE elim: producing.cases)

lemma produce_code[code]:
  "produce op lxs p = (case op of
    Read p' f \<Rightarrow> produce (f (CHD p' lxs)) (CTL p' lxs) p
  | Write op' p' x \<Rightarrow> (if p = p' then LCons x (produce op' lxs p) else produce op' lxs p)
  | End \<Rightarrow> LNil)"
  apply (subst produce.code)
  apply (simp split: op.splits if_splits)
  apply safe
  subgoal for p' f
    by (subst produce.code) (auto 0 5 split: op.splits intro: producing.intros)
  subgoal for op p x
    by (subst produce.code) (auto 0 4 split: op.splits intro: producing.intros)
  done
 *)
simps_of_case produce_simps[simp]: produce_code

lemma produce_inner_induct:
  "(\<And>op lxs p.
    (\<And>p' f. Read p' f = op \<Longrightarrow> Ex (producing p op lxs) \<Longrightarrow> P (f (CHD p' lxs)) (CTL p' lxs) p) \<Longrightarrow>
    (\<And>op' p' x. Write op' p' x = op \<Longrightarrow> p \<noteq> p' \<Longrightarrow> Ex (producing p op lxs) \<Longrightarrow> P op' lxs p) \<Longrightarrow> P op lxs p) \<Longrightarrow>
   P op lxs p"
  subgoal premises prems
    using produce.inner_induct[of "\<lambda> (op, lxs, p). P op lxs p" "(op, lxs, p)"] apply -
    apply (drule meta_mp)
    subgoal
      apply simp
      apply (rule prems)
       apply auto
      done
    apply simp
    done
  done

(* lemma produced_produce: "produced m op lxs (produce op lxs)"
  apply (coinduction arbitrary: m op lxs)
  subgoal for m op lxs
    by (cases op) (force simp: muted_def muted_produce[unfolded muted_def])+
  done *)


section\<open>History model\<close>

definition "history op lxs lys =
  (\<exists> ios. traced op ios \<and>
  (\<forall> p. lprefix (lproject (=) \<bottom> ios p) (lxs p)) \<and> lys = lproject \<bottom> (=) ios)"

corec produce_trace where
  "produce_trace op lxs = (case op of
    Read p f \<Rightarrow> LCons (Inp p (CHD p lxs)) (produce_trace (f (CHD p lxs)) (CTL p lxs))
  | Write op' p x \<Rightarrow> LCons (Out p x) (produce_trace op' lxs)
  | End \<Rightarrow> LNil)"

simps_of_case produce_trace_simps[simp]: produce_trace.code

lemma lset_produce_trace_not_LNil:
  "r \<in> lset (produce_trace op lxs) \<Longrightarrow>
   r = (Inp p x) \<Longrightarrow>
   x \<noteq> EOS \<Longrightarrow>
   lxs p \<noteq> LNil"
  apply (induct "produce_trace op lxs" arbitrary: op lxs rule: lset_induct[where x=r])
  subgoal for xs op lxs
    apply hypsubst_thin
    apply (cases op)
      apply (auto split: op.splits)
    done
  subgoal for x xs op lxs
    apply hypsubst_thin
    apply (cases op)
      apply (auto split: op.splits)
     apply fastforce
    apply (metis fun_upd_other fun_upd_same ltl_simps(1))
    done
  done

lemma lset_produce_trace_lhd:
  "(Inp p (Observed x)) \<in> lset (produce_trace op lxs) \<Longrightarrow>
   lhd (lproject (=) \<bottom> (produce_trace op lxs) p) = lhd (lxs p)"
  apply (induct "produce_trace op lxs" arbitrary: op lxs rule: lset_induct)
  subgoal for xs op lxs
    apply (cases op)
      apply (auto split: op.splits)
    apply (smt (verit, best) chd.elims eq_LConsD lproject_LCons(1) observation.disc(3) observation.discI)
    done
  subgoal for x xs op lxs
    apply (cases op)
      apply (auto split: op.splits)
    apply (smt (verit, best) chd.elims eq_LConsD fun_upd_other fun_upd_same
       lproject_LCons_False lproject_LCons_True lset_produce_trace_not_LNil ltl_simps(1) observation.disc(1) observation.sel)
    done
  done
(* 
lemma EOB_not_ind_produce_trace[simp]:
  "(Inp p EOB) \<notin> lset (produce_trace op lxs)"
  unfolding not_def
  apply (rule impI)
  apply (induct "produce_trace op lxs" arbitrary: op lxs rule: lset_induct)
  subgoal for xs op lxs
    apply (cases op)
      apply (auto simp add: split_beta split: observation.splits prod.splits)
    apply (metis chd.elims observation.simps(3) observation.simps(7))
    done
  subgoal for x xs op lxs
    apply (cases op)
      apply (auto simp add: split_beta split: observation.splits prod.splits)
    done
  done *)

inductive input_along where
  "input_along p (Read p f) lxs"
| "p \<noteq> p' \<Longrightarrow> input_along p (f (CHD p' lxs)) (CTL p' lxs) \<Longrightarrow> input_along p (Read p' f) lxs"
| "input_along p op' lxs \<Longrightarrow> input_along p (Write op' p' x) lxs"

lemma input_along_evidence:
  "(Inp p (Observed x)) \<in> lset (produce_trace op lxs) \<Longrightarrow>
   input_along p op lxs"
  apply (induct "produce_trace op lxs" arbitrary: op lxs rule: lset_induct)
  subgoal for xs op lxs
    apply (cases op)
      apply (auto intro: input_along.intros)
    done
  subgoal for x' xs op lxs
    apply (cases op)
      apply (auto intro: input_along.intros)
    done
  done

lemma in_Out_produce_trace_in_produce:
  "(Out p x) \<in> lset (produce_trace op lxs) \<Longrightarrow>
   x \<in> lset (produce op lxs p)"
  apply (induct "produce_trace op lxs" arbitrary: op lxs rule: lset_induct)
  subgoal for xs op lxs
    apply (cases op)
      apply auto
    done
  subgoal for x' xs op lxs
    apply (cases op)
      apply auto
    done
  done

inductive output_along where
  "output_along p (Write op p x) lxs x"
| "output_along p (f (CHD p' lxs)) (CTL p' lxs) x \<Longrightarrow> output_along p (Read p' f) lxs x"
| "output_along p op' lxs x \<Longrightarrow> x \<noteq> y \<Longrightarrow> output_along p (Write op' p y) lxs x"
| "output_along p op' lxs x \<Longrightarrow> p \<noteq> p' \<Longrightarrow> output_along p (Write op' p' y) lxs x"

lemma output_along_produce_trace:
  "output_along p op lxs x \<Longrightarrow>
   (Out p x) \<in> lset (produce_trace op lxs)"
  apply (induct p op lxs x rule: output_along.induct)
    apply (auto simp flip: fun_upd_apply split: if_splits)
  done

lemma producing_in_produce_in_produce_trace_Out:
  "producing p op lxs n \<Longrightarrow>
   produce op lxs p = LCons x lys \<Longrightarrow>
   (Out p x) \<in> lset (produce_trace op lxs)"
  apply (induct op lxs n rule: producing.induct)
     apply auto
  done

lemma in_produce_trace_output_along:
  "(Out p x) \<in> lset (produce_trace op lxs) \<Longrightarrow>
   output_along p op lxs x"
  apply (induct "produce_trace op lxs" arbitrary: op lxs rule: lset_induct)
  subgoal for xs op lxs
    apply (cases op)
      apply (auto intro: output_along.intros)
    done
  subgoal for x' xs op lxs
    apply (cases op)
      apply (auto intro: output_along.intros)
    done
  done

lemma in_produce_output_along:
  "produce op lxs p = LCons x lys \<Longrightarrow>
   output_along p op lxs x"
  apply (induct  rule: produce_inner_induct[where p=p and op=op and lxs=lxs])
  subgoal for op lxs p
    apply (subst (asm) (3) produce.code)
    apply (auto simp del: produce_simps split: if_splits op.splits intro: producing.intros output_along.intros)
    done
  done

lemma producing_trace_lhd_output:
  "producing p op lxs n \<Longrightarrow> 
   \<not> lnull (produce_trace op lxs) \<Longrightarrow>
   lhd (lproject \<bottom> (=) (produce_trace op lxs) p) = lhd (produce op lxs p)"
  apply (induct op lxs n rule: producing.induct)
     apply auto
  apply (metis llist.collapse(1) lproject_LNil lset_cases neq_LNil_conv producing_in_produce_in_produce_trace_Out)
  apply (metis empty_iff llist.collapse(1) llist.exhaust_sel lproject_LNil lset_LNil producing_in_produce_in_produce_trace_Out)
  done

lemma lset_produce_trace_lhd_output:
  "(Out p x) \<in> lset (produce_trace op lxs) \<Longrightarrow>
   \<not> lnull (produce op lxs p) \<Longrightarrow>
   lhd (lproject \<bottom> (=) (produce_trace op lxs) p) = lhd (produce op lxs p)"
 apply (induct "produce_trace op lxs" arbitrary: op lxs rule: lset_induct)
  subgoal for xs op lxs
    unfolding lnull_def
    apply (subst produce.code)
    apply (subst (asm) produce.code)
    apply (auto split: op.splits if_splits intro:  producing.intros)
    done
  subgoal for x' xs op lxs
    apply (subst produce.code)
    apply (subst (asm) (3) produce.code)
    apply (auto split: op.splits if_splits intro:  producing.intros)
    done
  done
(* 
lemma history_produce:
  "history op lxs (produce op lxs)"
  unfolding history_def
  apply (rule exI[of _ "produce_trace op lxs"])
  apply (intro impI conjI allI)
  subgoal 
    apply (coinduction arbitrary: op lxs)
    subgoal for op lxs
      apply (cases op)
        apply simp_all
      subgoal for p' f
        apply (cases "CHD p' lxs")
          apply (auto elim: chd.elims)
        done
      subgoal for op' p' x
        apply auto
        done
      done
    done
  subgoal for p
    apply (coinduction arbitrary: op lxs rule: lprefix_coinduct)
    subgoal for op lxs
      apply (intro disjI1 impI conjI)
      subgoal
        by (auto simp add: lproject_empty_conv(1) lnull_def dest: lset_produce_trace_not_LNil intro: lproject_False elim!: chd.elims)
      subgoal
        by (auto simp add: lproject_empty_conv(1) lnull_def dest: lset_produce_trace_lhd intro: lproject_False elim!: chd.elims)
      subgoal
        apply (subgoal_tac "input_along p op lxs")
        subgoal
          apply (rotate_tac 2)
          apply (induct p op lxs rule: input_along.induct)
            apply simp_all
          apply (smt (verit, best) chd.elims fun_upd_same lnull_def lproject_LCons(1) ltl_simps(2))
          done
        subgoal
          using input_along_evidence lnull_def lproject_empty_conv(1)
          by (metis (mono_tags, lifting) bot2E)
        done
      done
    done
  subgoal
    apply (rule ext)
    subgoal for p
      apply (coinduction arbitrary: op lxs)
      subgoal for op lxs
        apply (intro impI context_conjI iffI)
        subgoal
          using in_Out_produce_trace_in_produce 
          by (metis (mono_tags, lifting) empty_iff llist.collapse(1) lproject_empty_conv(1) lset_LNil bot2E)
        subgoal
          by (metis (mono_tags, lifting) in_produce_output_along lhd_LCons_ltl llist.collapse(1) lproject_empty_conv(1) output_along_produce_trace)
        subgoal
          using lset_produce_trace_lhd_output
          by (metis (mono_tags, lifting) lnull_def lproject_False bot2E)
        subgoal
          apply (subgoal_tac "output_along p op lxs (lhd (produce op lxs p))")
          subgoal
            apply (rotate_tac 2)
            apply (rotate_tac 2)
            apply (induct p op lxs "lhd (produce op lxs p)" rule: output_along.induct)
               apply simp_all
            apply blast
            done
          subgoal
            by (metis in_produce_output_along lhd_LCons_ltl)
          done
        done
      done
    done
  done
 *)
*)


section\<open>Buffer infrastrcuture\<close>

datatype 'd buf = BEmpty | BEnded | BCons 'd "'d buf"

fun bhd where
  "bhd BEmpty = None"
| "bhd BEnded = Some EOS"
| "bhd (BCons x xs) = Some (Observed x)"

fun btl where
  "btl BEmpty = BEmpty"
| "btl BEnded = BEnded"
| "btl (BCons x xs) = xs"

fun bend where
  "bend BEmpty = BEnded"
| "bend BEnded = BEnded"
| "bend (BCons xs xss) = BCons xs (bend xss)"

lemma bend_assoc[simp]:
  "bend \<circ> (bend \<circ> buf) = (bend \<circ> bend) \<circ> buf"
  using fun.map_comp by blast

lemma bend_bend[simp]:
  "(bend \<circ> bend) = bend"
  apply (rule ext)
  subgoal for buf
    apply (induct buf)
      apply auto
    done
  done

lemma bend_fun_upd[simp]:
  "(bend \<circ> buf)(p := bend xs) = bend \<circ> buf(p := xs)"
  by (simp add: fun_upd_comp)

lemma btl_bend:
  "btl (bend buf) = bend (btl buf)"
  by (metis bend.elims btl.simps(1) btl.simps(2) btl.simps(3))

fun benq where
  "benq x BEmpty = BCons x BEmpty"
| "benq x BEnded = BCons x BEnded"
| "benq x (BCons y ys) = BCons y (benq x ys)"

abbreviation BHD :: "'a \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> 'd observation option" where "BHD p buf \<equiv> bhd (buf p)"
abbreviation (input) BUPD where "BUPD f p buf \<equiv> buf(p := f (buf p))"
abbreviation BTL :: "'a \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BTL \<equiv> BUPD btl"
abbreviation BENQ :: "'a \<Rightarrow> 'd \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BENQ p x buf \<equiv> BUPD (benq x) p buf"
abbreviation BENQ_TL :: "'a \<Rightarrow> 'd \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BENQ_TL p x buf \<equiv> BUPD (btl o benq x) p buf"

lemma BHD_neq_None_bend:
  "BHD p buf \<noteq> None \<Longrightarrow> BHD (buf p) bend = BHD p buf"
  apply (induct "buf p")
    apply auto[1]
   apply simp
  apply (metis bend.simps(3) bhd.simps(3))
  done

fun bapp where
  "bapp BEmpty lxs = lxs"
| "bapp BEnded lxs = LNil"
| "bapp (BCons x xs) lxs = LCons x (bapp xs lxs)"

definition "extend A buf R lxs lys =
  (\<exists>lzs. R lxs (case_sum (lys o Inl) lzs) \<and> (\<forall>p. lys (Inr p) = (if p \<in> A then bapp (buf p) (lzs p) else lzs p)))"

lemma extend_empty: "extend {} buf R = R"
  using arg_cong2[of x x "case_sum (f o Inl) (f o Inr)" f R for x f, unfolded o_def, OF refl surjective_sum]
  by (auto simp: extend_def o_def fun_eq_iff[of "extend _ _ _"] fun_eq_iff[of "extend _ _ _ _"]
      simp flip: fun_eq_iff split: sum.splits)

section\<open>Well-typed\<close>

coinductive dwelltyped and nwelltyped where
  "nwelltyped A B (f EOS) \<Longrightarrow> \<forall>x \<in> A p. nwelltyped A B (f (Observed x)) \<Longrightarrow> dwelltyped A B (Read p f)"
| "x \<in> B p \<Longrightarrow> nwelltyped A B op \<Longrightarrow> dwelltyped A B (Write op p x)"
| "(\<forall>ops |\<in>| ops. dwelltyped A B op) \<Longrightarrow> nwelltyped A B (Choice ops)"

inductive_cases welltyped_ReadE[elim!]: "dwelltyped A B (Read p f)"
inductive_cases welltyped_WriteE[elim!]: "dwelltyped A B (Write op q x)"
inductive_cases welltyped_ChoiceE[elim!]: "nwelltyped A B (Choice ops)"
  (*
(*characteristic property of welltyped*)
lemma "x \<in> lset (lproject (=) lxs (Out q)) \<Longrightarrow> traced m op lxs \<Longrightarrow> welltyped A B op \<Longrightarrow> \<forall>p. lset (lproject (=) lxs (Inp p)) \<subseteq> A p \<Longrightarrow> x \<in> B q"
  apply (induct x "lproject (=) lxs (Out q)" arbitrary: m op lxs rule: llist.set_induct)
   apply (erule traced.cases; auto split: if_splits)
  oops
*)

section\<open>Convenient types\<close>

type_synonym 'd dop22 = "(2, 2, 'd) dop"
type_synonym 'd dop11 = "(1, 1, 'd) dop"
type_synonym 'd nop22 = "(2, 2, 'd) nop"
type_synonym 'd nop11 = "(1, 1, 'd) nop"

end
