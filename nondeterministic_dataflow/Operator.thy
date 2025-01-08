text \<open>Operators, trace model, history model, cleaned predicate, and welltyped predicate\<close>

theory Operator

imports
  Linear_Temporal_Logic_on_Llists
  "HOL-Library.BNF_Corec"
  "HOL-Library.Code_Lazy"
  "HOL-Library.Numeral_Type"
  "HOL-Library.Code_Cardinality"
  "HOL-Library.Simps_Case_Conv"
  "HOL-Library.Countable_Set_Type"
begin

section \<open>cset Syntax\<close>
syntax
  "_insert_fset"     :: "args => 'a cset"  ("{|(_)|}")

notation cempty ("{||}")

translations
  "{|x, xs|}" == "CONST cinsert x {|xs|}"
  "{|x|}"     == "CONST csingle x"

abbreviation cmember :: "'a \<Rightarrow> 'a cset \<Rightarrow> bool" (infix "|\<in>|" 50) where
  "x |\<in>| X \<equiv> cin x X"

section \<open>cset lifts\<close>
context includes cset.lifting begin
lift_definition natcUNIV :: "nat cset" is UNIV by auto
lift_definition cproduct :: "'a cset \<Rightarrow> 'b cset \<Rightarrow> ('a \<times> 'b) cset" is "(\<times>)" by auto
lift_definition cfilter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a cset \<Rightarrow> 'a cset" is Set.filter by (simp add: Set.filter_def)
lift_definition cUNIV :: "('m :: countable) cset" is UNIV by auto

end

declare cBall.rep_eq[simp] cinsert.rep_eq[simp] bot_cset.rep_eq[simp] sup_cset.rep_eq[simp] cimage.rep_eq[simp] cUnion.rep_eq[simp] rel_cset.rep_eq[simp]
  cfilter.rep_eq[simp]

lemma cfilter_eq[simp]:
  "cfilter P A = B \<longleftrightarrow>
   Set.filter P (cset.rcset A) = (cset.rcset B)"
  by (auto simp add: cin.rep_eq)

lemma cin_cfilter[simp]:
  "x |\<in>| cfilter P A \<longleftrightarrow> x |\<in>| A \<and> P x"
  by (metis cfilter.rep_eq cin.rep_eq member_filter)


lemma cin_cimage_cfilter[simp]:
  "x |\<in>| cimage f (cfilter P A) \<longleftrightarrow> (\<exists> y. y |\<in>| A \<and> P y \<and> x = f y)"
  by auto

lemma cUnion_cempty[simp]:
  "cUnion {||} = {||}"
  using cUN_empty by auto

lemma cfilter_cempty[simp]:
  "cfilter P {||} = {||}"
  by auto

lemma cfilter_cfilter[simp]:
  "cfilter P (cfilter P S) = cfilter P S"
  by force


lemma cUnion_cinsert[simp]:
  "cUnion (cinsert x A) = cUn x (cUnion A)"
  apply (subst (3 8) cset.map_id[symmetric])
  apply (metis cUN_cinsert eq_id_iff)
  done

section\<open>Channels\<close>

code_lazy_type llist

section\<open>Buffer infrastrcuture\<close>

type_alias buf = list

abbreviation "bhd \<equiv> hd"
abbreviation "btl \<equiv> tl"
abbreviation "benq x xs \<equiv> xs @ [x]"

abbreviation BHD :: "'a \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> 'd" where "BHD p buf \<equiv> bhd (buf p)"
abbreviation (input) BUPD where "BUPD f p buf \<equiv> buf(p := f (buf p))"
abbreviation BTL :: "'a \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BTL \<equiv> BUPD btl"
abbreviation BENQ :: "'a \<Rightarrow> 'd \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BENQ p x buf \<equiv> BUPD (benq x) p buf"
abbreviation BENQ_TL :: "'a \<Rightarrow> 'd \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BENQ_TL p x buf \<equiv> BUPD (btl o benq x) p buf"

(* fun buf_len where
  "buf_len BEmpty = 0"
| "buf_len BEnded = 0"
| "buf_len (BCons x buf) = Suc (buf_len buf)"

lemma buf_len_btl:
  "0 < buf_len buf \<Longrightarrow>
   buf_len (btl buf) < buf_len buf"
  by (induct buf) auto *)

abbreviation "bulk_benq xs ys \<equiv> ys @ xs"

abbreviation BULK_BENQ (infixr ">>" 65) where "BULK_BENQ buf1 buf2 \<equiv> (\<lambda> p. bulk_benq (buf1 p) (buf2 p))"

lemma BULK_BENQ_assoc:
  "buf1 >> (buf2 >> buf3) = (buf1 >> buf2) >> buf3"
  by auto

lemma BULK_BENQ_bulk_benq:
  "(buf1 >> buf2) p = bulk_benq (buf1 p) (buf2 p)"
  by auto

(* 
definition "extend A buf R lxs lys =
  (\<exists>lzs. R lxs (case_sum (lys o Inl) lzs) \<and> (\<forall>p. lys (Inr p) = (if p \<in> A then bapp (buf p) (lzs p) else lzs p)))"

lemma extend_empty: "extend {} buf R = R"
  using arg_cong2[of x x "case_sum (f o Inl) (f o Inr)" f R for x f, unfolded o_def, OF refl surjective_sum]
  by (auto simp: extend_def o_def fun_eq_iff[of "extend _ _ _"] fun_eq_iff[of "extend _ _ _ _"]
      simp flip: fun_eq_iff split: sum.splits)

lemma set_buf_benq[simp]:
  "set_buf (benq x xs) = insert x (set_buf xs)"
  apply (induct x xs rule: benq.induct)
    apply auto
  done *)

section\<open>Operator\<close>

codatatype (inputs: 'ip, outputs: 'op, dead 'd) op =
  Read 'ip "'d \<Rightarrow> ('ip, 'op, 'd) op"
  | Write "('ip, 'op, 'd) op" 'op 'd
  | Choice "('ip, 'op, 'd) op cset"
  | Silent "('ip, 'op, 'd) op"

subsection\<open>Basic Operators\<close>

corec spin_op :: "('a, 'b, 'd) op" ("\<otimes>") where
  "spin_op = Choice (cimage (\<lambda> _. spin_op) (csingle ()))"

abbreviation end_op ("\<oslash>") where "end_op \<equiv> Choice cempty"
abbreviation "ARead i f op \<equiv> Choice (cimage (\<lambda> x. if x then op else Read i f) (cinsert True (csingle False)))"
lemma ARead_simp[simp]: "ARead i f op = Choice ({| op, Read i f |})"
  by simp

abbreviation "safe_choice_stop stop f ops \<equiv> (if ops = cempty then stop else Choice (cimage f ops))"
abbreviation "safe_choice f \<equiv> safe_choice_stop (f end_op) f"
abbreviation "safe_choice2 f op1s op2s \<equiv> (if op1s = cempty \<and> op2s = cempty then end_op
  else if op1s = cempty then Choice (cimage (f end_op) op2s)
  else if op2s = cempty then Choice (cimage (\<lambda>op1. f op1 end_op) op1s)
  else Choice (cimage (case_prod f) (cproduct op1s op2s)))"
abbreviation "choice1 op \<equiv> Choice (cimage (\<lambda>_. op) {|()|})"
abbreviation "choice2 op1 op2 \<equiv> Choice (cimage (\<lambda>b. if b then op1 else op2) (cinsert True (csingle False)))"
abbreviation "safe_read f x \<equiv> (case x of None \<Rightarrow> end_op | Some x \<Rightarrow> f x)"

datatype (discs_sels) ('m, 'd) id_op_aux =
  id_Read_aux "'m" "'d \<Rightarrow> ('m \<Rightarrow> 'd buf)"
  | id_Write_aux "('m \<Rightarrow> 'd buf)" "'m" 'd

abbreviation eval_id_op_aux where
  "eval_id_op_aux c aux \<equiv> (case aux of
    id_Read_aux p f \<Rightarrow> Read p (\<lambda>y. let buf = f y in c buf)
  | id_Write_aux buf q x \<Rightarrow> Write (c buf) q x)"

corec id_op :: "_ \<Rightarrow> ('m :: countable, 'm, 'd) op" where
  "id_op buf = Choice (cimage (eval_id_op_aux id_op) (cUn 
    (cimage (\<lambda> p. id_Read_aux p (\<lambda> x. BENQ p x buf)) (cUNIV :: 'm cset)) 
    (cimage (\<lambda> p. id_Write_aux (BTL p buf) p (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (cUNIV :: 'm cset)))))"


lemma id_op_code:
  "id_op buf = Choice (cUn 
    (cimage (\<lambda> p. Read p ((\<lambda> x. id_op (BENQ p x buf)))) (cUNIV :: 'm cset))
    (cimage (\<lambda> p. Write (id_op (BTL p buf)) p  (BHD p buf)) (cfilter (\<lambda> p. buf p \<noteq> []) (cUNIV :: ('m :: countable) cset))))"
  apply (subst id_op.code)
  apply (unfold cimage_cUn cimage_cinsert op.inject)
  apply simp
  apply (rule arg_cong2[where f = cUn])
  apply (auto simp add: cset.map_comp o_def cimage_cUn intro!: arg_cong2[where f = cUn] cimage_cong
      split: id_op_aux.splits op.splits option.splits)
  done

corec cp_op :: "(1, 1, 'd) op" where
  "cp_op = Read 1 (Write cp_op 1)"

corec W :: "(1, 1, nat) op" where
  "W = Write W 1 42"

corec AW :: "('b, 1, nat) op" where
  "AW = choice2 AW (Write AW 1 42)"

corec dummy_source_op :: "_ \<Rightarrow> (1,'m :: countable, nat) op" where
  "dummy_source_op x = Choice (cimage (\<lambda> p. Write (dummy_source_op x) p x) (cUNIV :: 'm cset))"

corec sink_op :: "(1, 'b, 'd) op" where
  "sink_op = Read 1 (\<lambda>_. sink_op)"

type_synonym 'd channel = "'d llist"

code_lazy_type op

section \<open>Sub operators\<close>

declare cin.rep_eq[simp]

inductive sub_op :: \<open>('ip, 'op, 'd) op \<Rightarrow> ('ip, 'op, 'd) op \<Rightarrow> nat \<Rightarrow> bool\<close> for op where
  sub_op_Refl: \<open>sub_op op op 0\<close>
| sub_op_Read: \<open>sub_op op (f x) n \<Longrightarrow> sub_op op (Read p f) (Suc n)\<close>
| sub_op_Write: \<open>sub_op op op' n \<Longrightarrow> sub_op op (Write op' p x) (Suc n)\<close>
| sub_op_Choice: \<open>cin op' ops \<Longrightarrow> sub_op op op' n \<Longrightarrow> sub_op op (Choice ops) (Suc n)\<close>

inductive_cases sub_op_ReflE [elim!]: \<open>sub_op op op n\<close>
inductive_cases sub_op_ReadE [elim!]: \<open>sub_op op (Read p f) n\<close>
inductive_cases sub_op_WriteE [elim!]: \<open>sub_op op (Write op' p x) n\<close>   
inductive_cases sub_op_ChoiceE [elim!]: \<open>sub_op op (Choice ops) n\<close>   

(* lemma inputs_sub_op_Read: \<open>p \<in> inputs op \<Longrightarrow> \<exists>f n. sub_op (Read p f) op n\<close>
  by (induct op pred: inputs) (force intro: sub_op.intros)+

lemma sub_op_Read_inputs: \<open>sub_op (Read p f) op n \<Longrightarrow> p \<in> inputs op\<close>
  by (induct op n pred: sub_op) auto

lemma outputs_sub_op_Write: \<open>p \<in> outputs op \<Longrightarrow> \<exists>op' x n. sub_op (Write op' p x) op n\<close>
  by (induct op pred: outputs) (force intro: sub_op.intros)+
 *)

lemma sub_op_Write_outputs: \<open>sub_op (Write op' p x) op n \<Longrightarrow> p \<in> outputs op\<close>
  by (induct op n pred: sub_op) auto

lemma sub_op_Read_induct [consumes 1, case_names Read1 Read2 Write Choice]:
  assumes \<open>sub_op (Read p g) op d\<close>
    and \<open>\<And>f p. P p (Read p f)\<close>
    and \<open>\<And>p p' f x d g. sub_op (Read p g) (f x) d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Read p g) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Read p' f)\<close>
    and \<open>\<And>p p' op' x d g. sub_op (Read p g) op' d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Read p g) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Write op' p' x)\<close>
    and \<open>\<And>p p' ops x d g. \<exists>op'. cin op' ops \<and> sub_op (Read p g) op' d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Read p g) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Choice ops)\<close>
  shows \<open>P p op\<close>
  using assms(1)
proof (induct d arbitrary: op p rule: less_induct)
  case (less m)
  from this(2,1) show ?case
    by (induct op m pred: sub_op) (auto intro!: assms)
qed

lemma sub_op_Write_induct [consumes 1, case_names Read Write1 Choice Write2]:
  assumes \<open>sub_op (Write op2 p y) op d\<close>
    and \<open>\<And>p p' f x op2 y d. sub_op (Write op2 p y) (f x) d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Write op2 p y) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Read p' f)\<close>
    and \<open>\<And>p p' op' x op2 y d. sub_op (Write op2 p y) op' d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Write op2 p y) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Write op' p' x)\<close>
    and \<open>\<And>p op' op2 y d ops.  \<exists>op'. cin op' ops \<and> sub_op (Write op2 p y) op' d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Write op2 p y) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Choice ops)\<close>
    and \<open>\<And>p op' x. P p (Write op' p x)\<close>
  shows \<open>P p op\<close>
  using assms(1)
proof (induct d arbitrary: op p rule: less_induct)
  case (less m)
  from this(2,1) show ?case
    by (induct op m pred: sub_op) (auto intro!: assms)
qed

section\<open>Inputs measure\<close>

inductive input_at where
  "input_at p (Read p f) n"
| "p \<noteq> p' \<Longrightarrow> input_at p (f x) n \<Longrightarrow> input_at p (Read p' f) (Suc n)"
| "input_at p op' n \<Longrightarrow> input_at p (Write op' p' x) (Suc n)"
| "cin op' ops \<Longrightarrow> input_at p op' n \<Longrightarrow> input_at p (Choice ops) (Suc n)"
(* 

lemma inputs_input_at: "p \<in> inputs op \<Longrightarrow> \<exists>n. input_at p op n"
  by (induct p op rule: op.set_induct(1)) (auto 4 4 intro: input_at.intros)
 *)
lemma input_at_inputs: "input_at p op n \<Longrightarrow> p \<in> inputs op"
  by (induct p op n rule: input_at.induct) auto
(* 
lemma inputs_alt: "p \<in> inputs op \<longleftrightarrow> (\<exists>n. input_at p op n)"
  by (metis input_at_inputs inputs_input_at)
 *)
definition "input_depth p op = (LEAST n. input_at p op n)"

(* lemma input_depth_Read: "p \<in> inputs op \<Longrightarrow> input_depth p op = 0 \<longleftrightarrow> (\<exists>f. op = Read p f)"
  unfolding input_depth_def
  apply (cases op)
    apply (auto intro: input_at.intros Least_eq_0)
    apply (metis LeastI_ex Zero_not_Suc input_at.simps inputs_input_at op.inject(1))
   apply (metis LeastI_ex input_at.cases inputs_input_at op.set_intros(3) op.simps(4) zero_less_Suc)
  apply (metis LeastI_ex Zero_not_Suc input_at.cases inputs_alt op.set_intros(4) op.simps(7) zero_less_iff_neq_zero)
  done *)
(* 
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
 *)(* 
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
| "cin op' ops \<Longrightarrow> output_at p op' n \<Longrightarrow> output_at p (Choice ops) (Suc n)"

lemma outputs_output_at: "p \<in> outputs op \<Longrightarrow> \<exists>n. output_at p op n"
  by (induct p op rule: op.set_induct(2)) (auto 4 4 intro: output_at.intros)

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
datatype ('a, 'b, 'd) IO = Inp (proji: 'a) (data: "'d") | Out (projo: 'b) (data: 'd) | Tau

inductive step where
  "step (Read p f) (Inp p x) (f x)"
| "step (Write op q x) (Out q x) op"
| "step (Silent op) Tau op"
| "cin op ops \<Longrightarrow> step op l op' \<Longrightarrow> step (Choice ops) l op'"

inductive_cases stepReadE [elim!]: "step (Read p f) io op'"
inductive_cases stepWriteE [elim!]: "step (Write op q x) io op'"
inductive_cases stepSilentE [elim!]: "step (Silent op) io op'"
inductive_cases stepChoiceE [elim!]: "step (Choice ops) io op'"

lemma step_map_op:
  "step op io op' \<Longrightarrow> io' = map_IO f g id io \<Longrightarrow>
   step (map_op f g op) io' (map_op f g op')"
  by (induct op io op' rule: step.induct) (force simp add: comp_def intro: step.intros)+

lemma step_map_op_inv:
  "step (map_op f g op) io op' \<Longrightarrow>
   \<exists> io' op''. step op io' op'' \<and> io = map_IO f g id io' \<and> op' = map_op f g op''"
  apply (induct "map_op f g op" io op' arbitrary: op rule: step.induct)
     apply (auto intro: step.intros)
  subgoal for p fa x op
    apply (cases op)
       apply (auto 10 10 simp add: intro: step.intros)
    done
  subgoal for _ _ _ op
    apply (cases op)
       apply (auto 10 10 simp add: intro: step.intros)
    done
  subgoal for _  op
    apply (cases op)
       apply (auto 10 10 simp add: intro: step.intros)
    done
  subgoal for op ops l op' opa
    apply (cases opa)
       apply (force simp add: cimage.rep_eq intro: step.intros)+
    done
  done

definition "sim R s t = (\<forall>l s'. step s l s' \<longrightarrow> (\<exists>t'. step t l t' \<and> R s' t'))"

abbreviation "visible_step io op1 op2 \<equiv> (if io = Tau then False else step op1 io op2)"

abbreviation "tau_step op1 op2 \<equiv> step op1 Tau op2"

definition "wstep io = tau_step^** OO visible_step io OO tau_step^**"

definition "wsim R s t = (\<forall>l s'. wstep l s s' \<longrightarrow> (\<exists>t'. wstep l t t' \<and> R s' t'))"

lemma sim_mono[mono]: "R \<le> S \<Longrightarrow> sim R \<le> sim S"
  by (force simp: sim_def le_fun_def)

lemma wsim_mono[mono]: "R \<le> S \<Longrightarrow> wsim R \<le> wsim S"
  by (force simp: wsim_def le_fun_def)

coinductive wbisim (infix "\<approx>"40) where
  "wsim wbisim s t \<Longrightarrow> wsim wbisim t s \<Longrightarrow> wbisim s t"

inductive wbisim_cong for R where
  wbc_base:  "R x y \<Longrightarrow> wbisim_cong R x y"
| wbc_bisim:  "wbisim x y \<Longrightarrow> wbisim_cong R x y"
| wbc_refl: "x = y \<Longrightarrow> wbisim_cong R x y"
| wbc_sym: "wbisim_cong R x y \<Longrightarrow> wbisim_cong R y x"
| wbc_trans: "wbisim_cong R x y \<Longrightarrow> wbisim_cong R y z \<Longrightarrow> wbisim_cong R x z"
| wbc_Read:"x1 = y1 \<Longrightarrow> rel_fun (=) (wbisim_cong R) x2 y2 \<Longrightarrow> wbisim_cong R (Read x1 x2) (Read y1 y2)"
| wbc_Write: "wbisim_cong R x1 y1 \<Longrightarrow> wbisim_cong R (Write x1 x2 x3) (Write y1 x2 x3)"
| wbc_Silent: "wbisim_cong R x1 y1 \<Longrightarrow> wbisim_cong R (Silent x1) (Silent y1)"
| wbc_Choice:"rel_cset (wbisim_cong R) x y \<Longrightarrow> wbisim_cong R (Choice x) (Choice y)"

lemma wbisim_cong_disj:
  "(wbisim_cong R x y \<or> wbisim x y) = wbisim_cong R x y"
  by (auto intro: wbisim_cong.intros)

lemma trans_tau_Read:
  "tau_step\<^sup>*\<^sup>* (Read p f) op \<Longrightarrow> op = Read p f"
  apply (erule converse_rtranclpE)
   apply auto
  done
  
lemma trans_tau_Write:
  "tau_step\<^sup>*\<^sup>* (Write op p x) op \<Longrightarrow> op = Write op p x"
  apply (erule converse_rtranclpE)
   apply auto
  done

lemma wbisim_coinduct_upto:
  "R op1 op2 \<Longrightarrow>
   (\<And>s t. R s t \<Longrightarrow> wsim (wbisim_cong R) s t \<and> wsim (wbisim_cong R) t s) \<Longrightarrow>
   wbisim op1 op2"
  apply (rule wbisim.coinduct[where X="wbisim_cong R", unfolded wbisim_cong_disj, of op1 op2])
  subgoal
    by (auto intro: wbisim_cong.intros)
  subgoal premises prems for s' t'
    using prems(3) apply -
    apply (induct s' t' rule: wbisim_cong.induct)
    subgoal
      by (drule prems(2)) auto
    subgoal
      using wsim_mono[of wbisim "wbisim_cong R"]
      apply (auto simp: le_fun_def wbc_bisim elim: wbisim.cases)
      done
    subgoal
      by (auto intro: wbc_refl simp: wsim_def)
    subgoal
      by (fastforce)
    subgoal
      by (smt (verit, ccfv_threshold) wbc_trans wsim_def)
    subgoal
      apply (auto simp: rel_fun_def wstep_def wsim_def intro: wbc_Read wbc_sym step.intros dest!: trans_tau_Read)
      sorry
    subgoal
      sorry
    subgoal
      sorry
    subgoal
      sorry
    done
  done

coinductive finished where
  "(\<forall>op. op |\<in>|ops \<longrightarrow> finished op) \<Longrightarrow> finished (Choice ops)"

inductive_cases finished_ReadE[elim!]: "finished (Read p f)"
inductive_cases finished_WriteE[elim!]: "finished (Write op p x)"
inductive_cases finished_ChoiceE[elim!]: "finished (Choice ops)"

lemma finished_spin_op[simp]:
  "finished spin_op"
  apply coinduction
  apply (subst spin_op.code)
  apply auto
  done

lemma finished_end_op[simp]:
  "finished end_op"
  by coinduction blast

lemma Read_not_finished[simp]:
  "\<not> finished (Read p f)"
  by force
lemma Write_not_finished[simp]:
  "\<not> finished (Write op p x)"
  by force

inductive ends where
  "(\<forall>op. op |\<in>|ops \<longrightarrow> ends op) \<Longrightarrow> ends (Choice ops)"

lemma step_end_op[simp]: "step end_op l t' = False"
  by (auto simp: bot_cset.rep_eq)

lemma ends_no_step:
  "ends op \<Longrightarrow> (\<forall> io op'. \<not> step op io op')"
  by (induct op rule: ends.induct) auto

(* lemma ends_not_finished:
  "ends op \<Longrightarrow> \<not> finished op"
  by (induct op rule: ends.induct) (auto elim: finished.cases)
 *)

lemma step_not_finished: "step op l op' \<Longrightarrow> \<not> finished op"
  by (induct op l op' pred: step) (auto elim: finished.cases)

(* lemma not_finished_iff_step[simp]: "\<not> finished op \<longleftrightarrow> (\<exists>l op'. step op l op')"
  by (metis not_step_finished step_not_finished) *)


lemma step_exchange: "step op (Inp p x) op' \<Longrightarrow> \<exists>op'. step op (Inp p y) op'"
  apply (induct op "Inp p x :: ('a, 'b, 'c) IO" op' pred: step)
   apply (auto intro!: step.intros)
  done

lemma finished_is_spin_op:
  "finished op \<Longrightarrow>
   op = spin_op"
  apply (subst spin_op.code)
  apply (coinduction arbitrary: op rule: op.coinduct_upto)
  subgoal for op
    apply (cases op)
      apply clarsimp+
    apply (rule rel_setI)
    subgoal
      apply clarsimp
      apply (metis (mono_tags, lifting) cimage_cinsert cimage_is_cempty spin_op.code spin_op.cong_base)
      done
    subgoal
      apply clarsimp
      oops


inductive converges where
  "converges (Read p f)"
| "converges (Write op p x)"
| "op |\<in>| ops \<Longrightarrow> converges op \<Longrightarrow> converges (Choice ops)"

lemma sub_op_finished:
  "sub_op op' op n \<Longrightarrow> finished op \<Longrightarrow> finished op'"
  by (induct op n rule: sub_op.induct) auto
(* 
lemma finished_iff_all_sub_op_finished:
  "finished op \<longleftrightarrow> (\<forall> op' n. sub_op op' op n \<longrightarrow> finished op')"
  apply safe
  subgoal for op' n
    apply (induct n arbitrary: op op')
    subgoal for op op'
      apply (cases op)
        apply (auto intro: finished.intros)
      done
    subgoal for n op op'
      apply (cases op)
        apply (auto intro: finished.intros)
      done
    done
  subgoal
    using sub_op_Refl by blast
  done
 *)
(* 
lemma not_finished_stepes:
  "\<not> finished op \<Longrightarrow> \<exists> io op'. step op io op'"
  apply (erule contrapos_np)
  apply auto
  apply (coinduction arbitrary: op)
  subgoal for op
    apply (cases op)
      apply (auto intro: sub_op_Refl finished.intros step.intros)
     apply (meson cin.rep_eq step.intros(3))
    done
  done

lemma not_step_finished_or_can_end: "\<forall>l op'. \<not> step op l op' \<Longrightarrow> finished op \<or> can_end op"
  apply safe
  apply (coinduction arbitrary: op)
  subgoal for op
    apply (cases op)
      apply (force intro: step.intros)+
    done
  done *)
(* 
lemma no_can_end_ChoiceD: "\<not> can_end (Choice ops) \<Longrightarrow> (\<forall>op. op |\<in>| ops \<longrightarrow> (\<exists>l op'. step op l op'))"
  apply (erule contrapos_np)
  apply (coinduction arbitrary: ops)
  subgoal for ops
    apply (auto simp flip: cin.rep_eq intro: step.intros)
    oops

lemma finished_can_end:
  "finished op \<Longrightarrow> can_end op"
  by (metis (no_types, opaque_lifting) finished.simps ex_cin_conv can_end.coinduct)
 *)

coinductive bisim (infix "~"40) where
  "sim bisim s t \<Longrightarrow> sim bisim t s \<Longrightarrow> bisim s t"
(* 
lemma sim_finished_can_end_split:
  "sim bisim s t \<Longrightarrow> sim bisim t s \<Longrightarrow> can_end s \<and> \<not> finished s \<longleftrightarrow> can_end t \<and> \<not> finished t \<Longrightarrow> (can_end s \<longleftrightarrow> can_end t) \<and> (finished s \<longleftrightarrow> finished t)"
  apply (auto dest: finished_can_end)
     apply (metis finished_can_end not_step_finished_or_can_end sim_def step_not_finished)+
  done
 *)

inductive bisim_cong for R where
  bc_base:  "R x y \<Longrightarrow> bisim_cong R x y"
| bc_bisim:  "bisim x y \<Longrightarrow> bisim_cong R x y"
| bc_refl: "x = y \<Longrightarrow> bisim_cong R x y"
| bc_sym: "bisim_cong R x y \<Longrightarrow> bisim_cong R y x"
| bc_trans: "bisim_cong R x y \<Longrightarrow> bisim_cong R y z \<Longrightarrow> bisim_cong R x z"
| bc_Read:"x1 = y1 \<Longrightarrow> rel_fun (=) (bisim_cong R) x2 y2 \<Longrightarrow> bisim_cong R (Read x1 x2) (Read y1 y2)"
| bc_Write: "bisim_cong R x1 y1 \<Longrightarrow> x2 = y2 \<Longrightarrow> x3 = y3 \<Longrightarrow> bisim_cong R (Write x1 x2 x3) (Write y1 y2 y3)"
| bc_Choice:"rel_cset (bisim_cong R) x y \<Longrightarrow> bisim_cong R (Choice x) (Choice y)"

lemma bc_bisim_cong:
  "bisim x x' \<Longrightarrow> bisim y y' \<Longrightarrow> bisim_cong R x' y' \<Longrightarrow> bisim_cong R x y"
  by (meson bc_bisim bc_sym bc_trans)

lemma bisim_cong_disj:
  "(bisim_cong R x y \<or> bisim x y) = bisim_cong R x y"
  by (auto intro: bisim_cong.intros)

lemma bisim_coinduct_upto:
  "R s t \<Longrightarrow>
   (\<And>s t. R s t \<Longrightarrow> sim (bisim_cong R) s t \<and> sim (bisim_cong R) t s) \<Longrightarrow>
   s ~ t"
  apply (rule bisim.coinduct[where X="bisim_cong R", unfolded bisim_cong_disj, simplified])
  subgoal
    by (auto intro: bisim_cong.intros)
  subgoal premises prems for s' t'
    using prems(3) apply -
    apply (induct s' t' rule: bisim_cong.induct)
    subgoal
      by (drule prems(2)) auto
    subgoal
      using sim_mono[of bisim "bisim_cong R"]
      by (auto simp: le_fun_def bc_bisim elim: bisim.cases)
    subgoal
      by (auto intro: bc_refl simp: sim_def)
    subgoal
      by (fastforce intro: bc_sym)
    subgoal
      by (smt (verit, ccfv_threshold) bc_trans sim_def)
    subgoal
      by (auto simp: rel_fun_def sim_def intro: bc_sym step.intros)
    subgoal
      by (auto simp: rel_fun_def sim_def intro: bc_sym step.intros)
    subgoal
      unfolding rel_cset.rep_eq rel_set_def
      apply (auto simp: Ball_def Bex_def sim_def bot_cset.rep_eq
          simp flip: bot_cset.abs_eq cin.rep_eq
          dest!: arg_cong[where f="acset"] intro: step.intros)
      oops
(* 
lemma bisim_refl:
  "op1 ~ op1"
  by (coinduction rule: bisim_coinduct_upto) (auto intro: bc_refl simp: sim_def)

lemma bisim_sym:
  "op1 ~ op2 \<longleftrightarrow> op2 ~ op1"
  apply safe
  subgoal
    by (coinduction arbitrary: op1 op2 rule: bisim_coinduct_upto) 
      (smt (verit, del_insts) bc_sym bisim.cases bisim_cong.simps sim_def)
  subgoal
    by (coinduction arbitrary: op1 op2 rule: bisim_coinduct_upto) 
      (smt (verit, del_insts) bc_sym bisim.cases bisim_cong.simps sim_def)
  done

lemma bisim_trans:
  "op1 ~ op2 \<Longrightarrow> op2 ~ op3 \<Longrightarrow> op1 ~ op3"
  apply (coinduction arbitrary: op1 op2 op3 rule: bisim_coinduct_upto)
  apply (erule bisim.cases)+
  apply (unfold sim_def)
  apply (metis (no_types, lifting) bc_base)
  done
 *)

lemma bisim_Write_cong:
  "op1 \<approx> op2 \<Longrightarrow> Write op1 p x \<approx> Write op2 p x"
  sorry
(*   apply (coinduction arbitrary: op1 op2 rule: bisim_coinduct_upto)
  apply (erule bisim.cases)
  apply (unfold sim_def)
  apply clarsimp
  apply safe
   apply (metis (no_types, lifting) bc_bisim bisim.intros sim_def step.intros(2))+
  done *)

lemma bisim_Silent_cong:
  "op1 \<approx> op2 \<Longrightarrow> Silent op1 \<approx> Silent op2"
  sorry

 lemma bisim_Choice_cong:
  "rel_cset (\<approx>) ops1 ops2 \<Longrightarrow> Choice ops1 \<approx> Choice ops2"
   sorry
(*   apply (coinduction arbitrary: ops1 ops2 rule: bisim_coinduct_upto)
   apply (auto simp add: sim_def rel_cset.rep_eq rel_set_def)
  apply (smt (verit, ccfv_SIG) bc_bisim bisim.cases cin.rep_eq sim_def step.intros(3))
  apply (smt (verit, ccfv_SIG) bc_bisim bisim.cases cin.rep_eq sim_def step.intros(3))
   done *)

lemma bisim_Read_cong:
  "rel_fun (=) (\<approx>) f1 f2 \<Longrightarrow> Read p f1 \<approx> Read p f2"
  sorry
 (*  apply (coinduction arbitrary: f1 f2 rule: bisim_coinduct_upto)
  apply (auto simp add: sim_def rel_fun_def rel_set_def)
  subgoal for f1 f2 x
    apply (drule spec[of _ x])
    apply (erule bisim.cases)
    apply (unfold sim_def)
    apply clarsimp
    apply (metis (no_types, lifting) bc_bisim bisim.intros sim_def step.intros(1))+
    done
  subgoal for f1 f2 x
    apply (drule spec[of _ x])
    apply (erule bisim.cases)
    apply (unfold sim_def)
    apply clarsimp
    apply (metis (no_types, lifting) bc_bisim bisim.intros sim_def step.intros(1))+
    done
  done *)

lemma bisim_ReadI: "p = q \<Longrightarrow> \<forall>x. f x \<approx> g x \<Longrightarrow> Read p f \<approx> Read q g"
(*   by (coinduction) (auto simp: sim_def wbisim_sym elim!: step.cases intro: step.intros)
 *)
  sorry

lemma bisim_ReadD: "Read p f ~ Read q g \<Longrightarrow> p = q \<and> f x ~ g x"
  by (erule bisim.cases)
    (auto simp: sim_def dest: meta_spec2[of _ "Inp p x" "f x"] meta_spec2[of _ "Inp q x" "g x"] intro!: step.intros elim!: step.cases)

(* lemma bisim_Read_Read[simp]: "Read p f ~ Read q g \<longleftrightarrow> (p = q \<and> (\<forall>x. (f x) ~ (g x)))"
  by (metis bisim_ReadI bisim_ReadD) *)

(* lemma bisim_WriteI: "p = q \<Longrightarrow> x = y \<Longrightarrow> bisim op op' \<Longrightarrow> bisim (Write op p x) (Write op' q y)"
  by (coinduction) (auto simp: sim_def bisim_sym elim!: step.cases intro: step.intros)
 *)
lemma bisim_WriteD: "Write op p x ~ Write op' q y \<Longrightarrow> p = q \<and> y = x \<and> op ~ op'"
  by (erule bisim.cases)
    (auto simp: sim_def dest: meta_spec2[of _ "Out p x" "op"] meta_spec2[of _ "Out q y" op'] intro!: step.intros elim!: step.cases)
(* 
lemma bisim_Write_Write[simp]: "Write op p x ~ Write op' q y \<longleftrightarrow> (p = q \<and> y = x \<and> op ~ op')"
  by (metis bisim_WriteI bisim_WriteD)
 *)
lemma not_bisim[simp]:
  "\<not> bisim (Read p1 f1) (Write op p2 x)"
  "\<not> bisim (Write op p1' x) (Read p2' f2)"
  by (auto 10 10 simp: sim_def intro: step.intros elim: bisim.cases)

lemma bisim_Read_not_finished: "bisim (Read p f) op \<Longrightarrow> finished op \<Longrightarrow> False"
  by (metis bisim.cases sim_def step.intros(1) step_not_finished)

lemma bisim_Write_not_finished: "bisim (Write op' x p) op \<Longrightarrow> finished op \<Longrightarrow> False"
  by (metis bisim.cases sim_def step.intros(2) step_not_finished)

lemma simE:
  assumes "sim R s t" "step s l s'"
  obtains t' where "step t l t'" "R s' t'"
  using assms unfolding sim_def by auto

lemma sim_Read[simp]: "sim R (Read p f) op \<longleftrightarrow> (\<forall>x. \<exists>op'. step op (Inp p x) op' \<and> R (f x) op')"
  by (auto simp: sim_def intro!: step.intros(1))

lemma sim_Write[simp]: "sim R (Write op p x) op' \<longleftrightarrow> (\<exists>op''. step op' (Out p x) op'' \<and> R op op'')"
  by (auto simp: sim_def intro!: step.intros(2))

(* lemma sim_Choice[simp]: "sim R (Choice ops) t \<longleftrightarrow> (\<forall>op. op |\<in>| ops \<longrightarrow> sim R op t)"
  by (auto simp: sim_def simp flip: cin.rep_eq intro!: step.intros(3))
 *)
lemma sim_refl: "reflp R \<Longrightarrow> sim R s s"
  by (fastforce simp: sim_def reflp_def)

lemma sim_trans: "transp R \<Longrightarrow> sim R s t \<Longrightarrow> sim R t u \<Longrightarrow> sim R s u"
  by (fastforce simp: sim_def transp_def)
    (* 
lemma bisim_Choice_Read[simp]:
  "bisim (Choice ops) (Read p f) \<longleftrightarrow> (\<forall>op. op |\<in>| ops \<longrightarrow> bisim op (Read p f)) \<and> ops \<noteq> {||}"
  using bisim_sym bisim_Read_Choice by meson
 *)
    (* 
lemma bisim_Write_Choice[simp]:
  "bisim (Write op p x) (Choice ops) \<longleftrightarrow> (\<forall>op'. op' |\<in>| ops \<longrightarrow> bisim (Write op p x) op')  \<and> ops \<noteq> {||}"
  apply (safe intro!: context_conjI)
  subgoal for op
    apply (rule bisim.intros)
      apply (auto simp flip: cin.rep_eq)
    subgoal
      apply (erule bisim.cases)
      apply auto
      done
    subgoal
      apply (erule bisim.cases)
      apply (auto simp flip: cin.rep_eq)
        apply (erule contrapos_np)
      apply (drule no_can_end_ChoiceD)
      apply (drule spec, drule mp[of _ "Ex _"], assumption)
       apply (force simp: bisim_sym elim!: simE)
      apply (meson step_not_finished)
      done
    subgoal
      apply (erule bisim.cases)
      apply (auto simp flip: cin.rep_eq)
      done
    done
  subgoal
    apply (erule bisim.cases; auto)
    done
  subgoal for op
    apply (erule notE)
    apply (rule bisim.intros)
      apply (auto simp flip: cin.rep_eq)
    subgoal
      by (meson bisim.cases bisim_Write_not_finished)
    subgoal
      by (metis bisim.cases sim_Write step.intros(3))
    subgoal
      by (meson bisim.cases)
    done
  done *)


lemma step_spin_op_no_label:
  "step op l s \<Longrightarrow> op = spin_op \<Longrightarrow> False"
  apply (induct op l s arbitrary: l s rule: step.induct)
    apply (subst (asm) spin_op.code)
    apply simp
   apply (subst (asm) spin_op.code)
   apply simp
 (*  apply (clarsimp simp add: sup_cset.rep_eq cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq intro:; hypsubst_thin?)
  apply (metis cimage.rep_eq spin_op.code image_iff op.inject(3))
  done *)
  oops

    (* 
lemma bisim_Choice_Write[simp]:
  "bisim (Choice ops) (Write op p x) \<longleftrightarrow> (\<forall>op'. op' |\<in>| ops \<longrightarrow> bisim op' (Write op p x)) \<and> ops \<noteq> {||}"
  using bisim_Write_Choice bisim_sym by meson
 *)

    (* 
lemma W_AW_not_bisim: "\<not> bisim W AW"
  apply (rule notI)
  apply (erule bisim.cases)
  using can_end_AW not_can_end_op_W sim_finished_can_end_split apply blast
  done *)

lemma end_op_not_spin_op:
  "end_op \<noteq> spin_op"
  apply safe
  apply (subst (asm) spin_op.code)
  apply auto
  done
    (* 
lemma
  "\<not> bisim (Choice {| spin_op, W |}) W"
  apply (rule notI)
  apply (erule bisim.cases)
  apply (metis can_end_Choice cinsertI1 not_can_end_op_W sim_finished_can_end_split spin_op_can_end)
  done
 *)

(* lemma
  "\<not> bisim (Choice {| end_op, W |}) W"
  apply (rule notI)
  apply (erule bisim.cases)
  apply auto
  done *)

lemma spin_op_finished[simp]:
  "finished spin_op"
  apply coinduction
  apply (subst spin_op.code)
  apply (auto 0 0 simp add:  sup_cset.rep_eq cinsert.rep_eq cimage.rep_eq bot_cset.rep_eq; hypsubst_thin?)
  done

(* lemma end_op_not_bisim_spin_op:
  "bisim end_op spin_op \<Longrightarrow> False"
  apply (erule bisim.cases)
  apply auto
  done
 *)
(*
lemma bisim_ChoiceI: "rel_cset bisim ops1 ops2 \<Longrightarrow> bisim (Choice ops1) (Choice ops2)"
  apply (coinduction arbitrary: ops1 ops2)
  apply (clarsimp simp: rel_cset_def)
  apply safe
  subgoal for ops1 ops2 x op' op
  apply (drule rel_setD1)
    apply assumption
    apply (elim bexE)
    apply (erule bisim.cases)
    apply hypsubst_thin
    apply (drule meta_spec2, drule meta_mp, assumption)
    apply (elim exE conjE)
    apply (intro exI conjI)
     apply (rule step.intros(3))
    unfolding cin.rep_eq
      apply assumption+
    apply blast
    done
 subgoal for ops1 ops2 x op' op
  apply (drule rel_setD2)
    apply assumption
    apply (elim bexE)
    apply (erule bisim.cases)
    apply hypsubst_thin
    apply (drule meta_spec2, drule meta_mp, assumption)
    apply (elim exE conjE)
    apply (intro exI conjI)
     apply (rule step.intros(3))
    unfolding cin.rep_eq
      apply assumption+
    apply blast
    done
  done
*)

fun choices_at where
  "choices_at _ (Read p f) = csingle (Read p f)"
| "choices_at _ (Write op p x) = csingle (Write op p x)"
| "choices_at _ (Silent op) = csingle (Silent op)"
| "choices_at 0 (Choice ops) = cempty"
| "choices_at (Suc n) (Choice ops) = cUnion (cimage (choices_at n) ops)"

definition "choices op = cUnion (cimage (\<lambda>i. choices_at i op) natcUNIV)"

lemma choices_Read[simp]: "choices (Read p f) = csingle (Read p f)"
  unfolding choices_def by (auto simp: cset_eq_iff bot_cset.rep_eq natcUNIV.rep_eq)

lemma choices_Silent[simp]: "choices (Silent op) = csingle (Silent op)"
  unfolding choices_def by (auto simp: cset_eq_iff bot_cset.rep_eq natcUNIV.rep_eq)

lemma choices_Write[simp]: "choices (Write op p x) = csingle (Write op p x)"
  unfolding choices_def by (auto simp: cset_eq_iff bot_cset.rep_eq natcUNIV.rep_eq)

lemma choices_Choice[simp]: "choices (Choice ops) = cUnion (cimage choices ops)"
  apply (auto simp: choices_def cUnion.rep_eq cimage.rep_eq natcUNIV.rep_eq)
  subgoal for x n
    apply (induct n "Choice ops" arbitrary: ops rule: choices_at.induct)
     apply (auto simp: bot_cset.rep_eq cUnion.rep_eq cimage.rep_eq)
    done
  subgoal for x op n
    apply (rule exI[of _ "Suc n"])
    apply (auto simp: cUnion.rep_eq cimage.rep_eq)
    done
  done

lemma no_Choice_in_choices[simplified, simp, dest!]: "Choice ops |\<in>| choices op \<Longrightarrow> False"
  unfolding choices_def
  apply (auto simp: cUnion.rep_eq cimage.rep_eq natcUNIV.rep_eq)
  subgoal for n
    apply (induct n op rule: choices_at.induct)
(*        apply (auto simp: cinsert.rep_eq bot_cset.rep_eq cUnion.rep_eq cimage.rep_eq)
    done
  done *)
    oops


lemma choices_map_op[simp]:
  "cimage (map_op f g) (choices op) = choices (map_op f g op)"
  apply safe
  unfolding choices_def
   apply (clarsimp simp add: cUnion.rep_eq cimage.rep_eq natcUNIV.rep_eq)
  subgoal for x n
    apply (induct n arbitrary: op)
    subgoal for op
      apply (cases op)
        apply (auto simp add: bot_cset.rep_eq cinsert.rep_eq elim: finished.cases)
       done
    subgoal for n op
      apply (cases op)
        apply (auto simp add: bot_cset.rep_eq cinsert.rep_eq cUnion.rep_eq cimage.rep_eq elim: finished.cases)
      apply hypsubst_thin
      subgoal sorry
      done
    done
  subgoal for op'
    apply (clarsimp simp add: cUnion.rep_eq cimage.rep_eq natcUNIV.rep_eq)
    subgoal for n
      apply (induct n arbitrary: op)
      subgoal for op''
        apply (cases op'')
          apply (auto simp add: bot_cset.rep_eq cinsert.rep_eq elim: finished.cases)
        done
      subgoal for n op
        apply (cases op)
          apply (auto simp add: bot_cset.rep_eq cinsert.rep_eq cUnion.rep_eq cimage.rep_eq elim: finished.cases)
        apply hypsubst_thin
        apply (drule meta_spec)
        apply (drule meta_mp)
         apply assumption
        apply (auto simp add: bot_cset.rep_eq cinsert.rep_eq cUnion.rep_eq cimage.rep_eq elim: finished.cases)
        apply (rule image_eqI)
         apply (rule refl)
        apply (auto simp add: bot_cset.rep_eq cinsert.rep_eq cUnion.rep_eq cimage.rep_eq elim: finished.cases)
        subgoal sorry
      done
      done
    done
  done

lemma finished_choices_empty:
  "finished op \<Longrightarrow>
   choices op = {||}"
  apply safe
  unfolding choices_def
  apply (clarsimp simp add: cUnion.rep_eq cimage.rep_eq natcUNIV.rep_eq)
  subgoal for x n
    apply (induct n arbitrary: op)
    subgoal for op
      by (auto simp add: elim: finished.cases)
    subgoal for n op
      apply (cases op)
        apply (auto simp add: bot_cset.rep_eq elim: finished.cases)
      done
    done
  done

lemma choices_AW[simp]:
  "choices AW = {|Write AW 1 42|}"
  unfolding choices_def
  apply auto
  subgoal for x n
    sorry
  subgoal sorry
  done
(*    apply (induct n)
      apply (metis AW.code bot_cset.rep_eq choices_at.simps(3) emptyE)
    apply (subst (asm) (3) AW.code)
    apply (auto simp:sup_cset.rep_eq finished_choices_empty bot_cset.rep_eq cinsert.rep_eq cUnion.rep_eq cimage.rep_eq natcUNIV.rep_eq split: op.splits)
    done
  subgoal
    apply (auto simp:sup_cset.rep_eq finished_choices_empty bot_cset.rep_eq cinsert.rep_eq cUnion.rep_eq cimage.rep_eq natcUNIV.rep_eq split: op.splits)
    apply (subst (2) AW.code)
    apply auto
    apply (metis cUN_I choices_at.simps(2) choices_at.simps(4) cin.rep_eq cinsert_iff)
    done
  done *)

lemma choices_W[simp]:
  "choices W = {|Write W 1 42|}"
  unfolding choices_def
  apply auto
  subgoal for x n
    apply (induct n)
     apply (metis W.code bot_cset.rep_eq choices_at.simps(2) cinsert.rep_eq empty_iff insert_iff)
    apply (metis UNIV_I W.code natcUNIV.rep_eq choices_at.simps(2))
    done
  subgoal
    by (metis W.code natcUNIV.rep_eq choices_at.simps(2) cin.rep_eq csingleton_iff iso_tuple_UNIV_I)
  done

lemma bisim_map_op:
  "op \<approx> op' \<Longrightarrow> map_op f g op \<approx> map_op f g op'"
  sorry(* 
  apply (coinduction arbitrary: op op' rule: bisim_coinduct_upto)
  subgoal for op op'
    apply clarsimp
    apply (erule bisim.cases)
    subgoal for s t
      unfolding sim_def
      apply auto
      subgoal for l s'
        apply hypsubst_thin
        apply (drule step_map_op_inv[where f=f and g=g])
        apply auto
        apply (drule spec2)
        apply (drule mp)
        apply assumption
        apply auto
        apply hypsubst_thin
        apply (drule step_map_op[where f=f and g=g and op=t])
        apply (rule refl)
        apply (intro conjI exI)
        apply assumption
        apply (metis (mono_tags, lifting) bc_base bisim_sym)
        done
      subgoal for l s'
        apply hypsubst_thin
        apply rotate_tac
        apply (drule step_map_op_inv[where f=f and g=g])
        apply auto
        apply (drule spec2)
        apply (drule mp)
        apply assumption
        apply auto
        apply hypsubst_thin
        apply (drule step_map_op[where f=f and g=g and op=s])
        apply (rule refl)
        apply (intro conjI exI)
        apply assumption
        apply (metis (mono_tags, lifting) bc_base bisim_sym)
        done
      done
    done
  done *)

lemma choices_cp_op[simp]:
  "choices cp_op = {|Read 1 (Write cp_op 1)|}"
  unfolding choices_def
  apply auto
  subgoal for x n
    apply (induct n)
     apply (metis cp_op.code bot_cset.rep_eq choices_at.simps(1) cinsert.rep_eq empty_iff insert_iff)
    apply (metis cp_op.code UNIV_I natcUNIV.rep_eq choices_at.simps(1))
    done
  subgoal 
    by (metis cp_op.code natcUNIV.rep_eq choices_at.simps(1) cin.rep_eq csingleton_iff iso_tuple_UNIV_I)
  done

lemma in_choices_step:
  "op' |\<in>| choices op \<Longrightarrow>
   \<exists> io op''. step op' io op''"
  oops

lemma Read_in_choices_step:
  "Read p f |\<in>| choices op \<Longrightarrow> step op (Inp p x) (f x)"
  unfolding choices_def
  apply safe
  subgoal for n
    apply (induct n arbitrary: op)
    subgoal for op
      apply (cases op)
      by (auto simp: bot_cset.rep_eq cinsert.rep_eq step.intros(1))
    subgoal for n op
      apply (cases op)
        apply (auto simp: bot_cset.rep_eq cinsert.rep_eq step.intros(1))
      subgoal sorry
      done
    done
  done

lemma Read_in_choices_stepEx:
  "Read p f |\<in>| choices op \<Longrightarrow> \<exists> x. step op (Inp p x) (f x)"
  unfolding choices_def
  apply safe
  subgoal for n
    apply (induct n arbitrary: op)
    subgoal for op
      apply (cases op)
      by (auto simp: bot_cset.rep_eq cinsert.rep_eq step.intros(1))
    subgoal for n op
      apply (cases op)
        apply (auto simp: bot_cset.rep_eq cinsert.rep_eq step.intros(1))
      subgoal sorry
      done
    done
  done

lemma choices_spin_op[simp]:
  "choices spin_op = {||}"
  by (simp add: finished_choices_empty)

lemma choices_sink_op[simp]:
  "choices sink_op = {|Read 1 (\<lambda> _. sink_op)|}"
  unfolding choices_def
  apply safe
  subgoal premises prems for x n
    using prems(2) apply -
    apply (induct n)
     apply (subst (asm) sink_op.code)
     apply simp 
    apply (subst (asm) (3) sink_op.code)
    apply simp
    done
  subgoal for x
    apply auto
    apply (metis UNIV_witness natcUNIV.rep_eq choices_at.simps(1) cin.rep_eq cinsertI1 sink_op.code)
    done
  done

lemma Write_in_choices_step:
  "Write op' p x |\<in>| choices op \<Longrightarrow> step op (Out p x) op'"
  unfolding choices_def
  apply safe
  subgoal for n
    apply (induct n arbitrary: op)
    subgoal for op
      apply (cases op)
      by (clarsimp simp: step.intros(2) bot_cset.rep_eq cinsert.rep_eq intro: step.intros(2))+     
    subgoal for n op
      apply (cases op)
        apply (auto simp: bot_cset.rep_eq cinsert.rep_eq step.intros(2))
      subgoal sorry
      done
    done
  done

lemma step_choicesE:
  assumes  "step op io op'"
  obtains p f x where "io = Inp p x" "Read p f |\<in>| choices op" "op' = f x" |
   p x where "io = Out p x" "Write op' p x |\<in>| choices op" |
   "io = Tau" and "Silent op' |\<in>| choices op"
  apply (atomize_elim)
  using assms by (induct op io op' rule: step.induct) (auto 10 10 simp add: cinsert.rep_eq cUnion.rep_eq cimage.rep_eq)
(* 
lemma Choice_singleton_bisim:
  "Choice {|op|} ~ op"
  apply (rule bisim.intros)
  unfolding sim_def
   apply (auto intro: step.intros wbisim_refl)
  done

lemma choices_Choice_bisim:
  "choices op1 = choices op2  \<Longrightarrow>
   op1 ~ op2"
 apply (coinduction arbitrary: op1 op2 rule: bisim_coinduct_upto)
  unfolding sim_def
  apply (intro impI allI conjI)
  subgoal for op1 op2 l s'
    apply (erule step_choicesE)
    subgoal for p f x
      apply simp
      apply (meson Read_in_choices_step bc_refl cin.rep_eq)
      done
    subgoal
      apply simp
      apply (meson Write_in_choices_step bc_refl cin.rep_eq)
      done
    done
  subgoal
  apply (erule step_choicesE)
    subgoal for p f x
      apply simp
      apply (metis Read_in_choices_step bc_refl cin.rep_eq)
      done
    subgoal
      apply simp
      apply (metis Write_in_choices_step bc_refl cin.rep_eq)
      done
    done
  done
 *)

lemma step_no_inputs:
  "step op1 io op1' \<Longrightarrow> io = Inp p x \<Longrightarrow> inputs op1 = {} \<Longrightarrow> False"
  apply (induct op1 io op1' rule: step.induct)
    apply auto
  done

lemma step_no_inputs_not_inputs:
  "step op1 io op1' \<Longrightarrow> inputs op1 = {} \<Longrightarrow> inputs op1' = {}"
  apply (induct op1 io op1' rule: step.induct)
    apply auto
  done

lemma inputs_W[simp]:
  "inputs W = {}"
  apply safe
  subgoal for p
    apply (induct W rule: op.set_induct(1))
       apply (subst (asm) W.code, auto)+
    done
  done
(* 
lemma step_AW_inv:
  "step op io op' \<Longrightarrow>
   op = AW \<Longrightarrow>
   io = Out 1 42 \<and> op' = AW"
  apply (induct op io op' rule: step.induct)
  subgoal
    by (subst (asm) AW.code, auto intro: step.intros)
  subgoal
    by (subst (asm) AW.code, auto intro: step.intros)
  subgoal
    by (subst (asm) AW.code, auto intro: step.intros)
  done *)
(* 
lemma step_W_inv:
  "step op io op' \<Longrightarrow>
   op = W \<Longrightarrow>
   io = Out 1 42 \<and> op' = W"
  apply (induct op io op' rule: step.induct)
  subgoal
    by (subst (asm) W.code, auto intro: step.intros)
  subgoal
    by (subst (asm) W.code, auto intro: step.intros)
  subgoal
    by (subst (asm) W.code, auto intro: step.intros)
  done

lemma step_cp_op_inv:
  "step op io op' \<Longrightarrow>
   op = cp_op \<Longrightarrow>
   (\<exists> x. io = Inp 1 x \<and> op' = Write cp_op 1 x)"
  apply (induct op io op' rule: step.induct)
  subgoal for p f x
     apply (subst (asm) cp_op.code, auto intro: step.intros )+
    done
  subgoal
    apply (subst (asm) cp_op.code, auto intro: step.intros )+
    done
  subgoal
    apply (subst (asm) cp_op.code, auto intro: step.intros )+
    done
  done
 *)
(*
corec Choices where
  "Choices = Choice (cimage (\<lambda>_. Choices) (csingle ()))"

corec W where
  "W = Write W 1 42"

abbreviation "choice2 op1 op2 \<equiv> Choice (cimage (\<lambda>b. if b then op1 else op2) (cinsert True (csingle False)))"
corec AW where
  "AW = choice2 AW (Write AW 1 42)"

lemma [simp]: "may_diverge AW"
  apply (coinduction)
  apply (subst (2) AW.code)
  apply (auto simp: cinsert.rep_eq)
  done


lemma [simp]: "\<not> may_diverge W"
  apply (subst W.code)
  apply (auto)
  done

lemma "\<not> bisim W AW"
  apply (rule notI)
  apply (erule bisim.cases)
  apply (auto)
  done

lemma bisim_end_op_Choices: "bisim end_op Choices"
  apply (coinduction)
  apply auto
  subgoal for l op
    apply (induct "Choices :: ('a, 'b, 'c) op" l op rule: step.induct)
    apply (subst (asm) Choices.code; simp)
    apply (subst (asm) Choices.code; simp)
    apply (subst (asm) Choices.code; simp add: cinsert.rep_eq bot_cset.rep_eq)
    done
  done
*)
(*
lemma "bisim op1 op2 \<longleftrightarrow> ((may_diverge op1 \<longleftrightarrow> may_diverge op2) \<and> rel_cset bisim (choices op1) (choices op2))"
  apply safe
  subgoal
    apply (coinduction arbitrary: op1 op2)
    subgoal for op1 op2
      apply (erule bisim.cases)
      apply (erule may_diverge.cases)
       apply hypsubst_thin
      apply (metis bisim.intros finished.simps ex_cin_conv may_diverge.simps not_step_finished step_not_finished)
      apply hypsubst_thin
      apply (cases op2)
        apply auto
        apply (drule meta_spec2, drule meta_mp, rule step.intros(1)[where x = undefined])
      apply auto
        apply (drule meta_spec2, drule meta_mp, rule step.intros(3))
      apply auto
  apply auto

lemma bisim_ChoiceD: "bisim (Choice ops1) (Choice ops2) \<Longrightarrow> rel_cset bisim (choices ops1) (cfilter (Not o finished) ops2)"
  apply (erule bisim.cases)
  apply  (auto simp add: rel_cset.rep_eq cfilter.rep_eq rel_set_def Set.filter_def)
  subgoal premises prems for op1 io op1'
    using prems(4,3,1) apply -
    apply (induct op1 io op1' arbitrary: ops1 ops2 rule: step.induct)
    subgoal for p f x ops1 ops2
    apply (drule meta_spec2, drule meta_mp, rule step.intros(3))
    unfolding cin.rep_eq
      apply assumption
     apply (rule step.intros(1))
    apply auto
    subgoal for op2' op2
    apply (intro exI conjI)
        apply assumption+
      apply (cases op2)
      apply auto
      oops

  find_theorems   "rel_set _ _ _ \<Longrightarrow> _ \<Longrightarrow> _"

  apply (erule step.cases)
*)

coinductive traced where
  Nil: "finished op \<Longrightarrow> traced op LNil"
| Step: "step op l op' \<Longrightarrow> traced op' lxs \<Longrightarrow> traced op (LCons l lxs)"

inductive_cases traced_LNilE[elim!]: "traced op LNil"
inductive_cases traced_LConsE[elim!]: "traced op (LCons l lxs)"

lemma traced_Read[simp]: "traced (Read p f) lxs \<longleftrightarrow> (\<exists>x l lxs'. lxs = LCons l lxs' \<and> l = Inp p x \<and> traced (f x) lxs')"
  by (cases lxs) (auto intro: traced.intros step.intros)

lemma traced_LCons_iff: "traced op (LCons l lxs') \<longleftrightarrow> (\<exists>op'. step op l op' \<and> traced op' lxs')"
  by (auto intro: traced.intros)

definition "traces op = {lxs. traced op lxs}"

lemma finished_no_step:
  "finished op \<longleftrightarrow> \<not> (\<exists>io op'. step op io op')"
  apply (intro iffI)
  subgoal
    apply safe
    apply (erule finished.cases)
    using step_not_finished apply auto
    done
  subgoal
    apply (coinduction arbitrary: op)
    subgoal for op
      apply auto
      subgoal sorry
      done
    done
  done

lemma bisim_traced: "bisim op op' \<Longrightarrow> traced op lxs \<Longrightarrow> traced op' lxs"
  apply (coinduction arbitrary: op op' lxs) 
  subgoal for op op' lxs
    apply (erule bisim.cases)
    subgoal for s t
      apply (erule traced.cases)
      subgoal
        apply simp
        apply hypsubst_thin
        unfolding sim_def
        apply (meson finished_no_step)
        done
      subgoal
        by (metis simE)
      done
    done
  done

lemma bisim_traces: "wbisim op op' \<Longrightarrow> (traces op = traces op')"
  unfolding traces_def set_eq_iff mem_Collect_eq
  apply (intro iffI allI)
(*    apply (auto elim: bisim_traced dest: wbisim_sym[THEN iffD1]) [2]
  done *)
  sorry

inductive traced_cong for R where
  tc_base: "R op lxs \<Longrightarrow> traced_cong R op lxs"
| tc_traced: "traced op lxs \<Longrightarrow> traced_cong R op lxs"
| tc_read: "traced_cong R (f x) lxs \<Longrightarrow> traced_cong R (Read p f) (LCons (Inp p x) lxs)"
| tc_write: "traced_cong R op lxs \<Longrightarrow> traced_cong R (Write op q x) (LCons (Out q x) lxs)"
| tc_silent: "traced_cong R op lxs \<Longrightarrow> traced_cong R (Silent op) (LCons Tau lxs)"
| tc_choice: "cin op ops \<Longrightarrow> \<not> finished op \<Longrightarrow> traced_cong R op lxs \<Longrightarrow> traced_cong R (Choice ops) lxs"

lemma traced_cong_disj:
  "(traced_cong R op lxs \<or> traced op lxs) = traced_cong R op lxs"
  by (auto intro: traced_cong.intros)

thm traced.coinduct[where X = "traced_cong X", unfolded traced_cong_disj, of op ios]

lemma traced_coinduct_upto_step:
  assumes  "X op ios"
    "(\<And>x1 x2. X x1 x2 \<Longrightarrow>
     (\<exists>op. x1 = op \<and> x2 = LNil \<and> finished op) \<or> (\<exists>op l op' lxs. x1 = op \<and> x2 = LCons l lxs \<and> step op l op' \<and> traced_cong X op' lxs))"
  shows "traced op ios"
  apply (rule traced.coinduct[where X = "traced_cong X", unfolded traced_cong_disj, of op ios])
   apply (rule tc_base, rule assms(1))
  subgoal for op lxs
    apply (induct op lxs rule: traced_cong.induct)
    subgoal for op lxs
      apply (drule assms(2))
      apply (auto simp del: fun_upd_apply intro: step.intros)
      done
    subgoal for op lxs
      by (erule traced.cases)
        (auto 10 10 simp add: tc_traced simp del: fun_upd_apply)
    subgoal for p f x lxs
      by (auto simp del: fun_upd_apply intro: step.intros)
    subgoal for p n f 
      by (auto simp del: fun_upd_apply intro: step.intros)
    subgoal
      by (auto simp del: fun_upd_apply intro: step.intros)
    subgoal
      by (auto 10 10 simp add: step.intros(3) simp del: fun_upd_apply intro: step.intros)
    done
  done

lemma traced_coinduct_upto:
  assumes "X op lxs"
    "(\<And>x1 x2.
     X x1 x2 \<Longrightarrow>
    (\<exists>f x lxs p. x1 = Read p f \<and> x2 = LCons (Inp p x) lxs \<and> traced_cong X (f x) lxs) \<or>
    (\<exists>op lxs p x. x1 = Write op p x \<and> x2 = LCons (Out p x) lxs \<and> traced_cong X op lxs) \<or>
     (x2 = LNil \<and> finished x1))"
  shows "traced op lxs"
  apply (rule traced.coinduct[where X = "traced_cong X"])
   apply (rule tc_base, rule assms(1))
  subgoal for op lxs
    apply (induct op lxs rule: traced_cong.induct)
    subgoal for op lxs
      apply (drule assms(2))
      apply (auto simp del: fun_upd_apply intro: step.intros)
      done
    subgoal for op lxs
      by (erule traced.cases)
        (auto 10 10 simp add: tc_traced simp del: fun_upd_apply)
    subgoal for p f x lxs
      by (auto simp del: fun_upd_apply intro: step.intros)
    subgoal for p n f 
      by (auto simp del: fun_upd_apply intro: step.intros)
    subgoal
      by (auto simp del: fun_upd_apply intro: step.intros) 
    subgoal
      by (auto 10 10 simp add: step.intros(3) simp del: fun_upd_apply intro: step.intros)
    done
  done


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
  by (auto simp: traces_def intro: step.intros(2) traced.intros elim: traced.cases)

lemma traces_end_op[simp]:
  "traces end_op = {LNil}"
  by (auto simp: traces_def intro: finished.intros traced.intros step.intros elim: traced.cases)
    (* 
corec traced_wit where
  "traced_wit op = (case op of
    Read p f \<Rightarrow> LCons (Inp p EOS) (traced_wit (f EOS))
  | Write op' p' x \<Rightarrow> LCons (Out p' x) (traced_wit op')
  | end_op \<Rightarrow> LNil)"

lemma lset_traced_wit: "t \<in> lset (traced_wit op) \<Longrightarrow> (\<exists>p \<in> inputs op. t = (Inp p EOS)) \<or> (\<exists>q \<in> outputs op. \<exists>x. t = (Out q x))"
  apply (induction t "traced_wit op" arbitrary: op rule: llist.set_induct)
   apply (subst (asm) traced_wit.code)
   apply (auto split: op.splits) []
  apply (subst (asm) (2) traced_wit.code)
  apply (fastforce split: op.splits) []
  done

definition agree :: "('l \<Rightarrow> 'l' \<Rightarrow> bool) \<Rightarrow> ('l \<times> 'c) llist \<Rightarrow> ('l' \<times> 'c) llist \<Rightarrow> bool" where
  "agree R lxs lys = llist_all2 (rel_prod R (=)) (lfilter (Domainp R o fst) lxs) (lfilter (Rangep R o fst) lys)"
 *)
(* 
definition "lproject R S ios = (\<lambda>p. lmap data (lfilter (\<lambda>qx. case qx of Inp q (Observed x) \<Rightarrow> R p q | Out q x \<Rightarrow> S p q | _ \<Rightarrow> False) ios))" *)

(* lemma lproject_LNil[simp]: "lproject R S LNil = (\<lambda>p. LNil)"
  by (simp add: lproject_def) *)

(* lemma lproject_LCons[simp]: "lproject R S (LCons (Inp q (Observed x)) lxs) =
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
      split:  IO.splits)

lemma lproject_False: 
  "(\<And>q x. Inp q (Observed x) \<in> lset lxs \<Longrightarrow> \<not> R p q) \<Longrightarrow> (\<And>q x. Out q x \<in> lset lxs \<Longrightarrow> \<not> S p q) \<Longrightarrow> lproject R S lxs p = LNil"
  by (simp add: lproject_empty_conv)

lemma lproject_False_weak: 
  "(\<And>qx. qx \<in> lset lxs \<Longrightarrow> case_IO (\<lambda> q _. \<not> R p q) (\<lambda> q _. \<not> S p q) qx) \<Longrightarrow> lproject R S lxs p = LNil"
  by (force simp add: lproject_empty_conv)
 *)
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
(* 
section\<open>Cleaned predicate\<close>

coinductive cleaned where
  cleaned_Read[intro]: "p \<notin> inputs (f EOS) \<Longrightarrow> (\<And>x. cleaned (f x)) \<Longrightarrow>  cleaned (Read p f)"
| cleaned_Write[intro]: "cleaned op \<Longrightarrow> cleaned (Write op q x)"
| cleaned_end_op[iff]: "cleaned end_op"

inductive_cases cleaned_ReadE[elim!]: "cleaned (Read p f)"
inductive_cases cleaned_WriteE[elim!]: "cleaned (Write op q x)"
inductive_cases cleaned_end_opE[elim!]: "cleaned end_op"

inductive cleaned_cong for R where
  cc_base: "R op \<Longrightarrow> cleaned_cong R op"
| cc_cleaned: "cleaned op \<Longrightarrow> cleaned_cong R op"
| cc_read: "p \<notin> inputs (f EOS) \<Longrightarrow> (\<And>x. cleaned_cong R (f x)) \<Longrightarrow> cleaned_cong R (Read p f)"
| cc_write: "cleaned_cong R op \<Longrightarrow> cleaned_cong R (Write op q x)"

lemma cleaned_coinduct_upto: "X op \<Longrightarrow>
  (\<And>op. X op \<Longrightarrow> (\<exists>p f. op = Read p f \<and> p \<notin> inputs (f EOS) \<and> (\<forall>x. cleaned_cong X (f x))) \<or> (\<exists>op' q x. op = Write op' q x \<and> (cleaned_cong X op')) \<or> op = end_op) \<Longrightarrow>
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
  by (metis in_lset_ldropnD lset_intros(1)) *)

(* emma non_input_traces: "t \<in> lset lxs \<Longrightarrow> t = Inp p y \<Longrightarrow> p \<notin> inputs op \<Longrightarrow> lxs \<in> traces op \<Longrightarrow> False"
  apply (induct t lxs arbitrary: op rule: llist.set_induct)
  subgoal for t lxs op
    apply (cases op; auto)
    done
  subgoal for t lxs x op
    apply (cases op; auto split: nat.splits)
    done
  done
 
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
  apply (auto split: op.splits dest: lset_traced_wit simp: traced_wit.code[where op=end_op])
  done

lemma traced_wit_traces: "traced_wit op \<in> traces op"
  by (auto simp add: traced_traced_wit traces_def)

lemma traces_nonempty: "traces op \<noteq> {}"
  by (auto simp: traces_def intro!: traced_traced_wit)

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
  "producing p end_op lxs 0"
| "producing p (Write _ p _) lxs 0"
| "producing p (f (CHD p' lxs)) (CTL p' lxs) i \<Longrightarrow> producing p (Read p' f) lxs (Suc i)"
| "p \<noteq> p' \<Longrightarrow> producing p op lxs i \<Longrightarrow> producing p (Write op p' x) lxs (Suc i)"

inductive_cases producing_end_opE[elim!]: "producing p end_op lxs n"
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
  | end_op \<Rightarrow> LNil)"
  by (relation "measure (\<lambda>(op, lxs, p). THE i. producing p op lxs i)")
    (auto 0 3 simp: The_producing del: producing_ReadE producing_WriteE elim: producing.cases)

lemma produce_code[code]:
  "produce op lxs p = (case op of
    Read p' f \<Rightarrow> produce (f (CHD p' lxs)) (CTL p' lxs) p
  | Write op' p' x \<Rightarrow> (if p = p' then LCons x (produce op' lxs p) else produce op' lxs p)
  | end_op \<Rightarrow> LNil)"
  apply (subst produce.code)
  apply (simp split: op.splits if_splits)
  apply safe
  subgoal for p' f
    by (subst produce.code) (auto 0 5 split: op.splits intro: producing.intros)
  subgoal for op p x
    by (subst produce.code) (auto 0 4 split: op.splits intro: producing.intros)
  done
 
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
  done*)

(* lemma produced_produce: "produced m op lxs (produce op lxs)"
  apply (coinduction arbitrary: m op lxs)
  subgoal for m op lxs
    by (cases op) (force simp: muted_def muted_produce[unfolded muted_def])+
  done *)


section\<open>History model\<close>

(* definition "history op lxs lys =
  (\<exists> ios. traced op ios \<and>
  (\<forall> p. lprefix (lproject (=) \<bottom> ios p) (lxs p)) \<and> lys = lproject \<bottom> (=) ios)" *)
  (* 
corec produce_trace where
  "produce_trace op lxs = (case op of
    Read p f \<Rightarrow> LCons (Inp p (CHD p lxs)) (produce_trace (f (CHD p lxs)) (CTL p lxs))
  | Write op' p x \<Rightarrow> LCons (Out p x) (produce_trace op' lxs)
  | end_op \<Rightarrow> LNil)"

simps_of_case produce_trace_simps[simp]: produce_trace.code      *)

(* lemma lset_produce_trace_not_LNil:
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
 *)
(* 
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
 *)
(* 
lemma EOB_not_ind_produce_trace[simp]:
  "(Inp p EOB) \<notin> lset (produce_trace op lxs)"
  unfolding not_def
  apply (rule impI)
  apply (induct "produce_trace op lxs" arbitrary: op lxs rule: lset_induct)
  subgoal for xs op lxs
    apply (cases op)
      apply (auto simp add: split_beta split:  prod.splits)
    apply (metis chd.elims observation.simps(3) observation.simps(7))
    done
  subgoal for x xs op lxs
    apply (cases op)
      apply (auto simp add: split_beta split:  prod.splits)
    done
  done *)

(* 
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
  done *)
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
section\<open>Well-typed\<close>

coinductive welltyped where
  "welltyped A B (f EOB) \<Longrightarrow> welltyped A B (f EOS) \<Longrightarrow> \<forall>x \<in> A p. welltyped A B (f (Observed x)) \<Longrightarrow> welltyped A B (Read p f)"
| "x \<in> B p \<Longrightarrow> welltyped A B op \<Longrightarrow> welltyped A B (Write op p x)"
| "welltyped A B end_op"

inductive_cases welltyped_ReadE[elim!]: "welltyped A B (Read p f)"
inductive_cases welltyped_WriteE[elim!]: "welltyped A B (Write op q x)"
inductive_cases welltyped_end_opE[elim!]: "welltyped A B end_op"
  (*
(*characteristic property of welltyped*)
lemma "x \<in> lset (lproject (=) lxs (Out q)) \<Longrightarrow> traced m op lxs \<Longrightarrow> welltyped A B op \<Longrightarrow> \<forall>p. lset (lproject (=) lxs (Inp p)) \<subseteq> A p \<Longrightarrow> x \<in> B q"
  apply (induct x "lproject (=) lxs (Out q)" arbitrary: m op lxs rule: llist.set_induct)
   apply (erule traced.cases; auto split: if_splits)
  oops
*)


section\<open>Convenient types\<close>

type_synonym 'd op22 = "(2, 2, 'd) op"
type_synonym 'd op11 = "(1, 1, 'd) op"

end