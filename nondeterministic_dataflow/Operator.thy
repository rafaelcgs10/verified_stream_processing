text \<open>Operators, trace model, history model, cleaned predicate, and welltyped predicate\<close>

theory Operator

imports
  "Coinductive.Coinductive_List"
  "HOL-Library.BNF_Corec"
  "HOL-Library.Code_Lazy"
  "HOL-Library.Numeral_Type"
  "HOL-Library.Code_Cardinality"
  "HOL-Library.Simps_Case_Conv"
  "Cset_Setup"
begin

(* FIXME: move me to utils file *)
lemma case_sum_invert_Inl[simp]:
  "case_sum Inr Inl p' = Inl p \<longleftrightarrow> p' = Inr p"
  by (cases p'; auto)
lemma case_sum_invert_Inr[simp]:
  "case_sum Inr Inl p' = Inr p \<longleftrightarrow> p' = Inl p"
  by (cases p'; auto)


section\<open>Channels\<close>

section\<open>Buffer infrastrcuture\<close>

type_alias buf = list

abbreviation "bhd \<equiv> hd"
abbreviation "btl \<equiv> tl"
abbreviation "benq x xs \<equiv> xs @ [x]"

definition BHD :: "'a \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> 'd" where "BHD p buf = bhd (buf p)"
abbreviation (input) BUPD where "BUPD f p buf \<equiv> buf(p := f (buf p))"
definition BTL :: "'a \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BTL = BUPD btl"
definition BENQ :: "'a \<Rightarrow> 'd \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BENQ p x buf = BUPD (benq x) p buf"
abbreviation BENQ_TL :: "'a \<Rightarrow> 'd \<Rightarrow> ('a \<Rightarrow> 'd buf) \<Rightarrow> ('a \<Rightarrow> 'd buf)" where "BENQ_TL p x buf \<equiv> BUPD (btl o benq x) p buf"

abbreviation "bulk_benq xs ys \<equiv> ys @ xs"

definition BULK_BENQ (infixr ">>" 65) where "BULK_BENQ buf1 buf2 = (\<lambda> p. bulk_benq (buf1 p) (buf2 p))"

lemma BULK_BENQ_assoc[simp]:
  "buf1 >> (buf2 >> buf3) = (buf1 >> buf2) >> buf3"
  by (auto simp add: BULK_BENQ_def)

lemma BULK_BENQ_bulk_benq:
  "(buf1 >> buf2) p = bulk_benq (buf1 p) (buf2 p)"
  by (auto simp add: BULK_BENQ_def)

lemma BHD_BULK_BENQ_cases:
  \<open>(buf1 >> buf2) p \<noteq> [] \<Longrightarrow>
  BHD p (buf1 >> buf2) = x \<Longrightarrow>
  BHD p buf2 = x \<and> buf2 p \<noteq> [] \<or>
  buf2 p = [] \<and> BHD p buf1 = x \<and> buf1 p \<noteq> []\<close>
  by (metis append_Nil hd_append BULK_BENQ_def BHD_def)

lemma BHD_BAPPEND_2_cases:
  "((buf1 >> buf2) >> buf3) p \<noteq> [] \<Longrightarrow>
   BHD p ((buf1 >> buf2) >> buf3) = x \<Longrightarrow>
   BHD p buf3 = x \<and> buf3 p \<noteq> [] \<or>
   buf3 p = [] \<and> BHD p buf2 = x \<and> buf2 p \<noteq> [] \<or>
   buf3 p = [] \<and> buf2 p = [] \<and> BHD p buf1 = x \<and> buf1 p \<noteq> []"
  by (metis append_Nil hd_append BULK_BENQ_def BHD_def)

lemma BAPPEND_BENQ[simp]:
  "BENQ p x (buf1 >> buf2) = (BENQ p x buf1) >> buf2"
  unfolding BULK_BENQ_def BENQ_def by force
lemma BAPPEND_BTL[simp]:
  "BTL p (buf1 >> buf2) = (if buf2 p = [] then BTL p buf1 >> buf2 else buf1 >> (BTL p buf2))"
  unfolding BULK_BENQ_def BTL_def by force

lemma BAPPEND_BENQ_BHD[simp]:
  "buf1 p \<noteq> [] \<Longrightarrow> (BTL p buf1) >> (BENQ p (BHD p buf1) buf2) = buf1 >> buf2"
  unfolding BULK_BENQ_def BTL_def BENQ_def BHD_def by force

lemma BULK_BENQ_left_neutral[simp]:
  "(\<lambda> _. []) >> buf = buf"
  unfolding BULK_BENQ_def by force
lemma BULK_BENQ_right_neutral[simp]:
  "buf >> (\<lambda> _. []) = buf"
  unfolding BULK_BENQ_def by force

lemma BULK_BENQ_empty[simp]:
  \<open>(buf1 >> buf2) p = [] \<longleftrightarrow> buf1 p = [] \<and> buf2 p = []\<close>
  unfolding BULK_BENQ_def by auto

lemma BHD_BENQ_empty[simp]:
  "buf p = [] \<Longrightarrow> (BHD p (BENQ p x buf)) = x"
  unfolding BENQ_def BHD_def by force
lemma BTL_BENQ_empty[simp]:
  "buf p = [] \<Longrightarrow> BTL p (BENQ p x buf) = buf"
  unfolding BENQ_def BTL_def by force
lemma BENQ_access[simp]:
  "(BENQ p x buf) p = (buf p @ [x])"
  unfolding BENQ_def by force
lemma BENQ_diff_access:
  "p \<noteq> p' \<Longrightarrow> (BENQ p x buf) p' = buf p'"
  unfolding BENQ_def by force
lemma BTL_access:
  "(BTL p buf) p = tl (buf p)"
  unfolding BTL_def by force
lemma BTL_diff_access:
  "p \<noteq> p' \<Longrightarrow> (BTL p buf) p' = buf p'"
  unfolding BTL_def by force
lemma BTL_empty[simp]:
  "buf p = [] \<Longrightarrow> (BTL p buf) = buf"
  unfolding BTL_def by force

lemma case_sum_updateL[simp]:
  \<open>(case_sum x y)(Inl a := b) = case_sum (x(a := b)) y\<close>
  by (auto split: sum.splits)
lemma case_sum_updateR[simp]:
  \<open>(case_sum x y)(Inr a := b) = case_sum x (y(a := b))\<close>
  by (auto split: sum.splits)
lemma fun_empty_upd[simp]:
  "(\<lambda>_. [])(p := []) = (\<lambda>_. [])"
  by auto

lemma case_sum_same_left[simp]:
  "case_sum A B = case_sum A C \<longleftrightarrow> B = C"
  by (meson case_sum_inject)
lemma case_sum_same_right[simp]:
  "case_sum A C = case_sum B C \<longleftrightarrow> A = B"
  using case_sum_inject by blast

lemma case_sum_BENQ_R[simp]:
  "BENQ (Inr p) x (case_sum A buf) = case_sum A (BENQ p x buf)"
  unfolding BENQ_def by (auto split: sum.splits)
lemma case_sum_BTL_R[simp]:
  "BTL (Inr p) (case_sum A buf) = case_sum A (BTL p buf)"
  unfolding BTL_def by (auto split: sum.splits)
lemma case_sum_BENQ_L[simp]:
  "BENQ (Inl p) x (case_sum buf A) = case_sum (BENQ p x buf) A"
 unfolding BENQ_def by (auto split: sum.splits)
lemma case_sum_BTL_L[simp]:
  "BTL (Inl p) (case_sum buf A) = case_sum (BTL p buf) A"
  unfolding BTL_def by (auto split: sum.splits)
lemma case_sum_BHD_L[simp]:
  "BHD (Inl p) (case_sum buf A) = BHD p buf"
  unfolding BHD_def by (auto split: sum.splits)
lemma case_sum_BHD_R[simp]:
  "BHD (Inr p) (case_sum buf A) = BHD p A"
  unfolding BHD_def by (auto split: sum.splits)
lemma BHD_BULK_BENQ_right_empty[simp]:
  "buf1 p = [] \<Longrightarrow> BHD p (buf1 >> buf2) = BHD p buf2"
  by (simp add: BENQ_def BHD_def BULK_BENQ_def)
lemma BHD_BULK_BENQ_left_empty[simp]:
  "buf2 p = [] \<Longrightarrow> BHD p (buf1 >> buf2) = BHD p buf1"
  by (simp add: BENQ_def BHD_def BULK_BENQ_def)
lemma BULK_BENQ_right_empty[simp]:
  "buf2 p = [] \<Longrightarrow> (buf1 >> buf2) p = buf1 p "
  by (simp add: BENQ_def BULK_BENQ_def)
lemma BULK_BENQ_left_empty[simp]:
  "buf1 p = [] \<Longrightarrow> (buf1 >> buf2) p = buf2 p "
  by (simp add: BENQ_def BULK_BENQ_def)
lemma BHD_BULK_BENQ_right_not_empty[simp]:
  "buf2 p \<noteq> [] \<Longrightarrow> BHD p (buf1 >> buf2) = BHD p buf2"
  by (simp add: BENQ_def BHD_def BULK_BENQ_def)

lemma BENQ_case_sum_compose:
  \<open>BENQ (case_sum Inr Inl p) x (buf \<circ> case_sum Inr Inl) = (BENQ p x buf) \<circ> case_sum Inr Inl\<close>
  unfolding BENQ_def
  apply (auto split: sum.splits)
  done

lemma BTL_case_sum_compose:
  \<open>BTL (case_sum Inr Inl p) (buf \<circ> case_sum Inr Inl) = (BTL p buf) \<circ> case_sum Inr Inl\<close>
  unfolding BTL_def
  apply (auto split: sum.splits)
  done

lemma BULK_BENQ_BTL_right_not_empty_case_sum:
  \<open>buf2 (case_sum Inr Inl p) \<noteq> [] \<Longrightarrow>
  BTL p (buf1 >> buf2 \<circ> case_sum Inr Inl) = buf1 >> BTL (case_sum Inr Inl p) buf2 \<circ> case_sum Inr Inl\<close>
  unfolding BTL_def BULK_BENQ_def by (auto split: sum.splits)

lemma BULK_BENQ_eq_right[simp]:
  "A >> B = A >> C \<longleftrightarrow> B = C"
  unfolding BULK_BENQ_def by (meson append_same_eq ext)

lemma BULK_BENQ_eq_left[simp]:
  "A >> C = B >> C \<longleftrightarrow> A = B"
  unfolding BULK_BENQ_def by (meson ext same_append_eq)

section\<open>Operator\<close>

codatatype (inputs: 'ip, outputs: 'op, dead 'd) op =
  Read 'ip "'d \<Rightarrow> ('ip, 'op, 'd) op"
  | Write "('ip, 'op, 'd) op" 'op 'd
  | Choice "('ip, 'op, 'd) op cset"
  | Silent "('ip, 'op, 'd) op"

\<comment> \<open>Some useful functions for defining operators\<close>
abbreviation end_op ("\<oslash>") where "\<oslash> \<equiv> Choice {||}"

abbreviation "safe_choice_stop stop f ops \<equiv> (if ops = cempty then stop else Choice (cimage f ops))"
abbreviation "safe_choice f \<equiv> safe_choice_stop (f end_op) f"
abbreviation "safe_choice2 f op1s op2s \<equiv> (if op1s = cempty \<and> op2s = cempty then end_op
  else if op1s = cempty then Choice (cimage (f end_op) op2s)
  else if op2s = cempty then Choice (cimage (\<lambda>op1. f op1 end_op) op1s)
  else Choice (cimage (case_prod f) (cproduct op1s op2s)))"
abbreviation "choice1 op \<equiv> Choice (cimage (\<lambda>_. op) {|()|})"
abbreviation "choice2 op1 op2 \<equiv> Choice (cimage (\<lambda>b. if b then op1 else op2) (cinsert True (csingle False)))"
abbreviation "choice3 op1 op2 op3 \<equiv> Choice (cimage (\<lambda>b. case b of None \<Rightarrow> op1 | Some True \<Rightarrow> op2 | Some False \<Rightarrow> op3) (cinsert None (cinsert (Some True) (csingle (Some False)))))"
abbreviation "safe_read f x \<equiv> (case x of None \<Rightarrow> end_op | Some x \<Rightarrow> f x)"

abbreviation "sound_reads wire buf \<equiv> cfilter (\<lambda> op. case op of Read p f \<Rightarrow> p \<notin> ran wire \<or> buf p \<noteq> [] | _ \<Rightarrow> True)"

abbreviation "ARead i f op \<equiv> Choice (cimage (\<lambda> x. if x then op else Read i f) (cinsert True (csingle False)))"
lemma ARead_simp[simp]: "ARead i f op = Choice ({| op, Read i f |})"
  by simp

abbreviation "pull i f \<equiv> Choice (cimage (\<lambda> x. if x then f None else Read i (f o Some)) (cinsert True (csingle False)))"
lemma pull_simp[simp]: "pull i f = Choice ({| f None, Read i (f o Some) |})"
  by simp

lemma map_op_inj_inv:
  "inj f \<Longrightarrow>
   inj g \<Longrightarrow>
   map_op f g op = map_op f g op' \<Longrightarrow>
   op = op'"
  by (meson injD op.inj_map)


type_synonym 'd channel = "'d llist"

code_lazy_type op

section \<open>Sub operators\<close>

declare cin.rep_eq[simp]

inductive sub_op :: \<open>('ip, 'op, 'd) op \<Rightarrow> ('ip, 'op, 'd) op \<Rightarrow> nat \<Rightarrow> bool\<close> for op where
  sub_op_Refl[intro]: \<open>sub_op op op 0\<close>
| sub_op_Read[intro]: \<open>sub_op op (f x) n \<Longrightarrow> sub_op op (Read p f) (Suc n)\<close>
| sub_op_Write[intro]: \<open>sub_op op op' n \<Longrightarrow> sub_op op (Write op' p x) (Suc n)\<close>
| sub_op_Silent[intro]: \<open>sub_op op op' n \<Longrightarrow> sub_op op (Silent op') (Suc n)\<close>
| sub_op_Choice[intro]: \<open>cin op' ops \<Longrightarrow> sub_op op op' n \<Longrightarrow> sub_op op (Choice ops) (Suc n)\<close>

inductive_cases sub_op_ReflE [elim!]: \<open>sub_op op op n\<close>
inductive_cases sub_op_ReadE [elim!]: \<open>sub_op op (Read p f) n\<close>
inductive_cases sub_op_WriteE [elim!]: \<open>sub_op op (Write op' p x) n\<close>   
inductive_cases sub_op_SilentE [elim!]: \<open>sub_op op (Silent op') n\<close>   
inductive_cases sub_op_ChoiceE [elim!]: \<open>sub_op op (Choice ops) n\<close>   

 lemma inputs_sub_op_Read: \<open>p \<in> inputs op \<Longrightarrow> \<exists>f n. sub_op (Read p f) op n\<close>
  by (induct op pred: inputs) force+

lemma sub_op_Read_inputs[intro]: \<open>sub_op (Read p f) op n \<Longrightarrow> p \<in> inputs op\<close>
  by (induct op n pred: sub_op) auto

lemma outputs_sub_op_Write: \<open>p \<in> outputs op \<Longrightarrow> \<exists>op' x n. sub_op (Write op' p x) op n\<close>
  by (induct op pred: outputs) force+

lemma sub_op_Write_outputs[intro]: \<open>sub_op (Write op' p x) op n \<Longrightarrow> p \<in> outputs op\<close>
  by (induct op n pred: sub_op) auto

lemma sub_op_Read_induct [consumes 1, case_names Read1 Read2 Write Silent Choice]:
  assumes \<open>sub_op (Read p g) op d\<close>
    and \<open>\<And>f p. P p (Read p f)\<close>
    and \<open>\<And>p p' f x d g. sub_op (Read p g) (f x) d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Read p g) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Read p' f)\<close>
    and \<open>\<And>p p' op' x d g. sub_op (Read p g) op' d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Read p g) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Write op' p' x)\<close>
    and \<open>\<And>p op' d. sub_op (Read p g) op' d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Read p g) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Silent op')\<close>
    and \<open>\<And>p ops d g. \<exists>op'. cin op' ops \<and> sub_op (Read p g) op' d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Read p g) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Choice ops)\<close>
  shows \<open>P p op\<close>
  using assms(1)
proof (induct d arbitrary: op p rule: less_induct)
  case (less m)
  from this(2,1) show ?case
    by (induct op m pred: sub_op) (auto intro!: assms)
qed

lemma sub_op_Write_induct [consumes 1, case_names Read Write1 Silent Choice Write2]:
  assumes \<open>sub_op (Write op2 p y) op d\<close>
    and \<open>\<And>p p' f x op2 y d. sub_op (Write op2 p y) (f x) d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Write op2 p y) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Read p' f)\<close>
    and \<open>\<And>p p' op' x op2 y d. sub_op (Write op2 p y) op' d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Write op2 p y) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Write op' p' x)\<close>
    and \<open>\<And>p op' op2 y d. sub_op (Write op2 p y) op' d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Write op2 p y) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Silent op')\<close>
    and \<open>\<And>p op2 y d ops.  \<exists>op'. cin op' ops \<and> sub_op (Write op2 p y) op' d \<Longrightarrow> (\<And>m op. m < Suc d \<Longrightarrow> sub_op (Write op2 p y) op m \<Longrightarrow> P p op) \<Longrightarrow> P p (Choice ops)\<close>
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
| "input_at p op' n \<Longrightarrow> input_at p (Silent op') (Suc n)"
| "cin op' ops \<Longrightarrow> input_at p op' n \<Longrightarrow> input_at p (Choice ops) (Suc n)"

lemma inputs_input_at: "p \<in> inputs op \<Longrightarrow> \<exists>n. input_at p op n"
  by (induct p op rule: op.set_induct(1)) (auto 4 4 intro: input_at.intros)

lemma input_at_inputs: "input_at p op n \<Longrightarrow> p \<in> inputs op"
  by (induct p op n rule: input_at.induct) auto

lemma inputs_alt: "p \<in> inputs op \<longleftrightarrow> (\<exists>n. input_at p op n)"
  by (metis input_at_inputs inputs_input_at)
 
definition "input_depth p op = (LEAST n. input_at p op n)"

section\<open>Transition system\<close>

datatype ('a, 'b, 'd) IO = Inp (proji: 'a) (data: "'d") | Out (projo: 'b) (data: 'd) | Tau

inductive step where
  SR[intro]: "step (Inp p x) (Read p f) (f x)"
| SW[intro]: "step (Out q x) (Write op q x) op"
| ST[intro]: "step Tau (Silent op) op"
| SC[intro]: "cin op ops \<Longrightarrow> step io op op' \<Longrightarrow> step io (Choice ops) op'"

inductive_cases stepReadE [elim!]: "step io (Read p f) op'"
inductive_cases stepWriteE [elim!]: "step io (Write op q x) op'"
inductive_cases stepSilentE [elim!]: "step io (Silent op) op'"
inductive_cases stepChoiceE [elim!]: "step io (Choice ops) op'"

lemma ST':
  "op = op' \<Longrightarrow> step Tau (Silent op) op'"
  by auto

lemma step_map_op[intro!,simp]:
  "step io op op' \<Longrightarrow> map_IO f g id io = io' \<Longrightarrow>
   step io' (map_op f g op) (map_op f g op')"
  by (induct io op op' rule: step.induct) (force simp add: comp_def)+

lemma step_map_op_inv:
  "step io (map_op f g op) op' \<Longrightarrow>
   \<exists> io' op''. step io' op op'' \<and> map_IO f g id io' = io \<and> map_op f g op'' = op'"
  apply (induct io "map_op f g op" op' arbitrary: op rule: step.induct)
     apply (auto)
  subgoal for p fa x op
    apply (cases op)
       apply (auto 10 10)
    done
  subgoal for _ _ _ op
    apply (cases op)
       apply (auto 10 10)
    done
  subgoal for _  op
    apply (cases op)
       apply (auto 10 10)
    done
  subgoal for op ops l op' opa
    apply (cases opa)
       apply force+
    done
  done

lemma step_map_op_elim:
  assumes  "step io (map_op f g op) op'"
  obtains io' op'' where "step io' op op'' \<and> map_IO f g id io' = io \<and> map_op f g op'' = op'"
  apply atomize
  apply (simp add: assms step_map_op_inv)
  done

section\<open>Strong Bisimilarity\<close>
definition "sim R op1 op2 = (\<forall>io op1'. step io op1 op1' \<longrightarrow> (\<exists>op2'. step io op2 op2' \<and> R op1' op2'))"

lemma sim_mono[mono]: "R \<le> S \<Longrightarrow> sim R \<le> sim S"
  by (force simp: sim_def le_fun_def)

coinductive bisim (infix "~"40) where
  "sim bisim op1 op2 \<Longrightarrow> sim bisim op2 op1 \<Longrightarrow> bisim op1 op2"

inductive bisim_cong for R where
  bc_base:  "R x y \<Longrightarrow> bisim_cong R x y"
| bc_bisim:  "bisim x y \<Longrightarrow> bisim_cong R x y"
| bc_refl: "x = y \<Longrightarrow> bisim_cong R x y"
| bc_sym: "bisim_cong R x y \<Longrightarrow> bisim_cong R y x"
| bc_trans: "bisim_cong R x y \<Longrightarrow> bisim_cong R y z \<Longrightarrow> bisim_cong R x z"
| bc_Read:"x1 = y1 \<Longrightarrow> rel_fun (=) (bisim_cong R) x2 y2 \<Longrightarrow> bisim_cong R (Read x1 x2) (Read y1 y2)"
| bc_Write: "bisim_cong R x1 y1 \<Longrightarrow> x2 = y2 \<Longrightarrow> x3 = y3 \<Longrightarrow> bisim_cong R (Write x1 x2 x3) (Write y1 y2 y3)"
| bc_Silent: "bisim_cong R x1 y1 \<Longrightarrow> bisim_cong R (Silent x1) (Silent y1)"
| bc_Choice:"rel_cset (bisim_cong R) x y \<Longrightarrow> bisim_cong R (Choice x) (Choice y)"

lemma bc_bisim_cong:
  "bisim x x' \<Longrightarrow> bisim y y' \<Longrightarrow> bisim_cong R x' y' \<Longrightarrow> bisim_cong R x y"
  by (meson bc_bisim bc_sym bc_trans)

lemma bisim_cong_disj:
  "(bisim_cong R x y \<or> bisim x y) = bisim_cong R x y"
  by (auto intro: bisim_cong.intros)

lemma bisim_coinduct_upto[consumes 1, case_names BISIM]:
  "R s t \<Longrightarrow>
   (\<And>op1 op2. R op1 op2 \<Longrightarrow> sim (bisim_cong R) op1 op2 \<and> sim (bisim_cong R) op2 op1) \<Longrightarrow>
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
      by (auto simp: rel_fun_def sim_def intro: bc_sym)
    subgoal
      by (auto simp: rel_fun_def sim_def intro: bc_sym)
    subgoal
      by (auto simp: rel_fun_def sim_def intro: bc_sym)
    subgoal
      apply (auto simp: rel_fun_def sim_def intro: bc_sym)
       apply (smt (verit, del_insts) cin.rep_eq rel_setD1 step.intros(4))
      apply (smt (verit) cin.rep_eq rel_setD2 step.intros(4))
      done
    done
  done

lemma bisim_coinduct_upto'[unfolded sim_def, rule_format, consumes 1, case_names SIM1 SIM2]:
  "R op1 op2 \<Longrightarrow>
   (\<And>s t. R s t \<Longrightarrow> sim (bisim_cong R) s t) \<Longrightarrow>
   (\<And>s t. R s t \<Longrightarrow> sim (bisim_cong R) t s) \<Longrightarrow>
   op1 ~ op2"
  using bisim_coinduct_upto by blast

lemma bisim_coinduct_upto''[consumes 1, case_names SIM1 SIM2]:
  "R op1 op2 \<Longrightarrow>
  (\<And>s t io op1'. R s t \<Longrightarrow> step io s op1' \<Longrightarrow> \<exists>op2'. step io t op2' \<and> bisim_cong R op1' op2') \<Longrightarrow>
  (\<And>s t io op1'. R s t \<Longrightarrow> step io t op1' \<Longrightarrow> \<exists>op2'. step io s op2' \<and> bisim_cong R op2' op1') \<Longrightarrow>
   op1 ~ op2"
  using bisim_coinduct_upto' by (smt (verit, ccfv_SIG) bc_sym)

inductive bisim_R ("\<B>") for R where
  b_base[intro]:  "R x y \<Longrightarrow> \<B> R x y"
| b_bisim:  "bisim x y \<Longrightarrow> \<B> R x y"
| b_refl[intro]:  "x = y \<Longrightarrow> \<B> R x y"
| b_sym: "\<B> R x y \<Longrightarrow> \<B> R y x"

lemma bisim_R_bisim_cong:
  "bisim_R R op1 op2 \<Longrightarrow> bisim_cong R op1 op2"
  by (induction pred: bisim_R) (auto intro: bisim_cong.intros)

lemma bisim_coinduct[consumes 1, case_names SIM1 SIM2]:
  "R op1 op2 \<Longrightarrow>
  (\<And>op1 op2 io op1'. R op1 op2 \<Longrightarrow> step io op1 op1' \<Longrightarrow> \<exists>op2'. step io op2 op2' \<and> (bisim_R R op1' op2')) \<Longrightarrow>
  (\<And>op1 op2 io op2'. R op1 op2 \<Longrightarrow> step io op2 op2' \<Longrightarrow> \<exists>op1'. step io op1 op1' \<and> (bisim_R R op1' op2')) \<Longrightarrow>
   op1 ~ op2"
  apply (rule bisim_coinduct_upto'')
    apply assumption
  using bisim_R_bisim_cong apply blast+
  done

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

lemma bisim_Write_cong:
  "op1 ~ op2 \<Longrightarrow> Write op1 p x ~ Write op2 p x"
  apply (coinduction arbitrary: op1 op2)
  apply (erule bisim.cases)
  apply (unfold sim_def)
  apply (auto simp add: bisim.intros sim_def)
  done

lemma bisim_Silent_cong:
  "op1 ~ op2 \<Longrightarrow> Silent op1 ~ Silent op2"
  apply (coinduction arbitrary: op1 op2)
  apply (erule bisim.cases)
  apply (unfold sim_def)
  apply (auto simp add: bisim.intros sim_def)
  done

lemma bisim_Choice_cong:
  "rel_cset (~) ops1 ops2 \<Longrightarrow> Choice ops1 ~ Choice ops2"
  apply (coinduction arbitrary: ops1 ops2 rule: bisim_coinduct_upto)
  unfolding rel_cset_def
  apply (auto simp add: bisim.intros sim_def)
   apply (smt (verit, ccfv_SIG) bc_bisim bisim.cases cin.rep_eq rel_setD1 sim_def step.intros)
  apply (smt (verit, ccfv_threshold) bc_bisim bisim.cases cin.rep_eq rel_cset.rep_eq rel_cset_alt_def sim_def step.intros(4))
  done


lemma bisim_Read_cong:
  "rel_fun (=) (~) f1 f2 \<Longrightarrow> Read p f1 ~ Read p f2"
  apply (coinduction arbitrary: f1 f2 rule: bisim_coinduct_upto)
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
  done

lemma bisim_ReadI: "p = q \<Longrightarrow> \<forall>x. f x ~ g x \<Longrightarrow> Read p f ~ Read q g"
  by (coinduction) (auto simp: sim_def bisim_sym elim!: step.cases)

lemma bisim_ReadD: "Read p f ~ Read q g \<Longrightarrow> p = q \<and> f x ~ g x"
  by (erule bisim.cases)
    (auto simp: sim_def dest: meta_spec2[of _ "Inp p x" "f x"] meta_spec2[of _ "Inp q x" "g x"] elim!: step.cases)

lemma bisim_Read_Read[simp]: "Read p f ~ Read q g \<longleftrightarrow> (p = q \<and> (\<forall>x. (f x) ~ (g x)))"
  by (metis bisim_ReadI bisim_ReadD) 

lemma bisim_WriteI: "p = q \<Longrightarrow> x = y \<Longrightarrow> bisim op op' \<Longrightarrow> bisim (Write op p x) (Write op' q y)"
  by (coinduction) (auto simp: sim_def bisim_sym elim!: step.cases)

lemma bisim_WriteD: "Write op p x ~ Write op' q y \<Longrightarrow> p = q \<and> y = x \<and> op ~ op'"
  by (erule bisim.cases)
    (auto simp: sim_def dest: meta_spec2[of _ "Out p x" "op"] meta_spec2[of _ "Out q y" op'] elim!: step.cases)

lemma bisim_Write_Write[simp]: "Write op p x ~ Write op' q y \<longleftrightarrow> (p = q \<and> y = x \<and> op ~ op')"
  by (metis bisim_WriteI bisim_WriteD)

lemma not_bisim[simp]:
  "\<not> bisim (Read p1 f1) (Write op p2 x)"
  "\<not> bisim (Write op p1' x) (Read p2' f2)"
  by (auto 10 10 simp: sim_def elim: bisim.cases)

lemma simE:
  assumes "sim R s t" "step l s s'"
  obtains t' where "step l t t'" "R s' t'"
  using assms unfolding sim_def by auto

lemma sim_Read[simp]: "sim R (Read p f) op \<longleftrightarrow> (\<forall>x. \<exists>op'. step (Inp p x) op op' \<and> R (f x) op')"
  by (auto simp: sim_def)

lemma sim_Write[simp]: "sim R (Write op p x) op' \<longleftrightarrow> (\<exists>op''. step (Out p x) op' op'' \<and> R op op'')"
  by (auto simp: sim_def)

lemma sim_Choice[simp]: "sim R (Choice ops) t \<longleftrightarrow> (\<forall>op. op |\<in>| ops \<longrightarrow> sim R op t)"
  by (auto simp: sim_def simp flip: cin.rep_eq)

lemma sim_refl: "reflp R \<Longrightarrow> sim R s s"
  by (fastforce simp: sim_def reflp_def)

lemma sim_trans: "transp R \<Longrightarrow> sim R s t \<Longrightarrow> sim R t u \<Longrightarrow> sim R s u"
  by (fastforce simp: sim_def transp_def)


lemma bisim_map_op:
  "op ~ op' \<Longrightarrow> map_op f g op ~ map_op f g op'"
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
  done


section\<open>Weak Bisimilarity\<close>

fun estep where "estep Tau = (step Tau)\<^sup>=\<^sup>=" | "estep io = step io"
definition "wstep io = (step Tau)\<^sup>*\<^sup>* OO (estep io) OO (step Tau)\<^sup>*\<^sup>*"
definition "wsim R op1 op2 = (\<forall>io op1'. step io op1 op1' \<longrightarrow> (\<exists>op2'. wstep io op2 op2' \<and> R op1' op2'))"

lemma wsim_mono[mono]: "R \<le> S \<Longrightarrow> wsim R \<le> wsim S"
  by (force simp: wsim_def le_fun_def)

lemma wsim_conversep_mono[mono]: \<open>R \<le> S \<Longrightarrow> wsim (R\<inverse>\<inverse>) \<le> wsim (S\<inverse>\<inverse>)\<close>
  by (simp add: wsim_mono)

coinductive wbisim (infix "\<approx>"40) where
  "wsim wbisim op1 op2 \<Longrightarrow> wsim wbisim op2 op1 \<Longrightarrow> wbisim op1 op2"

inductive wbisim_cong for R where
  wbc_base[intro]:  "R x y \<Longrightarrow> wbisim_cong R x y"
| wbc_bisim:  "wbisim x y \<Longrightarrow> wbisim_cong R x y"
| wbc_refl[intro]: "x = y \<Longrightarrow> wbisim_cong R x y"
| wbc_sym[intro]: "wbisim_cong R x y \<Longrightarrow> wbisim_cong R y x"
| wbc_Read:"x1 = y1 \<Longrightarrow> rel_fun (=) (wbisim_cong R) x2 y2 \<Longrightarrow> wbisim_cong R (Read x1 x2) (Read y1 y2)"
| wbc_Write: "wbisim_cong R x1 y1 \<Longrightarrow> wbisim_cong R (Write x1 x2 x3) (Write y1 x2 x3)"
| wbc_Silent: "wbisim_cong R x1 y1 \<Longrightarrow> wbisim_cong R (Silent x1) (Silent y1)"

lemma wbisim_cong_disj:
  "(wbisim_cong R x y \<or> wbisim x y) = wbisim_cong R x y"
  by (auto intro: wbc_bisim)

lemma wbisim_refl:
  "wbisim op op"
  apply (coinduction arbitrary: op)
  apply (auto simp: wsim_def wstep_def)
  apply (metis (no_types, lifting) Nitpick.rtranclp_unfold estep.elims relcompp_apply sup2I1)
  done

lemma wbisim_sym:
  "op1 \<approx> op2 \<Longrightarrow> op2 \<approx> op1"
  apply (coinduction arbitrary: op1 op2)
  subgoal for op1 op2
    apply simp
    unfolding wsim_def wstep_def
    apply auto
    subgoal for io op
      apply (erule wbisim.cases)
      unfolding wsim_def wstep_def
      apply blast
      done
    subgoal for io op
      apply (erule wbisim.cases)
      unfolding wsim_def wstep_def
      apply blast
      done
    done
  done

lemma step_wstep[intro]:
  "step io op op' \<Longrightarrow> wstep io op op'"
  unfolding wstep_def 
  by (smt (verit) OO_eq eq_OO estep.elims reflclp_tranclp relcompp_distrib relcompp_distrib2 sup2CI)

lemma wstep_steps_Tau[simp]: "wstep Tau = (step Tau)\<^sup>*\<^sup>*"
  unfolding wstep_def by force

lemma step_io_step_tau_wstep:
  "step io op op' \<Longrightarrow> step Tau op' op'' \<Longrightarrow> wstep io op op''"
  unfolding wstep_def 
  by (smt (verit, best) predicate2D relcompp_apply rtranclp_trans step_wstep wstep_def wstep_steps_Tau)

lemma step_io_step_tau_tau_wstep:
  "step io op op' \<Longrightarrow> step Tau op' op'' \<Longrightarrow> step Tau op'' op''' \<Longrightarrow> wstep io op op'''"
  unfolding wstep_def 
  by (smt (verit, best) predicate2D relcompp_apply rtranclp_trans step_wstep wstep_def wstep_steps_Tau)

lemma step_tau_step_io_wstep:
  "step Tau op op' \<Longrightarrow> step io op' op'' \<Longrightarrow> wstep io op op''"
  unfolding wstep_def 
  by (smt (verit, del_insts) estep.elims reflclp_tranclp relcomppI step_wstep sup2CI wstep_steps_Tau)

lemma wstep_trans_tau_1[trans, intro]:
  "step Tau op op' \<Longrightarrow> wstep io op' op'' \<Longrightarrow> wstep io op op''"
  unfolding wstep_def 
  by (smt (verit, ccfv_SIG) converse_rtranclp_into_rtranclp relcompp_apply)

declare rtranclp.rtrancl_into_rtrancl[OF r_into_rtranclp, of "step Tau", trans]
lemma step_Tau_closure_single[trans]:
  "step Tau a c \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* a c"
  by force

lemma wstep_trans[trans]:
  "(step Tau)\<^sup>*\<^sup>* op1 op1' \<Longrightarrow> step (Out p x) op1' op1'' \<Longrightarrow> wstep (Out p x) op1 op1''"
  "(step Tau)\<^sup>*\<^sup>* op2 op2' \<Longrightarrow> step (Inp p' x') op2' op2'' \<Longrightarrow> wstep (Inp p' x') op2 op2''"
  unfolding wstep_def by (simp add: relcomppI)+
lemma wstep_trans_base[trans]:
  "step Tau op1 op1' \<Longrightarrow> step (Out p x) op1' op1'' \<Longrightarrow> wstep (Out p x) op1 op1''"
  "step Tau op2 op2' \<Longrightarrow> step (Inp p' x') op2' op2'' \<Longrightarrow> wstep (Inp p' x') op2 op2''"
  unfolding wstep_def by auto

lemma wstep_converse_trans:
  "step (Out p x) op1 op1' \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* op1' op1'' \<Longrightarrow> wstep (Out p x) op1 op1''"
  "step (Inp p' x') op2 op2' \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* op2' op2'' \<Longrightarrow> wstep (Inp p' x') op2 op2''"
  unfolding wstep_def by auto

lemma step_tau_step_tau_step_io_wstep:
  "step Tau op op' \<Longrightarrow> step Tau op' op'' \<Longrightarrow> step io op'' op''' \<Longrightarrow> wstep io op op'''"
  unfolding wstep_def 
  by (smt (verit, del_insts) estep.elims reflclp_tranclp relcomppI rtranclp.rtrancl_into_rtrancl sup2CI)

definition "wsimulation_canonical R = (\<forall> op1 op2. R op1 op2 \<longrightarrow> (\<forall> op1' io. step io op1 op1' \<longrightarrow> (\<exists> op2'. wstep io op2 op2' \<and> R op1' op2')))" 
abbreviation "wbisimulation_canonical R \<equiv> wsimulation_canonical R \<and> wsimulation_canonical (conversep R)"

abbreviation "wbisimulation R \<equiv> (\<forall>op1 op2. R op1 op2 \<longrightarrow> wsim R op1 op2 \<and> wsim (conversep R) op2 op1)"


lemma wbisim_wstep_Tau:
  assumes "wbisimulation R"
    and "R op1 op2"
    and "(step Tau)\<^sup>*\<^sup>* op1 op1'"
  shows "\<exists>op2'. wstep Tau op2 op2' \<and> R op1' op2'"
  using assms(3,2)
proof (induct op1 arbitrary: op2 rule: converse_rtranclp_induct)
  case (step op1 op1'')
  with assms(1) obtain op2'' where "wstep Tau op2 op2''" "R op1'' op2''"
    unfolding wsim_def by blast
  moreover from step(3)[OF \<open>R op1'' op2''\<close>] obtain op2' where "wstep Tau op2'' op2'" "R op1' op2'"
    by blast
  ultimately show ?case by (auto intro!: exI[of _ op2'])
qed force

lemma wbisim_wstep:
  assumes "wbisimulation R"
    and "R op1 op2"
    and "wstep io op1 op1'"
  obtains op2' where "wstep io op2 op2'" and "R op1' op2'"
proof -
  from assms(3) obtain opi opj where \<open>(step Tau)\<^sup>*\<^sup>* op1 opi\<close> \<open>estep io opi opj\<close> \<open>(step Tau)\<^sup>*\<^sup>* opj op1'\<close> unfolding wstep_def by blast
  moreover from assms(1,2) obtain \<open>wsim R op1 op2\<close> by blast
  ultimately have \<open>\<exists>op2'. wstep io op2 op2' \<and> R op1' op2'\<close> using assms(2)
  proof (induct op1 arbitrary: op2 rule: converse_rtranclp_induct)
    case base
    show ?case
    proof (cases "io = Tau \<and> opi = opj")
      case True
      with base(2,3,4) show ?thesis
        using wbisim_wstep_Tau[OF assms(1), of opi op2 op1'] by auto
    next
      case False
      with base obtain opj' where H1: \<open>wstep io op2 opj'\<close> \<open>R opj opj'\<close> unfolding wsim_def by (cases io) force+
      with assms(1) have \<open>wsim R opj opj'\<close> by blast
      with base(2) H1(2) have \<open>\<exists>op2'. (step Tau)\<^sup>*\<^sup>* opj' op2' \<and> R op1' op2'\<close>
        using wbisim_wstep_Tau[OF assms(1), of opj opj' op1'] by auto
      with \<open>wstep io op2 opj'\<close> show ?thesis unfolding wstep_def
        by (smt (verit, best) relcompp_apply rtranclp_trans)
    qed
  next
    case (step op1 opk)
    from step(1) obtain opk' where "(step Tau)\<^sup>*\<^sup>* op2 opk'" "R opk opk'"
      by (auto dest!: step(6)[unfolded wsim_def, rule_format])
    with step(3)[of opk'] step(4,5) assms(1) show ?case unfolding wstep_def
      by (smt (verit) relcompp.simps rtranclp_trans)  
  qed
  then show ?thesis using that by force
qed

lemma step_estep[intro]: "step io op1 op2 \<Longrightarrow> estep io op1 op2"
  by (cases io) auto

lemma wbisimulation_eq:
  shows "wbisimulation (=)"
  by (auto simp: wsim_def wstep_def)

lemma wbisimulation_conversep:
  assumes "wbisimulation R"
  shows   "wbisimulation (conversep R)"
  using assms by (auto simp: wsim_def wstep_def)

lemma wbisim_wstep':
  assumes "wbisimulation R"
    and "R op1 op2"
    and "wstep io op2 op2'"
  obtains op1' where "wstep io op1 op1'" and "R op1' op2'"
  by (smt (verit, best) assms conversep_iff wbisim_wstep wbisimulation_conversep)

lemma wbisimulation_relcompp:
  assumes "wbisimulation R" "wbisimulation S"
  shows "wbisimulation (R OO S)"
proof (unfold wsim_def, safe)
  fix op1 op2 op io op1'
  assume "R op1 op" "S op op2" "step io op1 op1'"
  then have "wsim R op1 op" using assms(1) by blast
  with \<open>step io op1 op1'\<close> obtain op' where "wstep io op op'" "R op1' op'" unfolding wsim_def by blast
  with wbisim_wstep \<open>S op op2\<close> obtain op2' where "wstep io op2 op2'" "S op' op2'" using assms(2) by blast
  with \<open>R op1' op'\<close> show "\<exists>op2'. wstep io op2 op2' \<and> (R OO S) op1' op2'" by blast
next
  fix op1 op2 op io op2'
  assume "R op1 op" "S op op2" "step io op2 op2'"
  then have "wsim (conversep S) op2 op" using assms(2) by blast
  with \<open>step io op2 op2'\<close> obtain op' where "wstep io op op'" "S op' op2'" unfolding wsim_def by blast
  with wbisim_wstep'[OF assms(1)] \<open>R op1 op\<close> obtain op1' where "wstep io op1 op1'" "R op1' op'" by blast
  with \<open>S op' op2'\<close> show "\<exists>op1'. wstep io op1 op1' \<and> conversep (R OO S) op2' op1'" by blast
qed

lemma wbisimulation_wbisim: "wbisimulation (\<approx>)"
  by (auto elim: wbisim.cases elim!: wsim_mono[THEN predicate2D, rotated] wbisim_sym)

thm wbisimulation_relcompp

lemma wbisim_trans[trans]:
  "op1 \<approx> op2 \<Longrightarrow> op2 \<approx> op3 \<Longrightarrow> op1 \<approx> op3"
  apply (coinduction arbitrary: op1 op2 op3)
  apply clarsimp
  subgoal for op1 op2 op3
    using wbisimulation_relcompp[OF wbisimulation_wbisim wbisimulation_wbisim, rule_format, OF relcomppI, of op1 op2 op3]
    apply (auto elim!: wsim_mono[THEN predicate2D, rotated] dest: wbisim_sym)
    done
  done

lemma conversep_wbc[simp]: "conversep (wbisim_cong R) = wbisim_cong R"
  using wbc_sym by fastforce

lemma wsim_Read[simp]: "wsim R (Read p f) op \<longleftrightarrow> (\<forall>x. \<exists>op'. wstep (Inp p x) op op' \<and> R (f x) op')"
  by (auto simp: wsim_def intro!: SR[of p])

lemma wsim_Write[simp]: "wsim R (Write op' p x) op \<longleftrightarrow> (\<exists>op''. wstep (Out p x) op op'' \<and> R op' op'')"
  by (auto simp: wsim_def intro!: SW[of p])

lemma wsim_Choice[simp]: "wsim R (Choice ops) t \<longleftrightarrow> (\<forall>op. op |\<in>| ops \<longrightarrow> wsim R op t)"
  by (auto simp: wsim_def simp flip: cin.rep_eq intro!: SC[of _ ops])

lemma wsim_SilentI: "R op1 op2 \<Longrightarrow> wsim R (Silent op1) (Silent op2)"
  unfolding wsim_def by (auto intro!: step_wstep[OF ST])

lemma wbisim_coinduct_upto[consumes 1, case_names BISIM]:
  "R op1 op2 \<Longrightarrow>
   (\<And>s t. R s t \<Longrightarrow> wsim (wbisim_cong R) s t \<and> wsim (wbisim_cong R) t s) \<Longrightarrow>
   op1 \<approx> op2"
  apply (rule wbisim.coinduct[where X="wbisim_cong R", unfolded wbisim_cong_disj, of op1 op2])
  subgoal
    by (auto intro: wbc_bisim)
  subgoal premises prems for s' t'
    using prems(3) apply -
    apply (induct s' t' rule: wbisim_cong.induct)
    subgoal for op1 op2
      by (drule prems(2)) auto
    subgoal for op1 op2
      using wsim_mono[of wbisim "wbisim_cong R"]
      apply (auto simp: le_fun_def wbc_bisim elim: wbisim.cases)
      done
    subgoal for op1 op2
      by (auto simp: wsim_def wstep_def)
    subgoal for op1 op2
      by fastforce
    subgoal for p q f g
      by (auto simp: rel_fun_def intro!: step_wstep[OF SR])
    subgoal for op1 op2 p x
      by (auto intro!: step_wstep[OF SW])
    subgoal for op1 op2
      by (auto intro: wsim_SilentI)
    done
  done

lemma wbisim_coinduct_upto'[unfolded wsim_def, rule_format, consumes 1, case_names SIM1 SIM2]:
  "R op1 op2 \<Longrightarrow>
   (\<And>s t. R s t \<Longrightarrow> wsim (wbisim_cong R) s t) \<Longrightarrow>
   (\<And>s t. R s t \<Longrightarrow> wsim (wbisim_cong R) t s) \<Longrightarrow>
   op1 \<approx> op2"
  using wbisim_coinduct_upto by blast

lemma wbisim_coinduct_upto''[rule_format, consumes 1, case_names SIM1 SIM2]:
  "R op1 op2 \<Longrightarrow>
  (\<And>s t io op1'. R s t \<Longrightarrow> step io s op1' \<Longrightarrow> \<exists>op2'. wstep io t op2' \<and> wbisim_cong R op1' op2') \<Longrightarrow>
  (\<And>s t io op1'. R s t \<Longrightarrow> step io t op1' \<Longrightarrow> \<exists>op2'. wstep io s op2' \<and> wbisim_cong R op2' op1') \<Longrightarrow>
   op1 \<approx> op2"
  using wbisim_coinduct_upto' by (smt (verit, ccfv_SIG) wbc_sym)

inductive wbisim_R ("\<W>")  for R where
  wbcr_base[intro]:  "R x y \<Longrightarrow> \<W> R x y"
| wbcr_bisim:  "x \<approx> y \<Longrightarrow> \<W> R x y"
| wbcr_refl[intro]:  "x = y \<Longrightarrow> \<W> R x y"
| wbcr_sym:  "\<W> R y x \<Longrightarrow> \<W> R x y"

lemma wbisim_R_wbisim_cong:
  "\<W> R op1 op2 \<Longrightarrow> wbisim_cong R op1 op2"
  by (induct pred: wbisim_R) (auto intro: wbc_bisim)

lemma wbisim_coinduct[rule_format, consumes 1, case_names SIM1 SIM2]:
  "R op1 op2 \<Longrightarrow>
  (\<And>op1 op2 io op1'. R op1 op2 \<Longrightarrow> step io op1 op1' \<Longrightarrow> \<exists>op2'. wstep io op2 op2' \<and> (\<W> R op1' op2')) \<Longrightarrow>
  (\<And>op1 op2 io op2'. R op1 op2 \<Longrightarrow> step io op2 op2' \<Longrightarrow> \<exists>op1'. wstep io op1 op1' \<and> (\<W> R op1' op2')) \<Longrightarrow>
   op1 \<approx> op2"
  apply (rule wbisim_coinduct_upto'')
    apply assumption
  using wbisim_R_wbisim_cong apply blast+
  done

lemma step_star_map_op[intro!]:
  "(step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow> (step Tau)\<^sup>*\<^sup>* (map_op f g op) (map_op f g op')"
    apply (induct op arbitrary: rule: converse_rtranclp_induct)
   apply auto[1]
  apply (metis (no_types, lifting) ST converse_rtranclp_into_rtranclp op.simps(39) stepSilentE step_map_op)
  done

lemma wstep_map_op[intro!]:
  "wstep io op op' \<Longrightarrow> map_IO f g id io  = io'\<Longrightarrow>
   wstep io' (map_op f g op) (map_op f g op')"
  unfolding wstep_def
  apply hypsubst_thin
  apply (erule relcomppE)
  subgoal for op''
    apply (induct op arbitrary: rule: converse_rtranclp_induct)
    subgoal
      apply (cases io)
      using step_star_map_op step_map_op apply fastforce+
      done
    subgoal
      by (smt (verit, ccfv_SIG) relcompp_apply rtranclp_trans step_star_map_op step_wstep wstep_steps_Tau)
    done
  done

lemma wbisim_map_op:
  "op \<approx> op' \<Longrightarrow> map_op f g op \<approx> map_op f g op'"
  apply (coinduction arbitrary: op op' rule: wbisim_coinduct_upto)
  subgoal for op op'
    apply clarsimp
    apply (erule wbisim.cases)
    subgoal for s t
      unfolding wsim_def
      apply auto
      subgoal for l s'
        apply hypsubst_thin
        apply (drule step_map_op_inv[where f=f and g=g])
        apply auto
        apply (drule spec2)
        apply (drule mp)
        apply assumption
        apply auto
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
        done
      done
    done
  done

lemma bisim_wbisim:
  "op1 ~ op2 \<Longrightarrow> op1 \<approx> op2"
  apply (coinduction arbitrary: op1 op2 rule: wbisim_coinduct_upto)
  subgoal for op1 op2
    apply clarsimp
    apply (erule bisim.cases)
    subgoal for s t
      unfolding sim_def
      apply auto
      subgoal
        apply hypsubst_thin
        unfolding wsim_def wstep_def
        apply auto
        apply (metis step_wstep wbc_base wstep_def)
        done
      subgoal
        apply hypsubst_thin
        unfolding wsim_def wstep_def
        apply auto
        apply (metis step_wstep wbc_base wstep_def)
        done
      done
    done
  done

section\<open>Trace model\<close>
coinductive finished where
  "(\<forall>op. op |\<in>|ops \<longrightarrow> finished op) \<Longrightarrow> finished (Choice ops)"

inductive_cases finished_ReadE[elim!]: "finished (Read p f)"
inductive_cases finished_WriteE[elim!]: "finished (Write op p x)"
inductive_cases finished_SilentE[elim!]: "finished (Silent op)"
inductive_cases finished_ChoiceE[elim!]: "finished (Choice ops)"

lemma Read_not_finished[simp]:
  "\<not> finished (Read p f)"
  by force
lemma Write_not_finished[simp]:
  "\<not> finished (Write op p x)"
  by force
lemma Silent_not_finished[simp]:
  "\<not> finished (Silent op)"
  by force

lemma step_not_finished: "step l op op' \<Longrightarrow> \<not> finished op"
  by (induct l op op' pred: step) (auto elim: finished.cases)

lemma step_exchange: "step (Inp p x) op op' \<Longrightarrow> \<exists>op'. step (Inp p y) op op'"
  apply (induct "Inp p x :: ('a, 'b, 'c) IO" op  op' pred: step)
   apply force+
  done

coinductive traced where
  Nil: "finished op \<Longrightarrow> traced op LNil"
| Step: "step io op op' \<Longrightarrow> traced op' lxs \<Longrightarrow> traced op (LCons io lxs)"

inductive_cases traced_LNilE[elim!]: "traced op LNil"
inductive_cases traced_LConsE[elim!]: "traced op (LCons l lxs)"

lemma traced_Read[simp]: "traced (Read p f) lxs \<longleftrightarrow> (\<exists>x l lxs'. lxs = LCons l lxs' \<and> l = Inp p x \<and> traced (f x) lxs')"
  by (cases lxs) (auto intro: traced.intros)

lemma traced_LCons_iff: "traced op (LCons io lxs') \<longleftrightarrow> (\<exists>op'. step io op op' \<and> traced op' lxs')"
  by (auto intro: traced.intros)

definition "traces op = {lxs. traced op lxs}"

lemma finished_no_step:
  "finished op \<longleftrightarrow> \<not> (\<exists>io op'. step io op op')"
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
      subgoal 
        by (metis cin.rep_eq op.exhaust step.intros(1) step.intros(2) step.intros(3) step.intros(4))
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

lemma bisim_traces: "bisim op op' \<Longrightarrow> (traces op = traces op')"
  unfolding traces_def set_eq_iff mem_Collect_eq
  apply (intro iffI allI)
   apply (auto elim: bisim_traced dest: bisim_sym[THEN iffD1]) [2]
  done

corec wbisim_finished_wit where
  "wbisim_finished_wit op = (if finished op then LNil else LCons Tau (wbisim_finished_wit (SOME op'. step Tau op op')))"

lemma traced_wbisim_finished_wit: "wbisim op op' \<Longrightarrow> finished op \<Longrightarrow> traced op' (wbisim_finished_wit op')"
  apply (coinduction arbitrary: op op')
  subgoal for op op'
    apply (cases "finished op'")
     apply (rule disjI1)
     apply (subst wbisim_finished_wit.code; simp)
     apply (rule disjI2)
    apply (subst wbisim_finished_wit.code; simp add: finished_no_step)
    apply (erule exE)+
    subgoal for io op''
      apply (cases "io = Tau"; hypsubst_thin?)
       apply (rule exI)
       apply (rule conjI[rotated])
        apply (rule disjI1)
        apply (rule conjI)
         apply (rule refl)
        apply (erule wbisim.cases; hypsubst_thin)
        apply (subst (asm) (2) wsim_def)
        apply (drule spec2, drule mp)
         apply (erule someI)
        apply (erule exE conjE)+
        apply (metis converse_rtranclpE wbisim_sym wstep_steps_Tau)
       apply (erule someI)
        apply (erule wbisim.cases; hypsubst_thin)
        apply (subst (asm) (2) wsim_def)
        apply (drule spec2, drule mp, assumption)
      apply (metis converse_rtranclpE estep.elims relcompp.cases wstep_def)
      done
    done
  done

lemma lset_wbisim_finished_wit:
  "x \<in> lset lxs \<Longrightarrow> lxs = wbisim_finished_wit op' \<Longrightarrow> x = Tau"
  apply (induct x lxs arbitrary: op' rule: llist.set_induct)
   apply (subst (asm) wbisim_finished_wit.code; auto split: if_splits)
  apply (subst (asm) wbisim_finished_wit.code; auto split: if_splits)
  done

lemma wbisim_finished:
  "wbisim op op' \<Longrightarrow> finished op \<Longrightarrow> (\<exists>\<tau>s. traced op' \<tau>s \<and> lset \<tau>s \<subseteq> {Tau})"
  using traced_wbisim_finished_wit lset_wbisim_finished_wit
  by blast


inductive chain for R where
  "chain R [x]"
| "R x y \<Longrightarrow> chain R (y # zs) \<Longrightarrow> chain R (x # y # zs)"

lemma chain_nonempty: "chain R xs \<Longrightarrow> xs \<noteq> []"
  by (erule chain.cases) auto

lemma rtranclp_chain: "rtranclp R x z \<Longrightarrow> \<exists>zs. chain R zs \<and> hd zs = x \<and> last zs = z"
proof (induct x rule: converse_rtranclp_induct)
  case (step x y)
  then obtain zs where "chain R zs" "bhd zs = y" "last zs = z" by blast
  with step(1,2) show ?case
    by (intro exI[of _ "x # zs"], cases zs)
      (auto intro: chain.intros dest: chain_nonempty)
qed (auto intro: chain.intros)

fun lshift (infixr \<open>@@-\<close> 65) where
  "lshift [] lys = lys"
| "lshift (x # xs) lys = LCons x (lshift xs lys)"

friend_of_corec lshift where
  "lshift xs lys = (case xs of [] \<Rightarrow> (case lys of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons x xs)
    | x # xs \<Rightarrow> LCons x (lshift xs lys))"
  subgoal by (cases xs; cases lys; simp)
  subgoal by transfer_prover
  done

lemma lset_lshift[simp]: "lset (lshift xs lxs) = set xs \<union> lset lxs"
  by (induct xs) auto

abbreviation "\<tau>shift ops \<equiv> lshift (replicate (length ops - Suc 0) Tau)"

lemma traced_Taus:
  "chain (step Tau) ops \<Longrightarrow> traced (last ops) lxs \<Longrightarrow> traced (hd ops) (\<tau>shift ops lxs)"
  by (induct ops rule: chain.induct) (auto intro!: traced.intros)

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

coinductive traced' where
  Nil': "finished op \<Longrightarrow> traced' op LNil"
| Step': "chain (step Tau) ops1 \<Longrightarrow> step io (last ops1) (hd ops2) \<Longrightarrow>
   chain (step Tau) ops2 \<Longrightarrow> traced' (last ops2) lxs \<Longrightarrow> traced' (hd ops1) (\<tau>shift ops1 (LCons io (\<tau>shift ops2 lxs)))"

lemma traced'_LCons: "step io op op' \<Longrightarrow> traced' op' lxs \<Longrightarrow> traced' op (LCons io lxs)"
  using Step'[of "[op]" io "[op']" lxs] by (auto intro: chain.intros)

lemma traced'_Taus:
  "chain (step Tau) ops \<Longrightarrow> traced' (last ops) lxs \<Longrightarrow> traced' (hd ops) (\<tau>shift ops lxs)"
  by (induct ops rule: chain.induct) (auto intro!: traced'_LCons)

lemma traced_traced': "traced op lxs \<Longrightarrow> traced' op lxs"
  apply (coinduction arbitrary: op lxs)
  apply (erule traced.cases)
   apply (rule disjI1)
  apply blast
  apply (rule disjI2)
  apply hypsubst_thin
  apply simp
  apply (rule exI[of _ "[_]"] conjI)+
  apply simp
  apply (rule exI[of _ "_"])
  apply (rule exI[of _ "[_]"])
  apply (rule exI[of _ "_"])
  apply (auto intro: chain.intros)
  done

lemma traced'_traced: "traced' op lxs \<Longrightarrow> traced op lxs"
  apply (coinduction arbitrary: op lxs)
  apply (erule traced'.cases)
   apply (rule disjI1)
   apply blast
  apply (rule disjI2)
  apply hypsubst_thin
  apply simp
  subgoal for ops1 op ops2 lxs
  apply (induct ops1 rule: chain.induct)
   apply simp
   apply (rule exI conjI | assumption)+
   apply (rule disjI1)
     apply (erule (1) traced'_Taus)
    apply (auto intro!: traced'_LCons Step)
    done
  done

lemma traced_alt: "traced op lxs = traced' op lxs"
  using traced_traced' traced'_traced by blast

lemmas traced_coinduct_alt = traced'.coinduct[folded traced_alt]
lemmas traced_cases_alt = traced'.cases[folded traced_alt]

lemma traced_coinduct_upto_step:
  assumes  "X op ios"
    "(\<And>x1 x2. X x1 x2 \<Longrightarrow>
     (\<exists>op. x1 = op \<and> x2 = LNil \<and> finished op) \<or>
     (\<exists>op l op' lxs. x1 = op \<and> x2 = LCons l lxs \<and> step l op op' \<and> traced_cong X op' lxs))"
  shows "traced op ios"
  apply (rule traced.coinduct[where X = "traced_cong X", unfolded traced_cong_disj, of op ios])
  apply (rule tc_base, rule assms(1))
  subgoal for op lxs
    apply (induct op lxs rule: traced_cong.induct)
    subgoal for op lxs
      apply (drule assms(2))
      apply (auto simp del: fun_upd_apply)
      done
    subgoal for op lxs
      by (erule traced.cases)
        (auto 10 10 simp add: tc_traced simp del: fun_upd_apply)
    subgoal for p f x lxs
      by (auto simp del: fun_upd_apply)
    subgoal for p n f 
      by (auto simp del: fun_upd_apply)
    subgoal
      by (auto simp del: fun_upd_apply)
    subgoal
      by (auto 10 10 simp add: step.intros(3) simp del: fun_upd_apply)
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
      apply (auto simp del: fun_upd_apply)
      done
    subgoal for op lxs
      by (erule traced.cases)
        (auto 10 10 simp add: tc_traced simp del: fun_upd_apply)
    subgoal for p f x lxs
      by (auto simp del: fun_upd_apply)
    subgoal for p n f 
      by (auto simp del: fun_upd_apply)
    subgoal
      by (auto simp del: fun_upd_apply) 
    subgoal
      by (auto 10 10 simp add: step.intros(3) simp del: fun_upd_apply)
    done
  done

lemma traces_Read[simp]:
  "traces (Read p f) = (\<Union>x. LCons (Inp p x) ` traces (f x))"
  by (auto simp: traces_def image_iff intro: traced.intros elim: traced.cases)

lemma traces_Write[simp]:
  "traces (Write op p x) = LCons (Out p x) ` traces op"
  by (auto simp: traces_def intro: traced.intros elim: traced.cases)

lemma traces_Silent[simp]: "traces (Silent op) = LCons Tau ` traces op"
  by (auto simp: traces_def intro: traced.intros elim: traced.cases)

section\<open>Choices function\<close>
fun choices_at where
  "choices_at _ (Read p f) = csingle (Read p f)"
| "choices_at _ (Write op p x) = csingle (Write op p x)"
| "choices_at _ (Silent op) = csingle (Silent op)"
| "choices_at 0 (Choice ops) = cempty"
| "choices_at (Suc n) (Choice ops) = cUnion (cimage (choices_at n) ops)"

definition "choices op = cUnion (cimage (\<lambda>i. choices_at i op) cUNIV)"

lemma choices_Read[simp]: "choices (Read p f) = csingle (Read p f)"
  unfolding choices_def by (auto simp: cset_eq_iff)

lemma choices_Silent[simp]: "choices (Silent op) = csingle (Silent op)"
  unfolding choices_def by (auto simp: cset_eq_iff)

lemma choices_Write[simp]: "choices (Write op p x) = csingle (Write op p x)"
  unfolding choices_def by (auto simp: cset_eq_iff)

lemma choices_Choice[simp]: "choices (Choice ops) = cUnion (cimage choices ops)"
  apply (auto simp: choices_def)
  subgoal for x n
    apply (induct n "Choice ops" arbitrary: ops rule: choices_at.induct)
     apply (auto)
    done
  subgoal for x op n
    apply (rule exI[of _ "Suc n"])
    apply (auto)
    done
  done

declare choices_def[code del]
lemmas choices_code[code] = choices_Read choices_Write choices_Silent choices_Choice

lemma no_Choice_in_choices[simplified, simp, dest!]: "Choice ops |\<in>| choices op \<Longrightarrow> False"
  unfolding choices_def
  apply clarsimp
  subgoal for n
    apply (induct n op rule: choices_at.induct)
        apply auto
    done
  done

lemma choices_map_op[simp]:
  "cimage (map_op f g) (choices op) = choices (map_op f g op)"
  apply safe
  unfolding choices_def
   apply (clarsimp)
  subgoal for x n
    apply (induct n arbitrary: op)
    subgoal for op
      apply (cases op)
         apply (auto elim: finished.cases)
      done
    subgoal for n op
      apply (cases op)
         apply (auto simp add: )
      apply hypsubst_thin
      subgoal 
        apply (drule meta_spec)
        apply (drule meta_mp)
         apply assumption
        apply auto
        apply (metis (no_types, opaque_lifting) cUN_I choices_at.simps(5) cimage_eqI cin.rep_eq)
        done
      done
    done
  subgoal for op'
    apply (clarsimp)
    subgoal for n
      apply (induct n arbitrary: op)
      subgoal for op''
        apply (cases op'')
           apply (auto simp add: elim: finished.cases)
        done
      subgoal for n op
        apply (cases op)
           apply (auto elim: finished.cases)
        apply hypsubst_thin
        apply (drule meta_spec)
        apply (drule meta_mp)
         apply assumption
        apply (auto elim: finished.cases)
        apply (rule image_eqI)
         apply (rule refl)
        apply (auto elim: finished.cases)
        subgoal 
          apply (metis (no_types, opaque_lifting) cUN_I choices_at.simps(5) cin.rep_eq)
          done
        done
      done
    done
  done

lemma finished_choices_empty:
  "finished op \<Longrightarrow>
   choices op = {||}"
  apply safe
  unfolding choices_def
  apply clarsimp
  subgoal for x n
    apply (induct n arbitrary: op)
    subgoal for op
      by (auto simp add: elim: finished.cases)
    subgoal for n op
      apply (cases op)
         apply (auto elim: finished.cases)
      done
    done
  done

lemma Read_in_choices_step[intro]:
  "Read p f |\<in>| choices op \<Longrightarrow> step (Inp p x) op (f x)"
  unfolding choices_def
  apply safe
  subgoal for n
    apply (induct n arbitrary: op)
    subgoal for op
      apply (cases op)
      by (auto simp: step.intros(1))
    subgoal for n op
      apply (cases op)
         apply (auto simp: step.intros(1))
      done
    done
  done

lemma Read_in_choices_stepEx:
  "Read p f |\<in>| choices op \<Longrightarrow> \<exists> x. step (Inp p x) op (f x)"
  unfolding choices_def
  apply safe
  subgoal for n
    apply (induct n arbitrary: op)
    subgoal for op
      apply (cases op)
      by (auto simp: step.intros(1))
    subgoal for n op
      apply (cases op)
         apply (auto simp: step.intros(1))
      subgoal    
        by (metis cin.rep_eq step.intros(4))
      done
    done
  done

lemma Write_in_choices_step[intro]:
  "Write op' p x |\<in>| choices op \<Longrightarrow> step (Out p x) op op'"
  unfolding choices_def
  apply safe
  subgoal for n
    apply (induct n arbitrary: op)
    subgoal for op
      apply (cases op)
      by (clarsimp simp: step.intros(2))+     
    subgoal for n op
      apply (cases op)
      apply (auto simp: step.intros(2))
      done
    done
  done

lemma Silent_in_choices_step[intro]:
  "Silent op' |\<in>| choices op \<Longrightarrow> step Tau op op'"
  unfolding choices_def
  apply safe
  subgoal for n
    apply (induct n arbitrary: op)
    subgoal for op
      apply (cases op)
      by (clarsimp simp: step.intros)+     
    subgoal for n op
      apply (cases op)
         apply (auto simp: step.intros)
      done
    done
  done

lemma step_choicesE:
  assumes  "step io op op'"
  obtains p f x where "io = Inp p x" "Read p f |\<in>| choices op" "op' = f x" |
    p x where "io = Out p x" "Write op' p x |\<in>| choices op" |
    "io = Tau" and "Silent op' |\<in>| choices op"
  apply (atomize_elim)
  using assms by (induct io op op' rule: step.induct) (auto 10 10)

lemma Choice_singleton_bisim:
  "Choice {|op|} ~ op"
  apply (rule bisim.intros)
  unfolding sim_def
   apply (auto intro: bisim_refl)
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
    subgoal
      apply simp
      apply (meson Silent_in_choices_step bc_refl cin.rep_eq)
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
    subgoal
      apply simp
      apply (metis Silent_in_choices_step bc_refl cin.rep_eq)
      done
    done
  done


lemma step_no_inputs:
  "step io op1 op1' \<Longrightarrow> io = Inp p x \<Longrightarrow> inputs op1 = {} \<Longrightarrow> False"
  apply (induct io op1  op1' rule: step.induct)
  apply auto
  done

lemma step_no_inputs_not_inputs:
  "step io op1 op1' \<Longrightarrow> inputs op1 = {} \<Longrightarrow> inputs op1' = {}"
  apply (induct io op1 op1' rule: step.induct)
  apply auto
  done

datatype ('a, 'b, 'd) VIO = VInp (vproji: 'a) (vdata: "'d") | VOut (vprojo: 'b) (vdata: 'd)
fun io_of_vio where
  "io_of_vio (VInp p x) = Inp p x"
| "io_of_vio (VOut p x) = Out p x"
fun vio_of_io where
  "vio_of_io (Inp p x) = VInp p x"
| "vio_of_io (Out p x) = VOut p x"
| "vio_of_io Tau = undefined"
lemma io_of_vio_inverse: "vio_of_io (io_of_vio vio) = vio"
  by (cases vio; simp)
lemma vio_of_io_inverse: "io \<noteq> Tau \<Longrightarrow> io_of_vio (vio_of_io io) = io"
  by (cases io; simp)
fun wsteps where
  "wsteps [] = rtranclp (step Tau)"
| "wsteps (vio # vios) = wstep (io_of_vio vio) OO wsteps vios"
definition "wsim' R op1 op2 = (\<forall>vios op1'. wsteps vios op1 op1' \<longrightarrow> (\<exists>op2'. wsteps vios op2 op2' \<and> R op1' op2'))"
abbreviation "wbisimulation' R \<equiv>
   (\<forall>op1 op2. R op1 op2 \<longrightarrow> wsim' R op1 op2 \<and> wsim' (conversep R) op2 op1)"
lemma wsim'D1: "wsim' R op1 op2 \<Longrightarrow> wstep (io_of_vio vio) op1 op1' \<Longrightarrow> \<exists>op2'. wstep (io_of_vio vio) op2 op2' \<and> R op1' op2'"
  unfolding wsim'_def
  by (auto 0 5 dest!: spec2[of _ "[vio]" op1'] simp: wstep_def intro: rtranclp_trans)

lemma wbisimulation_alt: "wbisimulation R \<longleftrightarrow> wbisimulation' R"
proof (intro allI impI iffI)
  fix op1 op2
  assume *: "wbisimulation R" "R op1 op2"
  have "wsim' R op1 op2"
    unfolding wsim'_def
  proof safe
    fix vios op1'
    assume "wsteps vios op1 op1'"
    with *(2) show "\<exists>op2'. wsteps vios op2 op2' \<and> R op1' op2'"
    proof (induct vios arbitrary: op1 op2)
      case Nil
      then show ?case
        unfolding wsteps.simps wstep_steps_Tau[symmetric]
        using wbisim_wstep[OF *(1)] by blast
    next
      case (Cons vio vios)
      then obtain op1'' where "wstep (io_of_vio vio) op1 op1''" and wsteps: "wsteps vios op1'' op1'"
        by auto
      then obtain op2'' where "wstep (io_of_vio vio) op2 op2''" "R op1'' op2''"
        using wbisim_wstep[OF *(1) Cons(2)] by blast
      moreover
      from Cons(1)[OF \<open>R op1'' op2''\<close> wsteps] obtain op2' where "wsteps vios op2'' op2'" "R op1' op2'" by blast
      ultimately show ?case by auto
    qed
  qed
  moreover have "wsim' R\<inverse>\<inverse> op2 op1"
    unfolding wsim'_def conversep_iff
  proof safe
    fix vios op2'
    assume "wsteps vios op2 op2'"
    with *(2) show "\<exists>op1'. wsteps vios op1 op1' \<and> R op1' op2'"
    proof (induct vios arbitrary: op1 op2)
      case Nil
      then show ?case
        unfolding wsteps.simps wstep_steps_Tau[symmetric]
        using wbisim_wstep'[OF *(1)] by blast
    next
      case (Cons vio vios)
      then obtain op2'' where "wstep (io_of_vio vio) op2 op2''" and wsteps: "wsteps vios op2'' op2'"
        by auto
      then obtain op1'' where "wstep (io_of_vio vio) op1 op1''" "R op1'' op2''"
        using wbisim_wstep'[OF *(1) Cons(2)] by blast
      moreover
      from Cons(1)[OF \<open>R op1'' op2''\<close> wsteps] obtain op1' where "wsteps vios op1'' op1'" "R op1' op2'" by blast
      ultimately show ?case by auto
    qed
  qed
  ultimately show "wsim' R op1 op2 \<and> wsim' R\<inverse>\<inverse> op2 op1" by blast
next
  fix op1 op2
  assume *: "wbisimulation' R" "R op1 op2"
  have "wsim R op1 op2"
    unfolding wsim_def
  proof safe
    fix io op1'
    assume step: "step io op1 op1'"
    then show "\<exists>op2'. wstep io op2 op2' \<and> R op1' op2'"
    proof (cases "io = Tau")
      case True
      with step have "wsteps [] op1 op1'" by auto
      then obtain op2' where "wsteps [] op2 op2'" "R op1' op2'" using *
        unfolding wsim'_def by blast
      with True show ?thesis
        by auto
    next
      case False
      from vio_of_io_inverse[OF False] step obtain vio where "wsteps [vio] op1 op1'" and vio[simp]: "io_of_vio vio = io"
        by auto
      then obtain op2' where "wsteps [vio] op2 op2'" "R op1' op2'" using *
        unfolding wsim'_def by blast
      then show ?thesis
        by (intro exI[of _ op2']) (fastforce simp: wstep_def)
    qed
  qed
  moreover have "wsim R\<inverse>\<inverse> op2 op1"
    unfolding wsim_def conversep_iff
  proof safe
    fix io op2'
    assume step: "step io op2 op2'"
    then show "\<exists>op1'. wstep io op1 op1' \<and> R op1' op2'"
    proof (cases "io = Tau")
      case True
      with step have "wsteps [] op2 op2'" by auto
      then obtain op1' where "wsteps [] op1 op1'" "R op1' op2'" using *
        unfolding wsim'_def by blast
      with True show ?thesis
        by auto
    next
      case False
      from vio_of_io_inverse[OF False] step obtain vio where "wsteps [vio] op2 op2'" and vio[simp]: "io_of_vio vio = io"
        by auto
      then obtain op1' where "wsteps [vio] op1 op1'" "R op1' op2'" using *
        unfolding wsim'_def by blast
      then show ?thesis
        by (intro exI[of _ op1']) (fastforce simp: wstep_def)
    qed
  qed
  ultimately show "wsim R op1 op2 \<and> wsim R\<inverse>\<inverse> op2 op1" by blast
qed

lemma wsim'_mono[mono]: "R \<le> S \<Longrightarrow> wsim' R \<le> wsim' S"
  by (force simp: wsim'_def le_fun_def)

coinductive wbisim' (infix "\<approx>\<approx>"40) where
  "wsim' wbisim' op1 op2 \<Longrightarrow> wsim' wbisim' op2 op1 \<Longrightarrow> wbisim' op1 op2"

lemma wbisim'_sym:
  "op1 \<approx>\<approx> op2 \<Longrightarrow> op2 \<approx>\<approx> op1"
  apply (coinduction arbitrary: op1 op2)
  subgoal for op1 op2
    apply simp
    unfolding wsim'_def wstep_def
    apply auto
    subgoal for io op
      apply (erule wbisim'.cases)
      unfolding wsim'_def wstep_def
      apply blast
      done
    subgoal for io op
      apply (erule wbisim'.cases)
      unfolding wsim'_def wstep_def
      apply blast
      done
    done
  done

lemma wbisimulation'_wbisim': "wbisimulation' (\<approx>\<approx>)"
  by (auto elim: wbisim'.cases elim!: wsim'_mono[THEN predicate2D, rotated] wbisim'_sym)

lemma wbisim'_wbisim: "op1 \<approx>\<approx> op2 \<Longrightarrow> op1 \<approx> op2"
  apply (coinduction arbitrary: op1 op2)
  using wbisimulation'_wbisim'[folded wbisimulation_alt]
  apply (auto elim!: wsim_mono[THEN predicate2D, rotated] wbisim'_sym)
  done

lemma wbisim_wbisim': "op1 \<approx> op2 \<Longrightarrow> op1 \<approx>\<approx> op2"
  apply (coinduction arbitrary: op1 op2)
  using wbisimulation_wbisim[unfolded wbisimulation_alt]
  apply (auto elim!: wsim'_mono[THEN predicate2D, rotated] wbisim_sym)
  done

lemma wbisim'_alt: "(\<approx>\<approx>) = (\<approx>)"
  using wbisim'_wbisim wbisim_wbisim'
  by blast

coinductive wfinished where
  "(\<forall>op. op |\<in>|ops \<longrightarrow> wfinished op) \<Longrightarrow> wfinished (Choice ops)"
| "wfinished op \<Longrightarrow> wfinished (Silent op)"

coinductive wtraced where
  Nil: "wtraced op LNil"
| Step: "wstep (io_of_vio vio) op op' \<Longrightarrow> wtraced op' lxs \<Longrightarrow> wtraced op (LCons vio lxs)"

inductive_cases wtraced_LNilE[elim!]: "wtraced op LNil"
inductive_cases wtraced_StepE[elim!]: "wtraced op (LCons vio lxs)"

definition "wtraces op = {lxs. wtraced op lxs}"

lemma finished_wfinished[simp]: "finished op \<Longrightarrow> wfinished op"
  by (coinduction arbitrary: op) (auto elim: finished.cases)

corec wfinished_wit where
  "wfinished_wit op = (if \<exists>op'. Silent op' |\<in>| choices op then LCons Tau (wfinished_wit (SOME op'. Silent op' |\<in>| choices op)) else LNil)"

lemma wfinished_choices_at: "wfinished op \<Longrightarrow> op' |\<in>| choices_at n op \<Longrightarrow> wfinished op'"
proof (induct n arbitrary: op)
  case 0
  then show ?case by (cases op) (auto intro: wfinished.intros)
next
  case (Suc n)
  then show ?case
    by (cases op) (auto 0 3 elim: wfinished.cases)
qed

lemma wfinished_choices: "wfinished op \<Longrightarrow> op' |\<in>| choices op \<Longrightarrow> wfinished op'"
  unfolding choices_def by (auto elim: wfinished_choices_at)

lemma wfinished_finished:
  "wfinished op \<Longrightarrow> \<not> (\<exists>op'. Silent op' |\<in>| choices op) \<Longrightarrow> finished op"
  by (coinduction arbitrary: op) (auto elim: wfinished.cases)

lemma lset_wfinished_wit: "x \<in> lset lxs \<Longrightarrow> lxs = wfinished_wit op \<Longrightarrow> x = Tau"
  apply (induct x lxs arbitrary: op rule: llist.set_induct)
  apply (subst (asm) wfinished_wit.code; simp split: if_splits)
  apply (subst (asm) (2) wfinished_wit.code; simp split: if_splits)
  done

lemma traced_wfinished_wit: "wfinished op \<Longrightarrow> traced op (wfinished_wit op)"
  apply (coinduction arbitrary: op)
  subgoal for op
    apply (cases "\<exists>op'. Silent op' |\<in>| choices op")
    subgoal
      apply (rule disjI2)
      apply (rule exI[of _ Tau])
      apply (rule exI[of _ op])
      apply (rule exI[of _ "SOME op'. Silent op' |\<in>| choices op"])
      apply (rule exI[of _ "wfinished_wit (SOME op'. Silent op' |\<in>| choices op)"])
      apply (rule conjI refl)+
      apply (subst wfinished_wit.code; simp)
      apply (rule conjI refl)+
       apply (rule Silent_in_choices_step)
       apply (erule someI_ex)
      apply (rule disjI1 exI conjI refl)+
      apply (drule wfinished_choices)
       apply (erule someI_ex)
      apply (blast elim: wfinished.cases)
      done
    apply (rule disjI1)
    apply (subst wfinished_wit.code; simp add: wfinished_finished)
    done
  done

coinductive fair_traced where
  Nil: "wfinished op \<Longrightarrow> fair_traced op (wfinished_wit op)"
| Step: "chain (step Tau) ops1 \<Longrightarrow> step io (last ops1) (hd ops2) \<Longrightarrow> io \<noteq> Tau \<Longrightarrow>
    chain (step Tau) ops2 \<Longrightarrow> fair_traced (last ops2) lxs \<Longrightarrow>
    fair_traced (hd ops1) (\<tau>shift ops1 (LCons io (\<tau>shift ops2 lxs)))"

lemma fair_traced_traced: "fair_traced op lxs \<Longrightarrow> traced op lxs"
  apply (coinduction arbitrary: op lxs rule: traced_coinduct_alt)
  subgoal for op lxs
    apply (erule fair_traced.cases; hypsubst_thin; simp)
     apply (drule traced_wfinished_wit)
     apply (erule traced_cases_alt)
      apply blast
     apply blast
    apply blast
    done
  done

corec wtraced_traced_wit where
  "wtraced_traced_wit op lxs = 
    (if wfinished op then wfinished_wit op
    else let io = io_of_vio (lhd lxs); lxs' = ltl lxs;
         (ops1, ops2) = SOME (ops1, ops2). hd ops1 = op \<and> chain (step Tau) ops1 \<and> step io (last ops1) (hd ops2) \<and> chain (step Tau) ops2 \<and> wtraced (last ops2) lxs'
     in \<tau>shift ops1 (LCons io (\<tau>shift ops2 (wtraced_traced_wit (last ops2) lxs'))))"

lemma WSC: "op |\<in>| ops \<Longrightarrow> wstep (io_of_vio vio) op op' \<Longrightarrow> wstep (io_of_vio vio) (Choice ops) op'"
  unfolding wstep_def
  apply clarsimp
  subgoal premises prems for opi opj
    using prems(2,1,3,4)
    apply (induct op rule: converse_rtranclp_induct)
     apply (cases vio; simp)
      apply (meson SC cin.rep_eq relcomppI rtranclp.rtrancl_refl)
     apply (meson SC cin.rep_eq relcomppI rtranclp.rtrancl_refl)
    apply (cases vio; simp)
     apply (meson SC cin.rep_eq converse_rtranclp_into_rtranclp relcomppI)
    apply (meson SC cin.rep_eq converse_rtranclp_into_rtranclp relcomppI)
    done
  done

lemma step_not_wfinished: "step (io_of_vio vio) op op' \<Longrightarrow> \<not> wfinished op"
  by (induct "io_of_vio vio" op op' pred: step) (cases vio; auto elim: wfinished.cases)+

lemma step_Tau_wfinished: "step Tau op op' \<Longrightarrow> wfinished op \<Longrightarrow> wfinished op'"
  by (induct op op' pred: step) (auto elim: wfinished.cases)

lemma wfinished_no_wstep:
  "wfinished op \<longleftrightarrow> \<not> (\<exists>vio op'. wstep (io_of_vio vio) op op')"
  apply safe
  subgoal for vio op'
    unfolding wstep_def
    apply clarsimp
    subgoal premises prems for opi opj
      using prems(2,1,3,4)
      apply (induct op rule: converse_rtranclp_induct)
      using step_not_wfinished[of vio opi opj]
       apply (cases vio; auto elim: wfinished.cases)
      apply (auto dest: step_Tau_wfinished)
      done
    done
  subgoal
    apply (coinduction arbitrary: op)
    subgoal for op
      apply (cases op)
         apply (auto)
      apply (metis SR io_of_vio.simps(1) step_wstep)
       apply (metis SW io_of_vio.simps(2) step_wstep)
      apply (meson WSC cin.rep_eq)
      done
    done
  done
(* 
lemma wtraced_fair_traced: "wtraced op lxs \<Longrightarrow> fair_traced op (wtraced_traced_wit op lxs)"
  apply (coinduction arbitrary: op lxs)
  apply (erule wtraced.cases)
    apply (subst wtraced_traced_wit.code; simp)
   apply (rule disjI2)
   apply (subst wtraced_traced_wit.code; simp)
  apply (auto simp: Let_def split_beta wfinished_no_wstep)
  apply (auto simp add: wstep_def dest!: rtranclp_chain)
  apply (rule exI)
  apply (rule conjI[rotated])
   apply (rule exI conjI)+
    apply (rule refl)
   apply (rule someI2_ex)
  subgoal for vio
    apply (cases vio; auto)
    done
  subgoal for vio
    apply (cases vio; auto)
    done
  apply (rule someI2_ex)
  subgoal for vio
    apply (cases vio; auto)
    done
  apply force
  done *)

lemma io_of_vio_not_Tau[simp]:
  "Tau \<noteq> io_of_vio vio"
  "io_of_vio vio \<noteq> Tau"
  by (cases vio; auto)+

lemma lfilter_Tau_lshift[simp]: "lfilter ((\<noteq>) Tau) (lshift (replicate n Tau) lxs) = lfilter ((\<noteq>) Tau) lxs"
  by (induct n) auto
lemma ldropWhile_Tau_lshift[simp]: "ldropWhile ((=) Tau) (lshift (replicate n Tau) lxs) = ldropWhile ((=) Tau) lxs"
  by (induct n) auto
(* 
lemma lmap_lfilter_wtraced_traced_wit: "wtraced op lxs \<Longrightarrow> lmap vio_of_io (lfilter ((\<noteq>) Tau) (wtraced_traced_wit op lxs)) = lxs"
  apply (coinduction arbitrary: op lxs)
  apply simp
  apply (intro conjI impI)
    apply (subst wtraced_traced_wit.code)
    apply (auto dest: lset_wfinished_wit simp: wfinished_no_wstep Let_def split_beta elim: wtraced.cases) []
   apply (subst wtraced_traced_wit.code)
   apply (auto dest: lset_wfinished_wit simp: wfinished_no_wstep Let_def split_beta io_of_vio_inverse
     elim: wtraced.cases) []
  apply (subst wtraced_traced_wit.code)
  apply (auto dest: lset_wfinished_wit simp: wfinished_no_wstep Let_def split_beta io_of_vio_inverse
     elim: wtraced.cases) []
  apply (rule exI conjI refl)+
  apply (rule someI2_ex)
   apply (erule wtraced.cases)
  apply (auto simp add: wstep_def dest!: rtranclp_chain)
  subgoal for _ _ vio
    apply (cases vio; auto)
    done
  done
 *)
lemma chain_rtranclp: "chain R xs \<Longrightarrow> rtranclp R (hd xs) (last xs)"
  by (induct xs rule: chain.induct) auto

lemma traced_wtraced: "fair_traced op lxs \<Longrightarrow> wtraced op (lmap vio_of_io (lfilter ((\<noteq>) Tau) lxs))"
  apply (coinduction arbitrary: op lxs)
  apply (erule fair_traced.cases)
   apply (auto simp: vio_of_io_inverse lmap_eq_LNil lfilter_eq_LNil
    lmap_eq_LCons_conv dest: lset_wfinished_wit)
    apply (rule exI conjI[rotated] disjI1)+
      apply assumption
     apply (rule refl)
  apply (auto simp add: wstep_def dest: chain_rtranclp) []
  done

definition "fair_traces op = {lxs. fair_traced op lxs}"

(* lemma wtraces_alt: "wtraces op = ((lmap vio_of_io o lfilter ((\<noteq>) Tau)) ` fair_traces op)"
  unfolding wtraces_def fair_traces_def
  apply (auto simp: traced_wtraced image_iff
    intro!: lmap_lfilter_wtraced_traced_wit[symmetric] wtraced_fair_traced)
  done *)

lemmas wbisim_coinduct_alt = wbisim'.coinduct[unfolded wbisim'_alt]
lemmas wbisim_cases_alt = wbisim'.cases[unfolded wbisim'_alt]

thm wbisim_wstep[OF wbisimulation_wbisim]

lemma wbisim_wfinished: "op1 \<approx> op2 \<Longrightarrow> wfinished op1 \<Longrightarrow> wfinished op2"
  unfolding wfinished_no_wstep by (erule wbisim_cases_alt) (auto dest: wsim'D1)

lemma wbisim_wtraced: "op1 \<approx> op2 \<Longrightarrow> wtraced op1 lxs \<Longrightarrow> wtraced op2 lxs"
  apply (coinduction arbitrary: op1 op2 lxs rule: wtraced.coinduct)
  apply (erule wtraced.cases)
   apply (rule disjI1)
   apply (auto intro: wbisim_wfinished) []
  apply hypsubst_thin
  apply clarsimp
  apply (erule wbisim_cases_alt)
  apply (auto dest!: wsim'D1)
  done

abbreviation wtrace_equiv (infix "\<equiv>\<^sub>t"40) where
 "wtrace_equiv op1 op2 \<equiv> wtraces op1 = wtraces op2" 

lemma wtrace_equiv_refl:
  "op1 \<equiv>\<^sub>t op1"
  by simp

lemma wtrace_equiv_sym:
  "op1 \<equiv>\<^sub>t op2 \<longleftrightarrow> op2 \<equiv>\<^sub>t op1"
  by auto

lemma wtrace_equiv_trans:
  "op1 \<equiv>\<^sub>t op2 \<Longrightarrow> op2 \<equiv>\<^sub>t op3 \<Longrightarrow> op1 \<equiv>\<^sub>t op3"
  by auto

term map_op

lemma wbisim_wtraces: "op1 \<approx> op2 \<Longrightarrow> op1 \<equiv>\<^sub>t op2"
  by (auto simp: wtraces_def elim: wbisim_wtraced wbisim_wtraced[OF wbisim_sym])

lemma lmap_vio_of_io:
  "lmap (\<lambda>z. io_of_vio (vio_of_io z)) (lfilter ((\<noteq>) Tau) lxs) = lfilter ((\<noteq>) Tau) lxs"
  by (rule llist.map_ident_strong) (auto simp: vio_of_io_inverse)

(* lemma wbisim_fair_traces:
  "op1 \<approx> op2 \<Longrightarrow> lfilter ((\<noteq>) Tau) ` fair_traces op1 = lfilter ((\<noteq>) Tau) ` fair_traces op2"
  by (drule wbisim_wtraces, unfold wtraces_alt, drule image_eq_imp_comp[where h = "lmap io_of_vio"])
    (auto simp: wtraces_alt simp: llist.map_comp lmap_vio_of_io) *)

section\<open>Convenient types\<close>

type_synonym 'd op22 = "(2, 2, 'd) op"
type_synonym 'd op11 = "(1, 1, 'd) op"


(* FIXME : move *)
lemma map_IO_projr_eq_Out[intro!]:
  "IO = Out (Inr p) x \<Longrightarrow>
   map_IO f projr id IO = Out p x"
  by auto

lemma map_IO_projl_eq_Inp[intro!]:
  "IO = Inp (Inl p) x \<Longrightarrow>
   map_IO projl g id IO = Inp p x"
  by auto


(* FIXME: move me *)
lemma choices_at_sub_op:
  "op |\<in>| (choices_at n op') \<Longrightarrow> \<exists> m \<le> n. sub_op op op' m"
  apply (induct n arbitrary: op op')
  subgoal for op op'
    apply (cases op')
       apply auto
    done
  subgoal for n op op'
    apply (cases op')
    by fastforce+
  done

lemma choices_sub_op:
  "op |\<in>| choices op' \<Longrightarrow> \<exists> n. sub_op op op' n"
  unfolding choices_def
  using choices_at_sub_op by force

lemma Read_choices_inputs:
  "Read p f |\<in>| choices op \<Longrightarrow> p \<in> inputs op"
  by (meson choices_sub_op sub_op_Read_inputs)

lemma inputs_after_choices_at:
  "p' \<in> inputs op' \<Longrightarrow> op' |\<in>| choices_at n op \<Longrightarrow> p' \<in> inputs op"
  apply (induct n arbitrary: op)
  subgoal for op
    apply (cases op)
       apply auto
    done
  subgoal for n op
    apply (cases op)
       apply auto
    done
  done

(* FIXME: move me *)
lemma inputs_after_choices:
  "op' |\<in>| (choices op) \<Longrightarrow> p' \<in> inputs op' \<Longrightarrow> p' \<in> inputs op"
  unfolding choices_def
    inputs_after_choices_at 
  by (meson cUN_E inputs_after_choices_at)
(* FIXME: move me *)
lemma step_inputs_outputs:
  "step io op op' \<Longrightarrow>
   inputs op' \<subseteq> inputs op \<and> outputs op' \<subseteq> outputs op"
  by (induct io op op' pred: step) auto
(* FIXME: move me *)
lemma step_inputs_not_in_defaults[elim!]:
  "inputs op \<inter> defaults = {} \<Longrightarrow>
   p \<in> defaults \<Longrightarrow> step (Inp p x) op op' \<Longrightarrow> False"
  by (auto simp add: Read_choices_inputs disjoint_iff elim: step_choicesE)

lemma Write_choices_outputs:
  "Write op p x |\<in>| choices op \<Longrightarrow> p \<in> outputs op"
  using choices_sub_op by blast

lemma outputs_after_choices_at:
  "p' \<in> outputs op' \<Longrightarrow> op' |\<in>| choices_at n op \<Longrightarrow> p' \<in> outputs op"
  apply (induct n arbitrary: op)
  subgoal for op
    apply (cases op)
       apply auto
    done
  subgoal for n op
    apply (cases op)
       apply auto
    done
  done

lemma outputs_after_choices:
  "op' |\<in>| (choices op) \<Longrightarrow> p' \<in> outputs op' \<Longrightarrow> p' \<in> outputs op"
  unfolding choices_def
  by (meson cUN_E outputs_after_choices_at)
lemma step_outputs_not_in_defaults[elim!]:
  "outputs op \<inter> defaults = {} \<Longrightarrow>
   p \<in> defaults \<Longrightarrow> step (Out p x) op op' \<Longrightarrow> False"
  by (auto simp add: outputs_after_choices Write_choices_outputs disjoint_iff elim: step_choicesE)

lemma step_Inp_inputs:
  "step (Inp p x) op op' \<Longrightarrow> p \<in> inputs op"
  by (metis IO.distinct(3) IO.sel(1) IO.simps(4) Read_choices_inputs step_choicesE)

lemma step_Out_outputs:
  "step (Out p x) op op' \<Longrightarrow> p \<in> outputs op"
  by (metis IO.distinct(5) IO.sel(4) IO.simps(4) op.set_intros(8) outputs_after_choices step_choicesE)

lemma wstep_Inp_inputs:
  "wstep (Inp p x) op opf \<Longrightarrow> p \<in> inputs op"
  unfolding wstep_def
  apply safe
  subgoal for op' op''
    apply (induct op rule: converse_rtranclp_induct)
    subgoal
      using step_Inp_inputs by force
    subgoal for op1 op2
      using step_inputs_outputs by blast
    done
  done

lemma wstep_Out_outputs:
  "wstep (Out p x) op opf \<Longrightarrow> p \<in> outputs op"
  unfolding wstep_def
  apply safe
  subgoal for op' op''
    apply (induct op rule: converse_rtranclp_induct)
    subgoal
      using step_Out_outputs by force
    subgoal for op1 op2
      using step_inputs_outputs by blast
    done
  done

lemma wsim_Silent[simp]: "wsim R (Silent op'') op \<longleftrightarrow> (\<exists>op'. wstep Tau op op' \<and> R op'' op')"
  by (fastforce simp: wsim_def)

lemma step_taus_inputs_outputs:
  "(step Tau)\<^sup>*\<^sup>* op op' \<Longrightarrow>
   inputs op' \<subseteq> inputs op \<and> outputs op' \<subseteq> outputs op"
  apply (induct op arbitrary:  rule: converse_rtranclp_induct)
  subgoal
    by simp
  subgoal
    by (meson dual_order.trans step_inputs_outputs)
  done

lemma wstep_inputs_outputs:
  "wstep io op op' \<Longrightarrow>
   inputs op' \<subseteq> inputs op \<and> outputs op' \<subseteq> outputs op"
  unfolding wstep_def by (smt (verit, ccfv_SIG) estep.elims pick_middlep rtranclp.rtrancl_into_rtrancl rtranclp_less_eq step_inputs_outputs step_taus_inputs_outputs wstep_def wstep_steps_Tau)

lemma wstep_Inp: "wstep (Inp p x) op op' \<Longrightarrow> p \<in> inputs op"
  unfolding wstep_def
  by (auto dest!: step_taus_inputs_outputs elim!: step_choicesE dest: Read_choices_inputs)

lemma sub_op_Read_wsim: "sub_op (Read p f) op n \<Longrightarrow> wsim (\<approx>) op op' \<Longrightarrow> \<exists>g m. sub_op (Read p g) op' m"
  apply (induct op n arbitrary: op' rule: sub_op.induct)
      apply auto
     apply (meson inputs_sub_op_Read wstep_Inp)
  subgoal for g x n q op
    apply (drule spec[of _ x])
    apply (auto elim!: wbisim.cases)
    apply (metis inputs_sub_op_Read sub_op_Read_inputs subset_iff wstep_inputs_outputs)
    done
  subgoal for g x n q op
    apply (auto elim!: wbisim.cases)
    apply (metis inputs_sub_op_Read sub_op_Read_inputs subset_iff wstep_inputs_outputs)
    done
  subgoal for op n op'
    apply (auto elim!: wbisim.cases)
    apply (meson inputs_sub_op_Read step_taus_inputs_outputs sub_op_Read_inputs subsetD)
    done
  done

lemma wsim_inputs: "wsim (\<approx>) op op' \<Longrightarrow> p \<in> inputs op \<Longrightarrow> p \<in> inputs op'"
  by (meson inputs_sub_op_Read sub_op_Read_inputs sub_op_Read_wsim)

lemma wbisim_inputs: "op \<approx> op' \<Longrightarrow> inputs op = inputs op'"
  by (meson antisym wsim_inputs subset_eq wbisim.cases)

lemma wstep_Out: "wstep (Out p x) op op' \<Longrightarrow> p \<in> outputs op"
  unfolding wstep_def
  by (auto dest!: step_taus_inputs_outputs outputs_after_choices elim!: step_choicesE)

lemma sub_op_Write_wsim: "sub_op (Write opw p x) op n \<Longrightarrow> wsim (\<approx>) op op' \<Longrightarrow> \<exists>x op m. sub_op (Write op p x) op' m"
  apply (induct op n arbitrary: op' rule: sub_op.induct)
      apply auto
     apply (meson outputs_sub_op_Write wstep_Out)
  subgoal for g x n q op
    apply (drule spec[of _ x])
    apply (auto elim!: wbisim.cases)
    apply (meson in_mono outputs_sub_op_Write sub_op_Write_outputs wstep_inputs_outputs)
    done
  subgoal for g x n q op
    apply (auto elim!: wbisim.cases)
    apply (meson in_mono outputs_sub_op_Write sub_op_Write_outputs wstep_inputs_outputs)
    done
  subgoal for op n op'
    apply (auto elim!: wbisim.cases)
    apply (meson outputs_sub_op_Write step_taus_inputs_outputs sub_op_Write_outputs subset_iff)
    done
  done

lemma wsim_outputs: "wsim (\<approx>) op op' \<Longrightarrow> p \<in> outputs op \<Longrightarrow> p \<in> outputs op'"
  by (meson outputs_sub_op_Write sub_op_Write_outputs sub_op_Write_wsim)

lemma wbisim_outputs: "op \<approx> op' \<Longrightarrow> outputs op = outputs op'"
  by (meson antisym wsim_outputs subset_eq wbisim.cases)

section \<open>Shows our definitions to match the literature\<close>

definition "simulation_canonical R = (\<forall> op1 op2. R op1 op2 \<longrightarrow> (\<forall> io op1'. step io op1 op1' \<longrightarrow> (\<exists> op2'. step io op2 op2' \<and> R op1' op2')))" 
lemma sim_correct:
  "simulation_canonical R = (\<forall> op1 op2. R op1 op2 \<longrightarrow> (sim R op1 op2))"
  unfolding sim_def simulation_canonical_def by auto

abbreviation "bisimulation_canonical R \<equiv> simulation_canonical R \<and> simulation_canonical (conversep R)"
abbreviation "bisimulation R \<equiv> (\<forall>op1 op2. R op1 op2 \<longrightarrow> sim R op1 op2 \<and> sim (conversep R) op2 op1)"

lemma bisimulation_correct:
  "bisimulation_canonical R = bisimulation R"
    by (auto simp add: sim_def simulation_canonical_def)

lemma bisim_set_correct:
 "(~) = \<Squnion> {R. bisimulation_canonical R}"
  unfolding sim_def simulation_canonical_def
  apply (rule ext)+
  apply safe
  subgoal for op1 op2
    apply clarsimp
    apply (smt (verit) bisim.cases bisim_sym sim_def)
    done
  subgoal for op1 op2 R
    apply (coinduction arbitrary: op1 op2 rule: bisim_coinduct)
     apply blast+
    done
  done

lemma wsim_correct:
  "wsimulation_canonical R = (\<forall> op1 op2. R op1 op2 \<longrightarrow> (wsim R op1 op2))"
  unfolding wsim_def wsimulation_canonical_def by auto

lemma wbisimulation_correct:
  "wbisimulation_canonical R = wbisimulation R"
  by (auto simp add: wsim_def wsimulation_canonical_def)

lemma wbisim_set_correct:
 "(\<approx>) = \<Squnion> {R. wbisimulation_canonical R}"
  unfolding wsim_def wsimulation_canonical_def
  apply (rule ext)+
  apply safe
  subgoal for op1 op2
    apply clarsimp
    apply (smt (verit) wbisim.cases wbisim_sym wsim_def)
    done
  subgoal for op1 op2 R
    apply (coinduction arbitrary: op1 op2 rule: wbisim_coinduct)
     apply blast+
    done
  done

end