theory Operational

imports
  "HOL-Library.Countable_Set_Type"
  "Composition"
begin

section \<open>Syntax\<close>

datatype 'd dataflow =
    Stu 
  | Wri 'd "'d dataflow"
  | Rea 'd "'d dataflow"
  | Par "'d dataflow" "'d dataflow" 
  | Cho "('d dataflow) cset"
(*   | Seq "'d dataflow" "'d dataflow" 
 *)
    (* TODO: add loop, join and merge *)

datatype 'd io = In 'd | Ou 'd 
  (* | Tau *)

inductive step where
  "step (Rea d df) (In d) df"
| "step (Wri d df) (Ou d) df"
| "step df1 io df1' \<Longrightarrow> step (Par df1 df2) io (Par df1' df2)"
| "step df2 io df2' \<Longrightarrow> step (Par df1 df2) io (Par df1 df2')"
| "step df io df' \<Longrightarrow> cin df dts \<Longrightarrow> step (Cho dts) io df'"

(* | "step df1 (Ou d) df1' \<Longrightarrow> step df2 (In d) df2' \<Longrightarrow> step (Seq df1 df2) Tau (Seq df1' df2')"
 *)

inductive_cases stepEndE [elim!]: "step Stu io df'"
inductive_cases stepReaE [elim!]: "step (Rea d df) io df'"
inductive_cases stepWriE [elim!]: "step (Wri d df) io df'"
(* inductive_cases stepSeqE [elim!]: "step (Seq df1 df2) io df'"
 *)
inductive_cases stepParE [elim!]: "step (Par df1 df2) io df'"
inductive_cases stepChoiE [elim!]: "step (Cho dts) io df'"

definition "dsim R s t = (\<forall>l s'. step s l s' \<longrightarrow> (\<exists>t'. step t l t' \<and> R s' t'))"

lemma sim_mono[mono]: "R \<le> S \<Longrightarrow> dsim R \<le> dsim S"
  by (force simp: dsim_def le_fun_def)

coinductive dbisim where
  "dsim dbisim s t \<Longrightarrow> dsim dbisim t s \<Longrightarrow> dbisim s t"

inductive dbisim_cong for R where
  dbc_base:  "R x y \<Longrightarrow> dbisim_cong R x y"
| dbc_bisim:  "dbisim x y \<Longrightarrow> dbisim_cong R x y"
| dbc_refl: "x = y \<Longrightarrow> dbisim_cong R x y"
| dbc_sym: "dbisim_cong R x y \<Longrightarrow> dbisim_cong R y x"
| dbc_trans: "dbisim_cong R x y \<Longrightarrow> dbisim_cong R y z \<Longrightarrow> dbisim_cong R x z"
| dbc_Rea:"dbisim_cong R df1 df2 \<Longrightarrow> dbisim_cong R (Rea d df1) (Rea d df2)"
| dbc_Wri:"dbisim_cong R df1 df2 \<Longrightarrow> dbisim_cong R (Wri d df1) (Wri d df2)"
| dbc_Par:"dbisim_cong R df1 df1' \<Longrightarrow> dbisim_cong R df2 df2' \<Longrightarrow> dbisim_cong R (Par df1 df2) (Par df1' df2')"
| dbc_Cho:"rel_cset (dbisim_cong R) dfs dfs' \<Longrightarrow> dbisim_cong R (Cho dfs) (Cho dfs')"

(* | dbc_Seq:"dbisim_cong R df1 df1' \<Longrightarrow> dbisim_cong R df2 df2' \<Longrightarrow> dbisim_cong R (Seq df1 df2) (Seq df1' df2')"
 *)

lemma bisim_cong_disj:
  "(dbisim_cong R x y \<or> dbisim x y) = dbisim_cong R x y"
  by (auto intro: dbisim_cong.intros)

lemma dbisim_coinduct_upto:
  "R df1 df2 \<Longrightarrow>
   (\<And>x1 x2. R x1 x2 \<Longrightarrow> \<exists>s t. x1 = s \<and> x2 = t \<and> dsim (dbisim_cong R) s t \<and> dsim (dbisim_cong R) t s) \<Longrightarrow>
   dbisim df1 df2"
  apply (rule dbisim.coinduct[where X="dbisim_cong R", of df1 df2, unfolded bisim_cong_disj])
   apply (simp add: dbc_base)
  subgoal premises prems for df1 df2
    using prems(3) apply -
    apply (induct df1 df2 rule: dbisim_cong.induct)
    subgoal
      by (meson bc_base prems(2))
    subgoal
      by (metis dbc_bisim dbisim.cases dsim_def)
    subgoal
      by (metis dbc_refl dsim_def)
    subgoal
      by blast
    subgoal
      by (auto 10 10 simp add: dsim_def intro: dbc_trans)
    subgoal
      by (auto simp add: dsim_def intro: step.intros dbc_sym)
    subgoal
      by (auto simp add: dsim_def intro: step.intros dbc_sym)
  (*   subgoal
      by (auto 10 10 simp add: dsim_def intro: step.intros dbc_Seq)
 *)    subgoal
      by (auto 10 10 simp add: dsim_def intro: step.intros dbc_sym dbc_Par)
    subgoal
      unfolding rel_cset.rep_eq rel_set_def
      by (fastforce simp: Ball_def Bex_def dsim_def bot_cset.rep_eq
          simp flip: bot_cset.abs_eq cin.rep_eq
          dest!: arg_cong[where f="acset"] intro: step.intros)
    done
  done

lemma Par_comm:
  "dbisim (Par df1 df2) (Par df2 df1)"
  by (coinduction arbitrary: df1 df2) (auto simp add: dsim_def intro: step.intros)

lemma Par_End1:
  "dbisim (Par df Stu) df"
  by (coinduction arbitrary: df rule: dbisim_coinduct_upto) (auto simp add: dsim_def intro: dbc_base dbc_sym step.intros)

lemma Par_End2:
  "dbisim (Par Stu df) df"
  by (coinduction arbitrary: df rule: dbisim_coinduct_upto) (auto simp add: dsim_def intro: dbc_base dbc_sym step.intros)

lemma Par_Assoc:
  "dbisim (Par df1 (Par df2 df3)) (Par (Par df1 df2) df3)"
  by (coinduction arbitrary: df1 df2 df3 rule: dbisim_coinduct_upto) (auto 10 10 simp add: dsim_def intro: dbc_base dbc_sym step.intros)

(* lemma Seq_Assoc:
  "dbisim (Seq df1 (Seq df2 df3)) (Seq (Seq df1 df2) df3)"
  by (coinduction arbitrary: df1 df2 df3 rule: dbisim_coinduct_upto) (auto simp add: dsim_def)
 *)

function embed :: "'d dataflow \<Rightarrow> (_, _, 'd) op" where
  "embed Stu = End"
| "embed (Par df1 df2) = pcomp_op (map_op projl projl (embed df1)) (map_op projr projr (embed df2))"
| "embed (Wri d df) = Write (embed df) (Inl 1) d"
| "embed (Rea d df) = Read (Inl 1) (\<lambda> _. embed df)"
| "embed (Cho dfs) = Choice (cimage embed dfs)"
                      apply auto
  by (meson dataflow.exhaust)
termination
  sorry

fun embed_IO where
  "embed_IO (In x) = Inp (Inl 1) (Observed x)"
| "embed_IO (Ou x) = Out (Inl 1) x"


lemma
  "step df io df' \<Longrightarrow>
   stepped (embed df) (embed_IO io) (embed df')"
  apply (induct df io df' rule: step.induct)
       apply (auto intro: stepped.intros)
  subgoal for df1 io df1' df2
    oops


lemma
  "step df1 io df1' \<Longrightarrow>
   stepped (pcomp_op (map_op projl projl (Operational.embed df1)) (map_op projr projr (Operational.embed df2))) (embed_IO io)
  (pcomp_op (map_op projl projl (Operational.embed df1')) (map_op projr projr (Operational.embed df2)))"
  apply (induct df1 io df1' arbitrary: df2 rule: step.induct)
  subgoal for d df df2
    apply (cases df; cases df2)
    subgoal
      by (auto simp add: comp_def intro: stepped.intros)
    subgoal
      apply (clarsimp simp add: comp_def intro: stepped.intros)
      oops

lemma
  "bisim (embed (df :: 'd dataflow)) (op :: (_, _, 'd) op) \<Longrightarrow>
   io \<noteq> Tau \<Longrightarrow>
   step df io df' \<Longrightarrow>
   \<exists> op'. stepped op (embed_IO io) op' \<and> bisim (embed df') op'"
  apply (rotate_tac 2)
  apply (induction df io df' arbitrary: op rule: step.induct)
  subgoal
    apply (erule bisim.cases)
    apply (auto simp add: sim_def intro: stepped.intros)
    done
  subgoal
    apply (erule bisim.cases)
    apply (auto simp add: sim_def intro: stepped.intros)
    done
  subgoal
    apply (erule bisim.cases)
    apply (auto simp add: sim_def intro: stepped.intros)
    oops

end

