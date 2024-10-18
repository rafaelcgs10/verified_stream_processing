theory Operational

imports
  "HOL-Library.Countable_Set_Type"
begin

section \<open>Syntax\<close>

datatype 'd dataflow =
    End 
  | Wri 'd "'d dataflow"
  | Rea 'd "'d dataflow"
  | Seq "'d dataflow" "'d dataflow" 
  | Par "'d dataflow" "'d dataflow" 
  | Cho "('d dataflow) cset"
(* TODO: add loop, join and merge *)

datatype 'd io = In 'd | Ou 'd | Tau

inductive step where
  "step (Rea d df) (In d) df"
| "step (Wri d df) (Ou d) df"
| "step df1 (Ou d) df1' \<Longrightarrow> step df2 (In d) df2' \<Longrightarrow> step (Seq df1 df2) Tau (Seq df1' df2')"
| "step df1 io df1' \<Longrightarrow> step (Par df1 df2) io (Par df1' df2)"
| "step df2 io df2' \<Longrightarrow> step (Par df1 df2) io (Par df1 df2')"
| "step df io df' \<Longrightarrow> cin df dts \<Longrightarrow> step (Cho dts) io df'"

inductive_cases stepEndE [elim!]: "step End io df'"
inductive_cases stepReaE [elim!]: "step (Rea d df) io df'"
inductive_cases stepWriE [elim!]: "step (Wri d df) io df'"
inductive_cases stepSeqE [elim!]: "step (Seq df1 df2) io df'"
inductive_cases stepParE [elim!]: "step (Par df1 df2) io df'"
inductive_cases stepChoiE [elim!]: "step (Cho dts) io df'"

definition "sim R s t = (\<forall>l s'. step s l s' \<longrightarrow> (\<exists>t'. step t l t' \<and> R s' t'))"

lemma sim_mono[mono]: "R \<le> S \<Longrightarrow> sim R \<le> sim S"
  by (force simp: sim_def le_fun_def)

coinductive bisim where
  "sim bisim s t \<Longrightarrow> sim bisim t s \<Longrightarrow> bisim s t"

inductive bisim_cong for R where
  bc_base:  "R x y \<Longrightarrow> bisim_cong R x y"
| bc_bisim:  "bisim x y \<Longrightarrow> bisim_cong R x y"
| bc_refl: "x = y \<Longrightarrow> bisim_cong R x y"
| bc_sym: "bisim_cong R x y \<Longrightarrow> bisim_cong R y x"
| bc_trans: "bisim_cong R x y \<Longrightarrow> bisim_cong R y z \<Longrightarrow> bisim_cong R x z"
| bc_Rea:"bisim_cong R df1 df2 \<Longrightarrow> bisim_cong R (Rea d df1) (Rea d df2)"
| bc_Wri:"bisim_cong R df1 df2 \<Longrightarrow> bisim_cong R (Wri d df1) (Wri d df2)"
| bc_Seq:"bisim_cong R df1 df1' \<Longrightarrow> bisim_cong R df2 df2' \<Longrightarrow> bisim_cong R (Seq df1 df2) (Seq df1' df2')"
| bc_Par:"bisim_cong R df1 df1' \<Longrightarrow> bisim_cong R df2 df2' \<Longrightarrow> bisim_cong R (Par df1 df2) (Par df1' df2')"
| bc_Cho:"rel_cset (bisim_cong R) dfs dfs' \<Longrightarrow> bisim_cong R (Cho dfs) (Cho dfs')"

lemma bisim_cong_disj:
  "(bisim_cong R x y \<or> bisim x y) = bisim_cong R x y"
  by (auto intro: bisim_cong.intros)

lemma bisim_coinduct_upto:
  "R df1 df2 \<Longrightarrow>
   (\<And>x1 x2. R x1 x2 \<Longrightarrow> \<exists>s t. x1 = s \<and> x2 = t \<and> sim (bisim_cong R) s t \<and> sim (bisim_cong R) t s) \<Longrightarrow>
   bisim df1 df2"
  apply (rule bisim.coinduct[where X="bisim_cong R", of df1 df2, unfolded bisim_cong_disj])
   apply (simp add: bc_base)
  subgoal premises prems for df1 df2
    using prems(3) apply -
    apply (induct df1 df2 rule: bisim_cong.induct)
    subgoal
      by (meson bc_base prems(2))
    subgoal
      by (metis bc_bisim bisim.cases sim_def)
    subgoal
      by (metis bc_refl sim_def)
    subgoal
      by blast
    subgoal
      by (auto 10 10 simp add: sim_def intro: bc_trans)
    subgoal
      by (auto simp add: sim_def intro: step.intros bc_sym)
    subgoal
      by (auto simp add: sim_def intro: step.intros bc_sym)
    subgoal
      by (auto 10 10 simp add: sim_def intro: step.intros bc_Seq)
    subgoal
      by (auto 10 10 simp add: sim_def intro: step.intros bc_sym bc_Par)
    subgoal
      unfolding rel_cset.rep_eq rel_set_def
      by (fastforce simp: Ball_def Bex_def sim_def bot_cset.rep_eq
          simp flip: bot_cset.abs_eq cin.rep_eq
          dest!: arg_cong[where f="acset"] intro: step.intros)
    done
  done

lemma Par_comm:
  "bisim (Par df1 df2) (Par df2 df1)"
  by (coinduction arbitrary: df1 df2) (auto simp add: sim_def intro: step.intros)

lemma Par_End1:
  "bisim (Par df End) df"
  by (coinduction arbitrary: df rule: bisim_coinduct_upto) (auto simp add: sim_def intro: bc_base bc_sym step.intros)

lemma Par_End2:
  "bisim (Par End df) df"
  by (coinduction arbitrary: df rule: bisim_coinduct_upto) (auto simp add: sim_def intro: bc_base bc_sym step.intros)

lemma Par_Assoc:
  "bisim (Par df1 (Par df2 df3)) (Par (Par df1 df2) df3)"
  by (coinduction arbitrary: df1 df2 df3 rule: bisim_coinduct_upto) (auto 10 10 simp add: sim_def intro: bc_base bc_sym step.intros)

lemma Seq_Assoc:
  "bisim (Seq df1 (Seq df2 df3)) (Seq (Seq df1 df2) df3)"
  by (coinduction arbitrary: df1 df2 df3 rule: bisim_coinduct_upto) (auto simp add: sim_def)

end

