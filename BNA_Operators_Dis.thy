
theory BNA_Operators_Dis

imports
  "HOL-ex.Sketch_and_Explore"
  Eval
begin


section \<open>sum_op\<close>

datatype (discs_sels) sum_op_aux =
  sum_Read_aux "1" "(nat \<times> nat) \<Rightarrow> (nat \<Rightarrow> nat)"
  | sum_Write_aux "nat \<Rightarrow> nat" "1" "nat \<times> nat"
  | sum_Silent_aux "nat \<Rightarrow> nat"

abbreviation eval_sum_op_aux where
  "eval_sum_op_aux c aux \<equiv> (case aux of
    sum_Read_aux p f \<Rightarrow> Read p (\<lambda>y. let part_sum = f y in c part_sum)
  | sum_Write_aux part_sum q x \<Rightarrow> (Write (c part_sum) q x))"

corec sum_op :: "_ \<Rightarrow> (1, 1, nat \<times> nat) op" where
  "sum_op part_sum = Choice (cimage (eval_sum_op_aux sum_op) (cUn 
    (csingle (sum_Read_aux 1 (\<lambda> (n,m). part_sum(n:= part_sum n + m)))) 
    (cimage (\<lambda> n. sum_Write_aux (part_sum(n := 0)) 1 (n, part_sum n)) (cfilter (\<lambda> n. part_sum n \<noteq> 0) (acset Nats)))))"

lemma sum_op_code[code]:
  "sum_op part_sum = Choice (cUn 
    (csingle (Read 1 ((\<lambda> (n,m). sum_op (part_sum(n:= part_sum n + m))))))
    (cimage (\<lambda> n. Write (sum_op (part_sum(n := 0))) 1 (n, part_sum n)) (cfilter (\<lambda> n. part_sum n \<noteq> 0) (acset Nats))))"
  apply (subst sum_op.code)
  apply (unfold cimage_cUn cimage_cinsert op.inject)
  apply simp
   apply (auto simp add: cset.map_comp o_def cimage_cUn intro!: arg_cong2[where f = cUn] cimage_cong
      split: sum_op_aux.splits op.splits option.splits)
  done

lemma step_sum_inp_case :
  "step (Inp p (x1,x2)) (sum_op part_sum) op2 \<Longrightarrow> op2 = sum_op (part_sum(x1:=(part_sum x1 + x2)))"
  apply(subst (asm) sum_op_code)
  apply(erule stepChoiceE)
  by auto

lemma step_sum_out_case :
  "step (Out p (x1,x2)) (sum_op part_sum) op2 \<Longrightarrow> 0 < x2 \<and> part_sum x1 = x2 \<and> op2 = sum_op (part_sum(x1:=0))"
  apply(subst (asm) sum_op_code)
  apply(erule stepChoiceE)
  by auto

lemma step_sum_tau_case :
  "step Tau (sum_op part_sum) op2 \<Longrightarrow> False"
  apply(subst (asm) sum_op_code)
  apply(erule stepChoiceE)
  by auto

lemma step_sum_inp_intro :
  "part_sum2 = part_sum1(x1:=(part_sum1 x1 + x2)) \<Longrightarrow> step (Inp p (x1,x2)) (sum_op part_sum1) (sum_op part_sum2)"
  apply simp
  apply(subst sum_op_code[where part_sum = part_sum1])
  apply(rule step.SC[where op = "Read 1 (\<lambda>(n,m). sum_op (part_sum1(n := part_sum1 n + m)))"])
   apply auto
  by (metis (mono_tags, lifting) SR case_prod_conv num1_eq1)

lemma step_sum_out_intro :
  "part_sum2 = part_sum1(x1:=0) \<Longrightarrow> x2 = part_sum1 x1 \<Longrightarrow>  0 < part_sum1 x1 \<Longrightarrow> step (Out p (x1,x2)) (sum_op part_sum1) (sum_op part_sum2)"
  apply simp
  apply(subst sum_op_code[where part_sum = part_sum1])
  apply(rule step.SC[where op = "Write (sum_op (part_sum1(x1 := 0))) 1 (x1, part_sum1 x1)"])
  apply auto
  unfolding image_def Nats_def
  by auto


subsection \<open>Extended extension (allows for communication)\<close>

datatype (discs_sels) ('ip, 'op, 'd) exchange_op_aux =
  exchange_Read_aux "'ip \<times> (nat \<times> nat)" "'d \<Rightarrow> (nat \<Rightarrow> ('ip, 'op, 'd) op)"
  | exchange_Write_aux "nat \<Rightarrow> ('ip, 'op, 'd) op" "'op \<times> (nat \<times> nat)" 'd
  | exchange_Silent_aux "nat \<Rightarrow> ('ip, 'op, 'd) op"

abbreviation eval_exchange_op_aux where
  "eval_exchange_op_aux c aux \<equiv> (case aux of
    exchange_Read_aux p f \<Rightarrow> Read p (\<lambda>y. let n_op = f y in c n_op)
  | exchange_Write_aux n_op q x \<Rightarrow> Write (c n_op) q x
  | exchange_Silent_aux n_op \<Rightarrow> Silent (c n_op))"

corec exchange_op :: "nat set \<Rightarrow> (nat \<Rightarrow> 'op \<Rightarrow> 'd \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> ('ip, 'op, 'd) op) \<Rightarrow> ('ip \<times> (nat \<times> nat), 'op \<times> (nat \<times> nat), 'd) op" where
  "exchange_op work_set pact n_op =
     Choice (cimage (eval_exchange_op_aux (exchange_op work_set pact)) 
      (cUnion (cUnion (cimage (\<lambda> n. cimage (\<lambda> op. case op of
     Read p f \<Rightarrow> cimage (\<lambda> m. (exchange_Read_aux (p,(m, n)) (\<lambda> x. (n_op(n:=f x))))) (acset Nats)
     | Write op' p x \<Rightarrow> csingle (exchange_Write_aux (n_op(n:= op')) (p,(n,pact n p x)) x)
     | Silent op' \<Rightarrow> csingle (exchange_Silent_aux (n_op(n:= op')))
     ) ((choices (n_op n)))) (acset work_set)))))"

subsection \<open>Basic simplification properties\<close>
lemma exchange_op_code[code]: "exchange_op work_set pact n_op =
 Choice (cUnion (cUnion (cimage (\<lambda> n. cimage (\<lambda> op. case op of
     Read p f \<Rightarrow> cimage (\<lambda>m. (Read (p,(m, n)) (\<lambda> x. exchange_op work_set pact (n_op(n:=f x))))) (acset Nats)
   | Write op' p x \<Rightarrow> csingle (Write (exchange_op work_set pact (n_op(n:= op'))) (p,(n, pact n p x)) x)
   | Silent op' \<Rightarrow> csingle (Silent (exchange_op work_set pact (n_op(n:= op'))))
   ) ((choices (n_op n)))) (acset work_set))))"
  apply (subst exchange_op.code)
  apply (unfold cimage_cUn op.inject)
   apply (auto simp add: cset.map_comp o_def cimage_cUn intro!: arg_cong2[where f = cUn] cimage_cong
      split: exchange_op_aux.splits op.splits option.splits)
  subgoal for n op a m k f
    by blast
  subgoal for n op f a m k g
    by blast
  subgoal for n op f
    by blast
  subgoal for n op a m k f
    by blast
  subgoal for n op f a m k g
    by blast
  subgoal for n op f
    by blast
  subgoal for op n op'
    unfolding image_def
    apply(simp)
    apply(rule exI[where x = _])
    apply(rule conjI)
    unfolding Bex_def
    apply(rule exI[where x = n])
    apply(rule conjI, simp)
    apply(rule refl)
    apply(cases op')
    subgoal for p f
      apply auto
      subgoal for m
        apply (rule exI[where x = _])
        apply(rule conjI)
        apply(rule exI[where x = _])
        apply(rule conjI)
        apply(rule exI[where x = "Read p f"])
          apply(rule conjI, assumption)
          apply(rule refl)
         apply simp
        unfolding image_def
         apply simp
        unfolding Bex_def
         apply(rule exI[where x = m])
         apply simp
        apply simp
        done
      done
    subgoal for op'' q x
      apply auto
      apply (rule exI[where x = _])
      apply(rule conjI)
      apply(rule exI[where x = _])
      apply(rule conjI)
      apply(rule exI[where x = "Write op'' q x"])
        apply(rule conjI, assumption)
        apply(rule refl)
       apply simp
      unfolding image_def
      apply simp
      done
    subgoal
      apply simp
      done
    subgoal for op''
      apply auto
      apply (rule exI[where x = _])
      apply(rule conjI)
      apply(rule exI[where x = _])
      apply(rule conjI)
      apply(rule exI[where x = "Silent op''"])
        apply(rule conjI, assumption)
        apply(rule refl)
       apply simp
      unfolding image_def
      apply simp
      done
    done
  subgoal for op n op'
    unfolding image_def
    apply(simp)
    apply(rule exI[where x = _])
    apply(rule conjI)
    unfolding Bex_def
    apply(rule exI[where x = n])
    apply(rule conjI, simp)
    apply(rule refl)
    apply(cases op')
    subgoal for p f
      apply auto
      subgoal for m
        apply (rule exI[where x = _])
        apply(rule conjI)
        apply(rule exI[where x = _])
        apply(rule conjI)
        apply(rule exI[where x = "Read p f"])
          apply(rule conjI, assumption)
          apply(rule refl)
         apply simp
        unfolding image_def
         apply simp
        unfolding Bex_def
         apply(rule exI[where x = m])
         apply simp
        apply simp
        done
      done
    subgoal for op'' q x
      apply auto
      apply (rule exI[where x = _])
      apply(rule conjI)
      apply(rule exI[where x = _])
      apply(rule conjI)
      apply(rule exI[where x = "Write op'' q x"])
        apply(rule conjI, assumption)
        apply(rule refl)
       apply simp
      unfolding image_def
      apply simp
      done
    subgoal
      apply auto
      done
    subgoal for op''
      apply auto
      apply (rule exI[where x = _])
      apply(rule conjI)
      apply(rule exI[where x = _])
      apply(rule conjI)
      apply(rule exI[where x = "Silent op''"])
        apply(rule conjI, assumption)
        apply(rule refl)
       apply simp
      unfolding image_def
      apply simp
      done
    done
  done

definition exchange_wire :: "('op \<rightharpoonup> 'ip) \<Rightarrow> (('op \<times> (nat \<times> nat)) \<rightharpoonup> ('ip \<times> (nat \<times> nat)))" where 
  "exchange_wire wire op_n = (case op_n of
    (op, (n,m)) \<Rightarrow> (case (wire op) of
      Some op' \<Rightarrow> Some (op',(n,m))
      | None \<Rightarrow> None))"

record ('w, 'ip, 'op, 'd) conf =
  msg :: "'w \<Rightarrow> 'w \<Rightarrow> ('ip \<times> (nat \<times> nat)) \<Rightarrow> 'd buf"
  ops :: "'w \<Rightarrow> ('ip \<times> (nat \<times> nat), 'op \<times> (nat \<times> nat), 'd) op"
  used_wire :: "'op \<rightharpoonup> 'ip"
  work_respons :: "nat \<Rightarrow> 'w"


inductive step_dis :: "'w \<Rightarrow> ('ip \<times> (nat \<times> nat), 'op \<times> (nat \<times> nat), 'd) IO \<Rightarrow> ('w, 'ip, 'op, 'd) conf \<Rightarrow> ('w, 'ip, 'op, 'd) conf \<Rightarrow> bool" where
  SDT: "step Tau (ops c w) op' \<Longrightarrow> c' = (c\<lparr>ops := ((ops c)(w := op'))\<rparr>) \<Longrightarrow> step_dis w Tau c c'"
| SDTR: "step (Inp (p,(n,m)) (hd (msg c w w' (p,(n,m))))) (ops c w') op' \<Longrightarrow> c' = (c\<lparr>ops := ((ops c)(w' := op')), msg := ((msg c)(w := ((msg c w)(w' := (BTL (p,(n,m)) (msg c w w'))))))\<rparr>) \<Longrightarrow> 
    \<exists>q. used_wire c q = Some p \<Longrightarrow> w' \<noteq> w \<Longrightarrow> work_respons c n = w \<Longrightarrow> work_respons c m = w' \<Longrightarrow> (msg c w w' (p,(n,m))) \<noteq> [] \<Longrightarrow> step_dis w' Tau c c'"
| SDTW: "step (Out (q,(n,m)) x) (ops c w) op' \<Longrightarrow> c' = (c\<lparr>ops := ((ops c)(w := op')), msg := ((msg c)(w := ((msg c w)(w' := (BENQ (p,(n,m)) x (msg c w w'))))))\<rparr>) \<Longrightarrow> 
    used_wire c q = Some p \<Longrightarrow> w' \<noteq> w \<Longrightarrow> work_respons c n = w \<Longrightarrow> work_respons c m = w' \<Longrightarrow> step_dis w Tau c c'"
| SDR: "step (Inp (p,(n,m)) x) (ops c w) op' \<Longrightarrow> c' = (c\<lparr>ops := ((ops c)(w := op'))\<rparr>) \<Longrightarrow> \<forall>q. used_wire c q \<noteq> Some p \<Longrightarrow> work_respons c m = w \<Longrightarrow> step_dis w (Inp (p,(n,m)) x) c c'"
| SDW: "step (Out (q,(n,m)) x) (ops c w) op' \<Longrightarrow> c' = (c\<lparr>ops := ((ops c)(w := op'))\<rparr>) \<Longrightarrow> used_wire c q = None \<Longrightarrow> work_respons c n = w \<Longrightarrow> step_dis w (Out (q,(n,m)) x) c c'"

inductive_cases stepDisInE [elim!]: "step_dis w (Inp p_simp x) c c'"
inductive_cases stepDisOutE [elim!]: "step_dis w (Out q_simp x) c c'"
inductive_cases stepDisTauE [elim!]: "step_dis w Tau c c'"


inductive step_dis' :: "('ip \<times> (nat \<times> nat), 'op \<times> (nat \<times> nat), 'd) IO \<Rightarrow> ('w, 'ip, 'op, 'd) conf \<Rightarrow> ('w, 'ip, 'op, 'd) conf \<Rightarrow> bool" where
  S: "step_dis w io c c' \<Longrightarrow> step_dis' io c c'"

lemma step_dis'_elim:
  "step_dis' io c c \<Longrightarrow> \<exists>w. step_dis w io c c"
  using step_dis'.cases
  by meson


(*
definition sum_sum :: "(1 \<times> nat \<Rightarrow> (nat \<times> nat) buf) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (1 \<times> nat, 1 \<times> nat, nat \<times> nat) op" where
  "sum_sum buf st1 st2 = map_op projl projr (comp_op Some buf (exchange_op (\<lambda> _ op (m,_). m) (\<lambda> n. sum_op (\<lambda> m. st1 n m))) (exchange_op (\<lambda> _ _ _. 0) (\<lambda> n. sum_op (\<lambda> m. st2 n m))))"

definition sum_sum_n :: "(1 \<times> (nat + nat) + 1 \<times> (nat + nat) \<Rightarrow> (nat \<times> nat) buf) \<Rightarrow> (nat \<Rightarrow> 1 \<times> (nat + nat) \<Rightarrow> (nat \<times> nat) buf) \<Rightarrow>
  (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (nat, 1 \<times> (nat + nat) + 1 \<times> (nat + nat), 1 \<times> nat, 1 \<times> nat + 1 \<times> nat, 1 \<times> nat, nat \<times> nat) conf" where
  "sum_sum_n msg' bufs st1 st2 \<equiv> \<lparr> 
    msg = msg', 
    ops = (\<lambda>n. comp_dis_op {n} (\<lambda>n. Some n) (bufs n) (exchange'_op (\<lambda> _ op (m,_). m) (\<lambda> n. sum_op (\<lambda> m. st1 n m)))
        (exchange'_op (\<lambda> _ op _. 0) (\<lambda> n. sum_op (\<lambda> m. st2 n m)))), 
    inp_w = (\<lambda> ip. case ip of 
      Inl (n,(Inl m)) \<Rightarrow> m
      | Inl (n,(Inr m)) \<Rightarrow> m
      | Inr (n,(Inl m)) \<Rightarrow> m
      | Inr (n,(Inr m)) \<Rightarrow> m),
    work_respons = id,
    used_wire = (\<lambda> op. case op of
      Inl (n,m) \<Rightarrow> Some (Inr (n, Inr m))
      |  Inr (n,m) \<Rightarrow> None),
    ip_trans = (\<lambda>p. case p of (n,m) \<Rightarrow> Inl (n,Inl m)),
    op_trans = Inr\<rparr>"

definition sum_sum_1 :: "(1 \<times> (nat + nat) + 1 \<times> (nat + nat) \<Rightarrow> (nat \<times> nat) buf) \<Rightarrow> (nat \<Rightarrow> 1 \<times> (nat + nat) \<Rightarrow> (nat \<times> nat) buf) \<Rightarrow> 
  (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (nat, 1 \<times> (nat + nat) + 1 \<times> (nat + nat), 1 \<times> nat, 1 \<times> nat + 1 \<times> nat, 1 \<times> nat, nat \<times> nat) conf" where
  "sum_sum_1 msg' bufs st1 st2 \<equiv> \<lparr> 
    msg = msg', 
    ops = (\<lambda>n. if n = 0 then 
      comp_dis_op Nats (\<lambda>n. Some n) (bufs n) (exchange'_op (\<lambda> _ op (m,_). m) (\<lambda> n. sum_op (\<lambda> m. st1 n m)))
        (exchange'_op (\<lambda> _ _ _. 0) (\<lambda> n. sum_op (\<lambda> m. st2 n m))) else
      comp_dis_op {} (\<lambda>n. Some n) (\<lambda>_. []) (exchange'_op (\<lambda> _ op (m,_). m) (\<lambda> _. sum_op (\<lambda> _. 0)))
        (exchange'_op (\<lambda> _ _ _. 0) (\<lambda> _. sum_op (\<lambda> _. 0)))), 
    inp_w = (\<lambda>_. 0), 
    work_respons = (\<lambda>_. 0),
    used_wire = (\<lambda> op. case op of
      Inl (n,m) \<Rightarrow> Some (Inr (n, Inr m))
      |  Inr (n,m) \<Rightarrow> None),
    ip_trans = (\<lambda>p. case p of (n,m) \<Rightarrow> Inl (n,Inl m)),
    op_trans = Inr\<rparr>"
*)

section\<open>Strong Bisimilarity\<close>

(*Should just be bisim*)
definition sim_dis :: "(('ip \<times> (nat \<times> nat), 'op \<times> (nat \<times> nat), 'd) op \<Rightarrow> ('w, 'ip, 'op, 'd) conf \<Rightarrow> bool) \<Rightarrow> ('ip \<times> (nat \<times> nat), 'op \<times> (nat \<times> nat), 'd) op \<Rightarrow> ('w, 'ip, 'op, 'd) conf \<Rightarrow> bool" where
  "sim_dis R op c = ((\<forall>io op'. step io op op' \<longrightarrow> (\<exists>c'. step_dis' io c c' \<and> R op' c')) \<and> (\<forall>io c'. step_dis' io c c' \<longrightarrow> (\<exists>op'. step io op op' \<and> R op' c')))"

lemma sim_dis_mono[mono]: "R \<le> S \<Longrightarrow> sim_dis R \<le> sim_dis S"
  by (force simp: sim_dis_def le_fun_def)

coinductive bisim_dis (infix "~d"40) where
  "sim_dis bisim_dis op c \<Longrightarrow> bisim_dis op c"

lemma bisim_op_elim:
  "step io op op' \<Longrightarrow> op ~d c \<Longrightarrow> \<exists> w c'. step_dis w io c c' \<and> op' ~d c'"
  by (metis bisim_dis.cases sim_dis_def step_dis'.simps)

lemma bisim_c_elim:
  "step_dis' io c c' \<Longrightarrow> op ~d c \<Longrightarrow> \<exists>op'. step io op op' \<and> op' ~d c'"
  by (metis bisim_dis.cases sim_dis_def)

inductive bisim_dis_cong for R where
  bc'_base:  "R x y \<Longrightarrow> bisim_dis_cong R x y"
| bc'_bisim:  "bisim_dis x y \<Longrightarrow> bisim_dis_cong R x y"

lemma bisim_dis_cong_disj:
  "(bisim_dis_cong R x y \<or> bisim_dis x y) = bisim_dis_cong R x y"
  by (auto intro: bisim_dis_cong.intros)

lemma bisim_dis_coinduct_upto[consumes 1, case_names BISIM]:
  "R s t \<Longrightarrow>
   (\<And>op c. R op c \<Longrightarrow> sim_dis (bisim_dis_cong R) op c) \<Longrightarrow>
   s ~d t"
  apply (rule bisim_dis.coinduct[where X="bisim_dis_cong R", unfolded bisim_dis_cong_disj, simplified])
  subgoal
    by (auto intro: bisim_dis_cong.intros)
  subgoal premises prems for s' t'
    using prems(3) apply -
    apply (induct s' t' rule: bisim_dis_cong.induct)
    subgoal
      by (drule prems(2)) auto
    subgoal
      using sim_dis_mono[of bisim_dis "bisim_dis_cong R"]
      by (auto simp: le_fun_def bc'_bisim elim: bisim_dis.cases)
    done
  done

lemma bisim_dis_coinduct_upto'[unfolded sim_dis_def, rule_format, consumes 1, case_names SIM1 SIM2]:
  "R op c \<Longrightarrow>
   (\<And>op c. R op c \<Longrightarrow> sim_dis (bisim_dis_cong R) op c) \<Longrightarrow>
   op ~d c"
  using bisim_dis_coinduct_upto by blast

lemma bisim_dis_coinduct_upto''[consumes 1, case_names SIM1 SIM2]:
  "R op c \<Longrightarrow>
  (\<And>op c io op'. R op c \<Longrightarrow> step io op op' \<Longrightarrow> \<exists>c'. step_dis' io c c' \<and> bisim_dis_cong R op' c') \<Longrightarrow>
  (\<And>op c io c'. R op c \<Longrightarrow> step_dis' io c c' \<Longrightarrow> \<exists>op'. step io op op' \<and> bisim_dis_cong R op' c') \<Longrightarrow>
   op ~d c"
  using bisim_dis_coinduct_upto' by (smt (verit, ccfv_SIG))

(* show bisim of sum_sum_n and sum_sum_1 by the relation that they are bisim when then msg' and bufs combined match (disregarding nonused parts) *)

(*
definition sum_R :: "(1 \<times> nat, 1 \<times> nat, nat \<times> nat) op \<Rightarrow> 
  (nat, 1 \<times> (nat + nat) + 1 \<times> (nat + nat), 1 \<times> nat, 1 \<times> nat + 1 \<times> nat, 1 \<times> nat, nat \<times> nat) conf \<Rightarrow> bool" where
  "sum_R op c = (\<exists> buf msg' bufs st1 st2. op = sum_sum buf st1 st2 \<and> c = sum_sum_1 msg' bufs st1 st2 \<and> (\<forall> p n. buf (p,n) = bufs 0 (p, Inl n)))"
*)
lemma step_exchange_inp_case :
  "step (Inp (p, (n, m)) x) (exchange_op nset pact op1) op2 \<Longrightarrow> \<exists> op'. step (Inp p x) (op1 m) op' \<and> op2 = (exchange_op nset pact (op1(m:= op'))) \<and> m \<in> nset"
  apply(subst (asm) exchange_op_code)
  apply(erule stepChoiceE)
  apply auto
  subgoal for op' n' op''
    apply(cases op'')
    subgoal for p' n_op''
      apply simp
      apply auto
      apply(rule exI[where x= "n_op'' x"])
      by auto
    by auto
  done

lemma step_exchange_out_case :
  "step (Out (q, (n, m)) x) (exchange_op nset pact op1) op2 \<Longrightarrow> \<exists>op'. step (Out q x) (op1 n) op' \<and> pact n q x = m \<and> op2 = (exchange_op nset pact (op1(n:= op'))) \<and> n \<in> nset"
  apply(subst (asm) exchange_op_code)
  apply(erule stepChoiceE)
  apply auto
  subgoal for op' n' op''
    apply(cases op'')
    subgoal
      by auto
    subgoal for op''' q' x'
      apply simp
      apply(erule stepWriteE)
      by fastforce
    by auto
  done

lemma step_exchange_tau_case :
  "step Tau (exchange_op nset pact op1) op2 \<Longrightarrow> \<exists> n op'. step Tau (op1 n) op' \<and> op2 = (exchange_op nset pact (op1(n:= op'))) \<and> n \<in> nset"
  apply(subst (asm) exchange_op_code)
  apply(erule stepChoiceE)
  apply auto
  subgoal for op' n op''
    apply(cases op'')
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal for op'''
      using Silent_in_choices_step
      by auto
    done
  done

lemma step_exchange_inp_intro :
  "step (Inp p x) (op1 m) op' \<Longrightarrow> op2 = (op1(m:= op')) \<Longrightarrow> m \<in> nset \<Longrightarrow> step (Inp (p, (n,m)) x) (exchange_op nset pact op1) (exchange_op nset pact op2)"
    apply(erule step_choicesE)
    apply auto
    subgoal for f
      apply(subst exchange_op_code[where n_op = op1])
      apply(rule step.SC[where op = "Read (p, (n,m)) (\<lambda>x. exchange_op nset pact (op1(m := f x)))"])
      subgoal
        apply auto
        unfolding Bex_def image_def Nats_def
        apply(rule exI[where x = m])
        by auto
      subgoal
        by (metis (mono_tags, lifting) SR)
      done
    done

lemma step_exchange_out_intro :
  "step (Out q x) (op1 n) op' \<Longrightarrow> pact n q x = m \<Longrightarrow> op2 = op1(n:= op') \<Longrightarrow> n \<in> nset \<Longrightarrow> step (Out (q, (n,m)) x) (exchange_op nset pact op1) (exchange_op nset pact op2)"
    apply(erule step_choicesE)
    apply auto
    apply(subst exchange_op_code[where n_op = op1])
      apply(rule step.SC[where op = "Write (exchange_op nset pact (op1(n := op'))) (q, (n,m)) x"])
      subgoal
        apply auto
        unfolding Bex_def image_def Nats_def
        apply(rule exI[where x = n])
        by auto
      subgoal
        by (simp add: SW)
      done

lemma step_exchange_tau_intro :
  "step Tau (op1 n) op' \<Longrightarrow> op2 = op1(n:= op') \<Longrightarrow> n \<in> nset \<Longrightarrow> step Tau (exchange_op nset pact op1) (exchange_op nset pact op2)"
    apply(erule step_choicesE)
    apply auto
    apply(subst exchange_op_code[where n_op = op1])
      apply(rule step.SC[where op = "Silent (exchange_op nset pact (op1(n := op')))"])
      subgoal
        apply auto
        unfolding Bex_def image_def Nats_def
        apply(rule exI[where x = n])
        by auto
      subgoal
        by (simp add: ST)
      done

coinductive step_spec_conf where
  SSC: "(\<And>op' w c_msg. step Tau (ops c w) op' \<Longrightarrow> step_spec_conf (c\<lparr>ops := (ops c)(w := op'), msg := c_msg\<rparr>)) \<Longrightarrow>
    (\<And>p pn pm x w op' c_msg. step (Inp (p, pn, pm) x) (ops c w) op' \<Longrightarrow> (work_respons c pm = w \<and> step_spec_conf (c\<lparr>ops := (ops c)(w := op'), msg := c_msg\<rparr>))) \<Longrightarrow>
    (\<And>q qn qm x w op' c_msg. step (Out (q, qn, qm) x) (ops c w) op' \<Longrightarrow> (work_respons c qn = w \<and> step_spec_conf (c\<lparr>ops := (ops c)(w := op'), msg := c_msg\<rparr>))) \<Longrightarrow> step_spec_conf c"

definition conf_exchange :: "(nat \<Rightarrow> 'w) \<Rightarrow> (nat \<Rightarrow> 'op \<Rightarrow> 'd \<Rightarrow> nat) \<Rightarrow> ('w \<Rightarrow> nat \<Rightarrow> ('ip, 'op, 'd) op) \<Rightarrow> ('w, 'ip, 'op, 'd) conf" where
  "conf_exchange work_respons' pact w_n_op = \<lparr> 
    msg = (\<lambda>_ _ _. []),
    ops = (\<lambda>w. exchange_op {n. work_respons' n = w} pact (w_n_op w)),
    used_wire = (\<lambda>_. None),
    work_respons = work_respons'
\<rparr>"


lemma exchange_spec :
  shows "step_spec_conf (conf_exchange work_respons' pact w_n_op)"
  apply(coinduct rule: step_spec_conf.coinduct[where X = "\<lambda>c. \<exists> work_respons' pact w_n_op c_msg. c = conf_exchange work_respons' pact w_n_op\<lparr>msg := c_msg \<rparr>"])
  subgoal
    apply(rule exI[where x = "work_respons'"])
    apply(rule exI[where x = "pact"])
    apply(rule exI[where x = "w_n_op"])
    apply(rule exI[where x = "msg (conf_exchange work_respons' pact w_n_op)"])
    apply auto
    done
  subgoal for c
    apply(safe)
    subgoal for work_respons' pact w_n_op
      apply(rule exI[where x = c])
      apply simp
      apply(rule conjI)
      subgoal
        apply auto
        subgoal for op' w c_msg
          unfolding conf_exchange_def
          apply simp
          apply(drule step_exchange_tau_case)
          apply auto
          subgoal for n op''
            apply(rule exI[where x = pact])
            apply(rule exI[where x = "\<lambda>w'. (if work_respons' n = w' then ((w_n_op w')(n := op'')) else w_n_op w')"])
            unfolding fun_upd_def if_distrib
            apply auto
            done
          done
        done
      apply(rule conjI)
      subgoal
        apply auto
        subgoal for p pn pm x w op'
          unfolding conf_exchange_def
          apply auto
          apply(drule step_exchange_inp_case)
          apply auto
          done
        subgoal for p pn pm x w op'
          unfolding conf_exchange_def
          apply simp
          apply(drule step_exchange_inp_case)
          apply auto
          subgoal for op''
            apply(rule exI[where x = pact])
            apply(rule exI[where x = "\<lambda>w'. (if work_respons' pm = w' then ((w_n_op w')(pm := op'')) else w_n_op w')"])
            unfolding fun_upd_def if_distrib
            apply auto
            done
          done
        done
      subgoal
        apply auto
        subgoal for p pn pm x w op'
          unfolding conf_exchange_def
          apply auto
          apply(drule step_exchange_out_case)
          apply auto
          done
        subgoal for q qn qm x w op'
          unfolding conf_exchange_def
          apply simp
          apply(drule step_exchange_out_case)
          apply auto
          subgoal for op''
            apply(rule exI[where x = pact])
            apply(rule exI[where x = "\<lambda>w'. (if work_respons' qn = w' then ((w_n_op w')(qn := op'')) else w_n_op w')"])
            unfolding fun_upd_def if_distrib
            apply auto
            done
          done
        done
      done
    done
  done

lemma exchange_bisim :
  assumes H: "\<forall>n. n_op n = w_n_op (work_respons' n) n"
  shows "(exchange_op Nats pact n_op) ~d ((conf_exchange work_respons' pact (w_n_op)) :: ('w, 'ip, 'op, 'd) conf)"
proof (rule bisim_dis_coinduct_upto'' [where R = "\<lambda> op c. \<exists> work_respons' pact n_op w_n_op. (\<forall>n. n_op n = w_n_op (work_respons' n) n) \<and> op = (exchange_op Nats pact n_op) \<and> c = conf_exchange work_respons' pact (w_n_op)"])
  show "\<exists>work_respons'a pacta n_opa w_n_opa. (\<forall>n. n_opa n = w_n_opa (work_respons'a n) n) \<and> exchange_op \<nat> pact n_op = exchange_op \<nat> pacta n_opa \<and> conf_exchange work_respons' pact w_n_op = conf_exchange work_respons'a pacta w_n_opa"
    using H
    by auto
next
  fix op :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) op"
    and c :: "('w, 'ip, 'op, 'd) conf"
    and io :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) IO"
    and op' :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) op"
  assume H1: "\<exists>work_respons' pact n_op w_n_op. (\<forall>n. n_op n = w_n_op (work_respons' n) n) \<and> op = exchange_op \<nat> pact n_op \<and> c = conf_exchange work_respons' pact w_n_op"
    and H2: "step io op op'"
  obtain work_respons' pact n_op w_n_op where H1_1: "\<forall>n. n_op n = w_n_op (work_respons' n) n" and H1_2: "op = exchange_op Nats pact n_op" and H1_3: "c = conf_exchange work_respons' pact w_n_op"
    using H1
    by blast
  show "\<exists>c'. step_dis' io c c' \<and> bisim_dis_cong (\<lambda>op c. \<exists>work_respons' pact n_op w_n_op. (\<forall>n. n_op n = w_n_op (work_respons' n) n) \<and> op = exchange_op \<nat> pact n_op \<and> c = conf_exchange work_respons' pact w_n_op) op' c'"
    sketch(cases io)
  proof (cases io)
    fix p :: "'ip \<times> nat \<times> nat"
      and x :: 'd
    obtain p1 p2 p3 where p_def: "p = (p1,p2,p3)"
      by (meson prod_cases3)
    assume io_def: "io = Inp p x"
    show "\<exists>c'. step_dis' io c c' \<and> bisim_dis_cong (\<lambda>op c. \<exists>work_respons' pact n_op w_n_op. (\<forall>n. n_op n = w_n_op (work_respons' n) n) \<and> op = exchange_op \<nat> pact n_op \<and> c = conf_exchange work_respons' pact w_n_op) op' c'"
    using H1_2 H2 io_def p_def H1_3
      apply -
      apply simp
      apply(drule step_exchange_inp_case)
      apply safe
      subgoal for op''
        apply(rule exI[where x= "conf_exchange work_respons' pact (w_n_op((work_respons' p3):=(w_n_op (work_respons' p3))(p3 := op'')))"])
        apply(rule conjI)
        subgoal
          apply(rule S[where w = "work_respons' p3"])
          unfolding conf_exchange_def
          apply(rule SDR[where op' = "exchange_op {n. work_respons' n = work_respons' p3} pact ((w_n_op (work_respons' p3))(p3 := op''))"]; simp)
          subgoal
            apply(rule step_exchange_inp_intro)
            using H1_1
            by auto
          subgoal
            unfolding fun_upd_def if_distrib
            apply auto
            done
          done
        subgoal
          apply(rule bc'_base)
          apply(rule exI[where x= "work_respons'"])
          apply(rule exI[where x= "pact"])
          apply(rule exI[where x= "(n_op(p3 := op''))"])
          apply(rule exI[where x= "(w_n_op(work_respons' p3 := (w_n_op (work_respons' p3))(p3 := op'')))"])
          using H1_1
          by auto
        done
      done
  next
    fix q :: "'op \<times> nat \<times> nat"
      and x :: 'd
    obtain q1 q2 q3 where p_def: "q = (q1,q2,q3)"
      by (meson prod_cases3)
    assume io_def: "io = Out q x"
    show "\<exists>c'. step_dis' io c c' \<and> bisim_dis_cong (\<lambda>op c. \<exists>work_respons' pact n_op w_n_op. (\<forall>n. n_op n = w_n_op (work_respons' n) n) \<and> op = exchange_op \<nat> pact n_op \<and> c = conf_exchange work_respons' pact w_n_op) op' c'"
      using H1_2 H2 io_def p_def H1_3
      apply -
      apply simp
      apply(drule step_exchange_out_case)
      apply safe
      subgoal for op''
        apply(rule exI[where x= "conf_exchange work_respons' pact (w_n_op((work_respons' q2):=(w_n_op (work_respons' q2))(q2 := op'')))"])
        apply(rule conjI)
        subgoal
          apply(rule S[where w = "work_respons' q2"])
          unfolding conf_exchange_def
          apply(rule SDW[where op' = "exchange_op {n. work_respons' n = work_respons' q2} pact ((w_n_op (work_respons' q2))(q2 := op''))"]; simp)
          subgoal
            apply(rule step_exchange_out_intro[where n = q2 and op' = op''])
            using H1_1
              apply simp
              apply(rule refl)+
            by simp
          subgoal
            unfolding fun_upd_def if_distrib
            by fastforce
          done
        subgoal
          apply(rule bc'_base)
          apply(rule exI[where x= "work_respons'"])
          apply(rule exI[where x= "pact"])
          apply(rule exI[where x= "(n_op(q2 := op''))"])
          apply(rule exI[where x= "(w_n_op(work_respons' q2 := (w_n_op (work_respons' q2))(q2 := op'')))"])
          using H1_1
          by fastforce
        done
      done
  next
    assume io_def: "io = Tau"
    show "\<exists>c'. step_dis' io c c' \<and> bisim_dis_cong (\<lambda>op c. \<exists>work_respons' pact n_op w_n_op. (\<forall>n. n_op n = w_n_op (work_respons' n) n) \<and> op = exchange_op \<nat> pact n_op \<and> c = conf_exchange work_respons' pact w_n_op) op' c'"
      using H1_2 H2 H1_3 io_def
      apply -
      apply simp
      apply(drule step_exchange_tau_case)
      apply safe
      subgoal for n' op''
        apply(rule exI[where x= "conf_exchange work_respons' pact (w_n_op((work_respons' n'):=(w_n_op (work_respons' n'))(n' := op'')))"])
        apply(rule conjI)
        subgoal
          apply(rule S[where w = "work_respons' n'"])
          unfolding conf_exchange_def
          apply(rule SDT[where op' = "exchange_op {n. work_respons' n = work_respons' n'} pact ((w_n_op (work_respons' n'))(n' := op''))"]; simp)
          subgoal
            apply(rule step_exchange_tau_intro[where n = n' and op' = op''])
            using H1_1
             apply fastforce
             apply simp
            by simp
          subgoal
            unfolding fun_upd_def if_distrib
            by force
          done
        subgoal
          apply(rule bc'_base)
          apply(rule exI[where x= "work_respons'"])
          apply(rule exI[where x= "pact"])
          apply(rule exI[where x= "(n_op(n' := op''))"])
          apply(rule exI[where x= "(w_n_op(work_respons' n' := (w_n_op (work_respons' n'))(n' := op'')))"])
          using H1_1
          by fastforce
        done
      done
  qed
next
  fix op :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) op"
    and c :: "('w, 'ip, 'op, 'd) conf"
    and io :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) IO"
    and c' :: "('w, 'ip, 'op, 'd) conf"
  assume H1: "\<exists>work_respons' pact n_op w_n_op. (\<forall>n. n_op n = w_n_op (work_respons' n) n) \<and> op = exchange_op \<nat> pact n_op \<and> c = conf_exchange work_respons' pact w_n_op"
    and H2: "step_dis' io c c'"
  obtain work_respons' pact n_op w_n_op where H1_1: "\<forall>n. n_op n = w_n_op (work_respons' n) n" and H1_2: "op = exchange_op Nats pact n_op" and H1_3: "c = conf_exchange work_respons' pact w_n_op"
    using H1
    by blast
  obtain w where H2': "step_dis w io c c'"
    using H2
    by (meson step_dis'.cases)
  show "\<exists>op'. step io op op' \<and> bisim_dis_cong (\<lambda>op c. \<exists>work_respons' pact n_op w_n_op. (\<forall>n. n_op n = w_n_op (work_respons' n) n) \<and> op = exchange_op \<nat> pact n_op \<and> c = conf_exchange work_respons' pact w_n_op) op' c'"
  proof (cases io)
    fix p :: "'ip \<times> nat \<times> nat"
      and x :: 'd
    obtain p1 p2 p3 where p_def: "p = (p1,p2,p3)"
      by (meson prod_cases3)
    assume io_def: "io = Inp p x"
    show "\<exists>op'. step io op op' \<and> bisim_dis_cong (\<lambda>op c. \<exists>work_respons' pact n_op w_n_op. (\<forall>n. n_op n = w_n_op (work_respons' n) n) \<and> op = exchange_op \<nat> pact n_op \<and> c = conf_exchange work_respons' pact w_n_op) op' c'"
      using H2'
      apply -
      unfolding io_def
      apply(erule stepDisInE)
      subgoal for ip n m op'
        unfolding H1_2 p_def H1_3 conf_exchange_def
        apply auto
        apply(drule step_exchange_inp_case)
        apply safe
        subgoal for op''
          apply(rule exI[where x = "(exchange_op Nats pact (n_op(m := op'')))"])
          apply(rule conjI)
          subgoal
            apply(rule step_exchange_inp_intro[where op' = op''])
            subgoal
              using H1_1
              by presburger
            subgoal
              by blast
            unfolding Nats_def
            by auto
          subgoal
            apply(rule bc'_base)
            apply(rule exI[where x= work_respons'])
            apply(rule exI[where x= pact])
            apply(rule exI[where x= "(n_op(m := op''))"])
            apply(rule exI[where x= "(w_n_op(work_respons' m := (w_n_op (work_respons' m))(m := op'')))"])
            using H1_1
            by auto
          done
        done
      done
  next
    fix q :: "'op \<times> nat \<times> nat"
      and x :: 'd
    obtain q1 q2 q3 where p_def: "q = (q1,q2,q3)"
      by (meson prod_cases3)
    assume io_def: "io = Out q x"
    show "\<exists>op'. step io op op' \<and> bisim_dis_cong (\<lambda>op c. \<exists>work_respons' pact n_op w_n_op. (\<forall>n. n_op n = w_n_op (work_respons' n) n) \<and> op = exchange_op \<nat> pact n_op \<and> c = conf_exchange work_respons' pact w_n_op) op' c'"
      using H2'
      apply -
      unfolding io_def
      apply(erule stepDisOutE)
      apply safe
      subgoal for o n m op'
        unfolding H1_2 p_def H1_3 conf_exchange_def
        apply auto
        apply(drule step_exchange_out_case)
        apply safe
        subgoal for op''
          apply(rule exI[where x = "(exchange_op Nats pact (n_op(n := op'')))"])
          apply(rule conjI)
          subgoal
            apply(rule step_exchange_out_intro[where op' = op'' and n = n])
            subgoal
              using H1_1
              by simp
            subgoal
              by blast
            subgoal
              by blast
            unfolding Nats_def
            by auto
          subgoal
            apply(rule bc'_base)
            apply(rule exI[where x= work_respons'])
            apply(rule exI[where x= pact])
            apply(rule exI[where x= "(n_op(n := op''))"])
            apply(rule exI[where x= "(w_n_op(work_respons' n := (w_n_op (work_respons' n))(n := op'')))"])
            using H1_1
            by auto
          done
        done
      done
  next
    assume io_def: "io = Tau"
    show "\<exists>op'. step io op op' \<and> bisim_dis_cong (\<lambda>op c. \<exists>work_respons' pact n_op w_n_op. (\<forall>n. n_op n = w_n_op (work_respons' n) n) \<and> op = exchange_op \<nat> pact n_op \<and> c = conf_exchange work_respons' pact w_n_op) op' c'"
      using H2'
      apply -
      unfolding io_def
      apply(erule stepDisTauE)
      apply safe
      subgoal for op'
        unfolding H1_2 H1_3 conf_exchange_def
        apply auto
        apply(drule step_exchange_tau_case)
        apply safe
        subgoal for n' op''
          apply(rule exI[where x = "(exchange_op Nats pact (n_op(n' := op'')))"])
          apply(rule conjI)
          subgoal
            apply(rule step_exchange_tau_intro[where op' = op'' and n = n'])
            subgoal
              using H1_1
              by simp
             apply auto
            unfolding Nats_def
            by auto
          subgoal
            apply(rule bc'_base)
            apply(rule exI[where x= work_respons'])
            apply(rule exI[where x= pact])
            apply(rule exI[where x= "(n_op(n' := op''))"])
            apply(rule exI[where x= "(w_n_op(work_respons' n' := (w_n_op (work_respons' n'))(n' := op'')))"])
            using H1_1
            by auto
          done
        done
      subgoal for p1 p2 op'
        unfolding H1_3 conf_exchange_def
        by simp
      subgoal for p1 p2 x op' p1' p2'
        unfolding H1_3 conf_exchange_def
        by simp
      done
  qed
qed

definition simp_wire' :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> (nat \<Rightarrow> 'w) \<Rightarrow> ('op1 \<times> (nat \<times> nat) \<rightharpoonup> 'ip2 \<times> (nat \<times> nat))" where
  "simp_wire' wire work_respons' = (\<lambda>op. case op of
    (op',n,m) \<Rightarrow> (case (wire op', work_respons' n = work_respons' m) of
      (Some ip',True) \<Rightarrow> Some (ip',n,m)
      | _ \<Rightarrow> None))"

definition simp_wire :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('op1 \<times> (nat \<times> nat) \<rightharpoonup> 'ip2 \<times> (nat \<times> nat))" where
  "simp_wire wire = (\<lambda>op. case op of
    (op',n,m) \<Rightarrow> (case wire op' of
      Some ip' \<Rightarrow> Some (ip',n,m)
      | None \<Rightarrow> None))"


abbreviation map_op_comp_fun where
  "map_op_comp_fun  \<equiv> (\<lambda>ip. case ip of Inl (ip',n,m) \<Rightarrow> (Inl ip',n,m) | Inr (ip',n,m) \<Rightarrow> (Inr ip',n,m))"

definition map_op_comp :: "('ip1 \<times> (nat \<times> nat) + 'ip2 \<times> (nat \<times> nat), 'op1 \<times> (nat \<times> nat) + 'op2 \<times> (nat \<times> nat), 'd) op \<Rightarrow> (('ip1 + 'ip2) \<times> (nat \<times> nat), ('op1 + 'op2) \<times> (nat \<times> nat), 'd) op" where
  "map_op_comp op = map_op map_op_comp_fun map_op_comp_fun op"

definition conf_comp :: "('op1 \<rightharpoonup> 'ip2) \<Rightarrow> ('w \<Rightarrow> 'ip2 \<times> (nat \<times> nat) \<Rightarrow> 'd buf) \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> 'ip2 \<times> (nat \<times> nat) \<Rightarrow> 'd buf) \<Rightarrow> ('w, 'ip1, 'op1, 'd) conf \<Rightarrow> ('w, 'ip2, 'op2, 'd) conf \<Rightarrow> 
    ('w, 'ip1 + 'ip2, 'op1 + 'op2, 'd) conf" where
  "conf_comp wire buf msg' c c' = \<lparr> 
    msg = (\<lambda>w w' ip. case ip of
      (Inl ip',n,m) \<Rightarrow> msg c w w' (ip',n,m)
      | (Inr ip',n,m) \<Rightarrow> if (\<exists>q. used_wire c' q = Some ip') then msg c' w w' (ip',n,m) else msg' w w' (ip',n,m)),
    ops = (\<lambda>w. map_op_comp (comp_op (simp_wire' wire (work_respons c)) (buf w) (ops c w) (ops c' w))),
    used_wire = (\<lambda>op. case op of
      Inl op' \<Rightarrow> (case (used_wire c op', wire op') of
        (Some ip, _) \<Rightarrow> Some (Inl ip)
        | (None, Some ip) \<Rightarrow> Some (Inr ip)
        | (None, None) \<Rightarrow> None)
      | Inr op' \<Rightarrow> (case used_wire c' op' of
        None \<Rightarrow> None
        | Some ip \<Rightarrow> Some (Inr ip))),
    work_respons = work_respons c
\<rparr>"

(*
lemma comp_spec :
  assumes bisim1: "op ~d c"
      and bisim2: "op' ~d c'"
      and conf_spec1: "conf_spec c"
      and conf_spec2: "conf_spec c'"
    shows "conf_spec (conf_comp wire buf msg' c c')"
proof -
  from assms show ?thesis
  unfolding conf_spec_def
  apply safe
  done
qed
*)

definition bufs_eq where
  "bufs_eq buf buf' msg' work_repons' = (\<forall>ip. case ip of (ip',n,m) \<Rightarrow> if (work_repons' n = work_repons' m) then buf ip = buf' (work_repons' n) ip else buf ip = msg' (work_repons' n) (work_repons' m) ip)"

lemma record_help:
  "msg (c\<lparr>ops := c_ops \<rparr>) = msg c"
  "ops (c\<lparr>ops := c_ops \<rparr>) = c_ops"
  "ops (c\<lparr>msg := c_msg \<rparr>) = ops c"
  "used_wire (c\<lparr>ops := c_ops \<rparr>) = used_wire c"
  "work_respons (c\<lparr>ops := c_ops \<rparr>) = work_respons c"
  "msg (c\<lparr>ops := c_ops, msg := c_msg \<rparr>) = c_msg"
  "ops (c\<lparr>ops := c_ops\<rparr>) = c_ops"
  "ops (c\<lparr>ops := c_ops, msg := c_msg \<rparr>) = c_ops"
  "work_respons (c\<lparr>ops := c_ops, msg := c_msg \<rparr>) = work_respons c"
  "used_wire (c\<lparr>ops := c_ops, msg := c_msg \<rparr>) = used_wire c"
  apply simp+
  done

lemma lambda_helper: "(\<forall>w. f w = g w) \<Longrightarrow> f = g"
  by auto

lemma comp_spec:
  assumes c_spec: "step_spec_conf c"
    and c'_spec: "step_spec_conf c'"
    and work_respons_eq: "work_respons c = work_respons c'"
  shows "step_spec_conf ((conf_comp wire buf' msg' c c') :: ('w, 'ip1 + 'ip2, 'op1 + 'op2, 'd) conf)"
proof (coinduct rule: step_spec_conf.coinduct [where X = "\<lambda>c1. \<exists> wire buf' msg' c c' c_msg. step_spec_conf c \<and> step_spec_conf c' \<and> work_respons c = work_respons c' \<and> c1 = conf_comp wire buf' msg' c c'\<lparr>msg := c_msg\<rparr>"])
  show "\<exists>wirea buf'a msg'a ca c'a c_msg. step_spec_conf ca \<and> step_spec_conf c'a \<and> work_respons ca = work_respons c'a \<and> conf_comp wire buf' msg' c c' = conf_comp wirea buf'a msg'a ca c'a\<lparr>msg := c_msg\<rparr>"
    using assms
    apply -
    apply(rule exI[where x = wire])
    apply(rule exI[where x = "buf'"])
    apply(rule exI[where x = "msg'"])
    apply(rule exI[where x = "c"])
    apply(rule exI[where x = "c'"])
    apply(rule exI[where x = "msg (conf_comp wire buf' msg' c c')"])
    by fastforce
next
  fix c1 :: "('w, 'ip1 + 'ip2, 'op1 + 'op2, 'd) conf"
  assume H1: "\<exists>wire buf' msg' c c' c_msg. step_spec_conf c \<and> step_spec_conf c' \<and> work_respons c = work_respons c' \<and> c1 = conf_comp wire buf' msg' c c'\<lparr>msg := c_msg\<rparr>"
  obtain wire buf' msg' c c' c_msg where H1_1: "step_spec_conf c" and H1_2: "step_spec_conf c'" and H1_3: "work_respons c = work_respons c'" and H1_4: "c1 = conf_comp wire buf' msg' c c'\<lparr>msg := c_msg\<rparr>"
    using H1
    by blast
  show "\<exists>c. c1 = c \<and>
             (\<forall>x xa xb.
                 step Tau (ops c xa) x \<longrightarrow>
                 (\<exists>wire buf' msg' ca c' c_msg.
                     step_spec_conf ca \<and> step_spec_conf c' \<and> work_respons ca = work_respons c' \<and> c\<lparr>ops := (ops c)(xa := x), msg := xb\<rparr> = conf_comp wire buf' msg' ca c'\<lparr>msg := c_msg\<rparr>) \<or>
                 step_spec_conf (c\<lparr>ops := (ops c)(xa := x), msg := xb\<rparr>)) \<and>
             (\<forall>x xa xb xc xd xe xf.
                 step (Inp (x, xa, xb) xc) (ops c xd) xe \<longrightarrow>
                 work_respons c xb = xd \<and>
                 ((\<exists>wire buf' msg' ca c' c_msg.
                      step_spec_conf ca \<and> step_spec_conf c' \<and> work_respons ca = work_respons c' \<and> c\<lparr>ops := (ops c)(xd := xe), msg := xf\<rparr> = conf_comp wire buf' msg' ca c'\<lparr>msg := c_msg\<rparr>) \<or>
                  step_spec_conf (c\<lparr>ops := (ops c)(xd := xe), msg := xf\<rparr>))) \<and>
             (\<forall>x xa xb xc xd xe xf.
                 step (Out (x, xa, xb) xc) (ops c xd) xe \<longrightarrow>
                 work_respons c xa = xd \<and>
                 ((\<exists>wire buf' msg' ca c' c_msg.
                      step_spec_conf ca \<and> step_spec_conf c' \<and> work_respons ca = work_respons c' \<and> c\<lparr>ops := (ops c)(xd := xe), msg := xf\<rparr> = conf_comp wire buf' msg' ca c'\<lparr>msg := c_msg\<rparr>) \<or>
                  step_spec_conf (c\<lparr>ops := (ops c)(xd := xe), msg := xf\<rparr>)))"
  proof (rule exI [where x = c1] , rule conjI , rule refl , (rule conjI ; (rule conjI) ? ; (rule allI) +; rule impI))
    fix op :: "(('ip1 + 'ip2) \<times> nat \<times> nat, ('op1 + 'op2) \<times> nat \<times> nat, 'd) op"
      and w :: 'w
      and c_msg 
    assume Step: "step Tau (ops c1 w) op"
    obtain op' where Step': "step Tau (comp_op (simp_wire' wire (work_respons c)) (buf' w) (ops c w) (ops c' w)) op'" and
      op_def: "op = map_op (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) op'"
      using Step
      unfolding H1_4 conf_comp_def map_op_comp_def
      apply auto
      by (metis (no_types, lifting) IO.map_disc_iff(3) step_map_op_inv)
    consider "\<exists>p x op1' q. op' = comp_op (simp_wire' wire (work_respons c)) (BENQ q x (buf' w)) op1' (ops c' w) \<and> simp_wire' wire (work_respons c) p = Some q \<and> step (Out p x) (ops c w) op1'" |
      "\<exists>p x op2'. op' = comp_op (simp_wire' wire (work_respons c)) (BTL p (buf' w)) (ops c w) op2' \<and> p \<in> ran (simp_wire' wire (work_respons c)) \<and>
       step (Inp p x) (ops c' w) op2' \<and> buf' w p \<noteq> [] \<and> BHD p (buf' w) = x" |
      "\<exists>op1'. op' = comp_op (simp_wire' wire (work_respons c)) (buf' w) op1' (ops c' w) \<and> step Tau (ops c w) op1'" |
      "\<exists>op2'. op' = comp_op (simp_wire' wire (work_respons c)) (buf' w) (ops c w) op2' \<and> step Tau (ops c' w) op2'"
      using Step' 
      apply -
      apply(erule step_comp_op_elim; simp)
      subgoal for p x op1' q
        by (metis prod_cases3)
      subgoal for p x op2'
        by (metis prod_cases3)
      subgoal for op1'
        by fast
      subgoal for op2'
        by fast
      done
    then show "(\<exists>wire buf' msg' ca c' c_msg'. step_spec_conf ca \<and> step_spec_conf c' \<and> work_respons ca = work_respons c' \<and> c1\<lparr>ops := (ops c1)(w := op), msg := c_msg\<rparr> = conf_comp wire buf' msg' ca c'\<lparr>msg := c_msg'\<rparr>) \<or>
       step_spec_conf (c1\<lparr>ops := (ops c1)(w := op), msg := c_msg\<rparr>)"
    proof (cases, goal_cases Tau_W Tau_R Tau_c1 Tau_c1')
      case Tau_W
      obtain p x op1' q where op'_def: "op' = comp_op (simp_wire' wire (work_respons c)) (BENQ q x (buf' w)) op1' (ops c' w)" and wire_some: "simp_wire' wire (work_respons c) p = Some q" and Step': "step (Out p x) (ops c w) op1'"
        using Tau_W
        by blast
      show ?case
        apply(rule disjI1)
        apply(rule exI[where x = wire])
        apply(rule exI[where x = "buf'(w:= (BENQ q x (buf' w)))"])
        apply(rule exI[where x = msg'])
        apply(rule exI[where x = "c\<lparr>ops := (ops c)(w := op1')\<rparr>"])
        apply(rule exI[where x = c'])
        apply(rule exI[where x = c_msg])
        unfolding op_def op'_def
        apply(safe)
        subgoal
          using H1_1 Step'
          unfolding step_spec_conf.simps[where a = c]
          apply -
          apply auto
          apply(cases p; simp)
          subgoal for p' pn pm
            apply(erule allE[where x = p'])
            apply(erule allE[where x = pn])
            apply(erule allE[where x = pm])
            apply(erule allE[where x = x])
            apply(erule allE[where x = w])
            apply(erule allE[where x = op1'])
            apply(erule allE[where x = op1'])
            apply(erule impE, assumption)
            apply(erule conjE)
            apply(erule allE[where x = "msg (c\<lparr>ops := (ops c)(w := op1')\<rparr>)"])
            by simp
          done
        subgoal
          using H1_2
          by simp
        subgoal
          using H1_3
          apply(simp add: record_help)
          done
        subgoal
          unfolding H1_4
          apply(subst conf_comp_def[where wire = wire and buf = buf'])+
          apply(subst conf_comp_def[symmetric])
          apply(subst conf_comp_def[where wire = wire and buf = "(buf'(w := BENQ q x (buf' w)))"])
          apply simp
          apply(subst conf_comp_def[where wire = wire and buf = buf'])+
          apply simp
          unfolding map_op_comp_def
          apply simp
          by auto
        done
    next
      case Tau_R
      obtain p x op2' where op'_def: "op' = comp_op (simp_wire' wire (work_respons c)) (BTL p (buf' w)) (ops c w) op2'" and wire_some: "p \<in> ran (simp_wire' wire (work_respons c))" and Step': "step (Inp p x) (ops c' w) op2'" and buf_empty: "buf' w p \<noteq> []" and buf_head: "BHD p (buf' w) = x"
        using Tau_R
        by blast
      show ?case
        apply(rule disjI1)
        apply(rule exI[where x = wire])
        apply(rule exI[where x = "buf'(w:= (BTL p (buf' w)))"])
        apply(rule exI[where x = msg'])
        apply(rule exI[where x = "c"])
        apply(rule exI[where x = "c'\<lparr>ops := (ops c')(w := op2')\<rparr>"])
        apply(rule exI[where x = "c_msg"])
        unfolding op_def op'_def
        apply(safe)
        subgoal
          using H1_1 Step'
          by auto
        subgoal
          using H1_2 Step'
          unfolding step_spec_conf.simps[where a = c']
          apply -
          apply auto
          apply(cases p; simp)
          subgoal for p' pn pm
            apply(erule allE[where x = p'])
            apply(erule allE[where x = pn])
            apply(erule allE[where x = pm])
            apply(erule allE[where x = x])
            apply(erule allE[where x = w])
            apply(erule allE[where x = op2'])
            apply(erule allE[where x = op2'])
            apply(erule impE, assumption)
            apply(erule conjE)
            apply(erule allE[where x = "msg (c'\<lparr>ops := (ops c')(w := op2')\<rparr>)"])
            by simp
          done
        subgoal
          using H1_3
          apply(simp add: record_help)
          done
        subgoal
          unfolding H1_4
          apply(subst conf_comp_def[where wire = wire and buf = buf'])+
          apply(subst conf_comp_def[symmetric])
          apply(subst conf_comp_def[where wire = wire and buf = "(buf'(w := BTL p (buf' w)))"])
          apply simp
          apply(subst conf_comp_def[where wire = wire and buf = buf'])+
          apply simp
          unfolding map_op_comp_def
          apply simp
          by auto
        done
    next
      case Tau_c1
      obtain op1' where op'_def: "op' = comp_op (simp_wire' wire (work_respons c)) (buf' w) op1' (ops c' w)" and Step': "step Tau (ops c w) op1'"
        using Tau_c1
        by blast
      show ?case
        apply(rule disjI1)
        apply(rule exI[where x = wire])
        apply(rule exI[where x = "buf'"])
        apply(rule exI[where x = msg'])
        apply(rule exI[where x = "c\<lparr>ops := (ops c)(w := op1')\<rparr>"])
        apply(rule exI[where x = "c'"])
        apply(rule exI[where x = "c_msg"])
        unfolding op_def op'_def
        apply(safe)
        subgoal
          using H1_1 Step'
          unfolding step_spec_conf.simps[where a = c]
          apply -
          apply auto
          apply(erule allE[where x = op1'])
          apply(erule allE[where x = w])
          apply(erule impE, assumption)
          apply(erule allE[where x = "msg (c\<lparr>ops := (ops c)(w := op1')\<rparr>)"])
          by simp
        subgoal
          using H1_2 Step'
          by simp
        subgoal
          using H1_3
          apply(simp add: record_help)
          done
        subgoal
          unfolding H1_4
          apply(subst conf_comp_def[where wire = wire and buf = buf'])+
          apply(subst conf_comp_def[symmetric])
          apply simp
          apply(subst conf_comp_def[where wire = wire and buf = buf'])
          apply simp
          unfolding map_op_comp_def
          apply simp
          by auto
        done
    next
      case Tau_c1'
      obtain op2' where op'_def: "op' = comp_op (simp_wire' wire (work_respons c)) (buf' w) (ops c w) op2'" and Step': "step Tau (ops c' w) op2'"
        using Tau_c1'
        by blast
      show ?case
        apply(rule disjI1)
        apply(rule exI[where x = wire])
        apply(rule exI[where x = "buf'"])
        apply(rule exI[where x = msg'])
        apply(rule exI[where x = "c"])
        apply(rule exI[where x = "c'\<lparr>ops := (ops c')(w := op2')\<rparr>"])
        apply(rule exI[where x = "c_msg"])
        unfolding op_def op'_def
        apply(safe)
        subgoal
          using H1_1 Step'
          by simp
        subgoal
          using H1_2 Step'
          unfolding step_spec_conf.simps[where a = c']
          apply -
          apply auto
          apply(erule allE[where x = op2'])
          apply(erule allE[where x = w])
          apply(erule impE, assumption)
          apply(erule allE[where x = "msg (c'\<lparr>ops := (ops c')(w := op2')\<rparr>)"])
          by simp
        subgoal
          using H1_3
          apply(simp add: record_help)
          done
        subgoal
          unfolding H1_4
          apply(subst conf_comp_def[where wire = wire and buf = buf'])+
          apply simp
          unfolding map_op_comp_def
          apply simp
          by auto
        done
    qed
  next
    fix p :: "'ip1 + 'ip2"
      and pn :: nat
      and pm :: nat
      and x :: 'd
      and w :: 'w
      and op :: "(('ip1 + 'ip2) \<times> nat \<times> nat, ('op1 + 'op2) \<times> nat \<times> nat, 'd) op"
      and c_msg
    assume Step: "step (Inp (p, pn, pm) x) (ops c1 w) op"
    obtain op' p' where Step': "step (Inp p' x) (comp_op (simp_wire' wire (work_respons c)) (buf' w) (ops c w) (ops c' w)) op'" and p'_def: "(case p' of Inl (ip', xa) \<Rightarrow> (Inl ip', xa) | Inr (ip', xa) \<Rightarrow> (Inr ip', xa)) = (p, pn, pm)" and
      op_def: "op = map_op (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) op'"
      using Step
      unfolding H1_4 conf_comp_def map_op_comp_def
      apply simp
      apply(erule step_map_op_elim)
      apply(erule conjE)+
      subgoal for io op'
        apply(cases io; simp)
        done
      done
    consider "\<exists> op'' p''. Inl p'' = p \<and> p' = Inl (p'', pn, pm) \<and> op' = comp_op (simp_wire' wire (work_respons c)) (buf' w) op'' (ops c' w) \<and> step (Inp (p'', pn, pm) x) (ops c w) op''" |
    "\<exists> op'' p''. Inr p'' = p \<and> p' = Inr (p'', pn, pm) \<and> op' = comp_op (simp_wire' wire (work_respons c)) (buf' w) (ops c w) op'' \<and> (p'', pn, pm) \<notin> ran (simp_wire' wire (work_respons c)) \<and> step (Inp (p'', pn, pm) x) (ops c' w) op''"
      using Step' p'_def 
      apply(cases p'; simp)
        subgoal for p1
          apply(cases p1; simp)
          subgoal for p''
            apply(erule step_comp_op_elim; simp)
            subgoal for p''' op''
              by blast
            done
          done
        subgoal for p1
          apply(cases p1; simp)
          subgoal for p''
            apply(erule step_comp_op_elim; simp)
            subgoal for p''' op''
              by blast
            done
        done
      done
    then show "work_respons c1 pm = w \<and> ((\<exists>wire buf' msg' ca c' c_msg'. step_spec_conf ca \<and> step_spec_conf c' \<and> work_respons ca = work_respons c' \<and> c1\<lparr>ops := (ops c1)(w := op), msg := c_msg\<rparr> = conf_comp wire buf' msg' ca c'\<lparr>msg := c_msg'\<rparr>) \<or> step_spec_conf (c1\<lparr>ops := (ops c1)(w := op), msg := c_msg\<rparr>))"
    proof (cases, goal_cases Inl Inr)
      case Inl
      obtain op'' p'' where p_def: "p = Inl p''" and p'_def: "p' = Inl (p'', pn, pm)" and op'_def: "op' = comp_op (simp_wire' wire (work_respons c)) (buf' w) op'' (ops c' w)" and 
        Step'': "step (Inp (p'', pn, pm) x) (ops c w) op''"
        using Inl
        by blast
      have w_def: "w = work_respons c pm" and c_new_spec: "step_spec_conf (c\<lparr>ops := (ops c)(w := op'')\<rparr>)"
        subgoal
          using H1_1 Step''
          apply -
          apply(erule step_spec_conf.cases)
          by auto
        subgoal
          using H1_1 Step''
          unfolding step_spec_conf.simps[where a = c]
          apply -
          apply auto
          apply(erule allE[where x = p''])
          apply(erule allE[where x = pn])
          apply(erule allE[where x = pm])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op''])
          apply(erule allE[where x = op''])
          apply(erule impE, assumption)
          apply(erule conjE)
          apply(erule allE[where x = "msg (c\<lparr>ops := (ops c)(w := op'')\<rparr>)"])
          by simp
        done
      show ?case
        apply(rule conjI)
        subgoal
          using w_def
          unfolding H1_4 conf_comp_def
          apply simp
          done
        subgoal
          apply(rule disjI1)
          unfolding H1_4 op_def op'_def
          apply(rule exI[where x = wire])
          apply(rule exI[where x = "buf'"])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = "c\<lparr>ops := (ops c)(w := op'')\<rparr>"])
          apply(rule exI[where x = "c'"])
          apply(rule exI[where x = c_msg])
          apply(safe)
          subgoal
            using c_new_spec
            by simp
          subgoal
            using H1_2
            by simp
          subgoal
            using H1_3
            apply(simp add: record_help)
            done
          subgoal
            unfolding H1_4
            apply(subst conf_comp_def[where wire = wire and buf = buf'])+
            apply simp
            unfolding map_op_comp_def
            apply simp
            by auto
          done
        done
     next
      case Inr
      obtain op'' p'' where p_def: "p = Inr p''" and p'_def: "p' = Inr (p'', pn, pm)" and op'_def: "op' = comp_op (simp_wire' wire (work_respons c)) (buf' w) (ops c w) op''" and 
        Step'': "step (Inp (p'', pn, pm) x) (ops c' w) op''"
        using Inr
        by blast
      have w_def: "w = work_respons c' pm" and c_new_spec: "step_spec_conf (c'\<lparr>ops := (ops c')(w := op'')\<rparr>)"
        subgoal
          using H1_2 Step''
          apply -
          apply(erule step_spec_conf.cases)
          by auto
        subgoal
          using H1_2 Step''
          unfolding step_spec_conf.simps[where a = c']
          apply -
          apply auto
          apply(erule allE[where x = p''])
          apply(erule allE[where x = pn])
          apply(erule allE[where x = pm])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op''])
          apply(erule allE[where x = op''])
          apply(erule impE, assumption)
          apply(erule conjE)
          apply(erule allE[where x = "msg (c'\<lparr>ops := (ops c')(w := op'')\<rparr>)"])
          by simp
          done
      show ?case
        apply(rule conjI)
        subgoal
          using w_def H1_3
          unfolding H1_4 conf_comp_def
          apply simp
          done
        subgoal
          apply(rule disjI1)
          unfolding H1_4 op_def op'_def
          apply(rule exI[where x = wire])
          apply(rule exI[where x = "buf'"])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = "c"])
          apply(rule exI[where x = "c'\<lparr>ops := (ops c')(w := op'')\<rparr>"])
          apply(rule exI[where x = c_msg])
          apply(safe)
          subgoal
            using H1_1
            by simp
          subgoal
            using c_new_spec
            by simp
          subgoal
            using H1_3
            apply(simp add: record_help)
            done
          subgoal
            unfolding H1_4
            apply(subst conf_comp_def[where wire = wire and buf = buf'])+
            apply simp
            unfolding map_op_comp_def
            apply simp
            by auto
          done
        done
    qed
  next
    fix q :: "'op1 + 'op2"
      and qn :: nat
      and qm :: nat
      and x :: 'd
      and w :: 'w
      and op :: "(('ip1 + 'ip2) \<times> nat \<times> nat, ('op1 + 'op2) \<times> nat \<times> nat, 'd) op"
      and c_msg
    assume Step: "step (Out (q, qn, qm) x) (ops c1 w) op"
    obtain op' q' where Step': "step (Out q' x) (comp_op (simp_wire' wire (work_respons c)) (buf' w) (ops c w) (ops c' w)) op'" and q'_def: "(case q' of Inl (ip', xa) \<Rightarrow> (Inl ip', xa) | Inr (ip', xa) \<Rightarrow> (Inr ip', xa)) = (q, qn, qm)" and
      op_def: "op = map_op (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) op'"
      using Step
      unfolding H1_4 conf_comp_def map_op_comp_def
      apply simp
      apply(erule step_map_op_elim)
      apply(erule conjE)+
      subgoal for io op'
        apply(cases io; simp)
        done
      done
    consider "\<exists> op'' q''. Inl q'' = q \<and> q' = Inl (q'', qn, qm) \<and> op' = comp_op (simp_wire' wire (work_respons c)) (buf' w) op'' (ops c' w) \<and> simp_wire' wire (work_respons c) (q'', qn, qm) = None \<and> step (Out (q'', qn, qm) x) (ops c w) op''" |
    "\<exists> op'' q''. Inr q'' = q \<and> q' = Inr (q'', qn, qm) \<and> op' = comp_op (simp_wire' wire (work_respons c)) (buf' w) (ops c w) op'' \<and> step (Out (q'', qn, qm) x) (ops c' w) op''"
      using Step' q'_def 
      apply(cases q'; simp)
        subgoal for q1
          apply(cases q1; simp)
          subgoal for q''
            apply(erule step_comp_op_elim; simp)
            subgoal for q''' op''
              by blast
            done
          done
        subgoal for q1
          apply(cases q1; simp)
          subgoal for q''
            apply(erule step_comp_op_elim; simp)
            subgoal for q''' op''
              by blast
            done
        done
      done
    then show "work_respons c1 qn = w \<and> ((\<exists>wire buf' msg' ca c' c_msg'. step_spec_conf ca \<and> step_spec_conf c' \<and> work_respons ca = work_respons c' \<and> c1\<lparr>ops := (ops c1)(w := op), msg := c_msg\<rparr> = conf_comp wire buf' msg' ca c'\<lparr>msg := c_msg'\<rparr>) \<or> step_spec_conf (c1\<lparr>ops := (ops c1)(w := op), msg := c_msg\<rparr>))"
    proof (cases, goal_cases Inl Inr)
      case Inl
      obtain op'' q'' where p_def: "q = Inl q''" and p'_def: "q' = Inl (q'', qn, qm)" and op'_def: "op' = comp_op (simp_wire' wire (work_respons c)) (buf' w) op'' (ops c' w)" and 
        Step'': "step (Out (q'', qn, qm) x) (ops c w) op''"
        using Inl
        by blast
      have w_def: "w = work_respons c qn" and c_new_spec: "step_spec_conf (c\<lparr>ops := (ops c)(w := op'')\<rparr>)"
        subgoal
          using H1_1 Step''
          apply -
          apply(erule step_spec_conf.cases)
          by auto
        subgoal
          using H1_1 Step''
          unfolding step_spec_conf.simps[where a = c]
          apply -
          apply auto
          apply(erule allE[where x = q''])
          apply(erule allE[where x = qn])
          apply(erule allE[where x = qm])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op''])
          apply(erule allE[where x = op''])
          apply(erule impE, assumption)
          apply(erule conjE)
          apply(erule allE[where x = "msg (c\<lparr>ops := (ops c)(w := op'')\<rparr>)"])
          by simp
          done
      show ?case
        apply(rule conjI)
        subgoal
          using w_def
          unfolding H1_4 conf_comp_def
          apply simp
          done
        subgoal
          apply(rule disjI1)
          unfolding H1_4 op_def op'_def
          apply(rule exI[where x = wire])
          apply(rule exI[where x = "buf'"])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = "c\<lparr>ops := (ops c)(w := op'')\<rparr>"])
          apply(rule exI[where x = "c'"])
          apply(rule exI[where x = c_msg])
          apply(safe)
          subgoal
            using c_new_spec
            by simp
          subgoal
            using H1_2
            by simp
          subgoal
            using H1_3
            apply(simp add: record_help)
            done
          subgoal
            unfolding H1_4
            apply(subst conf_comp_def[where wire = wire and buf = buf'])+
            apply simp
            unfolding map_op_comp_def
            apply simp
            by auto
          done
        done
     next
      case Inr
      obtain op'' q'' where p_def: "q = Inr q''" and p'_def: "q' = Inr (q'', qn, qm)" and op'_def: "op' = comp_op (simp_wire' wire (work_respons c)) (buf' w) (ops c w) op''" and 
        Step'': "step (Out (q'', qn, qm) x) (ops c' w) op''"
        using Inr
        by blast
      have w_def: "w = work_respons c' qn" and c_new_spec: "step_spec_conf (c'\<lparr>ops := (ops c')(w := op'')\<rparr>)"
        subgoal
          using H1_2 Step''
          apply -
          apply(erule step_spec_conf.cases)
          by auto
        subgoal
          using H1_2 Step''
          unfolding step_spec_conf.simps[where a = c']
          apply -
          apply auto
          apply(erule allE[where x = q''])
          apply(erule allE[where x = qn])
          apply(erule allE[where x = qm])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op''])
          apply(erule allE[where x = op''])
          apply(erule impE, assumption)
          apply(erule conjE)
          apply(erule allE[where x = "msg (c'\<lparr>ops := (ops c')(w := op'')\<rparr>)"])
          by simp
          done
      show ?case
        apply(rule conjI)
        subgoal
          using w_def H1_3
          unfolding H1_4 conf_comp_def
          apply simp
          done
        subgoal
          apply(rule disjI1)
          unfolding H1_4 op_def op'_def
          apply(rule exI[where x = wire])
          apply(rule exI[where x = "buf'"])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = "c"])
          apply(rule exI[where x = "c'\<lparr>ops := (ops c')(w := op'')\<rparr>"])
          apply(rule exI[where x = c_msg])
          apply(safe)
          subgoal
            using H1_1
            by simp
          subgoal
            using c_new_spec
            by simp
          subgoal
            using H1_3
            apply(simp add: record_help)
            done
          subgoal
            unfolding H1_4
            apply(subst conf_comp_def[where wire = wire and buf = buf'])+
            apply simp
            unfolding map_op_comp_def
            apply simp
            by auto
          done
        done
    qed
  qed
qed

lemma comp_bisim :
  assumes bisim1: "op ~d c"
      and bisim2: "op' ~d c'"
      and c_spec1: "step_spec_conf c"
      and c_spec2: "step_spec_conf c'"
      and buf_eq: "bufs_eq buf buf' msg' (work_respons c)"
      and work_respons_eq: "work_respons c = work_respons c'"
      and wires_not_overlapping: "\<forall>p q. wire q = Some p \<longrightarrow> (used_wire c q = None \<and> (\<forall>q'. used_wire c' q' \<noteq> Some p))"
    shows "(map_op_comp (comp_op (simp_wire wire) buf op op')) ~d ((conf_comp wire buf' msg' c c') :: ('w, 'ip1 + 'ip2, 'op1 + 'op2, 'd) conf)"
proof -
  let ?P = "\<lambda>io op' c. \<exists>c'. step_dis' io c c' \<and>
            bisim_dis_cong (\<lambda>total_op total_c. \<exists>wire buf buf' msg' op op' c c'. op ~d c \<and> op' ~d c' \<and> step_spec_conf c \<and> step_spec_conf c' \<and> bufs_eq buf buf' msg' (work_respons c') \<and> work_respons c = work_respons c' \<and> total_op = map_op_comp (comp_op (simp_wire wire) buf op op') \<and> total_c = conf_comp wire buf' msg' c c' \<and> (\<forall>p q. wire q = Some p \<longrightarrow> (used_wire c q = None \<and> (\<forall>q'. used_wire c' q' \<noteq> Some p)))) op' c'"
  show ?thesis
proof(rule bisim_dis_coinduct_upto''[where R = "\<lambda> total_op total_c. \<exists> wire buf buf' msg' op op' c c'. op ~d c \<and> op' ~d c' \<and> step_spec_conf c \<and> step_spec_conf c' \<and> bufs_eq buf buf' msg' (work_respons c') \<and> work_respons c = work_respons c' \<and> total_op = (map_op_comp (comp_op (simp_wire wire) buf op op')) \<and> total_c = conf_comp wire buf' msg' c c' \<and> (\<forall>p q. wire q = Some p \<longrightarrow> (used_wire c q = None \<and> (\<forall>q'. used_wire c' q' \<noteq> Some p)))"])
  show "\<exists>wirea bufa buf'a msg'a opa op'a ca c'a.
       opa ~d ca \<and> op'a ~d c'a \<and> step_spec_conf ca \<and> step_spec_conf c'a \<and> bufs_eq bufa buf'a msg'a (work_respons c'a) \<and> work_respons ca = work_respons c'a \<and> map_op_comp (comp_op (simp_wire wire) buf op op') = map_op_comp (comp_op (simp_wire wirea) bufa opa op'a) \<and> conf_comp wire buf' msg' c c' = conf_comp wirea buf'a msg'a ca c'a \<and> (\<forall>p q. wirea q = Some p \<longrightarrow> used_wire ca q = None \<and> (\<forall>q'. used_wire c'a q' \<noteq> Some p))"
    using assms
    by metis
next
  fix op :: "(('ip1 + 'ip2) \<times> nat \<times> nat, ('op1 + 'op2) \<times> nat \<times> nat, 'd) op"
    and c :: "('w, 'ip1 + 'ip2, 'op1 + 'op2, 'd) conf"
    and io :: "(('ip1 + 'ip2) \<times> nat \<times> nat, ('op1 + 'op2) \<times> nat \<times> nat, 'd) IO"
    and op' :: "(('ip1 + 'ip2) \<times> nat \<times> nat, ('op1 + 'op2) \<times> nat \<times> nat, 'd) op"
  assume H1: "\<exists>wire buf buf' msg' opa op' ca c'. opa ~d ca \<and> op' ~d c' \<and> step_spec_conf ca \<and> step_spec_conf c' \<and> bufs_eq buf buf' msg' (work_respons c') \<and> work_respons ca = work_respons c' \<and> op = map_op_comp (comp_op (simp_wire wire) buf opa op') \<and> c = conf_comp wire buf' msg' ca c' \<and> (\<forall>p q. wire q = Some p \<longrightarrow> (used_wire ca q = None \<and> (\<forall>q'. used_wire c' q' \<noteq> Some p)))"
    and H2: "step io op op'"
  obtain wire buf buf' msg' op1 op1' c1 c1' where H1_1: "op1 ~d c1" and H1_2: "op1' ~d c1'" and H1_3: "bufs_eq buf buf' msg' (work_respons c1')" and H1_4: "work_respons c1 = work_respons c1'" and H1_5: "op = map_op_comp (comp_op (simp_wire wire) buf op1 op1')" and H1_6: "c = conf_comp wire buf' msg' c1 c1'"
    and H1_7: "(\<forall>p q. wire q = Some p \<longrightarrow> (used_wire c1 q = None \<and> (\<forall>q'. used_wire c1' q' \<noteq> Some p)))" and H1_8: "step_spec_conf c1" and H1_9: "step_spec_conf c1'"
    using H1
    by blast
  obtain io' op'' where H2': "step io' (comp_op (simp_wire wire) buf op1 op1') op''" and io_def: "map_IO map_op_comp_fun map_op_comp_fun id io' = io" and op'_def: "map_op map_op_comp_fun map_op_comp_fun op'' = op'"
    using H2 H1_5 step_map_op_elim
    unfolding map_op_comp_def
    by meson
  show "?P io op' c"
  proof (rule step_comp_op_elim [of io' "(simp_wire wire)" buf op1 op1' op''])
    show "step io' (comp_op (simp_wire wire) buf op1 op1') op''"
      using H2'
      by auto
  next
    fix p :: "'ip1 \<times> nat \<times> nat"
      and x :: 'd
      and op2 :: "('ip1 \<times> nat \<times> nat, 'op1 \<times> nat \<times> nat, 'd) op"
    assume io'_def: "io' = Inp (Inl p) x"
      and op''_def: "op'' = comp_op (simp_wire wire) buf op2 op1'"
      and H3: "step (Inp p x) op1 op2"
    obtain w c2 where H3_1: "step_dis w (Inp p x) c1 c2" and H3_2: "op2 ~d c2"
      using bisim_op_elim H3 H1_1
      by meson
    show "?P io op' c"
      using H3_1
      apply -
      apply(erule stepDisInE)
      unfolding H1_6 io_def[symmetric] io'_def
      apply simp
      apply(rule exI[where x = "conf_comp wire buf' msg' c2 c1'"])
      apply(rule conjI)
      subgoal for p' pn pm op3'
        apply(rule S[where w = w])
        apply(rule SDR[where op' = "ops (conf_comp wire buf' msg' c2 c1') w"])
        subgoal
          unfolding conf_comp_def map_op_comp_def
          by auto
        subgoal
          unfolding conf_comp_def
          apply auto
          apply(simp only: record_help)
          done
        subgoal
          unfolding conf_comp_def
          apply auto
          subgoal for q
            apply(cases q; simp)
            subgoal for q'
              apply(cases "used_wire c1 q'"; simp)
              apply(cases "wire q'"; simp)
              done
            subgoal for q'
              apply(cases "used_wire c1' q'"; simp)
              done
            done
          done
        subgoal
          unfolding conf_comp_def
          apply auto
          done
        done
      subgoal for p' pn pm op3'
        apply(rule bc'_base)
        unfolding op'_def[symmetric] map_op_comp_def op''_def
        apply(rule exI[where x = wire])
        apply(rule exI[where x = buf])
        apply(rule exI[where x = buf'])
        apply(rule exI[where x = msg'])
        apply(rule exI[where x = op2])
        apply(rule exI[where x = op1'])
        apply(rule exI[where x = c2])
        using H3_2
        apply auto
        apply(rule exI[where x = c1'])
        using H1_2 H1_3 H1_4 work_respons_eq H1_7
        apply auto
        subgoal
          using H1_8
          unfolding step_spec_conf.simps[where a = c1]
          apply -
          apply safe
          apply(erule allE[where x = p'])
          apply(erule allE[where x = pn])
          apply(erule allE[where x = pm])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op3'])
          apply(erule allE[where x = op3'])
          apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := op3')\<rparr>)"])
          apply simp
          done
        using H1_9
        by simp
      done
  next
    fix q :: "'op2 \<times> nat \<times> nat"
      and x :: 'd
      and op2 :: "('ip2 \<times> nat \<times> nat, 'op2 \<times> nat \<times> nat, 'd) op"
    assume io'_def: "io' = Out (Inr q) x"
      and op''_def: "op'' = comp_op (simp_wire wire) buf op1 op2"
      and H3: "step (Out q x) op1' op2"
    obtain w c2 where H3_1: "step_dis w (Out q x) c1' c2" and H3_2: "op2 ~d c2"
      using bisim_op_elim H3 H1_2
      by meson
    show "?P io op' c"
      using H3_1
      apply -
      apply(erule stepDisOutE)
      unfolding H1_6 io_def[symmetric] io'_def
      apply simp
      apply(rule exI[where x = "conf_comp wire buf' msg' c1 c2"])
      apply(rule conjI)
      subgoal for q' qn qm op3'
        apply(rule S[where w = w])
        apply(rule SDW[where op' = "ops (conf_comp wire buf' msg' c1 c2) w"])
        subgoal
          unfolding conf_comp_def map_op_comp_def
          by auto
        subgoal
          unfolding conf_comp_def
          apply auto
          apply(simp only: record_help)
          done
        subgoal
          unfolding conf_comp_def
          apply auto
          done
        subgoal
          unfolding conf_comp_def
          using H1_4
          apply auto
          done
        done
      subgoal for p' pn pm op3'
        apply(rule bc'_base)
        unfolding op'_def[symmetric] map_op_comp_def op''_def
        apply(rule exI[where x = wire])
        apply(rule exI[where x = buf])
        apply(rule exI[where x = buf'])
        apply(rule exI[where x = msg'])
        apply(rule exI[where x = op1])
        apply(rule exI[where x = op2])
        apply(rule exI[where x = c1])
        using H1_1
        apply auto
        apply(rule exI[where x = c2])
        using H3_2 H1_3 H1_4 work_respons_eq H1_7
        apply auto
        subgoal using H1_8
          by simp
        subgoal
          using H1_9
          unfolding step_spec_conf.simps[where a = c1']
          apply -
          apply safe
          apply(erule allE[where x = p'])
          apply(erule allE[where x = pn])
          apply(erule allE[where x = pm])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op3'])
          apply(erule allE[where x = op3'])
          apply(erule allE[where x = "msg (c1'\<lparr>ops := (ops c1')(w := op3')\<rparr>)"])
          by fastforce
          done
        done
  next
    fix q :: "'op1 \<times> nat \<times> nat"
      and x :: 'd
      and op2 :: "('ip1 \<times> nat \<times> nat, 'op1 \<times> nat \<times> nat, 'd) op"
    assume io'_def: "io' = Out (Inl q) x"
      and op''_def: "op'' = comp_op (simp_wire wire) buf op2 op1'"
      and wire_none: "simp_wire wire q = None"
      and H3: "step (Out q x) op1 op2"
    obtain w c2 where H3_1: "step_dis w (Out q x) c1 c2" and H3_2: "op2 ~d c2"
      using bisim_op_elim H3 H1_1
      by meson
    show "?P io op' c"
      using H3_1
      apply -
      apply(erule stepDisOutE)
      unfolding H1_6 io_def[symmetric] io'_def
      apply simp
      apply(rule exI[where x = "conf_comp wire buf' msg' c2 c1'"])
      apply(rule conjI)
      subgoal for q' qn qm op3'
        apply(rule S[where w = w])
        apply(rule SDW[where op' = "ops (conf_comp wire buf' msg' c2 c1') w"])
        subgoal
          unfolding conf_comp_def map_op_comp_def
          apply simp
          apply(rule step_map_op[where io = "Out (Inl (q', qn, qm)) x"])
           apply auto
          using wire_none
          unfolding simp_wire_def simp_wire'_def
          apply -
          apply auto
          apply(cases "wire q'"; simp)
          done
        subgoal
          unfolding conf_comp_def
          apply auto
          apply(simp only: record_help)
          done
        subgoal
          unfolding conf_comp_def
          apply auto
          using wire_none
          apply -
          unfolding simp_wire_def
          apply auto
          apply(cases "wire q'"; simp)
          done
        subgoal
          unfolding conf_comp_def
          using H1_4
          apply auto
          done
        done
      subgoal for p' pn pm op3'
        apply(rule bc'_base)
        unfolding op'_def[symmetric] map_op_comp_def op''_def
        apply(rule exI[where x = wire])
        apply(rule exI[where x = buf])
        apply(rule exI[where x = buf'])
        apply(rule exI[where x = msg'])
        apply(rule exI[where x = op2])
        apply(rule exI[where x = op1'])
        apply(rule exI[where x = c2])
        using H3_2
        apply auto
        apply(rule exI[where x = c1'])
        using H1_2 H1_3 H1_4 work_respons_eq H1_7
        apply auto
        subgoal
          using H1_8
          unfolding step_spec_conf.simps[where a = c1]
          apply -
          apply safe
          apply(erule allE[where x = p'])
          apply(erule allE[where x = pn])
          apply(erule allE[where x = pm])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op3'])
          apply(erule allE[where x = op3'])
          apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := op3')\<rparr>)"])
          by fastforce
        subgoal using H1_9
          by simp
        done
      done
    next
    fix p :: "'ip2 \<times> nat \<times> nat"
      and x :: 'd
      and op2 :: "('ip2 \<times> nat \<times> nat, 'op2 \<times> nat \<times> nat, 'd) op"
    assume io'_def: "io' = Inp (Inr p) x"
      and op''_def: "op'' = comp_op (simp_wire wire) buf op1 op2"
      and wire_not_ran: "p \<notin> ran (simp_wire wire)"
      and H3: "step (Inp p x) op1' op2"
    obtain w c2 where H3_1: "step_dis w (Inp p x) c1' c2" and H3_2: "op2 ~d c2"
      using bisim_op_elim H3 H1_2
      by meson
    show "?P io op' c"
      using H3_1
      apply -
      apply(erule stepDisInE)
      unfolding H1_6 io_def[symmetric] io'_def
      apply simp
      apply(rule exI[where x = "conf_comp wire buf' msg' c1 c2"])
      apply(rule conjI)
      subgoal for p' pn pm op3'
        apply(rule S[where w = w])
        apply(rule SDR[where op' = "ops (conf_comp wire buf' msg' c1 c2) w"])
        subgoal
          unfolding conf_comp_def map_op_comp_def
          apply simp
          apply(rule step_map_op[where io = "Inp (Inr (p', pn, pm)) x"])
           apply auto
          using wire_not_ran
          apply -
          unfolding simp_wire_def simp_wire'_def ran_def
          apply auto
          subgoal for q' qn qm
            apply(cases "wire q'"; simp)
            subgoal for q''
              apply(erule allE[where x = q'])
              apply(cases "work_respons c1 qn = work_respons c1 qm"; simp)
              done
            done
          done
        subgoal
          unfolding conf_comp_def
          apply auto
          apply(simp only: record_help)
          done
        subgoal
          unfolding conf_comp_def
          apply auto
          subgoal for q'
            using wire_not_ran
            apply -
            unfolding simp_wire_def ran_def
            apply auto
            apply(cases q'; simp)
            subgoal for q''
              apply(cases "used_wire c1 q''"; simp)
              apply(cases "wire q''"; simp)
              apply(erule allE[where x = q''])
              apply(erule allE[where x = pn])
              apply(erule allE[where x = pm])
              apply auto
              done
            subgoal for q''
              apply(cases "used_wire c1' q''"; simp)
              done
            done
          done
        subgoal
          unfolding conf_comp_def
          using H1_4
          apply auto
          done
        done
      subgoal for p' pn pm op3'
        apply(rule bc'_base)
        unfolding op'_def[symmetric] map_op_comp_def op''_def
        apply(rule exI[where x = wire])
        apply(rule exI[where x = buf])
        apply(rule exI[where x = buf'])
        apply(rule exI[where x = msg'])
        apply(rule exI[where x = op1])
        apply(rule exI[where x = op2])
        apply(rule exI[where x = c1])
        using H1_1
        apply auto
        apply(rule exI[where x = c2])
        using H3_2 H1_3 H1_4 work_respons_eq H1_7
        apply auto
        subgoal using H1_8
          by simp
        subgoal
          using H1_9
          unfolding step_spec_conf.simps[where a = c1']
          apply -
          apply safe
          apply(erule allE[where x = p'])
          apply(erule allE[where x = p'])
          apply(erule allE[where x = pn])
          apply(erule allE[where x = pm])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op3'])
          apply(erule allE[where x = op3'])
          apply(erule allE[where x = "msg (c1'\<lparr>ops := (ops c1')(w := op3')\<rparr>)"])
          by fastforce
        done
      done
  next
    fix q :: "'op1 \<times> nat \<times> nat"
      and x :: 'd
      and op2 :: "('ip1 \<times> nat \<times> nat, 'op1 \<times> nat \<times> nat, 'd) op"
      and p :: "'ip2 \<times> nat \<times> nat"
    assume io'_def: "io' = Tau"
      and op''_def: "op'' = comp_op (simp_wire wire) (BENQ p x buf) op2 op1'"
      and wire_some: "simp_wire wire q = Some p"
      and H3: "step (Out q x) op1 op2"
    obtain w c2 where H3_1: "step_dis w (Out q x) c1 c2" and H3_2: "op2 ~d c2"
      using bisim_op_elim H3 H1_1
      by meson
    show "?P io op' c"
      using H3_1
      apply -
      apply(erule stepDisOutE)
      subgoal for q' qn qm op3'
        unfolding H1_6 io_def[symmetric] io'_def
        apply simp
        apply(cases "work_respons c1 qn = work_respons c1 qm")
        subgoal
          apply(rule exI[where x = "conf_comp wire (buf'(w:= BENQ p x (buf' w))) msg' c2 c1'"])
          apply(rule conjI)
          subgoal
            apply(rule S[where w = w])
            apply(rule SDT[where op' = "ops (conf_comp wire (buf'(w:= BENQ p x (buf' w))) msg' c2 c1') w"])
            subgoal
              unfolding conf_comp_def map_op_comp_def
              apply simp
              apply(rule step_map_op[where io = "Tau"])
              apply(rule step_Tau_comp_op_L_alt, assumption)
              subgoal
                using wire_some
                unfolding simp_wire_def simp_wire'_def
                apply auto
                apply(cases "wire q'"; simp)
                done
              apply simp
              done
            subgoal
              unfolding conf_comp_def
              apply simp
              apply auto
              apply(simp only: record_help)
              done
            done
          subgoal
            apply(rule bc'_base)
            unfolding op'_def[symmetric] map_op_comp_def op''_def
            apply(rule exI[where x = wire])
            apply(rule exI[where x = "(BENQ p x buf)"])
            apply(rule exI[where x = "(buf'(w := BENQ p x (buf' w)))"])
            apply(rule exI[where x = msg'])
            apply(rule exI[where x = op2])
            apply(rule exI[where x = op1'])
            apply(rule exI[where x = c2])
            using H3_2
            apply auto
            apply(rule exI[where x = c1'])
            apply safe
            subgoal
              using H1_2
              by auto
            subgoal
              using H1_8
              unfolding step_spec_conf.simps[where a = c1]
              apply -
              apply safe
              apply(erule allE[where x = q'])
              apply(erule allE[where x = qn])
              apply(erule allE[where x = qm])
              apply(erule allE[where x = x])
              apply(erule allE[where x = w])
              apply(erule allE[where x = op3'])
              apply(erule allE[where x = op3'])
              apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := op3')\<rparr>)"])
              by fastforce
            subgoal using H1_9
              by simp
            subgoal
              using H1_3
              unfolding bufs_eq_def
              apply -
              apply(rule allI)
              subgoal for p'
                apply(cases "p'")
                apply(erule allE[where x = p'])
                subgoal for p'' pn'' qn''
                  apply simp
                  apply safe
                  subgoal
                    unfolding BENQ_def
                    apply auto
                    done
                  subgoal
                    unfolding BENQ_def fun_upd_def if_distrib
                    apply auto
                    using wire_some
                    unfolding simp_wire_def
                    apply simp
                    apply(cases "wire q'")
                    subgoal
                      apply simp
                      done
                    subgoal for q'''
                      apply(simp only:)
                      apply simp
                      using H1_4
                      by argo
                    done
                  subgoal
                    unfolding BENQ_def fun_upd_def if_distrib
                    apply auto
                    using wire_some
                    unfolding simp_wire_def
                    apply simp
                    apply(cases "wire q'")
                    subgoal
                      apply simp
                      done
                    subgoal for q'''
                      apply(simp only:)
                      apply simp
                      using H1_4
                      by argo
                    done
                  subgoal
                    unfolding BENQ_def fun_upd_def if_distrib
                    apply auto
                    using wire_some
                    unfolding simp_wire_def
                    apply simp
                    apply(cases "wire q'")
                    subgoal
                      apply simp
                      done
                    subgoal for q'''
                      apply(simp only:)
                      apply simp
                      using H1_4
                      by argo
                    done
                  done
                done
              done
            using H1_4 H1_7
            apply auto
            done
          done
        subgoal
          apply(rule exI[where x = "conf_comp wire buf' (msg'((work_respons c1 qn):= (msg' (work_respons c1 qn))((work_respons c1 qm):= BENQ p x (msg' (work_respons c1 qn) (work_respons c1 qm))))) c2 c1'"])
          apply(rule conjI)
          subgoal
            apply(rule S[where w = w])
            using wire_some
            unfolding simp_wire_def
            apply(cases "wire q'"; simp)
            subgoal for p'
              apply(rule SDTW[where q = "Inl q'" and n = qn and m = qm and x = x and p = "Inr p'" and w' = "work_respons c1 qm" and op' = "ops (conf_comp wire buf' (msg'((work_respons c1 qn):= (msg' (work_respons c1 qn))((work_respons c1 qm):= BENQ p x (msg' (work_respons c1 qn) (work_respons c1 qm))))) c2 c1') w"])
              subgoal
                unfolding conf_comp_def map_op_comp_def
                apply simp
                apply(rule step_map_op[where io = "Out (Inl (q', qn, qm)) x"])
                subgoal
                  apply(rule step_comp_op_L_Out, assumption)
                  subgoal
                    unfolding dom_def
                    apply simp
                    unfolding simp_wire_def simp_wire'_def
                    apply auto
                    done
                  subgoal
                    apply(rule refl)
                    done
                  subgoal
                    apply(rule refl)
                    done
                  done
                apply simp
                done
              subgoal
                apply (simp add: record_help)
                apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                apply(subst conf_comp_def[symmetric])
                apply(subst conf_comp_def[symmetric])
                apply(subst conf_comp_def[symmetric])
                apply(subst conf_comp_def[symmetric])
                apply(subst conf_comp_def)
                apply(simp add: record_help)
                apply(rule conjI)
                subgoal
                  apply auto
                  apply(simp only: record_help)
                  apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                  apply simp
                  unfolding fun_upd_def if_distrib
                  apply(subst if_distribR)
                  apply(subst if_distribR)
                  apply(subst if_distribR)
                  apply(rule lambda_helper)
                  apply(rule allI)
                  subgoal for wt
                    apply(cases "wt = work_respons c1 qn"; simp)
                    subgoal
                      apply(rule lambda_helper)
                      apply(rule allI)
                      subgoal for wt'
                        unfolding conf_comp_def
                        apply(cases "wt' = work_respons c1 qm"; simp)
                        subgoal
                          unfolding fun_upd_def if_distrib BENQ_def
                          apply(subst if_distribR)
                          apply auto
                          apply(rule lambda_helper)
                          apply(rule allI)
                          subgoal for aa
                            apply(cases aa; simp)
                            subgoal for a b c
                              apply(cases a; simp)
                              using H1_7 by blast
                            done
                          done
                        subgoal
                          by presburger
                        done
                      done
                    subgoal
                      by presburger
                    done
                  done
                subgoal
                  apply auto
                  apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                  apply simp
                  apply(subst conf_comp_def[where wire = wire and buf = buf'])
                  apply simp
                  unfolding fun_upd_def if_distrib
                  apply auto
                  done
                done
              using wire_some
              unfolding conf_comp_def
             apply auto
              done
            done
            subgoal
              apply(rule bc'_base)
              unfolding op'_def[symmetric] map_op_comp_def op''_def
              apply(rule exI[where x = wire])
              apply(rule exI[where x = "(BENQ p x buf)"])
              apply(rule exI[where x = "buf'"])
              apply(rule exI[where x = "(msg'(work_respons c1 qn := (msg' (work_respons c1 qn))(work_respons c1 qm := BENQ p x (msg' (work_respons c1 qn) (work_respons c1 qm)))))"])
              apply(rule exI[where x = op2])
              apply(rule exI[where x = op1'])
              apply(rule exI[where x = c2])
              using H3_2
              apply auto
              apply(rule exI[where x = c1'])
              apply safe
              subgoal
                using H1_2
                by auto
              subgoal
                using H1_8
                unfolding step_spec_conf.simps[where a = c1]
                apply -
                apply safe
                apply(erule allE[where x = q'])
                apply(erule allE[where x = qn])
                apply(erule allE[where x = qm])
                apply(erule allE[where x = x])
                apply(erule allE[where x = w])
                apply(erule allE[where x = op3'])
                apply(erule allE[where x = op3'])
                apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := op3')\<rparr>)"])
                by fastforce
              subgoal using H1_9
                by simp
              subgoal
                using H1_3
                unfolding bufs_eq_def
                apply -
                apply(rule allI)
                subgoal for p'
                  apply(cases "p'")
                  apply(erule allE[where x = p'])
                  subgoal for p'' pn'' qn''
                    apply simp
                    apply safe
                    subgoal
                      unfolding BENQ_def
                      apply auto
                      done
                    subgoal
                      unfolding BENQ_def fun_upd_def if_distrib
                      apply auto
                      using wire_some
                      unfolding simp_wire_def
                      apply simp
                      apply(cases "wire q'")
                      subgoal
                        apply simp
                        done
                      subgoal for q'''
                        apply(simp only:)
                        apply simp
                        using H1_4
                        by argo
                      done
                    subgoal
                      unfolding BENQ_def fun_upd_def if_distrib
                      apply auto
                      using wire_some
                      unfolding simp_wire_def
                      apply simp
                      apply(cases "wire q'")
                      subgoal
                        apply simp
                        done
                      subgoal for q'''
                        apply(simp only:)
                        apply simp
                        using H1_4
                        by argo
                      done
                    subgoal
                      unfolding BENQ_def fun_upd_def if_distrib
                      apply auto
                      using wire_some
                      unfolding simp_wire_def
                      apply simp
                      apply(cases "wire q'")
                      subgoal
                        apply simp
                        done
                      subgoal for q'''
                        apply(simp only:)
                        apply simp
                        using H1_4
                        by argo
                      done
                    subgoal
                      unfolding BENQ_def fun_upd_def if_distrib
                      apply auto
                      using wire_some
                      unfolding simp_wire_def
                      apply simp
                      apply(cases "wire q'")
                      subgoal
                        apply simp
                        done
                      subgoal for q'''
                        apply(simp only:)
                        apply simp
                        using H1_4
                        by argo
                      done
                    subgoal
                      unfolding BENQ_def fun_upd_def if_distrib
                      apply auto
                      using wire_some
                      unfolding simp_wire_def
                      apply simp
                      apply(cases "wire q'")
                      subgoal
                        apply simp
                        done
                      subgoal for q'''
                        apply(simp only:)
                        apply simp
                        using H1_4
                        by argo
                      done
                    subgoal
                      unfolding BENQ_def fun_upd_def if_distrib
                      apply auto
                      using wire_some
                      unfolding simp_wire_def
                      apply simp
                      apply(cases "wire q'")
                      subgoal
                        apply simp
                        done
                      subgoal for q'''
                        apply(simp only:)
                        apply simp
                        using H1_4
                        by argo
                      done
                    done
                  done
                done
              using H1_4 H1_7
              apply auto
              done
            done
          done
        done
  next
    fix p :: "'ip2 \<times> nat \<times> nat"
      and x :: 'd
      and op2 :: "('ip2 \<times> nat \<times> nat, 'op2 \<times> nat \<times> nat, 'd) op"
    assume io'_def: "io' = Tau"
      and op''_def: "op'' = comp_op (simp_wire wire) (BTL p buf) op1 op2"
      and wire_ran: "p \<in> ran (simp_wire wire)"
      and H3: "step (Inp p x) op1' op2"
      and buf_nonempty: "buf p \<noteq> []"
      and buf_head: "BHD p buf = x"
    obtain q where q_wire: "simp_wire wire q = Some p"
      using wire_ran
      unfolding ran_def
      by fast
    obtain w c2 where H3_1: "step_dis w (Inp p x) c1' c2" and H3_2: "op2 ~d c2"
      using bisim_op_elim H3 H1_2
      by meson
    show "?P io op' c"
      using H3_1
      apply -
      apply(erule stepDisInE)
      subgoal for p' pn pm op3'
        unfolding H1_6 io_def[symmetric] io'_def
        apply simp
        apply(cases "work_respons c1 pn = work_respons c1 pm")
        subgoal
          apply(rule exI[where x = "conf_comp wire (buf'(w:= BTL p (buf' w))) msg' c1 c2"])
          apply(rule conjI)
          subgoal
            apply(rule S[where w = w])
            apply(rule SDT[where op' = "ops (conf_comp wire (buf'(w:= BTL p (buf' w))) msg' c1 c2) w"])
            subgoal
              unfolding conf_comp_def map_op_comp_def
              apply simp
              apply(rule step_map_op[where io = "Tau"])
               apply(rule step_Tau_comp_op_R_alt)
              subgoal
                using buf_head H1_3 H1_4
                unfolding bufs_eq_def
                apply -
                apply auto
                by (simp add: BHD_def)
              subgoal
                using q_wire
                unfolding simp_wire_def simp_wire'_def ran_def
                apply auto
                apply(cases q; simp)
                subgoal for q' qn qm
                  apply(cases "wire q'"; simp)
                  apply(rule exI[where x= q'])
                  apply(rule exI[where x= qn])
                  apply(rule exI[where x= qm])
                  by simp
                done
              subgoal
                using H1_3 buf_nonempty H1_4
                apply -
                unfolding bufs_eq_def
                apply auto
                done
              apply simp
              done
            unfolding conf_comp_def
            apply simp
            apply auto
            apply(simp only: record_help)
            done
          subgoal
            apply(rule bc'_base)
            unfolding op'_def[symmetric] map_op_comp_def op''_def
            apply(rule exI[where x = wire])
            apply(rule exI[where x = "(BTL p buf)"])
            apply(rule exI[where x = "(buf'(w := BTL p (buf' w)))"])
            apply(rule exI[where x = msg'])
            apply(rule exI[where x = op1])
            apply(rule exI[where x = op2])
            apply(rule exI[where x = c1])
            using H1_1
            apply auto
            apply(rule exI[where x = c2])
            apply safe
            subgoal
              using H3_2
              by auto
            subgoal using H1_8
              by simp
            subgoal
              using H1_9
              unfolding step_spec_conf.simps[where a = c1']
              apply -
              apply safe
              apply(erule allE[where x = p'])
              apply(erule allE[where x = pn])
              apply(erule allE[where x = pm])
              apply(erule allE[where x = x])
              apply(erule allE[where x = w])
              apply(erule allE[where x = op3'])
              apply(erule allE[where x = op3'])
              apply(erule allE[where x = "msg (c1'\<lparr>ops := (ops c1')(w := op3')\<rparr>)"])
              by fastforce
            subgoal
              using H1_3
              unfolding bufs_eq_def
              apply -
              apply(rule allI)
              subgoal for p''
                apply(cases "p''")
                apply(erule allE[where x = p''])
                subgoal for p''' pn''' qn'''
                  apply simp
                  apply safe
                  subgoal
                    unfolding BTL_def
                    apply auto
                    done
                  subgoal
                    unfolding BTL_def fun_upd_def if_distrib
                    apply auto
                    using q_wire
                    unfolding simp_wire_def
                    apply simp
                    apply(cases q)
                    subgoal for q1 q1n q1m
                      apply(cases "wire q1")
                      subgoal
                        apply simp
                        done
                      subgoal for q'''
                        apply(simp only:)
                        apply simp
                        using H1_4
                        by argo
                      done
                    done
                  subgoal
                    unfolding BTL_def fun_upd_def if_distrib
                    apply auto
                    done
                  subgoal
                    unfolding BTL_def fun_upd_def if_distrib
                    apply auto
                    done
                  done
                done
              done
            using H1_4 H1_7
            apply auto
            done
          done
        subgoal
          apply(rule exI[where x = "conf_comp wire buf' (msg'((work_respons c1 pn):= (msg' (work_respons c1 pn))((work_respons c1 pm):= BTL p (msg' (work_respons c1 pn) (work_respons c1 pm))))) c1 c2"])
          apply(rule conjI)
          subgoal
            apply(rule S[where w = w])
            using q_wire
            unfolding simp_wire_def
            apply -
            apply(cases q)
            subgoal for q' qn qm
              apply simp
              apply(cases "wire q'"; simp)
              apply(rule SDTR[where p = "Inr p'" and n = pn and m = pm and w = "(work_respons c1' pn)" and op' = "ops (conf_comp wire buf' (msg'((work_respons c1 pn):= (msg' (work_respons c1 pn))((work_respons c1 pm):= BTL p (msg' (work_respons c1 pn) (work_respons c1 pm))))) c1 c2) w"])
              subgoal
                unfolding conf_comp_def map_op_comp_def
                apply simp
                apply(rule step_map_op[where io = "Inp (Inr (p', pn, pm)) x"])
                subgoal
                  apply(rule step_comp_op_R_Inp, assumption)
                  subgoal
                    unfolding ran_def
                    apply simp
                    unfolding simp_wire_def simp_wire'_def
                    apply auto
                    subgoal for p'' pn' pm'
                      apply(cases "wire p''"; simp)
                      apply(cases "work_respons c1 pn' = work_respons c1 pm'"; simp)
                      done
                    done
                  subgoal
                    apply(rule refl)
                    done
                  subgoal
                    apply(rule refl)
                    done
                  done
                apply simp
                using buf_head H1_3 H1_4
                unfolding BHD_def bufs_eq_def
                apply auto
                done
              subgoal
                apply (simp add: record_help)
                apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                apply(subst conf_comp_def[symmetric])
                apply(subst conf_comp_def[symmetric])
                apply(subst conf_comp_def[symmetric])
                apply(subst conf_comp_def[symmetric])
                apply(subst conf_comp_def)
                apply(simp add: record_help)
                apply(rule conjI)
                subgoal
                  apply auto
                  apply(simp only: record_help)
                  apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                  apply simp
                  unfolding fun_upd_def if_distrib H1_4
                  apply(subst if_distribR)
                  apply(subst if_distribR)
                  apply(subst if_distribR)
                  apply(rule lambda_helper)
                  apply(rule allI)
                  subgoal for wt
                    unfolding BTL_def
                    apply(cases "wt = work_respons c1' pn"; simp)
                    subgoal
                      apply(rule lambda_helper)
                      apply(rule allI)
                      subgoal for wt'
                        unfolding conf_comp_def
                        apply(cases "wt' = work_respons c1' pm"; simp)
                        subgoal
                          apply(simp only: simp_thms if_True)
                          unfolding fun_upd_def if_distrib
                          apply(rule lambda_helper)
                          apply(rule allI)
                          subgoal for wa
                            apply(cases wa; simp)
                            subgoal for wa1 wa2 wa3
                              apply(cases wa1; simp)
                              done
                            done
                          done
                        subgoal
                          apply(simp only: simp_thms if_True if_False)
                          done
                        done
                      done
                    subgoal
                      by presburger
                    done
                  done
                subgoal
                  apply auto
                  apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                  apply simp
                  apply(subst conf_comp_def[where wire = wire and buf = buf'])
                  apply simp
                  unfolding fun_upd_def if_distrib
                  apply auto
                  done
                done
              subgoal
                using q_wire H1_7
                apply -
                apply(rule exI[where x = "Inl q'"])
              unfolding conf_comp_def
             apply auto
              done
            subgoal
              using H1_4
              by argo
            subgoal
              using H1_4
              unfolding conf_comp_def
              by auto
            subgoal
              using H1_4
              unfolding conf_comp_def
              by auto
            subgoal
              using buf_nonempty H1_3
              unfolding conf_comp_def bufs_eq_def H1_4
              apply auto
              done
            done
          done
            subgoal
              apply(rule bc'_base)
              unfolding op'_def[symmetric] map_op_comp_def op''_def
              apply(rule exI[where x = wire])
              apply(rule exI[where x = "(BTL p buf)"])
              apply(rule exI[where x = "buf'"])
              apply(rule exI[where x = "(msg'(work_respons c1 pn := (msg' (work_respons c1 pn))(work_respons c1 pm := BTL p (msg' (work_respons c1 pn) (work_respons c1 pm)))))"])
              apply(rule exI[where x = op1])
              apply(rule exI[where x = op2])
              apply(rule exI[where x = c1])
              using H1_1
              apply auto
              apply(rule exI[where x = c2])
              apply safe
              subgoal
                using H3_2
                by auto
              subgoal using H1_8
                by simp
              subgoal
                using H1_9
                unfolding step_spec_conf.simps[where a = c1']
                apply -
                apply safe
                apply(erule allE[where x = p'])
                apply(erule allE[where x = pn])
                apply(erule allE[where x = pm])
                apply(erule allE[where x = x])
                apply(erule allE[where x = w])
                apply(erule allE[where x = op3'])
                apply(erule allE[where x = op3'])
                apply(erule allE[where x = "msg (c1'\<lparr>ops := (ops c1')(w := op3')\<rparr>)"])
                by fastforce
              subgoal
                using H1_3
                unfolding bufs_eq_def
                apply -
                apply(rule allI)
                subgoal for p''
                  apply(cases "p''")
                  apply(erule allE[where x = p''])
                  subgoal for p''' pn''' qn'''
                    apply simp
                    apply safe
                    subgoal
                      unfolding BTL_def
                      apply auto
                      done
                    subgoal
                      unfolding BTL_def fun_upd_def if_distrib
                      apply auto
                      using q_wire
                      unfolding simp_wire_def
                      apply simp
                      apply(cases q; simp)
                      subgoal for q' qn' qm'
                        apply(cases "wire q'"; simp)
                        using H1_4
                        by argo
                      done
                    subgoal
                      unfolding BTL_def fun_upd_def if_distrib
                      apply auto
                      using q_wire
                      unfolding simp_wire_def
                      apply simp
                      apply(cases q)
                      subgoal for q' qn' qm'
                        apply(cases "wire q'")
                        subgoal
                          apply simp
                          done
                        subgoal for q'''
                          apply(simp only:)
                          apply simp
                          using H1_4
                          by argo
                        done
                      done
                    subgoal
                      unfolding BTL_def fun_upd_def if_distrib
                      apply auto
                      using q_wire
                      unfolding simp_wire_def
                      apply simp
                      apply(cases q)
                      subgoal for q' qn' qm'
                        apply(cases "wire q'")
                        subgoal
                          apply simp
                          done
                        subgoal for q'''
                          apply(simp only:)
                          apply simp
                          using H1_4
                          by argo
                        done
                      done
                    subgoal
                      unfolding BTL_def fun_upd_def if_distrib
                      apply auto
                      using q_wire
                      unfolding simp_wire_def
                      apply simp
                      apply(cases q)
                      subgoal for q' qn' qm'
                        apply(cases "wire q'")
                        subgoal
                          apply simp
                          done
                        subgoal for q'''
                          apply(simp only:)
                          apply simp
                          using H1_4
                          by argo
                        done
                      done
                    subgoal
                      unfolding BTL_def fun_upd_def if_distrib
                      apply auto
                      using q_wire
                      unfolding simp_wire_def
                      apply simp
                      apply(cases q)
                      subgoal for q' qn' qm'
                        apply(cases "wire q'")
                        subgoal
                          apply simp
                          done
                        subgoal for q'''
                          apply(simp only:)
                          apply simp
                          using H1_4
                          by argo
                        done
                      done
                    subgoal
                      unfolding BTL_def fun_upd_def if_distrib
                      apply auto
                      using q_wire
                      unfolding simp_wire_def
                      apply simp
                      apply(cases q)
                      subgoal for q' qn' qm'
                        apply(cases "wire q'")
                        subgoal
                          apply simp
                          done
                        subgoal for q'''
                          apply(simp only:)
                          apply simp
                          using H1_4
                          by argo
                        done
                      done
                    done
                  done
                done
              using H1_4 H1_7
              apply auto
              done
            done
          done
        done
  next
    fix p :: "'f"
      and x :: "'g"
      and op2 :: "('ip1 \<times> nat \<times> nat, 'op1 \<times> nat \<times> nat, 'd) op"
    assume io'_def: "io' = Tau"
      and op''_def: "op'' = comp_op (simp_wire wire) buf op2 op1'"
      and H3: "step Tau op1 op2"
    obtain w c2 where H3_1: "step_dis w Tau c1 c2" and H3_2: "op2 ~d c2"
      using bisim_op_elim H3 H1_1
      by meson
    show "?P io op' c"
      using H3_1
      apply -
      apply(erule stepDisTauE)
      subgoal for op3'
        unfolding H1_6 io_def[symmetric] io'_def
        apply simp
        apply(rule exI[where x = "conf_comp wire buf' msg' c2 c1'"])
        apply(rule conjI)
        apply(rule S[where w = w])
        apply(rule SDT[where op' = "ops (conf_comp wire buf' msg' c2 c1') w"])
        subgoal
          unfolding conf_comp_def map_op_comp_def
          apply simp
          apply(rule step_map_op[where io = "Tau"])
           apply auto
          done
        subgoal
          unfolding conf_comp_def
          apply auto
          apply(simp only: record_help)
          done
        subgoal
          apply(rule bc'_base)
          unfolding op'_def[symmetric] map_op_comp_def op''_def
          apply(rule exI[where x = wire])
          apply(rule exI[where x = buf])
          apply(rule exI[where x = buf'])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = op2])
          apply(rule exI[where x = op1'])
          apply(rule exI[where x = c2])
          using H3_2
          apply auto
          apply(rule exI[where x = c1'])
          using H1_2 H1_3 H1_4 work_respons_eq H1_7
          apply auto
          subgoal
            using H1_8
            unfolding step_spec_conf.simps[where a = c1]
            apply -
            apply safe
            apply(erule allE[where x = op3'])
            apply(erule allE[where x = w])
            apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := op3')\<rparr>)"])
            by fastforce
          subgoal using H1_9
            by simp
          done
        done
      subgoal for p' pn pm op3 q'
        unfolding H1_6 io_def[symmetric] io'_def
        apply simp
        apply(rule exI[where x = "conf_comp wire buf' msg' c2 c1'"])
        apply(rule conjI)
        subgoal
          apply(rule S[where w = w])
          apply(rule SDTR[where p = "Inl p'" and n = pn and m = pm and w = "work_respons c1 pn" and op' = "ops (conf_comp wire buf' msg' c2 c1') w"])
          subgoal
            unfolding conf_comp_def map_op_comp_def
            apply simp
            apply(rule step_map_op[where io = "(Inp (Inl (p', pn, pm)) (bhd (msg c1 (work_respons c1 pn) w (p', pn, pm))))"])
             apply auto
            done
          subgoal
            apply simp
            unfolding conf_comp_def
            apply auto
            apply(simp only: record_help)
            unfolding fun_upd_def if_distrib
            apply(subst if_distribR)+
            apply(rule lambda_helper)
            apply(rule allI)
            subgoal for wt
              unfolding BTL_def H1_4
              apply(cases "wt = work_respons c1' pn"; simp)
              subgoal
                apply(simp only: simp_thms if_True)
                apply(rule lambda_helper)
                apply(rule allI)
                subgoal for wt'
                  apply(cases "wt' = work_respons c1' pm"; simp)
                  subgoal
                    unfolding fun_upd_def if_distrib
                    apply(subst if_distribR)+
                    apply(simp only: if_True simp_thms)
                    apply(rule lambda_helper)
                    apply(rule allI)
                    subgoal for wa
                      apply(cases "wa"; simp)
                      subgoal for wa1 wa2 wa3
                        apply(cases wa1; simp)
                        done
                      done
                    done
                  subgoal
                    apply(simp only: if_False)
                    done
                  done
                done
              subgoal
                apply(simp only: if_False)
                done
              done
            done
          subgoal
            apply(rule exI[where x = "Inl q'"])
            unfolding conf_comp_def
            apply auto
            done
          unfolding conf_comp_def
            apply auto
          done
        subgoal
          apply(rule bc'_base)
          unfolding op'_def[symmetric] map_op_comp_def op''_def
          apply(rule exI[where x = wire])
          apply(rule exI[where x = buf])
          apply(rule exI[where x = buf'])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = op2])
          apply(rule exI[where x = op1'])
          apply(rule exI[where x = c2])
          using H3_2
          apply auto
          apply(rule exI[where x = c1'])
          using H1_2 H1_3 H1_4 work_respons_eq H1_7 H1_8 H1_9
          apply auto
          subgoal
            unfolding step_spec_conf.simps[where a = c1]
            apply -
            apply safe
            apply(erule allE[where x = p'])
            apply(erule allE[where x = pn])
            apply(erule allE[where x = pm])
            apply(erule allE[where x = "(bhd (msg c1 (work_respons c1' pn) (work_respons c1' pm) (p', pn, pm)))"])
            apply(erule allE[where x = "(work_respons c1' pm)"])
            apply(erule allE[where x = op3])
            apply(erule allE[where x = op3])
            apply(erule allE[where x = "(msg c1)(work_respons c1' pn := (msg c1 (work_respons c1' pn))(work_respons c1' pm := BTL (p', pn, pm) (msg c1 (work_respons c1' pn) (work_respons c1' pm))))"])
            apply(erule impE, assumption)
            apply(erule conjE)
            by blast
          done
        done
      subgoal for q' qn qm x op3 p'
        unfolding H1_6 io_def[symmetric] io'_def
        apply simp
        apply(rule exI[where x = "conf_comp wire buf' msg' c2 c1'"])
        apply(rule conjI)
        subgoal
          apply(rule S[where w = w])
          apply(rule SDTW[where w' = "(work_respons c1 qm)" and q = "Inl q'" and n = qn and m = qm and x = x and p = "Inl p'" and op' = "ops (conf_comp wire buf' msg' c2 c1') w"])
          subgoal
            unfolding conf_comp_def map_op_comp_def
            apply simp
            apply(rule step_map_op[where io = "(Out (Inl (q', qn, qm)) x)"])
            subgoal
              using H1_7
              unfolding simp_wire_def
              apply auto
              unfolding simp_wire'_def
              apply auto
              apply(cases " wire q'"; simp)
              done
            subgoal
              by simp
            done
          subgoal
            apply (simp add: record_help)
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[symmetric])
            apply(subst conf_comp_def[symmetric])
            apply(subst conf_comp_def[symmetric])
            apply(subst conf_comp_def[symmetric])
            apply(subst conf_comp_def)
            apply(simp add: record_help)
            apply(rule conjI)
            subgoal
              apply auto
              apply(simp only: record_help)
              apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
              apply simp
              unfolding fun_upd_def if_distrib H1_4
              apply(subst if_distribR)
              apply(subst if_distribR)
              apply(subst if_distribR)
              apply(rule lambda_helper)
              apply(rule allI)
              subgoal for wt
                apply(cases "wt = work_respons c1' qn"; simp)
                subgoal
                  apply(rule lambda_helper)
                  apply(rule allI)
                  subgoal for wt'
                    unfolding conf_comp_def BENQ_def
                    apply(simp only: simp_thms if_True)
                    apply(cases "wt' = work_respons c1' qm"; simp)
                    subgoal
                      apply(rule lambda_helper)
                      apply(rule allI)
                      subgoal for wa
                        apply(cases wa; simp)
                        subgoal for wa1 wa2 wa3
                          apply(cases wa1; simp)
                          done
                        done
                      done
                    subgoal
                      by presburger
                    done
                  done
                subgoal
                  by presburger
                done
              done
          subgoal
          unfolding conf_comp_def
          apply auto
          done
        done
        subgoal
          unfolding conf_comp_def
          apply auto
          done
        subgoal
          unfolding conf_comp_def
          apply auto
          done
        subgoal
          unfolding conf_comp_def
          apply auto
          done
        subgoal
          unfolding conf_comp_def
          by simp
        done
        subgoal
          apply(rule bc'_base)
          unfolding op'_def[symmetric] map_op_comp_def op''_def
          apply(rule exI[where x = wire])
          apply(rule exI[where x = buf])
          apply(rule exI[where x = buf'])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = op2])
          apply(rule exI[where x = op1'])
          apply(rule exI[where x = c2])
          using H3_2
          apply auto
          apply(rule exI[where x = c1'])
          using H1_2 H1_3 H1_4 work_respons_eq H1_7 H1_8 H1_9
          apply auto
          subgoal
            unfolding step_spec_conf.simps[where a = c1]
            apply -
            apply safe
            apply(erule allE[where x = q'])
            apply(erule allE[where x = qn])
            apply(erule allE[where x = qm])
            apply(erule allE[where x = x])
            apply(erule allE[where x = "(work_respons c1' qn)"])
            apply(erule allE[where x = op3])
            apply(erule allE[where x = op3])
            apply(erule allE[where x = "(msg c1)(work_respons c1' qn := (msg c1 (work_respons c1' qn))(work_respons c1' qm := BENQ (p', qn, qm) x (msg c1 (work_respons c1' qn) (work_respons c1' qm))))"])
            apply(erule impE, assumption)
            apply(erule conjE)
            by simp
          done
        done
      done
  next
    fix p :: "'h"
      and x :: "'i"
      and op2 :: "('ip2 \<times> nat \<times> nat, 'op2 \<times> nat \<times> nat, 'd) op"
    assume io'_def: "io' = Tau"
      and op''_def: "op'' = comp_op (simp_wire wire) buf op1 op2"
      and H3: "step Tau op1' op2"
    obtain w c2 where H3_1: "step_dis w Tau c1' c2" and H3_2: "op2 ~d c2"
      using bisim_op_elim H3 H1_2
      by meson
    show "?P io op' c"
      using H3_1
      apply -
      apply(erule stepDisTauE)
      subgoal for op3'
        unfolding H1_6 io_def[symmetric] io'_def
        apply simp
        apply(rule exI[where x = "conf_comp wire buf' msg' c1 c2"])
        apply(rule conjI)
        apply(rule S[where w = w])
        apply(rule SDT[where op' = "ops (conf_comp wire buf' msg' c1 c2) w"])
        subgoal
          unfolding conf_comp_def map_op_comp_def
          apply simp
          apply(rule step_map_op[where io = "Tau"])
           apply auto
          done
        subgoal
          unfolding conf_comp_def
          apply auto
          apply(simp only: record_help)
          done
        subgoal
          apply(rule bc'_base)
          unfolding op'_def[symmetric] map_op_comp_def op''_def
          apply(rule exI[where x = wire])
          apply(rule exI[where x = buf])
          apply(rule exI[where x = buf'])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = op1])
          apply(rule exI[where x = op2])
          apply(rule exI[where x = c1])
          using H1_1
          apply auto
          apply(rule exI[where x = c2])
          using H3_2 H1_3 H1_4 work_respons_eq H1_7
          apply auto
          subgoal using H1_8
            by simp
          subgoal
            using H1_9
            unfolding step_spec_conf.simps[where a = c1']
            apply -
            apply safe
            apply(erule allE[where x = op3'])
            apply(erule allE[where x = w])
            apply(erule allE[where x = "msg (c1'\<lparr>ops := (ops c1')(w := op3')\<rparr>)"])
            by fastforce
          done
        done
      subgoal for p' pn pm op3 q'
        unfolding H1_6 io_def[symmetric] io'_def
        apply simp
        apply(rule exI[where x = "conf_comp wire buf' msg' c1 c2"])
        apply(rule conjI)
        subgoal
          apply(rule S[where w = w])
          apply(rule SDTR[where p = "Inr p'" and n = pn and m = pm and w = "work_respons c1 pn" and op' = "ops (conf_comp wire buf' msg' c1 c2) w"])
          subgoal
            unfolding conf_comp_def map_op_comp_def
            apply simp
            apply(rule conjI)
            subgoal
              using H1_4
              apply -
              apply(rule impI)
              apply(rule step_map_op[where io = "(Inp (Inr (p', pn, pm)) (bhd (msg c1' (work_respons c1 pn) w (p', pn, pm))))"])
               apply auto
              unfolding ran_def
              apply auto
              using H1_7
              unfolding simp_wire'_def
              apply auto
              subgoal for q'' qn'' qm'' b
                apply(cases "wire qn''"; simp)
                subgoal for a
                  apply(cases "work_respons c1' qm'' = work_respons c1' b"; simp)
                  done
                done
              done
            apply auto
            done
          subgoal
            apply (simp add: record_help)
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[symmetric])
            apply(subst conf_comp_def[symmetric])
            apply(subst conf_comp_def[symmetric])
            apply(subst conf_comp_def[symmetric])
            apply(subst conf_comp_def)
            apply(simp add: record_help)
            apply(rule conjI)
            subgoal
              apply auto
              apply(simp only: record_help)
              apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
              apply simp
              unfolding fun_upd_def if_distrib
              apply(subst if_distribR)
              apply(subst if_distribR)
              apply(subst if_distribR)
              apply(rule lambda_helper)
              apply(rule allI)
              subgoal for wt
                unfolding H1_4
                apply(cases "wt = work_respons c1' pn"; simp)
                subgoal
                  apply(simp only: if_True simp_thms)
                  apply(rule lambda_helper)
                  apply(rule allI)
                  subgoal for wt'
                    unfolding conf_comp_def BTL_def
                    apply(cases "wt' = work_respons c1' pm"; simp)
                    subgoal
                      apply(simp only: simp_thms if_True)
                      apply auto
                      apply(rule lambda_helper)
                      apply(rule allI)
                      subgoal for qa wa
                        apply(cases wa)
                        subgoal for wa1 wa2 wa3
                          apply safe
                          apply(cases wa1; simp)
                          apply auto
                          done
                        done
                      done
                    subgoal
                      apply(simp only: if_False)
                      done
                    done
                  done
                subgoal
                  apply(simp only: if_False)
                  done
                done
              done
                subgoal
                  apply auto
                  apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                  apply simp
                  apply(subst conf_comp_def[where wire = wire and buf = buf'])
                  apply simp
                  unfolding fun_upd_def if_distrib
                  apply auto
                  done
                done
            subgoal
              apply(rule exI[where x = "Inr q'"])
              unfolding conf_comp_def
              apply auto
              done
            using H1_4
            unfolding conf_comp_def
              apply auto
            done
        subgoal
          apply(rule bc'_base)
          unfolding op'_def[symmetric] map_op_comp_def op''_def
          apply(rule exI[where x = wire])
          apply(rule exI[where x = buf])
          apply(rule exI[where x = buf'])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = op1])
          apply(rule exI[where x = op2])
          apply(rule exI[where x = c1])
          using H1_1
          apply auto
          apply(rule exI[where x = c2])
          using H3_2 H1_3 H1_4 work_respons_eq H1_7
          apply auto
          subgoal
            using H1_8
            by simp
          subgoal 
            using H1_9
            unfolding step_spec_conf.simps[where a = c1']
            by blast
          done
        done
      subgoal for q' qn qm x op3 p'
        unfolding H1_6 io_def[symmetric] io'_def
        apply simp
        apply(rule exI[where x = "conf_comp wire buf' msg' c1 c2"])
        apply(rule conjI)
        subgoal
          apply(rule S[where w = w])
          apply(rule SDTW[where w' = "(work_respons c1 qm)" and q = "Inr q'" and n = qn and m = qm and x = x and p = "Inr p'" and op' = "ops (conf_comp wire buf' msg' c1 c2) w"])
          subgoal
            unfolding conf_comp_def map_op_comp_def
            apply simp
            apply(rule step_map_op[where io = "(Out (Inr (q', qn, qm)) x)"])
            subgoal
              using H1_7
              unfolding simp_wire_def
              apply auto
            done
          subgoal
            apply auto
            done
          done
        subgoal
            apply (simp add: record_help)
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
            apply(subst conf_comp_def[symmetric])
            apply(subst conf_comp_def[symmetric])
            apply(subst conf_comp_def[symmetric])
            apply(subst conf_comp_def[symmetric])
            apply(subst conf_comp_def)
            apply(simp add: record_help)
            apply(rule conjI)
            subgoal
              apply(simp only: record_help)
              unfolding fun_upd_def if_distrib H1_4 conf_comp_def
              apply(subst if_distribR)+
              apply(rule lambda_helper)
              apply(rule allI)
              subgoal for wt
                apply(cases "wt = w"; simp)
                subgoal
                  unfolding BENQ_def
                  apply(rule lambda_helper)
                  apply(rule allI)
                  subgoal for wt'
                    apply(cases "wt' = work_respons c1' qm"; simp)
                    subgoal
                      apply(simp only: simp_thms if_True)
                      apply auto
                      apply(rule lambda_helper)
                      apply(rule allI)
                      subgoal for q'' wa
                        apply(cases wa; simp)
                        subgoal for wa1 wa2 wa3
                          apply(cases wa1; simp)
                          apply auto
                          done
                        done
                      done
                    subgoal
                      by presburger
                    done
                  done
                subgoal
                  by presburger
                done
              done
                subgoal
                  apply auto
                  apply(subst conf_comp_def[where wire = wire and buf = buf' and msg' = msg'  and c = c1 and c' = c1'])
                  apply simp
                  apply(subst conf_comp_def[where wire = wire and buf = buf'])
                  apply simp
                  unfolding fun_upd_def if_distrib
                  apply auto
                  done
                done
            subgoal
              unfolding conf_comp_def
              apply auto
              done
            using H1_4
            unfolding conf_comp_def
              apply auto
            done
        subgoal
          apply(rule bc'_base)
          unfolding op'_def[symmetric] map_op_comp_def op''_def
          apply(rule exI[where x = wire])
          apply(rule exI[where x = buf])
          apply(rule exI[where x = buf'])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = op1])
          apply(rule exI[where x = op2])
          apply(rule exI[where x = c1])
          using H1_1
          apply auto
          apply(rule exI[where x = c2])
          using H3_2 H1_3 H1_4 work_respons_eq H1_7
          apply auto
          subgoal
            using H1_8
            by simp
          subgoal
            using H1_9
            unfolding step_spec_conf.simps[where a = c1']
            by blast
          done
        done
      done
  qed
next
  fix op :: "(('ip1 + 'ip2) \<times> nat \<times> nat, ('op1 + 'op2) \<times> nat \<times> nat, 'd) op"
    and c :: "('w, 'ip1 + 'ip2, 'op1 + 'op2, 'd) conf"
    and io :: "(('ip1 + 'ip2) \<times> nat \<times> nat, ('op1 + 'op2) \<times> nat \<times> nat, 'd) IO"
    and c' :: "('w, 'ip1 + 'ip2, 'op1 + 'op2, 'd) conf"
  assume H1: "\<exists>wire buf buf' msg' opa op' ca c'. opa ~d ca \<and> op' ~d c' \<and> step_spec_conf ca \<and> step_spec_conf c' \<and> bufs_eq buf buf' msg' (work_respons c') \<and> work_respons ca = work_respons c' \<and> op = map_op_comp (comp_op (simp_wire wire) buf opa op') \<and> c = conf_comp wire buf' msg' ca c' \<and> (\<forall>p q. wire q = Some p \<longrightarrow> (used_wire ca q = None \<and> (\<forall>q'. used_wire c' q' \<noteq> Some p)))"
    and H2: "step_dis' io c c'"
  let ?Q = "\<exists>op'. step io op op' \<and>
             bisim_dis_cong
              (\<lambda>total_op total_c.
                  \<exists>wire buf buf' msg' op op' c c'.
                     op ~d c \<and>
                     op' ~d c' \<and> step_spec_conf c \<and> step_spec_conf c' \<and>
                     bufs_eq buf buf' msg' (work_respons c') \<and>
                     work_respons c = work_respons c' \<and>
                     total_op = map_op_comp (comp_op (simp_wire wire) buf op op') \<and> total_c = conf_comp wire buf' msg' c c' \<and> (\<forall>p q. wire q = Some p \<longrightarrow> used_wire c q = None \<and> (\<forall>q'. used_wire c' q' \<noteq> Some p)))
              op' c'"
  obtain wire buf buf' msg' op1 op1' c1 c1' where H1_1: "op1 ~d c1" and H1_2: "op1' ~d c1'" and H1_3: "bufs_eq buf buf' msg' (work_respons c1')" and H1_4: "work_respons c1 = work_respons c1'" and H1_5: "op = map_op_comp (comp_op (simp_wire wire) buf op1 op1')" and H1_6: "c = conf_comp wire buf' msg' c1 c1'"
    and H1_7: "(\<forall>p q. wire q = Some p \<longrightarrow> (used_wire c1 q = None \<and> (\<forall>q'. used_wire c1' q' \<noteq> Some p)))" and H1_8: "step_spec_conf c1" and H1_9: "step_spec_conf c1'"
    using H1
    by blast
  obtain w where H2': "step_dis w io c c'"
    using step_dis'.cases H2
    by metis
  show "?Q"
  proof (cases io)
    fix p :: "('ip1 + 'ip2) \<times> nat \<times> nat"
      and x :: 'd
    assume io_def: "io = Inp p x"
    obtain p' pn pm where p_def: "p=(p',pn,pm)"
      by (meson prod_cases3)
    obtain op' where c'_def: "c' = (conf_comp wire buf' msg' c1 c1')\<lparr>ops := (ops c)(w := op')\<rparr>" and Step: "step (Inp (p', pn, pm) x) (ops (conf_comp wire buf' msg' c1 c1') w) op'" and no_wire: "\<forall>q. used_wire c q \<noteq> Some p'" and w_def: "w = work_respons (conf_comp wire buf' msg' c1 c1') pm"
      using p_def io_def H2' H1_6
      by fast
    have w_def': "w = work_respons c1 pm"
      using w_def
      unfolding conf_comp_def
      by simp
    have Step': "step (Inp (p', pn, pm) x)
     (map_op (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y)))
       (comp_op (simp_wire' wire (work_respons c1)) (buf' w) (ops c1 w) (ops c1' w))) op'"
      using Step
      unfolding conf_comp_def map_op_comp_def
      by simp
    obtain io' op'' where Step'': "step io' (comp_op (simp_wire' wire (work_respons c1)) (buf' w) (ops c1 w) (ops c1' w)) op''" and 
       io'_def: "map_IO (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) id io' = (Inp (p', pn, pm) x)" and 
       op'_def: "map_op (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) op'' = op'"
      using Step' step_map_op_inv
      by meson
    consider "\<exists> p''. p' = Inl p''" | "\<exists> p''. p' = Inr p''"
      by (meson old.sum.exhaust)
    then show ?Q
    proof cases
      case 1
      obtain p'' where p'_def: "p' = Inl p''"
        using 1
        by auto
      have io'_def': "io' = (Inp (Inl (p'', pn, pm)) x)"
        using io'_def p'_def
        apply(cases io'; simp)
        subgoal for p'''
          apply(cases "p'''"; simp)
           apply auto
          done
        done
      obtain c2_w where op''_def: "op'' = comp_op (simp_wire' wire (work_respons c1)) (buf' w) c2_w (ops c1' w)" and Step1: "step (Inp (p'', pn, pm) x) (ops c1 w) c2_w"
        using Step'' io'_def' step_comp_op_cases
        by force
      have Step1': "step_dis' (Inp (p'', pn, pm) x) c1 (c1\<lparr>ops := (ops c1)(w := c2_w)\<rparr>)"
        apply(rule S[where w = w])
        using Step1
        apply -
        apply(drule SDR, rule refl)
        subgoal
          using no_wire
          unfolding H1_6 conf_comp_def p'_def
          apply auto
          subgoal for q1
            apply(erule allE[where x = "Inl q1"])
            apply auto
            done
          done
        subgoal
          using w_def
          unfolding conf_comp_def
          apply auto
          done
        apply auto
        done
      obtain op2 where Step2: "step (Inp (p'', pn, pm) x) op1 op2" and H3_2: "op2 ~d (c1\<lparr>ops := (ops c1)(w := c2_w)\<rparr>)"
        using bisim_c_elim Step1' H1_1
        by meson
      show ?Q
        unfolding H1_5
        apply(rule exI[where x = "(map_op_comp (comp_op (simp_wire wire) buf op2 op1'))"])
        unfolding map_op_comp_def io_def p_def p'_def
        apply(rule conjI)
        subgoal
          apply(rule step_map_op[where io = "Inp (Inl (p'', pn, pm)) x"])
          using Step2
           apply auto
          done
        subgoal
          apply(rule bc'_base)
          apply(rule exI[where x = wire])
          apply(rule exI[where x = buf])
          apply(rule exI[where x = buf'])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = op2])
          apply(rule exI[where x = op1'])
          apply(rule exI[where x = "(c1\<lparr>ops := (ops c1)(w := c2_w)\<rparr>)"])
          apply(rule exI[where x = c1'])
          using H3_2 H1_2 H1_3 H1_4 H1_7
          unfolding c'_def
          apply auto
          unfolding conf_comp_def H1_6
            apply auto
          subgoal
            using H1_8 Step1
            unfolding step_spec_conf.simps[where a = c1]
            apply -
            apply safe
            apply(erule allE[where x = p''])
            apply(erule allE[where x = pn])
            apply(erule allE[where x = pm])
            apply(erule allE[where x = x])
            apply(erule allE[where x = w])
            apply(erule allE[where x = c2_w])
            apply(erule allE[where x = c2_w])
            apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := c2_w)\<rparr>)"])
            by auto
          subgoal
            using H1_9
            by simp
          subgoal
            apply(simp only: record_help)
            done
          subgoal
            unfolding op'_def[symmetric] op''_def H1_4 map_op_comp_def
            unfolding fun_upd_def if_distrib
            apply(subst if_distribR)
            unfolding if_distrib
            by auto
          done
        done
    next
      case 2
      obtain p'' where p'_def: "p' = Inr p''"
        using 2
        by auto
      have io'_def': "io' = (Inp (Inr (p'', pn, pm)) x)"
        using io'_def p'_def
        apply(cases io'; simp)
        subgoal for p'''
          apply(cases "p'''"; simp)
           apply auto
          done
        done
      obtain c2_w where op''_def: "op'' = comp_op (simp_wire' wire (work_respons c1)) (buf' w)(ops c1 w) c2_w" and Step1: "step (Inp (p'', pn, pm) x) (ops c1' w) c2_w"
        using Step'' io'_def' step_comp_op_cases
        by force
      have Step1': "step_dis' (Inp (p'', pn, pm) x) c1' (c1'\<lparr>ops := (ops c1')(w := c2_w)\<rparr>)"
        apply(rule S[where w = w])
        using Step1
        apply -
        apply(drule SDR, rule refl)
        subgoal
          using no_wire
          unfolding H1_6 conf_comp_def p'_def
          apply auto
          subgoal for q1
            apply(erule allE[where x = "Inr q1"])
            apply auto
            done
          done
        subgoal
          using w_def H1_4
          unfolding conf_comp_def
          apply auto
          done
        apply auto
        done
      obtain op2 where Step2: "step (Inp (p'', pn, pm) x) op1' op2" and H3_2: "op2 ~d (c1'\<lparr>ops := (ops c1')(w := c2_w)\<rparr>)"
        using bisim_c_elim Step1' H1_2
        by meson
      have no_wire': "\<forall> q''. wire q'' \<noteq> Some p''"
        using no_wire H1_7
        unfolding p'_def H1_6
        apply -
        apply(rule allI)
        subgoal for q''
          apply(erule allE[where x = "Inl q''"])
          unfolding conf_comp_def
          apply simp
          apply auto
          done
        done
      show ?Q
        unfolding H1_5
        apply(rule exI[where x = "(map_op_comp (comp_op (simp_wire wire) buf op1 op2))"])
        unfolding map_op_comp_def io_def p_def p'_def
        apply(rule conjI)
        subgoal
          apply(rule step_map_op[where io = "Inp (Inr (p'', pn, pm)) x"])
          subgoal
            apply(rule step_comp_op_R_Inp)
            subgoal
              apply(rule Step2)
              done
            subgoal
              unfolding ran_def simp_wire_def
              apply simp
            using Step2 no_wire no_wire'
            apply auto
            subgoal for p''' pn''' pm'''
              apply(cases "wire p'''"; simp)
              done
            done
           apply auto
          done
        apply auto
        done
      subgoal
        apply(rule bc'_base)
        apply(rule exI[where x = wire])
        apply(rule exI[where x = buf])
        apply(rule exI[where x = buf'])
        apply(rule exI[where x = msg'])
        apply(rule exI[where x = op1])
        apply(rule exI[where x = op2])
        apply(rule exI[where x = "c1"])
        apply(rule exI[where x = "(c1'\<lparr>ops := (ops c1')(w := c2_w)\<rparr>)"])
        using H3_2 H1_1 H1_3 H1_4 H1_7
        unfolding c'_def
        apply auto
        unfolding conf_comp_def H1_6
          apply auto
        subgoal
          using H1_8
          by simp
        subgoal
            using H1_9 Step1
            unfolding step_spec_conf.simps[where a = c1']
            apply -
            apply safe
            apply(erule allE[where x = p''])
            apply(erule allE[where x = p''])
            apply(erule allE[where x = pn])
            apply(erule allE[where x = pm])
            apply(erule allE[where x = x])
            apply(erule allE[where x = w])
            apply(erule allE[where x = c2_w])
            apply(erule allE[where x = c2_w])
            apply(erule allE[where x = "msg (c1'\<lparr>ops := (ops c1')(w := c2_w)\<rparr>)"])
            by auto
        subgoal
          apply(simp only: record_help)
          done
        subgoal
          unfolding fun_upd_def if_distrib
          unfolding op'_def[symmetric] op''_def map_op_comp_def H1_4
          by fastforce
        done
      done
  qed
  next
    fix q :: "('op1 + 'op2) \<times> nat \<times> nat"
      and x :: 'd
    assume io_def: "io = Out q x"
    obtain q' qn qm op' where q_def: "q = (q', qn, qm)" and c'_def: "c' = conf_comp wire buf' msg' c1 c1'\<lparr>ops := (ops (conf_comp wire buf' msg' c1 c1'))(w := op')\<rparr>" and
      Step: "step (Out (q', qn, qm) x) (ops (conf_comp wire buf' msg' c1 c1') w) op'" and no_wire: "used_wire (conf_comp wire buf' msg' c1 c1') q' = None" and w_def: "w = work_respons (conf_comp wire buf' msg' c1 c1') qn"
      using io_def H1_6 H2'
      by blast
    have w_def': "work_respons c1 qn = w"
      using w_def
      unfolding conf_comp_def
      by simp
    have Step': "step (Out (q', qn, qm) x) (map_op (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (comp_op (simp_wire' wire (work_respons c1)) (buf' w) (ops c1 w) (ops c1' w))) op'"
      using Step
      unfolding conf_comp_def map_op_comp_def
      by simp
    obtain io' op'' where Step'': "step io' (comp_op (simp_wire' wire (work_respons c1)) (buf' w) (ops c1 w) (ops c1' w)) op''" and
       io'_def: "map_IO (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) id io' = Out (q', qn, qm) x" and
       op'_def: "op' = map_op (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) op''"
      using Step' step_map_op_inv
      by blast
    consider "\<exists> q''. q' = Inl q''" | "\<exists> q''. q' = Inr q''"
      by (meson old.sum.exhaust)
    then show ?Q
    proof cases
      case 1
      obtain q'' where q'_def: "q' = Inl q''"
        using 1
        by auto
      have io'_def': "io' = (Out (Inl (q'', qn, qm)) x)"
        using io'_def q'_def
        apply(cases io'; simp)
        subgoal for p'''
          apply(cases "p'''"; simp)
           apply auto
          done
        done
      obtain c2_w where op''_def: "op'' = comp_op (simp_wire' wire (work_respons c1)) (buf' w) c2_w (ops c1' w)" and Step1: "step (Out (q'', qn, qm) x) (ops c1 w) c2_w"
        using Step'' io'_def' step_comp_op_cases
        by force
      have Step1': "step_dis' (Out (q'', qn, qm) x) c1 (c1\<lparr>ops := (ops c1)(w := c2_w)\<rparr>)"
        apply(rule S[where w = w])
        using Step1
        apply -
        apply(drule SDW, rule refl)
        subgoal
          using no_wire
          unfolding H1_6 conf_comp_def q'_def
          apply auto
          apply(cases "used_wire c1 q''"; simp)
          done
        subgoal
          using w_def
          unfolding conf_comp_def
          apply auto
          done
        apply auto
        done
      obtain op2 where Step2: "step (Out (q'', qn, qm) x) op1 op2" and H3_2: "op2 ~d (c1\<lparr>ops := (ops c1)(w := c2_w)\<rparr>)"
        using bisim_c_elim Step1' H1_1
        by meson
      show ?Q
        unfolding H1_5
        apply(rule exI[where x = "(map_op_comp (comp_op (simp_wire wire) buf op2 op1'))"])
        unfolding map_op_comp_def io_def q_def q'_def
        apply(rule conjI)
        subgoal
          apply(rule step_map_op[where io = "Out (Inl (q'', qn, qm)) x"])
          using Step2 no_wire
           apply auto
          subgoal for q1 q1n q1m
            unfolding simp_wire_def conf_comp_def q'_def
            apply simp
            apply(cases "wire q''"; simp)
            apply(cases "used_wire c1 q''"; simp)
            done
          done
        subgoal
          apply(rule bc'_base)
          apply(rule exI[where x = wire])
          apply(rule exI[where x = buf])
          apply(rule exI[where x = buf'])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = op2])
          apply(rule exI[where x = op1'])
          apply(rule exI[where x = "(c1\<lparr>ops := (ops c1)(w := c2_w)\<rparr>)"])
          apply(rule exI[where x = c1'])
          using H3_2 H1_2 H1_3 H1_4 H1_7
          unfolding c'_def
          apply auto
          unfolding conf_comp_def H1_6
            apply auto
          subgoal
            using H1_8 Step1
            unfolding step_spec_conf.simps[where a = c1]
            apply -
            apply safe
            apply(erule allE[where x = q''])
            apply(erule allE[where x = qn])
            apply(erule allE[where x = qm])
            apply(erule allE[where x = x])
            apply(erule allE[where x = w])
            apply(erule allE[where x = c2_w])
            apply(erule allE[where x = c2_w])
            apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := c2_w)\<rparr>)"])
            by auto
          subgoal
            using H1_9
            by simp
          subgoal
            apply(simp only: record_help)
            done
          subgoal
            unfolding op'_def op''_def H1_4 map_op_comp_def
            unfolding fun_upd_def if_distrib
            apply(subst if_distribR)
            unfolding if_distrib
            by auto
          done
        done
    next
      case 2
      obtain q'' where q'_def: "q' = Inr q''"
        using 2
        by auto
      have io'_def': "io' = (Out (Inr (q'', qn, qm)) x)"
        using io'_def q'_def
        apply(cases io'; simp)
        subgoal for q'''
          apply(cases "q'''"; simp)
           apply auto
          done
        done
      obtain c2_w where op''_def: "op'' = comp_op (simp_wire' wire (work_respons c1)) (buf' w)(ops c1 w) c2_w" and Step1: "step (Out (q'', qn, qm) x) (ops c1' w) c2_w"
        using Step'' io'_def' step_comp_op_cases
        by force
      have Step1': "step_dis' (Out (q'', qn, qm) x) c1' (c1'\<lparr>ops := (ops c1')(w := c2_w)\<rparr>)"
        apply(rule S[where w = w])
        using Step1
        apply -
        apply(drule SDW, rule refl)
        subgoal
          using no_wire
          unfolding H1_6 conf_comp_def q'_def
          apply auto
          apply(cases "used_wire c1' q''"; simp)
          done
        subgoal
          using w_def H1_4
          unfolding conf_comp_def
          apply auto
          done
        apply auto
        done
      obtain op2 where Step2: "step (Out (q'', qn, qm) x) op1' op2" and H3_2: "op2 ~d (c1'\<lparr>ops := (ops c1')(w := c2_w)\<rparr>)"
        using bisim_c_elim Step1' H1_2
        by meson
      show ?Q
        unfolding H1_5
        apply(rule exI[where x = "(map_op_comp (comp_op (simp_wire wire) buf op1 op2))"])
        unfolding map_op_comp_def io_def q_def q'_def
        apply(rule conjI)
        subgoal
          apply(rule step_map_op[where io = "Out (Inr (q'', qn, qm)) x"])
          subgoal
            apply(rule step_comp_op_R_Out)
            subgoal
              apply(rule Step2)
              done
            subgoal
              unfolding ran_def simp_wire_def
              apply simp
              done
            apply auto
            done
           apply auto
          done
        apply auto
      subgoal
        apply(rule bc'_base)
        apply(rule exI[where x = wire])
        apply(rule exI[where x = buf])
        apply(rule exI[where x = buf'])
        apply(rule exI[where x = msg'])
        apply(rule exI[where x = op1])
        apply(rule exI[where x = op2])
        apply(rule exI[where x = "c1"])
        using H1_1
        apply(rule conjI)
        apply(rule exI[where x = "(c1'\<lparr>ops := (ops c1')(w := c2_w)\<rparr>)"])
        using H3_2 H1_1 H1_3 H1_4 H1_7
        unfolding c'_def
        apply auto
        unfolding conf_comp_def H1_6
          apply auto
        subgoal
          using H1_8
          by simp
        subgoal
          using H1_9 Step1
          unfolding step_spec_conf.simps[where a = c1']
          apply -
          apply safe
          apply(erule allE[where x = q''])
          apply(erule allE[where x = qn])
          apply(erule allE[where x = qm])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = c2_w])
          apply(erule allE[where x = c2_w])
          apply(erule allE[where x = "msg (c1'\<lparr>ops := (ops c1')(w := c2_w)\<rparr>)"])
          by auto
        subgoal
          apply(simp only: record_help)
          done
        subgoal
          unfolding fun_upd_def if_distrib
          unfolding op'_def op''_def map_op_comp_def H1_4
          by fastforce
        done
      done
  qed
  next
    assume io_def: "io = Tau"
    consider "\<exists>op'. c' = c\<lparr>ops := (ops c)(w := op')\<rparr> \<and> step Tau (ops c w) op'" |
      "\<exists>p n m op' q. c' = c\<lparr>ops := (ops c)(w := op'), msg := (msg c)(work_respons c n := (msg c (work_respons c n))(w := BTL (p, n, m) (msg c (work_respons c n) w)))\<rparr> \<and>
        step (Inp (p, n, m) (bhd (msg c (work_respons c n) w (p, n, m)))) (ops c w) op' \<and> w \<noteq> work_respons c n \<and> work_respons c m = w \<and> used_wire c q = Some p \<and> (msg c (work_respons c n) w (p,(n,m))) \<noteq> []" |
      "\<exists>q n m x op' p. c' = c\<lparr>ops := (ops c)(w := op'), msg := (msg c)(w := (msg c w)(work_respons c m := BENQ (p, n, m) x (msg c w (work_respons c m))))\<rparr> \<and>
        step (Out (q, n, m) x) (ops c w) op' \<and> used_wire c q = Some p \<and> work_respons c m \<noteq> w \<and> work_respons c n = w"
      using H2' stepDisTauE
      unfolding H1_6 io_def
      by blast
    then show ?Q
    proof (cases, goal_cases Tau_Tau Tau_Inp Tau_Out)
      case Tau_Tau
      then obtain op' where c'_def: "c' = c\<lparr>ops := (ops c)(w := op')\<rparr>" and Step: "step Tau (ops c w) op'"
        by blast
      obtain io' op'' where Step': "step io' (comp_op (simp_wire' wire (work_respons c1)) (buf' w) (ops c1 w) (ops c1' w)) op''" and
       io'_def: "map_IO (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) id io' = Tau" and
       op'_def: "op' = map_op (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) op''"
        using Step step_map_op_inv
        unfolding H1_6 conf_comp_def map_op_comp_def
        by force
      have io'_def': "io' = Tau"
        using io'_def
        by simp
      consider "(\<exists>a aa b x op1' ab ac ba. op'' = comp_op (simp_wire' wire (work_respons c1)) (BENQ (ab, ac, ba) x (buf' w)) op1' (ops c1' w) \<and> simp_wire' wire (work_respons c1) (a, aa, b) = Some (ab, ac, ba) \<and> step (Out (a, aa, b) x) (ops c1 w) op1')" |
                "(\<exists>a aa b op2'. op'' = comp_op (simp_wire' wire (work_respons c1)) (BTL (a, aa, b) (buf' w)) (ops c1 w) op2' \<and> (a, aa, b) \<in> ran (simp_wire' wire (work_respons c1)) \<and> step (Inp (a, aa, b) (BHD (a, aa, b) (buf' w))) (ops c1' w) op2' \<and> buf' w (a, aa, b) \<noteq> [])" |
                "(\<exists>op1'. op'' = comp_op (simp_wire' wire (work_respons c1)) (buf' w) op1' (ops c1' w) \<and> step Tau (ops c1 w) op1')" | 
                "(\<exists>op2'. op'' = comp_op (simp_wire' wire (work_respons c1)) (buf' w) (ops c1 w) op2' \<and> step Tau (ops c1' w) op2')"
        using Step' step_comp_op_cases
        unfolding io'_def'
        by fast
      then show ?case
      proof (cases, goal_cases Tau_W Tau_R Tau_c1 Tau_c1')
        case Tau_W
        obtain q qn qm x op2 p pn pm where op''_def: "op'' = comp_op (simp_wire' wire (work_respons c1)) (BENQ (p, pn, pm) x (buf' w)) op2 (ops c1' w)" and
          wire_some: "simp_wire' wire (work_respons c1) (q, qn, qm) = Some (p, pn, pm)" and Step'': "step (Out (q, qn, qm) x) (ops c1 w) op2"
          using Tau_W
          by fast
        have qn_def: "qn = pn" and qm_def: "qm = pm" and wire_some': "wire q = Some p" and eq_work_respons: "work_respons c1 pn = work_respons c1 pm"
          using wire_some
          unfolding simp_wire'_def
          apply -
             apply(simp, cases "wire q"; simp;cases "work_respons c1 qn = work_respons c1 qm"; simp)+
          done
        have w_def: "w = (work_respons c1 qn)"
          using H1_8 Step''
          unfolding step_spec_conf.simps[where a = c1]
          apply -
          apply safe
          apply(erule allE[where x = q])
          apply(erule allE[where x = qn])
          apply(erule allE[where x = qm])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op2])
          apply(erule allE[where x = op2])
          apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"])
          by blast
        have Step1': "step_dis' (Out (q, qn, qm) x) c1 (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"
          apply(rule S[where w = "work_respons c1 pn"])
          using Step''
          apply -
          apply(drule SDW, rule refl)
          subgoal
            using wire_some' H1_7
            apply auto
            done
          subgoal
            using H1_8 Step''
            unfolding step_spec_conf.simps[where a = c1]
            apply -
            apply safe
            apply(erule allE[where x = q])
            apply(erule allE[where x = qn])
            apply(erule allE[where x = qm])
            apply(erule allE[where x = x])
            apply(erule allE[where x = w])
            apply(erule allE[where x = op2])
            apply(erule allE[where x = op2])
            apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"])
            by blast
          subgoal
            unfolding w_def qn_def
            by blast
        done
      obtain op3 where Step2: "step (Out (q, qn, qm) x) op1 op3" and H3_2: "op3 ~d (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"
        using bisim_c_elim Step1' H1_1
        by blast
      show ?case
        using Step2
        unfolding H1_5
        apply -
        apply(rule exI[where x = "(map_op_comp (comp_op (simp_wire wire) (BENQ (p, qn, qm) x buf) op3 op1'))"])
        apply(rule conjI)
        subgoal
          using wire_some'
          unfolding io_def map_op_comp_def simp_wire_def
          by auto
        subgoal
          apply(cases "work_respons c1 qn = work_respons c1 qm")
          subgoal
            apply(rule bc'_base)
            apply(rule exI[where x = wire])
            apply(rule exI[where x = "(BENQ (p, qn, qm) x buf)"])
            apply(rule exI[where x = "(buf'((work_respons c1 qm) := (BENQ (p, qn, qm) x (buf' (work_respons c1 qm)))))"])
            apply(rule exI[where x = msg'])
            apply(rule exI[where x = op3])
            apply(rule exI[where x = op1'])
            apply(rule exI[where x = "(c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"])
            apply(rule exI[where x = "c1'"])
            using H3_2
            apply(rule conjI)
            using H1_2 H1_1 H1_3 H1_4 H1_7
            unfolding c'_def
            apply auto
            unfolding conf_comp_def H1_6
              apply auto
            subgoal
              using H1_8 Step''
              unfolding step_spec_conf.simps[where a = c1]
              apply -
              apply safe
              apply(erule allE[where x = q])
              apply(erule allE[where x = qn])
              apply(erule allE[where x = qm])
              apply(erule allE[where x = x])
              apply(erule allE[where x = w])
              apply(erule allE[where x = op2])
              apply(erule allE[where x = op2])
              apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"])
              by auto
            subgoal
              using H1_9
              by simp
            subgoal
              unfolding bufs_eq_def
              apply safe
              subgoal for ip ipn ipm
                apply(erule allE[where x = "(ip, ipn, ipm)"])
                apply safe
                unfolding fun_upd_def if_distrib BENQ_def
                apply(cases "(ip, ipn, ipm) = (p, qn, qm)")
                subgoal
                  apply simp
                  done
                subgoal
                  apply auto
                  done
                done
              done
            subgoal
              apply(simp only: record_help)
              done
            subgoal
              unfolding op'_def map_op_comp_def op''_def H1_4 qn_def qm_def w_def
              by auto
            done
          subgoal
            using eq_work_respons qn_def qm_def
            by argo
          done
        done
      next
        case Tau_R
        obtain p pn pm x op2 where op''_def: "op'' = comp_op (simp_wire' wire (work_respons c1)) (BTL (p, pn, pm) (buf' w)) (ops c1 w) op2" and
          wire_some: "(p, pn, pm) \<in> ran (simp_wire' wire (work_respons c1))" and Step'': "step (Inp (p, pn, pm) (BHD (p, pn, pm) (buf' w))) (ops c1' w) op2" and buf'_nonempty: "buf' w (p, pn, pm) \<noteq> []"
          using Tau_R
          by fast
        obtain q qn qm where wire_some': "simp_wire' wire (work_respons c1) (q, qn, qm) = Some (p, pn, pm)"
          using wire_some
          unfolding ran_def
          by fast
        have qn_def: "qn = pn" and qm_def: "qm = pm" and wire_some'': "wire q = Some p" and eq_work_respons: "work_respons c1 pn = work_respons c1 pm"  and eq_work_respons': "work_respons c1 qn = work_respons c1 qm"
          using wire_some'
          unfolding simp_wire'_def
             apply -
             apply(simp, cases "wire q"; simp;cases "work_respons c1 qn = work_respons c1 qm"; simp)+
          done
        have w_def: "w = (work_respons c1 pm)"
          using H1_9 Step''
          unfolding step_spec_conf.simps[where a = c1'] H1_4
          apply -
          apply safe
          apply(erule allE[where x = p])
          apply(erule allE[where x = pn])
          apply(erule allE[where x = pm])
          apply(erule allE[where x = "(BHD (p, pn, pm) (buf' w))"])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op2])
          apply(erule allE[where x = op2])
          apply(erule allE[where x = "msg (c1'\<lparr>ops := (ops c1')(w := op2)\<rparr>)"])
          by blast
        have Step1': "step_dis' (Inp (p, pn, pm) (BHD (p, pn, pm) (buf' w))) c1' (c1'\<lparr>ops := (ops c1')(w := op2)\<rparr>)"
          apply(rule S[where w = "work_respons c1' pm"])
          using Step''
          apply -
          apply(drule SDR)
          apply(rule refl)
          subgoal
            using wire_some'' H1_7
            by blast
          subgoal
            using w_def H1_4
            by auto
          subgoal
            unfolding w_def qn_def H1_4
            by blast
        done
      obtain op3 where Step2: "step (Inp (p, pn, pm) (BHD (p, pn, pm) (buf' w))) op1' op3" and H3_2: "op3 ~d (c1'\<lparr>ops := (ops c1')(w := op2)\<rparr>)"
        using bisim_c_elim Step1' H1_2
        by blast
      have buf_head: "(BHD (p, pn, pm) (buf' w)) = (BHD (p, pn, pm) buf)"
        using H1_3 H1_4 eq_work_respons
        unfolding bufs_eq_def BHD_def w_def
        by auto
      show ?case
        using Step2
        unfolding H1_5
        apply -
        apply(rule exI[where x = "(map_op_comp (comp_op (simp_wire wire) (BTL (p, pn, pm) buf) op1 op3))"])
        apply(rule conjI)
        subgoal
          using wire_some''
          unfolding io_def map_op_comp_def simp_wire_def
          apply auto
          subgoal
            using buf_head
            by simp
          subgoal
            unfolding ran_def
            apply simp
            apply(rule exI[where x = q])
            by simp
          subgoal
            using H1_3 buf'_nonempty H1_4 eq_work_respons w_def
            unfolding bufs_eq_def
            apply auto
            done
          done
        subgoal
          apply(cases "work_respons c1 qn = work_respons c1 qm")
          subgoal
            apply(rule bc'_base)
            apply(rule exI[where x = wire])
            apply(rule exI[where x = "(BTL (p, pn, pm) buf)"])
            apply(rule exI[where x = "(buf'((work_respons c1 pm) := (BTL (p, pn, pm) (buf' (work_respons c1 pm)))))"])
            apply(rule exI[where x = msg'])
            apply(rule exI[where x = op1])
            apply(rule exI[where x = op3])
            apply(rule exI[where x = "c1"])
            apply(rule exI[where x = "(c1'\<lparr>ops := (ops c1')(w := op2)\<rparr>)"])
            using H1_1
            apply(rule conjI)
            using H3_2 H1_1 H1_3 H1_4 H1_7
            unfolding c'_def
            apply auto
            unfolding conf_comp_def H1_6
              apply auto
            subgoal
              using H1_8
              by simp
            subgoal
              using H1_9 Step''
              unfolding step_spec_conf.simps[where a = c1']
              apply -
              apply safe
              apply(erule allE[where x = p])
              apply(erule allE[where x = p])
              apply(erule allE[where x = pn])
              apply(erule allE[where x = pm])
              apply(erule allE[where x = "(BHD (p, pn, pm) (buf' w))"])
              apply(erule allE[where x = w])
              apply(erule allE[where x = op2])
              apply(erule allE[where x = op2])
              apply(erule allE[where x = "msg (c1'\<lparr>ops := (ops c1')(w := op2)\<rparr>)"])
              by auto
            subgoal
              unfolding bufs_eq_def
              apply safe
              subgoal for ip ipn ipm
                apply(erule allE[where x = "(ip, ipn, ipm)"])
                apply safe
                unfolding fun_upd_def if_distrib BENQ_def
                apply(cases "(ip, ipn, ipm) = (p, qn, qm)")
                subgoal
                  unfolding qm_def BTL_def
                  apply auto
                  done
                subgoal
                  using H1_4 eq_work_respons
                  unfolding qm_def BTL_def
                  apply auto
                  done
                done
              done
            subgoal
              apply(simp only: record_help)
              done
            subgoal
              unfolding op'_def map_op_comp_def op''_def H1_4 qn_def qm_def w_def
              by auto
            done
          subgoal
            using eq_work_respons qn_def qm_def
            by argo
          done
        done
      next
        case Tau_c1
        obtain op2 where op''_def: "op'' = comp_op (simp_wire' wire (work_respons c1)) (buf' w) op2 (ops c1' w)" and Step'': "step Tau (ops c1 w) op2"
          using Tau_c1
          by fast
        have Step1': "step_dis' Tau c1 (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"
          apply(rule S[where w = "w"])
          using Step''
          apply -
          apply(drule SDT)
          apply auto
          done
      obtain op3 where Step2: "step Tau op1 op3" and H3_2: "op3 ~d (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"
        using bisim_c_elim Step1' H1_1
        by blast
      show ?case
        using Step2
        unfolding H1_5
        apply -
        apply(rule exI[where x = "(map_op_comp (comp_op (simp_wire wire) buf op3 op1'))"])
        apply(rule conjI)
        subgoal
          unfolding io_def map_op_comp_def
          apply auto
          done
        subgoal
          apply(rule bc'_base)
          apply(rule exI[where x = wire])
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "buf'"])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = op3])
          apply(rule exI[where x = op1'])
          apply(rule exI[where x = "(c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"])
          apply(rule exI[where x = "c1'"])
          using H3_2
          apply(rule conjI)
          using H1_2 H1_1 H1_3 H1_4 H1_7
          unfolding c'_def
          apply auto
          unfolding conf_comp_def H1_6
            apply auto
          subgoal
            using H1_8 Step''
            unfolding step_spec_conf.simps[where a = c1]
            apply -
            apply safe
            apply(erule allE[where x = op2])
            apply(erule allE[where x = w])
            apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"])
            by auto
          subgoal
            using H1_9
            by simp
          subgoal
            apply(simp only: record_help)
              done
            subgoal
              unfolding op'_def map_op_comp_def op''_def H1_4
              by auto
            done
          done
      next
        case Tau_c1'
        obtain op2 where op''_def: "op'' = comp_op (simp_wire' wire (work_respons c1)) (buf' w) (ops c1 w) op2" and Step'': "step Tau (ops c1' w) op2"
          using Tau_c1'
          by fast
        have Step1': "step_dis' Tau c1' (c1'\<lparr>ops := (ops c1')(w := op2)\<rparr>)"
          apply(rule S[where w = "w"])
          using Step''
          apply -
          apply(drule SDT)
          apply auto
          done
      obtain op3 where Step2: "step Tau op1' op3" and H3_2: "op3 ~d (c1'\<lparr>ops := (ops c1')(w := op2)\<rparr>)"
        using bisim_c_elim Step1' H1_2
        by meson
      show ?case
        using Step2
        unfolding H1_5
        apply -
        apply(rule exI[where x = "(map_op_comp (comp_op (simp_wire wire) buf op1 op3))"])
        apply(rule conjI)
        subgoal
          unfolding io_def map_op_comp_def
          apply auto
          done
        subgoal
          apply(rule bc'_base)
          apply(rule exI[where x = wire])
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "buf'"])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = op1])
          apply(rule exI[where x = op3])
          apply(rule exI[where x = "c1"])
          apply(rule exI[where x = "(c1'\<lparr>ops := (ops c1')(w := op2)\<rparr>)"])
          using H1_1
          apply(rule conjI)
          using H3_2 H1_1 H1_3 H1_4 H1_7
          unfolding c'_def
          apply auto
          unfolding conf_comp_def H1_6
            apply auto
          subgoal
            using H1_8
            by simp
          subgoal
            using H1_9 Step''
            unfolding step_spec_conf.simps[where a = c1']
            apply -
            apply safe
            apply(erule allE[where x = op2])
            apply(erule allE[where x = w])
            apply(erule allE[where x = "msg (c1'\<lparr>ops := (ops c1')(w := op2)\<rparr>)"])
            by auto
          subgoal
            apply(simp only: record_help)
              done
            subgoal
              unfolding op'_def map_op_comp_def op''_def H1_4
              by auto
            done
          done
      qed
    next
      case Tau_Inp
      obtain p n m op' q where c'_def: "c' = c\<lparr>ops := (ops c)(w := op'), msg := (msg c)(work_respons c n := (msg c (work_respons c n))(w := BTL (p, n, m) (msg c (work_respons c n) w)))\<rparr>" and
        Step: "step (Inp (p, n, m) (bhd (msg c (work_respons c n) w (p, n, m)))) (ops c w) op'" and w_not: "w \<noteq> work_respons c n" and w_eq: "w = work_respons c m" and
         wire_some: "used_wire c q = Some p" and msg_nonempty: "(msg c (work_respons c n) w (p,(n,m))) \<noteq> []"
        using Tau_Inp
        by blast
      have w_eq': "w = work_respons c1 m"
        using w_eq
        unfolding H1_6 conf_comp_def
        apply auto
        done
      consider "\<exists>p'. p = Inl p'" | "\<exists>p'. p = Inr p'"
        apply(cases p; simp)
        done
      then show ?case
      proof (cases, goal_cases Inl Inr)
        case Inl
        obtain p' where p_def: "p = Inl p'"
          using Inl
          by auto
        obtain q' where q_def: "q = Inl q'" and wire_some': "used_wire c1 q' = Some p'"
          using wire_some
          unfolding p_def H1_6 conf_comp_def
          apply -
          apply simp
          apply(cases q; simp)
          subgoal for q'
            apply(cases "used_wire c1 q'"; simp)
            subgoal
              apply(cases "wire q'"; simp)
              done
            done
          subgoal for q'
            apply(cases "used_wire c1' q'"; simp)
            done
          done
        obtain io' op'' where io'_def: "io' = Inp (Inl (p', n, m)) (bhd (msg c1 (work_respons c1 n) w (p', n, m)))" and
          Step': "step (Inp (Inl (p', n, m)) (bhd (msg c1 (work_respons c1 n) w (p', n, m)))) (comp_op (simp_wire' wire (work_respons c1)) (buf' w) (ops c1 w) (ops c1' w)) op''" and
          op'_def: "op' = map_op (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) op''"
          using Step
          unfolding H1_6 conf_comp_def map_op_comp_def p_def
          apply simp
          apply(erule step_map_op_elim)
          subgoal for io' op''
            apply(cases io'; simp)
            subgoal for p''
              apply auto
              apply(cases p'')
              subgoal for p1
                apply auto
                apply(cases p1; simp)
                done
              subgoal for p1
                apply auto
                apply(cases p1; simp)
                done
              done
            done
          done
        obtain op2 where op''_def: "op'' = comp_op (simp_wire' wire (work_respons c1)) (buf' w) op2 (ops c1' w)" and
          Step'': "step (Inp (p', n, m) (bhd (msg c1 (work_respons c1 n) w (p', n, m)))) (ops c1 w) op2"
          using Step'
          apply -
          apply(drule step_comp_op_cases; simp)
          apply auto
          done
        have Step1': "step_dis' Tau c1 (c1\<lparr>ops := (ops c1)(w := op2),
           msg := (msg c1)(work_respons c1 n := (msg c1 (work_respons c1 n))(w := BTL (p', n, m) (msg c1 (work_respons c1 n) w)))\<rparr>)"
          apply(rule S[where w = "w"])
          using Step''
          apply -
          apply(drule SDTR, rule refl)
          subgoal
            using wire_some'
            by blast
          subgoal
            using w_not
            unfolding H1_6 conf_comp_def
            apply simp
            done
          subgoal
            by simp
          subgoal
            using w_eq
            unfolding H1_6 conf_comp_def
            apply simp
            done
          subgoal
            using msg_nonempty
            unfolding fun_upd_def if_distrib H1_6 conf_comp_def p_def
            apply simp
            done
          subgoal
            apply simp
            done
          done
      obtain op3 where Step2: "step Tau op1 op3" and H3_2: "op3 ~d (c1\<lparr>ops := (ops c1)(w := op2),
           msg := (msg c1)(work_respons c1 n := (msg c1 (work_respons c1 n))(w := BTL (p', n, m) (msg c1 (work_respons c1 n) w)))\<rparr>)"
        using bisim_c_elim Step1' H1_1
        by meson
      show ?case 
        unfolding H1_5
        apply(rule exI[where x = "(map_op_comp (comp_op (simp_wire wire) buf op3 op1'))"])
        apply(rule conjI)
        subgoal
          unfolding io_def map_op_comp_def
          apply simp
          apply(rule step_map_op; simp?)
          using Step2
          apply -
          apply(rule step_comp_op_L_Tau)
            apply auto
          done
        subgoal
          apply(rule bc'_base)
          apply(rule exI[where x = wire])
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "buf'"])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = op3])
          apply(rule exI[where x = op1'])
          apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(w := op2),
       msg := (msg c1)(work_respons c1 n := (msg c1 (work_respons c1 n))(w := BTL (p', n, m) (msg c1 (work_respons c1 n) w)))\<rparr>"])
          apply(rule exI[where x = "c1'"])
          using H3_2
          apply(rule conjI)
          using H1_2 H1_1 H1_3 H1_4 H1_7
          unfolding c'_def
          apply auto
          unfolding conf_comp_def H1_6
            apply auto
          subgoal
            using H1_8 Step''
            unfolding step_spec_conf.simps[where a = c1]
            apply -
            apply safe
            apply(erule allE[where x = p'])
            apply(erule allE[where x = n])
            apply(erule allE[where x = m])
            apply(erule allE[where x = "(bhd (msg c1 (work_respons c1 n) w (p', n, m)))"])
            apply(erule allE[where x = w])
            apply(erule allE[where x = op2])
            apply(erule allE[where x = op2])
            apply(erule allE[where x = "(msg c1)(work_respons c1' n := (msg c1 (work_respons c1' n))(w := BTL (p', n, m) (msg c1 (work_respons c1' n) w)))"])
            by auto
          subgoal
            using H1_9
            by simp
          subgoal
            apply(simp only: record_help)
            unfolding fun_upd_def if_distrib H1_4
            apply(subst if_distribR)+
            apply(rule lambda_helper)
            apply(rule allI)
            subgoal for wt
              apply(cases "wt = work_respons c1' n"; simp)
              subgoal
                unfolding BTL_def
                apply(simp only: simp_thms if_True)
                apply(rule lambda_helper)
                apply(rule allI)
                subgoal for wt'
                  apply(cases "wt' = w"; simp)
                  subgoal
                    apply(simp only: simp_thms if_True)
                    apply(rule lambda_helper)
                    apply(rule allI)
                    subgoal for wa
                      using wire_some'
                      unfolding fun_upd_def if_distrib H1_4 p_def
                      apply(subst if_distribR)+
                      apply(cases "wa = (Inl p', n, m)"; simp)
                      apply(cases wa; simp)
                      subgoal for wa1 wa2 wa3
                        apply(cases wa1; simp)
                        by linarith
                      done
                    done
                  subgoal
                    by presburger
                  done
                done
              subgoal
                by presburger
              done
            done
          subgoal
            unfolding op'_def map_op_comp_def op''_def H1_4
            by auto
            done
          done
      next
        case Inr
        obtain p' where p_def: "p = Inr p'"
          using Inr
          by auto
        consider "(\<exists>q'. q = Inr q' \<and> used_wire c1' q' = Some p')" | "(\<exists>q'. q = Inl q' \<and> wire q' = Some p')"
          using wire_some
          unfolding p_def H1_6 conf_comp_def
          apply -
          apply simp
          apply(cases q; simp)
          subgoal for q'
            apply(cases "used_wire c1 q'"; simp)
            subgoal
              apply(cases "wire q'"; simp)
              done
            done
          subgoal for q'
            apply(cases "used_wire c1' q'"; simp)
            done
          done
        then show ?case
        proof (cases, goal_cases Inr' Inl')
          case Inr'
          obtain q' where q_def: "q = Inr q'" and wire_some': "used_wire c1' q' = Some p'"
            using Inr'
            by blast
          obtain io' op2 where io'_def: "io' = Inp (Inr (p', n, m)) (bhd (msg c1' (work_respons c1 n) w (p', n, m)))" and
            op'_def: "op' = map_op (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (comp_op (simp_wire' wire (work_respons c1)) (buf' w) (ops c1 w) op2)" and
            Step'': "step (Inp (p', n, m) (bhd (msg c1' (work_respons c1 n) w (p', n, m)))) (ops c1' w) op2"
            using Step
            unfolding H1_6 conf_comp_def map_op_comp_def p_def
            apply simp
            apply(erule step_map_op_elim)
            subgoal for io' op''
              apply(cases io'; simp)
              subgoal for p''
                apply auto
                apply(cases p'')
                subgoal for p1
                  apply auto
                  apply(cases p1; simp)
                  done
                subgoal for p1
                  apply auto
                  apply(cases p1; simp)
                  apply auto
                  apply(drule step_comp_op_cases; simp)
                  using wire_some'
                  apply auto
                  by presburger
                done
              done
            done
          have Step1': "step_dis' Tau c1' (c1'\<lparr>ops := (ops c1')(w := op2), msg := (msg c1')(work_respons c1 n := (msg c1' (work_respons c1 n))(w := BTL (p', n, m) (msg c1' (work_respons c1 n) w)))\<rparr>)"
            apply(rule S[where w = "w"])
            using Step''
            apply -
            apply(drule SDTR, rule refl)
            subgoal
              using wire_some'
              by blast
            subgoal
              using w_not
              unfolding H1_6 conf_comp_def
              apply simp
              done
            subgoal
              using H1_4
              by simp
            subgoal
              using w_eq
              unfolding H1_6 conf_comp_def H1_4
              apply simp
              done
            subgoal
              using msg_nonempty wire_some'
              unfolding fun_upd_def if_distrib H1_6 conf_comp_def p_def
              apply auto
              apply(cases "\<exists>q. used_wire c1' q = Some p'"; simp)
              done
            subgoal
              apply simp
              done
            done
        obtain op3 where Step2: "step Tau op1' op3" and H3_2: "op3 ~d (c1'\<lparr>ops := (ops c1')(w := op2), msg := (msg c1')(work_respons c1 n := (msg c1' (work_respons c1 n))(w := BTL (p', n, m) (msg c1' (work_respons c1 n) w)))\<rparr>)"
          using bisim_c_elim Step1' H1_2
          by meson
        show ?case 
          unfolding H1_5
          apply(rule exI[where x = "(map_op_comp (comp_op (simp_wire wire) buf op1 op3))"])
          apply(rule conjI)
          subgoal
            unfolding io_def map_op_comp_def
            apply simp
            apply(rule step_map_op; simp?)
            using Step2
            apply -
            apply(rule step_comp_op_R_Tau)
              apply auto
            done
          subgoal
            apply(rule bc'_base)
            apply(rule exI[where x = wire])
            apply(rule exI[where x = "buf"])
            apply(rule exI[where x = "buf'"])
            apply(rule exI[where x = msg'])
            apply(rule exI[where x = op1])
            apply(rule exI[where x = op3])
            apply(rule exI[where x = "c1"])
            apply(rule exI[where x = "(c1'\<lparr>ops := (ops c1')(w := op2), msg := (msg c1')(work_respons c1 n := (msg c1' (work_respons c1 n))(w := BTL (p', n, m) (msg c1' (work_respons c1 n) w)))\<rparr>)"])
            using H1_1
            apply(rule conjI)
            using H3_2 H1_1 H1_3 H1_4 H1_7
            unfolding c'_def
            apply auto
            subgoal
              using H1_8
              by simp
            subgoal
              using H1_9 Step''
              unfolding step_spec_conf.simps[where a = c1']
              apply -
              apply safe
              apply(erule allE[where x = p'])
              apply(erule allE[where x = p'])
              apply(erule allE[where x = n])
              apply(erule allE[where x = m])
              apply(erule allE[where x = "(bhd (msg c1' (work_respons c1 n) w (p', n, m)))"])
              apply(erule allE[where x = w])
              apply(erule allE[where x = op2])
              apply(erule allE[where x = op2])
              apply(erule allE[where x = "(msg c1')(work_respons c1' n := (msg c1' (work_respons c1' n))(w := BTL (p', n, m) (msg c1' (work_respons c1' n) w)))"])
              by auto
            subgoal
              unfolding H1_6
              unfolding conf_comp_def
              apply auto
              subgoal
                apply(simp only: record_help)
                unfolding fun_upd_def if_distrib H1_4 conf_comp_def
                apply(subst if_distribR)+
                apply(rule lambda_helper)
                apply(rule allI)
                subgoal for wt
                  apply(cases "wt = work_respons c1' n"; simp)
                  subgoal
                    apply(simp only: simp_thms if_True)
                    apply(rule lambda_helper)
                    apply(rule allI)
                    subgoal for wt'
                      apply(cases "wt' = w"; simp)
                      subgoal
                        using wire_some'
                        unfolding fun_upd_def if_distrib BTL_def p_def
                        apply(subst if_distribR)+
                        apply(rule lambda_helper)
                        apply(rule allI)
                        subgoal for wa
                          apply(cases "wa = (Inr p', n, m)"; simp)
                          subgoal
                            by fast
                          subgoal
                            apply auto
                            apply(cases wa; simp)
                            subgoal for wa1 wa2 wa3
                              apply(cases wa1; simp)
                              by argo
                            done
                          done
                        done
                      subgoal
                        by presburger
                      done
                    done
                  subgoal
                    by presburger
                  done
                done
                subgoal
                  unfolding op'_def map_op_comp_def
                  apply(simp only: record_help)
                  by fastforce
                done
              done
            done
        next
          case Inl'
          obtain q' where q_def: "q = Inl q'" and wire_some': "wire q' = Some p'"
            using Inl'
            by blast
          have no_used_wire: "\<not>(\<exists>q'. used_wire c1' q' = Some p')"
            using wire_some' H1_7
            by fast
          obtain io' op2 where io'_def: "io' = Inp (Inr (p', n, m)) (bhd (msg' (work_respons c1 n) w (p', n, m)))" and
            op'_def: "op' = map_op (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y)))
        (comp_op (simp_wire' wire (work_respons c1)) (buf' w) (ops c1 w) op2)" and
            Step'': "step (Inp (p', n, m) (bhd (msg' (work_respons c1 n) w (p', n, m)))) (ops c1' w) op2"
            using Step
            unfolding H1_6 conf_comp_def map_op_comp_def p_def
            apply simp
            apply(erule step_map_op_elim)
            subgoal for io' op''
              apply(cases io'; simp)
              subgoal for p''
                apply auto
                apply(cases p'')
                subgoal for p1
                  apply auto
                  apply(cases p1; simp)
                  done
                subgoal for p1
                  apply auto
                  apply(cases p1; simp)
                  apply auto
                  apply(drule step_comp_op_cases; simp)
                  using no_used_wire
                  apply auto
                  done
                done
              done
            done
          have Step1': "step_dis' (Inp (p', n, m) (bhd (msg' (work_respons c1 n) w (p', n, m)))) c1' (c1'\<lparr>ops := (ops c1')(w := op2)\<rparr>)"
            apply(rule S[where w = w])
            using Step''
            apply -
            apply(drule SDR, rule refl)
            subgoal
              using no_used_wire
              by blast
            subgoal
              using w_eq H1_4
              unfolding H1_6 conf_comp_def
              apply simp
              done
            subgoal
              using H1_4
              by simp
            done
        obtain op3 where Step2: "step (Inp (p', n, m) (bhd (msg' (work_respons c1 n) w (p', n, m)))) op1' op3" and H3_2: "op3 ~d (c1'\<lparr>ops := (ops c1')(w := op2)\<rparr>)"
          using bisim_c_elim Step1' H1_2
          by meson
        show ?case 
          unfolding H1_5
          apply(rule exI[where x = "(map_op_comp (comp_op (simp_wire wire) (BTL (p', n, m) buf) op1 op3))"])
          apply(rule conjI)
          subgoal
            unfolding io_def map_op_comp_def
            apply simp
            apply(rule step_map_op; simp?)
            using Step2
            apply -
            apply(rule step_Tau_comp_op_R, assumption)
                apply auto
            subgoal
              using wire_some'
              unfolding simp_wire_def ran_def
              apply simp
              apply(rule exI[where x = q'])
              by auto
            subgoal
              using msg_nonempty wire_some' no_used_wire H1_3 w_not w_eq
              unfolding fun_upd_def if_distrib H1_6 conf_comp_def p_def bufs_eq_def H1_4
              apply auto
              done
            subgoal
              using msg_nonempty wire_some' no_used_wire H1_3 w_not w_eq
              unfolding fun_upd_def if_distrib H1_6 conf_comp_def p_def bufs_eq_def H1_4 BHD_def
              apply auto
              done
            done
          subgoal
            apply(rule bc'_base)
            apply(rule exI[where x = wire])
            apply(rule exI[where x = "(BTL (p', n, m) buf)"])
            apply(rule exI[where x = "buf'"])
            apply(rule exI[where x = "msg'(work_respons c1 n := ((msg' (work_respons c1 n))(work_respons c1 m := BTL (p', n, m) (msg' (work_respons c1 n) (work_respons c1 m)))))"])
            apply(rule exI[where x = op1])
            apply(rule exI[where x = op3])
            apply(rule exI[where x = "c1"])
            apply(rule exI[where x = "c1'\<lparr>ops := (ops c1')(w := op2)\<rparr>"])
            using H1_1
            apply(rule conjI)
            using H3_2 H1_1 H1_3 H1_4 H1_7
            unfolding c'_def
            apply auto
            subgoal
              using H1_8
              by simp
            subgoal
              using H1_9 Step''
              unfolding step_spec_conf.simps[where a = c1']
              apply -
              apply safe
              apply(erule allE[where x = p'])
              apply(erule allE[where x = p'])
              apply(erule allE[where x = n])
              apply(erule allE[where x = m])
              apply(erule allE[where x = "(bhd (msg' (work_respons c1 n) w (p', n, m)))"])
              apply(erule allE[where x = w])
              apply(erule allE[where x = op2])
              apply(erule allE[where x = op2])
              apply(erule allE[where x = "msg (c1'\<lparr>ops := (ops c1')(w := op2)\<rparr>)"])
              by auto
            subgoal
              using w_eq w_not
              unfolding bufs_eq_def BTL_def conf_comp_def H1_6
              apply auto
              done
            subgoal
              unfolding H1_6
              unfolding conf_comp_def
              apply auto
              subgoal
                apply(simp only: record_help)
                unfolding fun_upd_def if_distrib H1_4 conf_comp_def p_def BTL_def w_eq'
                apply(subst if_distribR)+
                apply(rule lambda_helper)
                apply(rule allI)
                subgoal for wt
                  apply(cases "wt = work_respons c1' n"; simp)
                  subgoal
                    apply(simp only: simp_thms if_True)
                    apply(rule lambda_helper)
                    apply(rule allI)
                    subgoal for wt'
                      apply(cases "wt' = work_respons c1' m"; simp)
                      subgoal
                        using wire_some
                        apply(simp only: simp_thms if_True)
                        apply(rule lambda_helper)
                        apply(rule allI)
                        subgoal for wa
                          apply(cases wa; simp)
                          subgoal for wa1 wa2 wa3
                            apply(cases wa1; simp)
                            apply auto
                            using wire_some' by blast
                          done
                        done
                      subgoal
                        by presburger
                      done
                    done
                  subgoal
                    by presburger
                  done
                done
              subgoal
                unfolding op'_def map_op_comp_def
                apply(simp only: record_help)
                by fastforce
                done
              done
            done
        qed
      qed
    next
      case Tau_Out
      obtain q n m x op' p where c'_def: "c' = c\<lparr>ops := (ops c)(w := op'), msg := (msg c)(w := (msg c w)(work_respons c m := BENQ (p, n, m) x (msg c w (work_respons c m))))\<rparr>" and
        Step: "step (Out (q, n, m) x) (ops c w) op'" and wire_some: "used_wire c q = Some p" and w_not: "work_respons c m \<noteq> w" and w_eq: "w = work_respons c n"
        using Tau_Out
        by blast
      have w_not': "work_respons c1 m \<noteq> w" and w_eq': "w = work_respons c1 n"
        using w_not w_eq
        unfolding H1_6 conf_comp_def
         apply auto
        done
      have w_eq': "w = work_respons c1 n"
        using w_eq
        unfolding H1_6 conf_comp_def
        apply auto
        done
      consider "\<exists>q'. q = Inr q'" | "\<exists>q'. q = Inl q'"
        apply(cases q; simp)
        done
      then show ?case
      proof (cases, goal_cases Inr Inl)
        case Inr
        obtain q' where q_def: "q = Inr q'"
          using Inr
          by auto
        obtain p' where p_def: "p = Inr p'" and wire_some': "used_wire c1' q' = Some p'"
          using wire_some
          unfolding q_def H1_6 conf_comp_def
          apply -
          apply simp
          apply(cases p; simp)
          subgoal for p'
            apply(cases "used_wire c1' q'"; simp)
            done
          subgoal for p'
            apply(cases "used_wire c1' q'"; simp)
            done
          done
        obtain io' op'' where io'_def: "io' = Out (Inr (q', n, m)) x" and Step': "step (Out (Inr (q', n, m)) x) (comp_op (simp_wire' wire (work_respons c1)) (buf' w) (ops c1 w) (ops c1' w)) op''" and
           op'_def: "op' = map_op (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) op''"
          using Step
          unfolding H1_6 conf_comp_def map_op_comp_def q_def
          apply simp
          apply(erule step_map_op_elim)
          subgoal for io' op''
            apply(cases io'; simp)
            subgoal for q''
              apply auto
              apply(cases q'')
              subgoal for q1
                apply auto
                apply(cases q1; simp)
                done
              subgoal for q1
                apply auto
                apply(cases q1; simp)
                done
              done
            done
          done
        obtain op2 where op''_def: "op'' = comp_op (simp_wire' wire (work_respons c1)) (buf' w) (ops c1 w) op2" and
          Step'': "step (Out (q', n, m) x) (ops c1' w) op2"
          using Step'
          apply -
          apply(drule step_comp_op_cases; simp)
          apply auto
          done
        have Step1': "step_dis' Tau c1' (c1'\<lparr>ops := (ops c1')(w := op2), msg := (msg c1')(w := (msg c1' w)(work_respons c1' m := BENQ (p', n, m) x (msg c1' w (work_respons c1' m))))\<rparr>)"
          apply(rule S[where w = w])
          using Step''
          apply -
          apply(drule SDTW[where p = p' and w' = "work_respons c1' m"], rule refl)
          subgoal
            using wire_some'
            by blast
          subgoal
            using w_not' H1_4
            by simp
          subgoal
            using w_eq' H1_4
            by simp
          subgoal
            by(rule refl)
          subgoal
            apply simp
            done
          done
      obtain op3 where Step2: "step Tau op1' op3" and H3_2: "op3 ~d (c1'\<lparr>ops := (ops c1')(w := op2), msg := (msg c1')(w := (msg c1' w)(work_respons c1' m := BENQ (p', n, m) x (msg c1' w (work_respons c1' m))))\<rparr>)"
        using bisim_c_elim Step1' H1_2
        by meson
      show ?case 
        unfolding H1_5
        apply(rule exI[where x = "(map_op_comp (comp_op (simp_wire wire) buf op1 op3))"])
        apply(rule conjI)
        subgoal
          unfolding io_def map_op_comp_def
          apply simp
          apply(rule step_map_op; simp?)
          using Step2
          apply -
          apply(rule step_comp_op_R_Tau)
            apply auto
          done
        subgoal
          apply(rule bc'_base)
          apply(rule exI[where x = wire])
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "buf'"])
          apply(rule exI[where x = msg'])
          apply(rule exI[where x = op1])
          apply(rule exI[where x = op3])
          apply(rule exI[where x = "c1"])
          apply(rule exI[where x = "(c1'\<lparr>ops := (ops c1')(w := op2), msg := (msg c1')(w := (msg c1' w)(work_respons c1' m := BENQ (p', n, m) x (msg c1' w (work_respons c1' m))))\<rparr>)"])
          using H1_1
          apply(rule conjI)
          using H3_2 H1_1 H1_3 H1_4 H1_7
          unfolding c'_def
          apply auto
          unfolding conf_comp_def H1_6
            apply auto
          subgoal
            using H1_8
            by simp
          subgoal
            using H1_9 Step''
            unfolding step_spec_conf.simps[where a = c1']
            apply -
            apply safe
            apply(erule allE[where x = q'])
            apply(erule allE[where x = n])
            apply(erule allE[where x = m])
            apply(erule allE[where x = x])
            apply(erule allE[where x = w])
            apply(erule allE[where x = op2])
            apply(erule allE[where x = op2])
            apply(erule allE[where x = "(msg c1')(w := (msg c1' w)(work_respons c1' m := BENQ (p', n, m) x (msg c1' w (work_respons c1' m))))"])
            by auto
          subgoal
            apply(simp only: record_help)
            unfolding fun_upd_def if_distrib H1_4 conf_comp_def BENQ_def
            apply(subst if_distribR)+
            apply(rule lambda_helper)
            apply(rule allI)
            subgoal for wt
              apply(cases "wt = w"; simp)
              subgoal
                apply(simp only: simp_thms if_True)
                apply(rule lambda_helper)
                apply(rule allI)
                subgoal for wt'
                  apply(cases "wt' = work_respons c1' m"; simp)
                  subgoal
                    using wire_some'
                    unfolding p_def
                    apply(simp only: simp_thms if_True)
                    apply(rule lambda_helper)
                    apply(rule allI)
                    subgoal for wa
                      apply(cases "wa")
                      subgoal for wa1 wa2 wa3
                        apply safe
                        apply(cases "wa1"; simp)
                        apply auto
                        done
                      done
                    done
                  subgoal
                    by presburger
                  done
                done
              subgoal
                by presburger
              done
            done
          subgoal
            unfolding op'_def map_op_comp_def op''_def H1_4
            by auto
            done
          done
      next
        case Inl
        obtain q' where q_def: "q = Inl q'"
          using Inl
          by auto
        consider "(\<exists>p'. p = Inl p' \<and> used_wire c1 q' = Some p')" | "(\<exists>p'. p = Inr p' \<and> wire q' = Some p')"
          using wire_some
          unfolding q_def H1_6 conf_comp_def
          apply -
          apply simp
          apply(cases p; simp)
          subgoal for p'
            apply(cases "used_wire c1 q'"; simp)
            subgoal
              apply(cases "wire q'"; simp)
              done
            done
          subgoal for p'
            apply(cases "used_wire c1 q'"; simp)
            apply(cases "wire q'"; simp)
            done
          done
        then show ?case
        proof (cases, goal_cases Inl' Inr')
          case Inl'
          obtain p' where p_def: "p = Inl p'" and wire_some': "used_wire c1 q' = Some p'"
            using Inl'
            by blast
          obtain op2 where op'_def: "op' = map_op (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (comp_op (simp_wire' wire (work_respons c1)) (buf' w) op2 (ops c1' w))" and
           Step'': "step (Out (q', n, m) x) (ops c1 w) op2"
            using Step
            unfolding H1_6 conf_comp_def map_op_comp_def q_def
            apply simp
            apply(erule step_map_op_elim)
            subgoal for io' op''
              apply(cases io'; simp)
              subgoal for q''
                apply auto
                apply(cases q'')
                subgoal for q1
                  apply auto
                  apply(cases q1; simp)
                  apply auto
                  apply(drule step_comp_op_cases; simp)
                  using wire_some'
                  apply auto
                  done
                subgoal for q1
                  apply auto
                  apply(cases q1; simp)
                  done
                done
              done
            done
          have Step1': "step_dis' Tau c1 (c1\<lparr>ops := (ops c1)(w := op2), msg := (msg c1)(w := (msg c1 w)(work_respons c1 m := BENQ (p', n, m) x (msg c1 w (work_respons c1 m))))\<rparr>)"
            apply(rule S[where w = w])
            using Step''
            apply -
            apply(drule SDTW[where p = p' and w' = " work_respons c1 m"], rule refl)
            subgoal
              using wire_some'
              by blast
            subgoal
              using w_not' w_eq'
              by simp
            subgoal
              using w_eq'
              by simp
            subgoal
              by(rule refl)
            subgoal
              apply simp
              done
            done
          obtain op3 where Step2: "step Tau op1 op3" and H3_2: "op3 ~d c1\<lparr>ops := (ops c1)(w := op2), msg := (msg c1)(w := (msg c1 w)(work_respons c1 m := BENQ (p', n, m) x (msg c1 w (work_respons c1 m))))\<rparr>"
            using bisim_c_elim Step1' H1_1
            by meson
        show ?case 
          unfolding H1_5
          apply(rule exI[where x = "(map_op_comp (comp_op (simp_wire wire) buf op3 op1'))"])
          apply(rule conjI)
          subgoal
            unfolding io_def map_op_comp_def
            apply simp
            apply(rule step_map_op; simp?)
            using Step2
            apply -
            apply(rule step_comp_op_L_Tau)
              apply auto
            done
          subgoal
            apply(rule bc'_base)
            apply(rule exI[where x = wire])
            apply(rule exI[where x = "buf"])
            apply(rule exI[where x = "buf'"])
            apply(rule exI[where x = msg'])
            apply(rule exI[where x = op3])
            apply(rule exI[where x = op1'])
            apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(w := op2), msg := (msg c1)(w := (msg c1 w)(work_respons c1 m := BENQ (p', n, m) x (msg c1 w (work_respons c1 m))))\<rparr>"])
            apply(rule exI[where x = c1'])
            using H3_2
            apply(rule conjI)
            using H1_2 H1_1 H1_3 H1_4 H1_7
            unfolding c'_def
            apply auto
            subgoal
              using H1_8 Step''
              unfolding step_spec_conf.simps[where a = c1]
              apply -
              apply safe
              apply(erule allE[where x = q'])
              apply(erule allE[where x = n])
              apply(erule allE[where x = m])
              apply(erule allE[where x = x])
              apply(erule allE[where x = w])
              apply(erule allE[where x = op2])
              apply(erule allE[where x = op2])
              apply(erule allE[where x = "(msg c1)(w := (msg c1 w)(work_respons c1' m := BENQ (p', n, m) x (msg c1 w (work_respons c1' m))))"])
              by auto
            subgoal
              using H1_9
              by simp
            subgoal
              unfolding H1_6
              unfolding conf_comp_def
              apply auto
              subgoal
                apply(simp only: record_help)
                unfolding fun_upd_def if_distrib H1_4 conf_comp_def BENQ_def p_def
                apply(subst if_distribR)+
                apply(rule lambda_helper)
                apply(rule allI)
                subgoal for wt
                  apply(cases "wt = w"; simp)
                  subgoal
                    apply(simp only: simp_thms if_True)
                    apply(rule lambda_helper)
                    apply(rule allI)
                    subgoal for wt'
                      apply(cases "wt' = work_respons c1' m"; simp)
                      subgoal
                        using wire_some'
                        apply(simp only: simp_thms if_True)
                        apply(rule lambda_helper)
                        apply(rule allI)
                        subgoal for wa
                          apply(cases wa; simp)
                          subgoal for wa1 wa2 wa3
                            apply(cases wa1; simp)
                            done
                          done
                        done
                      subgoal
                        by presburger
                      done
                    done
                  subgoal
                    by presburger
                  done
                done
                subgoal
                  unfolding op'_def map_op_comp_def
                  apply(simp only: record_help)
                  by fastforce
                done
              done
            done
        next
          case Inr'
          obtain p' where p_def: "p = Inr p'" and wire_some': "wire q' = Some p'"
            using Inr'
            by blast
          have no_used_wire: "used_wire c1 q' = None"
            using wire_some' H1_7
            apply auto
            done
          obtain op2 where op'_def: "op' = map_op (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (case_sum (\<lambda>(ip', y). (Inl ip', y)) (\<lambda>(ip', y). (Inr ip', y))) (comp_op (simp_wire' wire (work_respons c1)) (buf' w) op2 (ops c1' w))" and
            Step'': "step (Out (q', n, m) x) (ops c1 w) op2 "
            using Step
            unfolding H1_6 conf_comp_def map_op_comp_def q_def
            apply simp
            apply(erule step_map_op_elim)
            subgoal for io' op''
              apply(cases io'; simp)
              subgoal for q''
                apply auto
                apply(cases q'')
                subgoal for q1
                  apply auto
                  apply(cases q1; simp)
                  apply auto
                  apply(drule step_comp_op_cases; simp)
                  using wire_some'
                  apply auto
                  done
                subgoal for q1
                  apply auto
                  apply(cases q1; simp)
                  done
                done
              done
            done
          have Step1': "step_dis' (Out (q', n, m) x) c1 (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"
            apply(rule S[where w = w])
            using Step''
            apply -
            apply(drule SDW, rule refl)
            subgoal
              using wire_some' H1_7
              by blast
            subgoal
              using w_not' w_eq'
              by simp
            subgoal
              using w_eq'
              by simp
            done
          obtain op3 where Step2: "step (Out (q', n, m) x) op1 op3" and H3_2: "op3 ~d (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"
            using bisim_c_elim Step1' H1_1
            by meson
        show ?case 
          unfolding H1_5
          apply(rule exI[where x = "(map_op_comp (comp_op (simp_wire wire) (BENQ (p', n, m) x buf) op3 op1'))"])
          apply(rule conjI)
          subgoal
            unfolding io_def map_op_comp_def
            apply simp
            apply(rule step_map_op; simp?)
            using Step2
            apply -
            apply(rule step_Tau_comp_op_L[where q = "(p', n, m)"], assumption)
              apply auto
            unfolding simp_wire_def
            using wire_some'
            apply auto
            done
          subgoal
            apply(rule bc'_base)
            apply(rule exI[where x = wire])
            apply(rule exI[where x = "(BENQ (p', n, m) x buf) "])
            apply(rule exI[where x = "buf'"])
            apply(rule exI[where x = "msg'(work_respons c1 n := ((msg' (work_respons c1 n))(work_respons c1 m := BENQ (p', n, m) x (msg' (work_respons c1 n) (work_respons c1 m)))))"])
            apply(rule exI[where x = op3])
            apply(rule exI[where x = op1'])
            apply(rule exI[where x = "(c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"])
            apply(rule exI[where x = c1'])
            using H3_2
            apply(rule conjI)
            using H1_2 H1_1 H1_3 H1_4 H1_7
            unfolding c'_def
            apply auto
            subgoal
              using H1_8 Step''
              unfolding step_spec_conf.simps[where a = c1]
              apply -
              apply safe
              apply(erule allE[where x = q'])
              apply(erule allE[where x = n])
              apply(erule allE[where x = m])
              apply(erule allE[where x = x])
              apply(erule allE[where x = w])
              apply(erule allE[where x = op2])
              apply(erule allE[where x = op2])
              apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"])
              by auto
            subgoal
              using H1_9
              by simp
            subgoal
              unfolding bufs_eq_def BENQ_def
              apply(rule allI)
              subgoal for ip
                apply(cases ip; simp)
                subgoal for a b c
                  apply auto
                  using w_eq' w_not'
                  by argo
                done
              done
            subgoal
              unfolding H1_6
              unfolding conf_comp_def
              apply auto
              subgoal
                apply(simp only: record_help)
                unfolding fun_upd_def if_distrib H1_4 conf_comp_def p_def BENQ_def w_eq'
                apply(subst if_distribR)+
                apply(rule lambda_helper)
                apply(rule allI)
                subgoal for wt
                  apply(cases "wt = work_respons c1' n"; simp)
                  subgoal
                    apply(simp only: simp_thms if_True)
                    apply(rule lambda_helper)
                    apply(rule allI)
                    subgoal for wt'
                      apply(cases "wt' = work_respons c1' m"; simp)
                      subgoal
                        using wire_some'
                        apply(simp only: simp_thms if_True)
                        apply(rule lambda_helper)
                        apply(rule allI)
                        subgoal for wa
                          apply(cases wa; simp)
                          subgoal for wa1 wa2 wa3
                            apply(cases wa1; simp)
                            done
                          done
                        done
                      subgoal
                        by presburger
                      done
                    done
                  subgoal
                    by presburger
                  done
                done
              subgoal
                unfolding op'_def map_op_comp_def
                apply(simp only: record_help)
                by fastforce
                done
              done
            done
        qed
      qed
    qed
  qed
qed
qed


definition conf_loop :: "('op \<rightharpoonup> 'ip) \<Rightarrow> ('w \<Rightarrow> 'ip \<times> (nat \<times> nat) \<Rightarrow> 'd buf) \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> 'ip \<times> (nat \<times> nat) \<Rightarrow> 'd buf) \<Rightarrow> ('w, 'ip, 'op, 'd) conf \<Rightarrow> ('w, 'ip, 'op, 'd) conf" where
  "conf_loop wire buf msg' c = \<lparr> 
    msg = (\<lambda>w w' ip. (case ip of (ip',n,m) \<Rightarrow> if (\<exists>q. used_wire c q = Some ip') then msg c w w' ip else msg' w w' ip)),
    ops = (\<lambda>w. loop_op (simp_wire' wire (work_respons c)) (buf w) (ops c w)),
    used_wire = (\<lambda>op. (case (used_wire c op, wire op) of
        (Some ip, _) \<Rightarrow> Some ip
        | (None, Some ip) \<Rightarrow> Some ip
        | (None, None) \<Rightarrow> None)),
    work_respons = work_respons c
\<rparr>"

lemma loop_spec :
  assumes c_spec: "step_spec_conf c"
  shows "step_spec_conf ((conf_loop wire buf' msg' c) :: ('w, 'ip, 'op, 'd) conf)"
proof (coinduct rule: step_spec_conf.coinduct [where X = "\<lambda>c1. \<exists> wire buf' msg' c c_msg. step_spec_conf c \<and> c1 = conf_loop wire buf' msg' c\<lparr>msg := c_msg\<rparr>"])
  show "\<exists>wirea buf'a msg'a ca c_msg. step_spec_conf ca \<and> conf_loop wire buf' msg' c = conf_loop wirea buf'a msg'a ca\<lparr>msg := c_msg\<rparr>"
    using assms
    apply -
    apply(rule exI[where x = wire])
    apply(rule exI[where x = "buf'"])
    apply(rule exI[where x = "msg'"])
    apply(rule exI[where x = "c"])
    apply(rule exI[where x = "msg (conf_loop wire buf' msg' c)"])
    by fastforce
next
  fix c1 :: "('w, 'ip, 'op, 'd) conf"
  assume "\<exists>wire buf' msg' c c_msg. step_spec_conf c \<and> c1 = conf_loop wire buf' msg' c\<lparr>msg := c_msg\<rparr>"
  then obtain wire buf' msg' c c_msg where c_spec: "step_spec_conf c" and c1_def: "c1 = conf_loop wire buf' msg' c\<lparr>msg := c_msg\<rparr>"
    by blast
  show "\<exists>c. c1 = c \<and> (\<forall>x xa xb. step Tau (ops c xa) x \<longrightarrow> (\<exists>wire buf' msg' ca c_msg. step_spec_conf ca \<and> c\<lparr>ops := (ops c)(xa := x), msg := xb\<rparr> = conf_loop wire buf' msg' ca\<lparr>msg := c_msg\<rparr>) \<or> step_spec_conf (c\<lparr>ops := (ops c)(xa := x), msg := xb\<rparr>)) \<and> (\<forall>x xa xb xc xd xe xf. step (Inp (x, xa, xb) xc) (ops c xd) xe \<longrightarrow> work_respons c xb = xd \<and> ((\<exists>wire buf' msg' ca c_msg. step_spec_conf ca \<and> c\<lparr>ops := (ops c)(xd := xe), msg := xf\<rparr> = conf_loop wire buf' msg' ca\<lparr>msg := c_msg\<rparr>) \<or> step_spec_conf (c\<lparr>ops := (ops c)(xd := xe), msg := xf\<rparr>))) \<and> (\<forall>x xa xb xc xd xe xf. step (Out (x, xa, xb) xc) (ops c xd) xe \<longrightarrow> work_respons c xa = xd \<and> ((\<exists>wire buf' msg' ca c_msg. step_spec_conf ca \<and> c\<lparr>ops := (ops c)(xd := xe), msg := xf\<rparr> = conf_loop wire buf' msg' ca\<lparr>msg := c_msg\<rparr>) \<or> step_spec_conf (c\<lparr>ops := (ops c)(xd := xe), msg := xf\<rparr>)))"
  proof (rule exI [where x = c1] , rule conjI , rule refl , (rule conjI ; (rule conjI) ? ; (rule allI) + ; rule impI))
    fix op :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) op"
      and w :: 'w
      and msg1 :: "'w \<Rightarrow> 'w \<Rightarrow> 'ip \<times> nat \<times> nat \<Rightarrow> 'd buf"
    assume Step: "step Tau (ops c1 w) op"
    consider "\<exists>op''. op = loop_op (simp_wire' wire (work_respons c)) (buf' w) op'' \<and>  step Tau (ops c w) op''" | 
          "\<exists>op'' p x. p \<in> ran (simp_wire' wire (work_respons c)) \<and> op = loop_op (simp_wire' wire (work_respons c)) (BTL p (buf' w)) op'' \<and>
               step (Inp p x) (ops c w) op'' \<and> buf' w p \<noteq> [] \<and> BHD p (buf' w) = x" |
          "\<exists>op'' p q x. simp_wire' wire (work_respons c) p = Some q \<and> op = loop_op (simp_wire' wire (work_respons c)) (BENQ q x (buf' w)) op'' \<and>
             step (Out p x) (ops c w) op''"
      using Step
      unfolding c1_def conf_loop_def
      apply simp
      apply(drule step_loop_op_elim; simp)
      apply fast+
      done
    then show "(\<exists>wire buf' msg' ca c_msg. step_spec_conf ca \<and> c1\<lparr>ops := (ops c1)(w := op), msg := msg1\<rparr> = conf_loop wire buf' msg' ca\<lparr>msg := c_msg\<rparr>) \<or> step_spec_conf (c1\<lparr>ops := (ops c1)(w := op), msg := msg1\<rparr>)"
    proof(cases, goal_cases l_Tau l_Inp l_Out)
      case l_Tau
      obtain op'' where op_def: "op = loop_op (simp_wire' wire (work_respons c)) (buf' w) op''" and Step': "step Tau (ops c w) op''"
        using l_Tau
        by blast
      show ?case
        apply(rule disjI1)
        apply(rule exI[where x = wire])
        apply(rule exI[where x = "buf'"])
        apply(rule exI[where x = msg'])
        apply(rule exI[where x = "c\<lparr>ops := (ops c)(w := op'')\<rparr>"])
        apply(rule exI[where x = msg1])
        unfolding op_def
        apply(safe)
        subgoal
          using c_spec Step'
          unfolding step_spec_conf.simps[where a = c]
          apply -
          apply auto
          apply(erule allE[where x = op''])
          apply(erule allE[where x = w])
          apply(erule impE, assumption)
          apply(erule allE[where x = "msg (c\<lparr>ops := (ops c)(w := op'')\<rparr>)"])
          by simp
        subgoal
          unfolding c1_def
          unfolding fun_upd_def if_distrib
          apply auto
          unfolding conf_loop_def
          apply auto
          done
        done
    next
      case l_Inp
      obtain op'' p x where wire_some: "p \<in> ran (simp_wire' wire (work_respons c))" and op_def: "op = loop_op (simp_wire' wire (work_respons c)) (BTL p (buf' w)) op''" and
          Step': "step (Inp p x) (ops c w) op''" and buf_nonempty: "buf' w p \<noteq> []" and buf_head: "BHD p (buf' w) = x"
        using l_Inp
        by blast
      obtain p' pn pm where p_def: "p = (p', pn, pm)"
        using prod_cases3 by blast
      show ?case
        apply(rule disjI1)
        apply(rule exI[where x = wire])
        apply(rule exI[where x = "buf'(work_respons c pm := BTL p (buf' (work_respons c pm)))"])
        apply(rule exI[where x = msg'])
        apply(rule exI[where x = "c\<lparr>ops := (ops c)(w := op'')\<rparr>"])
        apply(rule exI[where x = msg1])
        unfolding op_def
        apply(safe)
        subgoal
          using c_spec Step'
          unfolding step_spec_conf.simps[where a = c] p_def
          apply -
          apply auto
          apply(erule allE[where x = p'])
          apply(erule allE[where x = pn])
          apply(erule allE[where x = pm])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op''])
          apply(erule allE[where x = op''])
          apply(erule impE, assumption)
          apply auto
          apply(erule allE[where x = "msg (c\<lparr>ops := (ops c)(w := op'')\<rparr>)"])
          by simp
        subgoal
          unfolding c1_def
          unfolding fun_upd_def if_distrib
          apply auto
          unfolding conf_loop_def
          apply auto
          apply(simp only: record_help conf.simps)
          using c_spec local.Step' p_def step_spec_conf.cases by fastforce
          done
    next
      case l_Out
      obtain op'' p q x where wire_some: "simp_wire' wire (work_respons c) q = Some p" and op_def: "op = loop_op (simp_wire' wire (work_respons c)) (BENQ p x (buf' w)) op''" and
        Step': "step (Out q x) (ops c w) op''"
        using l_Out
        by blast
      obtain p' pn pm where p_def: "p = (p', pn, pm)"
        using prod_cases3 by blast
      obtain q' qn qm where p_def: "q = (q', qn, qm)"
        using prod_cases3 by blast
      show ?case
        apply(rule disjI1)
        apply(rule exI[where x = wire])
        apply(rule exI[where x = "buf'(work_respons c qn := BENQ p x (buf' (work_respons c qn)))"])
        apply(rule exI[where x = msg'])
        apply(rule exI[where x = "c\<lparr>ops := (ops c)(w := op'')\<rparr>"])
        apply(rule exI[where x = msg1])
        unfolding op_def
        apply(safe)
        subgoal
          using c_spec Step'
          unfolding step_spec_conf.simps[where a = c] p_def
          apply -
          apply auto
          apply(erule allE[where x = q'])
          apply(erule allE[where x = qn])
          apply(erule allE[where x = qm])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op''])
          apply(erule allE[where x = op''])
          apply(erule impE, assumption)
          apply auto
          apply(erule allE[where x = "msg (c\<lparr>ops := (ops c)(w := op'')\<rparr>)"])
          by simp
        subgoal
          unfolding c1_def
          unfolding fun_upd_def if_distrib
          apply auto
          unfolding conf_loop_def
          apply auto
          apply(simp only: record_help conf.simps)
          using c_spec local.Step' p_def step_spec_conf.cases by fastforce
        done
    qed
  next
    fix p :: 'ip
      and pn :: nat
      and pm :: nat
      and x :: 'd
      and w :: 'w
      and op :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) op"
      and msg1 :: "'w \<Rightarrow> 'w \<Rightarrow> 'ip \<times> nat \<times> nat \<Rightarrow> 'd buf"
    assume Step: "step (Inp (p, pn, pm) x) (ops c1 w) op"
    obtain p' op'' where wire_no: "p' \<notin> ran (simp_wire' wire (work_respons c))" and p'_def: "p' = (p, pn, pm)" and
      op_def: "op = loop_op (simp_wire' wire (work_respons c)) (buf' w) op''" and Step': "step (Inp p' x) (ops c w) op''"
      using Step
      unfolding c1_def conf_loop_def
      apply simp
      apply(drule step_loop_op_elim; simp)
      done
    have w_def: "w = work_respons c1 pm"
      using Step' c_spec
      unfolding c1_def conf_loop_def p'_def
      apply simp
      by (metis step_spec_conf.cases)
    show "work_respons c1 pm = w \<and> ((\<exists>wire buf' msg' ca c_msg. step_spec_conf ca \<and> c1\<lparr>ops := (ops c1)(w := op), msg := msg1\<rparr> = conf_loop wire buf' msg' ca\<lparr>msg := c_msg\<rparr>) \<or> step_spec_conf (c1\<lparr>ops := (ops c1)(w := op), msg := msg1\<rparr>))"
      unfolding w_def
      apply(rule conjI, rule refl)
      apply(rule disjI1)
      apply(rule exI[where x = wire])
      apply(rule exI[where x = "buf'"])
      apply(rule exI[where x = msg'])
      apply(rule exI[where x = "c\<lparr>ops := (ops c)(w := op'')\<rparr>"])
      apply(rule exI[where x = msg1])
      unfolding op_def
      apply(safe)
      subgoal
        using c_spec Step'
        unfolding step_spec_conf.simps[where a = c] p'_def
        apply -
        apply auto
        apply(erule allE[where x = p])
        apply(erule allE[where x = pn])
        apply(erule allE[where x = pm])
        apply(erule allE[where x = x])
        apply(erule allE[where x = w])
        apply(erule allE[where x = op''])
        apply(erule allE[where x = op''])
        apply(erule impE, assumption)
        apply auto
        apply(erule allE[where x = "msg (c\<lparr>ops := (ops c)(w := op'')\<rparr>)"])
        by simp
      subgoal
        unfolding c1_def
        unfolding fun_upd_def if_distrib
        apply auto
        unfolding conf_loop_def
        apply auto
        apply(simp only: record_help conf.simps)
        using c_spec local.Step' p'_def step_spec_conf.cases by fastforce
      done
  next
    fix q :: 'op
      and qn :: nat
      and qm :: nat
      and x :: 'd
      and w :: 'w
      and op :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) op"
      and msg1 :: "'w \<Rightarrow> 'w \<Rightarrow> 'ip \<times> nat \<times> nat \<Rightarrow> 'd buf"
    assume Step: "step (Out (q, qn, qm) x) (ops c1 w) op"
    obtain q' op'' where wire_some: "simp_wire' wire (work_respons c) q' = None" and q'_def: "q' = (q, qn, qm)" and 
      op_def: "op = loop_op (simp_wire' wire (work_respons c)) (buf' w) op''" and Step': "step (Out q' x) (ops c w) op''"
      using Step
      unfolding c1_def conf_loop_def
      apply simp
      apply(drule step_loop_op_elim; simp)
      done
    have w_def: "w = work_respons c1 qn"
      using Step' c_spec
      unfolding c1_def conf_loop_def q'_def
      apply simp
      by (metis step_spec_conf.cases)
    show "work_respons c1 qn = w \<and> ((\<exists>wire buf' msg' ca c_msg. step_spec_conf ca \<and> c1\<lparr>ops := (ops c1)(w := op), msg := msg1\<rparr> = conf_loop wire buf' msg' ca\<lparr>msg := c_msg\<rparr>) \<or> step_spec_conf (c1\<lparr>ops := (ops c1)(w := op), msg := msg1\<rparr>))"
      unfolding w_def
      apply(rule conjI, rule refl)
      apply(rule disjI1)
      apply(rule exI[where x = wire])
      apply(rule exI[where x = "buf'"])
      apply(rule exI[where x = msg'])
      apply(rule exI[where x = "c\<lparr>ops := (ops c)(w := op'')\<rparr>"])
      apply(rule exI[where x = msg1])
      unfolding op_def
      apply(safe)
      subgoal
        using c_spec Step'
        unfolding step_spec_conf.simps[where a = c] q'_def
        apply -
        apply auto
        apply(erule allE[where x = q])
        apply(erule allE[where x = qn])
        apply(erule allE[where x = qm])
        apply(erule allE[where x = x])
        apply(erule allE[where x = w])
        apply(erule allE[where x = op''])
        apply(erule allE[where x = op''])
        apply(erule impE, assumption)
        apply auto
        apply(erule allE[where x = "msg (c\<lparr>ops := (ops c)(w := op'')\<rparr>)"])
        by simp
      subgoal
        unfolding c1_def
        unfolding fun_upd_def if_distrib
        apply auto
        unfolding conf_loop_def
        apply auto
        apply(simp only: record_help conf.simps)
        using c_spec local.Step' q'_def step_spec_conf.cases by fastforce
      done
  qed
qed


lemma loop_bisim :
  assumes bisim: "op ~d c"
      and c_spec: "step_spec_conf c"
      and buf_eq: "bufs_eq buf buf' msg' (work_respons c)"
      and wires_not_overlapping: "\<forall>p q. wire q = Some p \<longrightarrow> (used_wire c q = None \<and> (\<forall>q'. used_wire c q' \<noteq> Some p))"
    shows "(loop_op (simp_wire wire) buf op) ~d ((conf_loop wire buf' msg' c) :: ('w, 'ip, 'op, 'd) conf)"
proof (rule bisim_dis_coinduct_upto'' [where R = "\<lambda>total_op total_c. \<exists>wire buf buf' msg' op c. op ~d c \<and> step_spec_conf c \<and> bufs_eq buf buf' msg' (work_respons c) \<and> total_op = loop_op (simp_wire wire) buf op \<and> total_c = conf_loop wire buf' msg' c \<and> (\<forall>p q. wire q = Some p \<longrightarrow> (used_wire c q = None \<and> (\<forall>q'. used_wire c q' \<noteq> Some p)))"])
  show "\<exists>wirea bufa buf'a msg'a opa ca. opa ~d ca \<and> step_spec_conf ca \<and> bufs_eq bufa buf'a msg'a (work_respons ca) \<and> loop_op (simp_wire wire) buf op = loop_op (simp_wire wirea) bufa opa \<and> conf_loop wire buf' msg' c = conf_loop wirea buf'a msg'a ca \<and> (\<forall>p q. wirea q = Some p \<longrightarrow> used_wire ca q = None \<and> (\<forall>q'. used_wire ca q' \<noteq> Some p))"
    using assms
    by metis
next
  fix op :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) op"
    and c :: "('w, 'ip, 'op, 'd) conf"
    and io :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) IO"
    and op' :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) op"
  let ?P = "\<lambda>io op' c. \<exists>c'. step_dis' io c c' \<and>
            bisim_dis_cong (\<lambda>total_op total_c. \<exists>wire buf buf' msg' op c. op ~d c \<and> step_spec_conf c \<and> bufs_eq buf buf' msg' (work_respons c) \<and> total_op = loop_op (simp_wire wire) buf op \<and> total_c = conf_loop wire buf' msg' c \<and> (\<forall>p q. wire q = Some p \<longrightarrow> (used_wire c q = None \<and> (\<forall>q'. used_wire c q' \<noteq> Some p)))) op' c'"
  assume H1: "\<exists>wire buf buf' msg' opa ca. opa ~d ca \<and> step_spec_conf ca \<and> bufs_eq buf buf' msg' (work_respons ca) \<and> op = loop_op (simp_wire wire) buf opa \<and> c = conf_loop wire buf' msg' ca \<and> (\<forall>p q. wire q = Some p \<longrightarrow> used_wire ca q = None \<and> (\<forall>q'. used_wire ca q' \<noteq> Some p))"
    and Step: "step io op op'"
  obtain wire buf buf' msg' op1 c1 where H1_1: "op1 ~d c1" and H1_2: "step_spec_conf c1" and H1_3: "bufs_eq buf buf' msg' (work_respons c1)" and
    H1_4: "op = loop_op (simp_wire wire) buf op1" and H1_5: "c = conf_loop wire buf' msg' c1" and H1_6: "\<forall>p q. wire q = Some p \<longrightarrow> used_wire c1 q = None \<and> (\<forall>q'. used_wire c1 q' \<noteq> Some p)"
    using H1
    by blast
  show "?P io op' c"
  proof (rule step_loop_op_elim)
    show "step io (loop_op (simp_wire wire) buf op1) op'"
      using Step H1_4
      by meson
  next
    fix p :: "'ip \<times> nat \<times> nat"
      and x :: "'d"
      and op'' :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) op"
    assume no_wire: "p \<notin> ran (simp_wire wire)"
      and io_def: "io = Inp p x"
      and op'_def: "op' = loop_op (simp_wire wire) buf op''"
      and Step': "step io op1 op''"
    obtain p' pn pm where p_def: "p = (p',pn,pm)"
      using prod_cases3 by blast
    obtain w c1' where Step'': "step_dis w io c1 c1'" and H2: "op'' ~d c1'"
      using Step' H1_1 bisim_op_elim
      by blast
    obtain op2 where c1'_def: "c1' = c1\<lparr>ops := (ops c1)(work_respons c1 pm := op2)\<rparr>" and Step2: "step (Inp (p', pn, pm) x) (ops c1 (work_respons c1 pm)) op2" and 
        no_wire': "\<forall>q. used_wire c1 q \<noteq> Some p'" and "w = work_respons c1 pm"
      using Step'' step_dis.cases
      unfolding io_def p_def
      by blast
    have c1'_spec : "step_spec_conf c1'"
      using H1_2 Step''
      unfolding io_def p_def step_spec_conf.simps[where a = c1]
      apply -
      subgoal
        apply(drule step_dis.cases; simp)
        apply auto
        subgoal for op2
          apply(erule allE[where x = p'])
          apply(erule allE[where x = pn])
          apply(erule allE[where x = pm])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op2])
          apply(erule allE[where x = op2])
          apply auto
          apply(erule allE[where x = "msg c1"])
          by simp
        done
      done
    show "?P io op' c"
      unfolding H1_5
      apply(rule exI[where x = "conf_loop wire buf' msg' (c1\<lparr>ops := (ops c1)((work_respons c1 pm) := op2)\<rparr>)"])
      apply(rule conjI)
      subgoal
        unfolding io_def p_def
        apply(rule S[where w = "work_respons c1 pm"])
        unfolding conf_loop_def
        apply simp
        apply(rule SDR[where op' = "(loop_op (simp_wire' wire (work_respons c1)) (buf' (work_respons c1 pm)) op2)"])
        subgoal
          using Step2
          unfolding io_def p_def
          apply simp
          apply(rule step_Inp_loop_op)
          subgoal
            by simp
          subgoal
            using no_wire
            unfolding simp_wire'_def ran_def simp_wire_def p_def
            apply auto
            subgoal for a aa b
              apply(erule allE[where x = a])
              apply(erule allE[where x = aa])
              apply(erule allE[where x = b])
              apply(cases "wire a"; simp)
              apply(cases "work_respons c1 aa = work_respons c1 b"; simp)
              done
            done
          done
        subgoal
          apply auto
          apply(simp only:record_help)
          done
        subgoal
          using no_wire no_wire'
          unfolding ran_def simp_wire_def p_def
          apply auto
          subgoal for p1
            apply(cases "used_wire c1 p1"; simp)
            apply(cases "wire p1"; simp)
            apply auto
            apply(erule allE[where x = p1])
            apply(erule allE[where x = pn])
            apply(erule allE[where x = pm])
            apply auto
            done
          done
        subgoal
          by simp
        done
      subgoal
        apply(rule bc'_base)
        unfolding op'_def
        apply(rule exI[where x = "wire"])
        apply(rule exI[where x = "buf"])
        apply(rule exI[where x = "buf'"])
        apply(rule exI[where x = "msg'"])
        apply(rule exI[where x = "op''"])
        apply(rule exI[where x = "(c1\<lparr>ops := (ops c1)(work_respons c1 pm := op2)\<rparr>)"])
        apply auto
        subgoal
          using H2
          unfolding c1'_def
          by simp
        subgoal
          using c1'_spec
          unfolding c1'_def
          by simp
        subgoal
          using H1_3
          by simp
        subgoal for p q
          using H1_6
          by blast
        subgoal for p q
          using H1_6
          by blast
        done
      done
  next
    fix q :: "'op \<times> nat \<times> nat"
      and x :: "'d"
      and op'' :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) op"
    assume no_wire: "simp_wire wire q = None"
      and io_def: "io = Out q x"
      and op'_def: "op' = loop_op (simp_wire wire) buf op''"
      and Step': "step io op1 op''"
    obtain q' qn qm where q_def: "q = (q',qn,qm)"
      using prod_cases3 by blast
    obtain w c1' where Step'': "step_dis w io c1 c1'" and H2: "op'' ~d c1'"
      using Step' H1_1 bisim_op_elim
      by blast
    obtain op2 where c1'_def: "c1' = c1\<lparr>ops := (ops c1)(work_respons c1 qn := op2)\<rparr>" and Step2: "step (Out (q', qn, qm) x) (ops c1 (work_respons c1 qn)) op2" and 
        no_wire': "used_wire c1 q' = None" and "w = work_respons c1 qn"
      using Step'' step_dis.cases
      unfolding io_def q_def
      by blast
    have c1'_spec : "step_spec_conf c1'"
      using H1_2 Step''
      unfolding io_def q_def step_spec_conf.simps[where a = c1]
      apply -
      subgoal
        apply(drule step_dis.cases; simp)
        apply auto
        subgoal for op2
          apply(erule allE[where x = q'])
          apply(erule allE[where x = qn])
          apply(erule allE[where x = qm])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op2])
          apply(erule allE[where x = op2])
          apply auto
          apply(erule allE[where x = "msg c1"])
          by simp
        done
      done
    show "?P io op' c"
      unfolding H1_5
      apply(rule exI[where x = "conf_loop wire buf' msg' (c1\<lparr>ops := (ops c1)((work_respons c1 qn) := op2)\<rparr>)"])
      apply(rule conjI)
      subgoal
        unfolding io_def q_def
        apply(rule S[where w = "work_respons c1 qn"])
        unfolding conf_loop_def
        apply simp
        apply(rule SDW[where op' = "(loop_op (simp_wire' wire (work_respons c1)) (buf' (work_respons c1 qn)) op2)"])
        subgoal
          using Step2
          unfolding io_def q_def
          apply simp
          apply(rule step_Out_loop_op)
          subgoal
            by simp
          subgoal
            using no_wire
            unfolding simp_wire'_def ran_def simp_wire_def q_def
            apply auto
            apply(cases "wire q'"; simp)
            done
          subgoal
            by simp
          done
        subgoal
          apply auto
          apply(simp only:record_help)
          done
        subgoal
          using no_wire no_wire'
          unfolding ran_def simp_wire_def q_def
          apply auto
          apply(cases "wire q'"; simp)
          done
        subgoal
          by simp
        done
      subgoal
        apply(rule bc'_base)
        unfolding op'_def
        apply(rule exI[where x = "wire"])
        apply(rule exI[where x = "buf"])
        apply(rule exI[where x = "buf'"])
        apply(rule exI[where x = "msg'"])
        apply(rule exI[where x = "op''"])
        apply(rule exI[where x = "(c1\<lparr>ops := (ops c1)(work_respons c1 qn := op2)\<rparr>)"])
        apply auto
        subgoal
          using H2
          unfolding c1'_def
          by simp
        subgoal
          using c1'_spec
          unfolding c1'_def
          by simp
        subgoal
          using H1_3
          by simp
        subgoal for q
          using H1_6
          by blast
        subgoal for p q
          using H1_6
          by blast
        done
      done
  next
    fix op'' :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) op"
    assume io_def: "io = Tau"
      and op'_def: "op' = loop_op (simp_wire wire) buf op''"
      and Step': "step io op1 op''"
    obtain w c1' where Step'': "step_dis w io c1 c1'" and H2: "op'' ~d c1'"
      using Step' H1_1 bisim_op_elim
      by blast
    have c1'_spec : "step_spec_conf c1'"
      using H1_2 Step''
      unfolding io_def step_spec_conf.simps[where a = c1]
      apply -
      subgoal
        apply(drule step_dis.cases; simp)
        apply auto
        subgoal for op2
          apply(erule allE[where x = op2])
          apply(erule allE[where x = w])
          apply auto
          apply(erule allE[where x = "msg c1"])
          by simp
        done
      done
    consider "\<exists>op'. c1' = c1\<lparr>ops := (ops c1)(w := op')\<rparr> \<and> step Tau (ops c1 w) op'" |
      "\<exists>p n m op' q. c1' = c1\<lparr>ops := (ops c1)(work_respons c1 m := op'),
            msg := (msg c1) (work_respons c1 n := (msg c1 (work_respons c1 n))
                 (work_respons c1 m := BTL (p, n, m) (msg c1 (work_respons c1 n) (work_respons c1 m))))\<rparr> \<and>
       step (Inp (p, n, m) (bhd (msg c1 (work_respons c1 n) (work_respons c1 m) (p, n, m)))) (ops c1 (work_respons c1 m)) op' \<and>
       work_respons c1 m \<noteq> work_respons c1 n \<and> msg c1 (work_respons c1 n) (work_respons c1 m) (p, n, m) \<noteq> [] \<and>
       w = work_respons c1 m \<and> used_wire c1 q = Some p" |
      "\<exists>q n m x op' p. c1' = c1\<lparr>ops := (ops c1)(work_respons c1 n := op'),
            msg := (msg c1) (work_respons c1 n := (msg c1 (work_respons c1 n))
                 (work_respons c1 m := BENQ (p, n, m) x (msg c1 (work_respons c1 n) (work_respons c1 m))))\<rparr> \<and>
       step (Out (q, n, m) x) (ops c1 (work_respons c1 n)) op' \<and> used_wire c1 q = Some p \<and>
       work_respons c1 m \<noteq> work_respons c1 n \<and> w = work_respons c1 n"
      using Step''
      unfolding io_def
      apply -
      apply(drule step_dis.cases; simp)
        apply fast+
      done
    then show "?P io op' c"
    proof(cases, goal_cases Tau_Internal Tau_Msg_Rec Tau_Msg_Send)
      case Tau_Internal
      obtain op2 where c1'_def: "c1' = c1\<lparr>ops := (ops c1)(w := op2)\<rparr>" and Step2: "step Tau (ops c1 w) op2"
        using Tau_Internal
        by blast
      show ?case
        unfolding H1_5
        apply(rule exI[where x = "conf_loop wire buf' msg' (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"])
        apply(rule conjI)
        subgoal
          unfolding io_def
          apply(rule S[where w = "w"])
          unfolding conf_loop_def
          apply simp
          apply(rule SDT[where op' = "(loop_op (simp_wire' wire (work_respons c1)) (buf' w) op2)"])
          subgoal
            using Step2
            unfolding io_def
            apply simp
            apply(rule step_Tau_loop_op)
            subgoal
              by simp
            subgoal
              by simp
            done
          subgoal
            apply auto
            apply(simp only:record_help)
            done
          done
        subgoal
          apply(rule bc'_base)
          unfolding op'_def
          apply(rule exI[where x = "wire"])
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "buf'"])
          apply(rule exI[where x = "msg'"])
          apply(rule exI[where x = "op''"])
          apply(rule exI[where x = "(c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"])
          apply auto
          subgoal
            using H2
            unfolding c1'_def
            by simp
          subgoal
            using c1'_spec
            unfolding c1'_def
            by simp
          subgoal
            using H1_3
            by simp
          subgoal for q
            using H1_6
            by blast
          subgoal for p q
            using H1_6
            by blast
          done
        done
    next
      case Tau_Msg_Rec
      obtain p n m op2 q where c1'_def: "c1' = c1\<lparr>ops := (ops c1)(work_respons c1 m := op2),
          msg := (msg c1) (work_respons c1 n := (msg c1 (work_respons c1 n))
               (work_respons c1 m := BTL (p, n, m) (msg c1 (work_respons c1 n) (work_respons c1 m))))\<rparr>" and
        Step2: "step (Inp (p, n, m) (bhd (msg c1 (work_respons c1 n) (work_respons c1 m) (p, n, m)))) (ops c1 (work_respons c1 m)) op2" and
        work_noteq: "work_respons c1 m \<noteq> work_respons c1 n" and msg_nonempty: "msg c1 (work_respons c1 n) (work_respons c1 m) (p, n, m) \<noteq> []" and
        w_def: "w = work_respons c1 m" and some_wire: "used_wire c1 q = Some p"
        using Tau_Msg_Rec
        by blast
      show ?case
        unfolding H1_5
        apply(rule exI[where x = "conf_loop wire buf' msg' c1'"])
        apply(rule conjI)
        subgoal
          unfolding io_def
          apply(rule S[where w = "work_respons c1 m"])
          unfolding conf_loop_def
          apply simp
          apply(rule SDTR[where p = p and n = n and m = m and w = "(work_respons c1 n)" and op' = "(loop_op (simp_wire' wire (work_respons c1)) (buf' (work_respons c1 m)) op2)"])
          subgoal
            using Step2 some_wire
            unfolding io_def
            apply simp
            apply auto
            unfolding ran_def
            apply auto
            unfolding simp_wire'_def
            apply auto
            subgoal for q' a aa b
              apply(cases "wire a"; simp)
              subgoal for ab
                apply(cases "work_respons c1 aa = work_respons c1 b"; simp)
                using work_noteq
                by presburger
              done
            done
          subgoal
            unfolding c1'_def
            apply auto
            apply(simp only:record_help)
            unfolding fun_upd_def if_distrib H1_4 conf_loop_def BTL_def
            apply(subst if_distribR)+
            apply(rule lambda_helper)
            apply(rule allI)
            subgoal for wt
              apply(cases "wt = work_respons c1 n"; simp)
              subgoal
                apply(simp only: simp_thms if_True)
                apply(rule lambda_helper)
                apply(rule allI)
                subgoal for wt'
                  apply(cases "wt' = work_respons c1 m"; simp)
                  subgoal
                    using some_wire
                    apply(simp only: simp_thms if_True)
                    apply(rule lambda_helper)
                    apply(rule allI)
                    subgoal for wa
                      apply(cases wa; simp)
                      subgoal for wa1 wa2 wa3
                        apply auto
                        done
                      done
                    done
                  subgoal
                    by presburger
                  done
                done
              subgoal
                by presburger
              done
            done
          subgoal
            using some_wire
            apply -
            apply(rule exI[where x = q])
            apply auto
            done
          subgoal
            using work_noteq
            by simp
          subgoal
            apply auto
            done
          subgoal
            apply auto
            done
          subgoal
            using some_wire msg_nonempty
            using H1_6
            apply auto
            done
          done
        subgoal
          apply(rule bc'_base)
          unfolding op'_def
          apply(rule exI[where x = "wire"])
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "buf'"])
          apply(rule exI[where x = "msg'"])
          apply(rule exI[where x = "op''"])
          apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(work_respons c1 m := op2),
       msg := (msg c1)(work_respons c1 n := (msg c1 (work_respons c1 n))(work_respons c1 m := BTL (p, n, m) (msg c1 (work_respons c1 n) (work_respons c1 m))))\<rparr>"])
          apply auto
          subgoal
            using H2
            unfolding c1'_def
            by simp
          subgoal
            using c1'_spec
            unfolding c1'_def
            by simp
          subgoal
            using H1_3
            by simp
          subgoal
            unfolding c1'_def
            by simp
          subgoal for q
            using H1_6
            by blast
          subgoal for p q
            using H1_6
            by blast
          done
        done
    next
      case Tau_Msg_Send
      obtain q n m x op2 p where c1'_def: "c1' = c1\<lparr>ops := (ops c1)(work_respons c1 n := op2),
          msg := (msg c1)(work_respons c1 n := (msg c1 (work_respons c1 n))(work_respons c1 m := BENQ (p, n, m) x (msg c1 (work_respons c1 n) (work_respons c1 m))))\<rparr>" and
        Step2: "step (Out (q, n, m) x) (ops c1 (work_respons c1 n)) op2" and some_wire: "used_wire c1 q = Some p" and 
        work_noteq: "work_respons c1 m \<noteq> work_respons c1 n" and w_def: "w = work_respons c1 n"
        using Tau_Msg_Send
        by blast
      show ?case
        unfolding H1_5
        apply(rule exI[where x = "conf_loop wire buf' msg' c1'"])
        apply(rule conjI)
        subgoal
          unfolding io_def
          apply(rule S[where w = "work_respons c1 n"])
          unfolding conf_loop_def
          apply simp
          apply(rule SDTW[where q = q and p = p and n = n and m = m and x = x and w' = "(work_respons c1 m)" and op' = "(loop_op (simp_wire' wire (work_respons c1)) (buf' (work_respons c1 n)) op2)"])
          subgoal
            using Step2 some_wire
            unfolding io_def
            apply simp
            apply auto
            using H1_6
            unfolding simp_wire'_def
            apply auto
            apply(cases "wire q"; simp)
            done
          subgoal
            unfolding c1'_def
            apply auto
            apply(simp only:record_help)
            unfolding fun_upd_def if_distrib H1_4 conf_loop_def BENQ_def
            apply(subst if_distribR)+
            apply(rule lambda_helper)
            apply(rule allI)
            subgoal for wt
              apply(cases "wt = work_respons c1 n"; simp)
              subgoal
                apply(simp only: simp_thms if_True)
                apply(rule lambda_helper)
                apply(rule allI)
                subgoal for wt'
                  apply(cases "wt' = work_respons c1 m"; simp)
                  subgoal
                    using some_wire
                    apply(simp only: simp_thms if_True)
                    apply(rule lambda_helper)
                    apply(rule allI)
                    subgoal for wa
                      apply(cases wa; simp)
                      subgoal for wa1 wa2 wa3
                        apply auto
                        done
                      done
                    done
                  subgoal
                    by presburger
                  done
                done
              subgoal
                by presburger
              done
            done
          subgoal
            using some_wire
            apply auto
            done
          subgoal
            using work_noteq
            by simp
          subgoal
            apply auto
            done
          subgoal
            apply auto
            done
          done
        subgoal
          apply(rule bc'_base)
          unfolding op'_def
          apply(rule exI[where x = "wire"])
          apply(rule exI[where x = "buf"])
          apply(rule exI[where x = "buf'"])
          apply(rule exI[where x = "msg'"])
          apply(rule exI[where x = "op''"])
          apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(work_respons c1 n := op2),
          msg := (msg c1)(work_respons c1 n := (msg c1 (work_respons c1 n))(work_respons c1 m := BENQ (p, n, m) x (msg c1 (work_respons c1 n) (work_respons c1 m))))\<rparr>"])
          apply auto
          subgoal
            using H2
            unfolding c1'_def
            by simp
          subgoal
            using c1'_spec
            unfolding c1'_def
            by simp
          subgoal
            using H1_3
            by simp
          subgoal
            unfolding c1'_def
            by simp
          subgoal for q
            using H1_6
            by blast
          subgoal for p q
            using H1_6
            by blast
          done
        done
    qed
  next
    fix op'' :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) op"
      and p :: "'ip \<times> nat \<times> nat"
      and x :: "'d"
    assume io_def: "io = Tau"
      and some_wire: "p \<in> ran (simp_wire wire)"
      and op'_def: "op' = loop_op (simp_wire wire) (BTL p buf) op''"
      and Step': "step (Inp p x) op1 op''"
      and buf_nonempty: "buf p \<noteq> []"
      and x_def: "BHD p buf = x"
    obtain p' n m q' where some_wire': "wire q' = Some p'" and p_def: "p = (p', n, m)"
      using some_wire
      unfolding ran_def simp_wire_def
      apply auto
      subgoal for p' n m
        apply(cases "wire p'"; simp)
        apply auto
        done
      done
    obtain w c1' where Step'': "step_dis w (Inp (p', n, m) x) c1 c1'" and H2: "op'' ~d c1'"
      using Step' H1_1 bisim_op_elim p_def
      by meson
    have c1'_spec : "step_spec_conf c1'"
      using H1_2 Step''
      unfolding io_def step_spec_conf.simps[where a = c1]
      apply -
      subgoal
        apply(drule step_dis.cases; simp)
        apply auto
        subgoal for op2
          apply(erule allE[where x = p'])
          apply(erule allE[where x = n])
          apply(erule allE[where x = m])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op2])
          apply(erule allE[where x = op2])
          apply auto
          apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"])
          by simp
        done
      done
    obtain op2 where c1'_def: "c1' = c1\<lparr>ops := (ops c1)(work_respons c1 m := op2)\<rparr>" and 
          Step2: "step (Inp (p', n, m) x) (ops c1 (work_respons c1 m)) op2" and no_wire: "\<forall>q. used_wire c1 q \<noteq> Some p'" and w_def: "w = work_respons c1 m"
      using Step''
      apply -
      apply(erule step_dis.cases)
          apply blast+
      done
    consider "work_respons c1 n = work_respons c1 m" | "work_respons c1 n \<noteq> work_respons c1 m"
      by blast
    then show "?P io op' c"
    proof(cases, goal_cases work_eq work_noteq)
      case work_eq
      show ?case 
        unfolding H1_5
        apply(rule exI[where x = "conf_loop wire (buf'((work_respons c1 m) := (BTL p (buf' (work_respons c1 m))))) msg' c1'"])
        apply(rule conjI)
        subgoal
          unfolding io_def
          apply(rule S[where w = "work_respons c1 m"])
          unfolding conf_loop_def
          apply simp
          apply(rule SDT[where op' = "(loop_op (simp_wire' wire (work_respons c1)) (BTL p (buf' (work_respons c1 m))) op2)"])
          subgoal
            using Step2 some_wire p_def work_eq
            unfolding io_def x_def[symmetric]
            apply simp
            apply(rule step_Inp_Tau_loop_op[where x = "(BHD (p', n, m) buf)" and p = "(p', n, m)"])
                apply auto
            subgoal
              unfolding ran_def simp_wire_def simp_wire'_def
              apply auto
              subgoal for a aa b
                apply(cases "wire a"; simp)
                apply(rule exI[where x = a])
                apply(rule exI[where x = aa])
                apply(rule exI[where x = b])
                apply auto
                done
              done
            subgoal
              using buf_nonempty H1_3 some_wire' 
              unfolding ran_def bufs_eq_def
              apply auto
              done
            subgoal
              using buf_nonempty H1_3 some_wire' 
              unfolding ran_def bufs_eq_def BHD_def
              apply simp
              done
            done
          subgoal
            unfolding c1'_def
            apply auto
            apply(simp only:record_help)
            done
          done
        subgoal
          apply(rule bc'_base)
          unfolding op'_def
          apply(rule exI[where x = "wire"])
          apply(rule exI[where x = "(BTL p buf)"])
          apply(rule exI[where x = "(buf'((work_respons c1 m) := (BTL p (buf' (work_respons c1 m)))))"])
          apply(rule exI[where x = "msg'"])
          apply(rule exI[where x = "op''"])
          apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(work_respons c1 m := op2)\<rparr>"])
          apply auto
          subgoal
            using H2
            unfolding c1'_def
            by simp
          subgoal
            using c1'_spec
            unfolding c1'_def
            by simp
          subgoal
            using H1_3 work_eq
            unfolding bufs_eq_def BTL_def p_def
            apply safe
            subgoal for a aa b
              apply(erule allE[where x = "(a,aa,b)"])
              apply auto
              done
            done
          subgoal
            unfolding c1'_def
            by simp
          subgoal for q
            using H1_6
            by blast
          subgoal for p q
            using H1_6
            by blast
          done
        done
    next
      case work_noteq
      show ?case 
        unfolding H1_5
        apply(rule exI[where x = "conf_loop wire buf' (msg'(work_respons c1 n := (msg' (work_respons c1 n))(work_respons c1 m := BTL p (msg' (work_respons c1 n) (work_respons c1 m))))) c1'"])
        apply(rule conjI)
        subgoal
          unfolding io_def
          apply(rule S[where w = "work_respons c1 m"])
          unfolding conf_loop_def
          apply simp
          apply(rule SDTR[where p = p' and n = n and m = m and w = "work_respons c1 n" and op' = "(loop_op (simp_wire' wire (work_respons c1)) (buf' (work_respons c1 m)) op2)"])
          subgoal
            using Step2 some_wire' p_def work_noteq H1_6
            unfolding io_def x_def[symmetric] BHD_def
            apply simp
            apply(rule step_Inp_loop_op)
                apply auto
            subgoal
              using H1_3 work_noteq
              unfolding bufs_eq_def 
              unfolding ran_def simp_wire_def simp_wire'_def
              apply auto
              done
            subgoal
              unfolding ran_def simp_wire'_def
              apply auto
              subgoal for a aa b
                apply(cases "wire a"; simp)
                subgoal for ba
                  apply(cases "work_respons c1 aa = work_respons c1 b"; simp)
                  done
                done
              done
            done
          subgoal
            unfolding c1'_def
            apply auto
            apply(simp only:record_help)
            unfolding fun_upd_def if_distrib H1_4 conf_loop_def BTL_def p_def
            apply(subst if_distribR)+
            apply(rule lambda_helper)
            apply(rule allI)
            subgoal for wt
              apply(cases "wt = work_respons c1 n"; simp)
              subgoal
                apply(simp only: simp_thms if_True)
                apply(rule lambda_helper)
                apply(rule allI)
                subgoal for wt'
                  apply(cases "wt' = work_respons c1 m"; simp)
                  subgoal
                    using no_wire
                    apply(simp only: simp_thms if_True)
                    apply(rule lambda_helper)
                    apply(rule allI)
                    subgoal for wa
                      apply(cases "wa = (p', n, m)"; simp)
                      done
                    done
                  subgoal
                    by presburger
                  done
                done
              subgoal
                by presburger
              done
            done
          subgoal
            using some_wire' no_wire H1_6
            apply auto
            apply(rule exI[where x = q'])
            apply(cases "used_wire c1 q'"; simp)
            done
          subgoal
            using work_noteq
            by simp
          subgoal
            apply auto
            done
          subgoal
            apply auto
            done
          subgoal
            using buf_nonempty no_wire H1_3 work_noteq
            unfolding bufs_eq_def p_def
            apply auto
            done
          done
        subgoal
          apply(rule bc'_base)
          unfolding op'_def
          apply(rule exI[where x = "wire"])
          apply(rule exI[where x = "(BTL p buf)"])
          apply(rule exI[where x = "buf'"])
          apply(rule exI[where x = "(msg'(work_respons c1 n := (msg' (work_respons c1 n))(work_respons c1 m := BTL p (msg' (work_respons c1 n) (work_respons c1 m)))))"])
          apply(rule exI[where x = "op''"])
          apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(work_respons c1 m := op2)\<rparr>"])
          apply auto
          subgoal
            using H2
            unfolding c1'_def
            by simp
          subgoal
            using c1'_spec
            unfolding c1'_def
            by simp
          subgoal
            using H1_3 work_noteq
            unfolding bufs_eq_def BTL_def p_def
            apply safe
            subgoal for a aa b
              apply(erule allE[where x = "(a,aa,b)"])
              apply auto
              done
            done
          subgoal
            unfolding c1'_def
            by simp
          subgoal for q
            using H1_6
            by blast
          subgoal for p q
            using H1_6
            by blast
          done
        done
    qed
  next
    fix op'' :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) op"
      and q :: "'op \<times> nat \<times> nat"
      and p :: "'ip \<times> nat \<times> nat"
      and x :: "'d"
    assume io_def: "io = Tau"
      and some_wire: "simp_wire wire q = Some p"
      and op'_def: "op' = loop_op (simp_wire wire) (BENQ p x buf) op''"
      and Step': "step (Out q x) op1 op''"
    obtain p' n m q' where some_wire': "wire q' = Some p'" and p_def: "p = (p', n, m)" and q_def: "q = (q', n, m)"
      using some_wire
      unfolding ran_def simp_wire_def
      apply(cases q; simp)
      subgoal for q' n m
        apply(cases "wire q'"; simp)
        done
      done
    have no_used_wire: "\<not>(\<exists>q'. used_wire c1 q' = Some p')"
      using H1_6 some_wire'
      by fast
    obtain w c1' where Step'': "step_dis w (Out (q', n, m) x) c1 c1'" and H2: "op'' ~d c1'"
      using Step' H1_1 bisim_op_elim q_def
      by meson
    have c1'_spec : "step_spec_conf c1'"
      using H1_2 Step''
      unfolding io_def step_spec_conf.simps[where a = c1]
      apply -
      subgoal
        apply(drule step_dis.cases; simp)
        apply auto
        subgoal for op2
          apply(erule allE[where x = q'])
          apply(erule allE[where x = n])
          apply(erule allE[where x = m])
          apply(erule allE[where x = x])
          apply(erule allE[where x = w])
          apply(erule allE[where x = op2])
          apply(erule allE[where x = op2])
          apply auto
          apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"])
          by simp
        done
      done
    obtain op2 where c1'_def: "c1' = c1\<lparr>ops := (ops c1)(work_respons c1 n := op2)\<rparr>" and 
          Step2: "step (Out (q', n, m) x) (ops c1 (work_respons c1 n)) op2" and no_wire: "used_wire c1 q' = None" and w_def: "w = work_respons c1 n"
      using Step''
      apply -
      apply(erule step_dis.cases)
          apply blast+
      done
    consider "work_respons c1 n = work_respons c1 m" | "work_respons c1 n \<noteq> work_respons c1 m"
      by blast
    then show "?P io op' c"
    proof(cases, goal_cases work_eq work_noteq)
      case work_eq
      show ?case 
        unfolding H1_5
        apply(rule exI[where x = "conf_loop wire (buf'((work_respons c1 m) := (BENQ p x (buf' (work_respons c1 m))))) msg' c1'"])
        apply(rule conjI)
        subgoal
          unfolding io_def
          apply(rule S[where w = "work_respons c1 n"])
          unfolding conf_loop_def
          apply simp
          apply(rule SDT[where op' = "(loop_op (simp_wire' wire (work_respons c1)) (BENQ p x (buf' (work_respons c1 m))) op2)"])
          subgoal
            using Step2 some_wire p_def work_eq
            unfolding io_def
            apply simp
            apply(rule step_Out_Tau_loop_op[where p = "(q',n,m)" and q = p and x = x])
              apply auto
            using some_wire'
            unfolding simp_wire'_def
            apply auto
            done
          subgoal
            unfolding c1'_def
            apply auto
             apply(simp only:record_help)
            using H1_3
            unfolding bufs_eq_def work_eq
            apply auto
            done
          done
        subgoal
          apply(rule bc'_base)
          unfolding op'_def
          apply(rule exI[where x = "wire"])
          apply(rule exI[where x = "(BENQ p x buf)"])
          apply(rule exI[where x = "(buf'((work_respons c1 m) := (BENQ p x (buf' (work_respons c1 m)))))"])
          apply(rule exI[where x = "msg'"])
          apply(rule exI[where x = "op''"])
          apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(work_respons c1 n := op2)\<rparr>"])
          apply auto
          subgoal
            using H2
            unfolding c1'_def
            by simp
          subgoal
            using c1'_spec
            unfolding c1'_def
            by simp
          subgoal
            using H1_3 work_eq
            unfolding bufs_eq_def BENQ_def p_def
            apply safe
            subgoal for a aa b
              apply(erule allE[where x = "(a,aa,b)"])
              apply auto
              done
            done
          subgoal
            unfolding c1'_def
            by simp
          subgoal for q
            using H1_6
            by blast
          subgoal for p q
            using H1_6
            by blast
          done
        done
    next
      case work_noteq
      show ?case 
        unfolding H1_5
        apply(rule exI[where x = "conf_loop wire buf' (msg'(work_respons c1 n := (msg' (work_respons c1 n))(work_respons c1 m := BENQ p x (msg' (work_respons c1 n) (work_respons c1 m))))) c1'"])
        apply(rule conjI)
        subgoal
          unfolding io_def
          apply(rule S[where w = "work_respons c1 n"])
          unfolding conf_loop_def
          apply simp
          apply(rule SDTW[where q = q' and n = n and m = m and x = x and p = p' and w' = "work_respons c1 m" and op' = "(loop_op (simp_wire' wire (work_respons c1)) (buf' (work_respons c1 n)) op2)"])
          subgoal
            using Step2 some_wire' p_def work_noteq H1_6
            unfolding io_def BENQ_def
            apply simp
            apply(rule step_Out_loop_op)
                apply auto
            subgoal
              using H1_3 work_noteq
              unfolding bufs_eq_def 
              unfolding ran_def simp_wire_def simp_wire'_def
              apply auto
              done
            done
          subgoal
            unfolding c1'_def
            apply auto
            apply(simp only:record_help)
            unfolding fun_upd_def if_distrib H1_4 conf_loop_def BENQ_def p_def
            apply(subst if_distribR)+
            apply(rule lambda_helper)
            apply(rule allI)
            subgoal for wt
              apply(cases "wt = work_respons c1 n"; simp)
              subgoal
                apply(simp only: simp_thms if_True)
                apply(rule lambda_helper)
                apply(rule allI)
                subgoal for wt'
                  apply(cases "wt' = work_respons c1 m"; simp)
                  subgoal
                    using no_wire no_used_wire
                    apply(simp only: simp_thms if_True)
                    apply(rule lambda_helper)
                    apply(rule allI)
                    subgoal for wa
                      apply(cases "wa = (p', n, m)"; simp)
                      done
                    done
                  subgoal
                    by presburger
                  done
                done
              subgoal
                by presburger
              done
            done
          subgoal
            using some_wire' no_wire H1_6
            apply auto
            done
          subgoal
            using work_noteq
            by simp
          subgoal
            apply auto
            done
          subgoal
            apply auto
            done
          done
        subgoal
          apply(rule bc'_base)
          unfolding op'_def
          apply(rule exI[where x = "wire"])
          apply(rule exI[where x = "(BENQ p x buf)"])
          apply(rule exI[where x = "buf'"])
          apply(rule exI[where x = "(msg'(work_respons c1 n := (msg' (work_respons c1 n))(work_respons c1 m := BENQ p x (msg' (work_respons c1 n) (work_respons c1 m)))))"])
          apply(rule exI[where x = "op''"])
          apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(work_respons c1 n := op2)\<rparr>"])
          apply auto
          subgoal
            using H2
            unfolding c1'_def
            by simp
          subgoal
            using c1'_spec
            unfolding c1'_def
            by simp
          subgoal
            using H1_3 work_noteq
            unfolding bufs_eq_def BENQ_def p_def
            apply safe
            subgoal for a aa b
              apply(erule allE[where x = "(a,aa,b)"])
              apply auto
              done
            done
          subgoal
            unfolding c1'_def
            by simp
          subgoal for q
            using H1_6
            by blast
          subgoal for p q
            using H1_6
            by blast
          done
        done
    qed
  qed
next
  fix op :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) op"
    and c :: "('w, 'ip, 'op, 'd) conf"
    and io :: "('ip \<times> nat \<times> nat, 'op \<times> nat \<times> nat, 'd) IO"
    and c' :: "('w, 'ip, 'op, 'd) conf"
  let ?Q = "\<exists>op'. step io op op' \<and>
             bisim_dis_cong
              (\<lambda>total_op total_c.
                  \<exists>wire buf buf' msg' op c.
                     op ~d c \<and>
                     step_spec_conf c \<and>
                     bufs_eq buf buf' msg' (work_respons c) \<and>
                     total_op = loop_op (simp_wire wire) buf op \<and>
                     total_c = conf_loop wire buf' msg' c \<and> (\<forall>p q. wire q = Some p \<longrightarrow> used_wire c q = None \<and> (\<forall>q'. used_wire c q' \<noteq> Some p)))
              op' c'"
  assume H1: "\<exists>wire buf buf' msg' opa ca.
          opa ~d ca \<and>
          step_spec_conf ca \<and>
          bufs_eq buf buf' msg' (work_respons ca) \<and>
          op = loop_op (simp_wire wire) buf opa \<and>
          c = conf_loop wire buf' msg' ca \<and> (\<forall>p q. wire q = Some p \<longrightarrow> used_wire ca q = None \<and> (\<forall>q'. used_wire ca q' \<noteq> Some p))"
    and Step: "step_dis' io c c'"
  obtain wire buf buf' msg' op1 c1 where H1_1: "op1 ~d c1" and c1_spec: "step_spec_conf c1" and H1_2: "bufs_eq buf buf' msg' (work_respons c1)" and
    op_def: "op = loop_op (simp_wire wire) buf op1" and c_def: "c = conf_loop wire buf' msg' c1" and
    H1_3: "(\<forall>p q. wire q = Some p \<longrightarrow> used_wire c1 q = None \<and> (\<forall>q'. used_wire c1 q' \<noteq> Some p))"
    using H1
    by blast
  obtain w where Step': "step_dis w io c c'"
    using Step
    by (metis step_dis'.cases)
  show "?Q"
  proof (cases io)
    fix p :: "'ip \<times> nat \<times> nat"
      and x :: 'd
    assume io_def: "io = Inp p x"
    obtain p' n m op' where p_def: "p = (p', n, m)" and c'_def: "c' = c\<lparr>ops := (ops c)(work_respons c m := op')\<rparr>" and
      Step'': "step (Inp (p', n, m) x) (ops c (work_respons c m)) op'" and no_wire: "\<forall>q. used_wire c q \<noteq> Some p'" and w_def: "w = work_respons c m"
      using Step'
      unfolding io_def
      apply -
      apply(erule step_dis.cases)
          apply fast+
      done
    obtain op2 where no_wire': "(p', n, m) \<notin> ran (simp_wire' wire (work_respons c1))" and
       op'_def: "op' = loop_op (simp_wire' wire (work_respons c1)) (buf' (work_respons c1 m)) op2" and
       Step1: "step (Inp (p', n, m) x) (ops c1 (work_respons c1 m)) op2"
      using Step''
      apply -
      unfolding c_def conf_loop_def
      apply auto
      apply(erule step_loop_op_elim)
      apply auto
      done
    have no_wire': "\<not>(\<exists>q'. used_wire c1 q' = Some p')"
      using no_wire
      unfolding ran_def simp_wire'_def c_def conf_loop_def
      apply auto
      subgoal for q'
        apply(erule allE[where x = q'])
        apply auto
        done
      done
    have Step2: "step_dis' (Inp (p', n, m) x) c1 (c1\<lparr>ops := (ops c1)(work_respons c1 m := op2)\<rparr>)"
      using Step1 no_wire'
      apply -
      apply(rule S[where w = "work_respons c1 m"])
      apply(rule SDR[where op' = op2])
         apply auto
      done
    obtain op3 where Step3: "step (Inp (p', n, m) x) op1 op3" and H3: "op3 ~d c1\<lparr>ops := (ops c1)(work_respons c1 m := op2)\<rparr>"
      using Step2 H1_1 bisim_c_elim
      by blast
    show ?Q
      unfolding io_def p_def op_def
      apply(rule exI[where x = "(loop_op (simp_wire wire) buf op3)"])
      apply(rule conjI)
      subgoal
        using Step3 
        apply auto
        using no_wire H1_3
        unfolding c_def conf_loop_def ran_def simp_wire_def
        apply auto
        subgoal for a aa b
          apply(cases "wire a"; simp)
          apply auto
          apply(erule allE[where x = a])
          apply(erule allE[where x = p'])
          apply(erule allE[where x = a])
          apply(cases "used_wire c1 a"; simp)
          done
        done
      subgoal
        apply(rule bc'_base)
        unfolding op'_def
        apply(rule exI[where x = "wire"])
        apply(rule exI[where x = "buf"])
        apply(rule exI[where x = "buf'"])
        apply(rule exI[where x = "msg'"])
        apply(rule exI[where x = "op3"])
        apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(work_respons c1 m := op2)\<rparr>"])
        apply auto
        subgoal
          using H3
          by simp
        subgoal
          using c1_spec using Step1
          unfolding step_spec_conf.simps[where a = c1]
          apply safe
          apply(erule allE[where x = "p'"])
          apply(erule allE[where x = "n"])
          apply(erule allE[where x = "m"])
          apply(erule allE[where x = "x"])
          apply(erule allE[where x = "work_respons c1 m"])
          apply(erule allE[where x = "op2"])
          apply(erule allE[where x = "op2"])
          apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(work_respons c1 m := op2)\<rparr>)"])
          apply auto
          done
        subgoal
          using H1_2
          unfolding bufs_eq_def p_def
          apply safe
          done
        subgoal
          unfolding c'_def conf_loop_def c_def
          apply(simp only: record_help)
          apply auto
          unfolding op'_def
          by force
        subgoal for p q
          using H1_3
          by blast
        subgoal for p q
          using H1_3
          by blast
        done
      done
  next
    fix q :: "'op \<times> nat \<times> nat"
      and x :: 'd
    assume io_def: "io = Out q x"
    obtain q' n m op' where p_def: "q = (q', n, m)" and c'_def: "c' = c\<lparr>ops := (ops c)(work_respons c n := op')\<rparr>" and
      Step'': "step (Out (q', n, m) x) (ops c (work_respons c n)) op'" and no_wire: "used_wire c q' = None" and w_def: "w = work_respons c n"
      using Step'
      unfolding io_def
      apply -
      apply(erule step_dis.cases)
          apply blast+
      done
    obtain op2 where no_wire': "simp_wire' wire (work_respons c1) (q', n, m) = None" and
       op'_def: "op' = loop_op (simp_wire' wire (work_respons c1)) (buf' (work_respons c1 n)) op2" and
       Step1: "step (Out (q', n, m) x) (ops c1 (work_respons c1 n)) op2"
      using Step''
      apply -
      unfolding c_def conf_loop_def
      apply auto
      apply(erule step_loop_op_elim)
      apply auto
      done
    have no_wire': "used_wire c1 q' = None"
      using no_wire
      unfolding ran_def simp_wire'_def c_def conf_loop_def
      apply auto
      apply(cases "used_wire c1 q'"; simp)
      done
    have Step2: "step_dis' (Out (q', n, m) x) c1 (c1\<lparr>ops := (ops c1)(work_respons c1 n := op2)\<rparr>)"
      using Step1 no_wire'
      apply -
      apply(rule S[where w = "work_respons c1 n"])
      apply(rule SDW[where op' = op2])
         apply auto
      done
    obtain op3 where Step3: "step (Out (q', n, m) x) op1 op3" and H3: "op3 ~d c1\<lparr>ops := (ops c1)(work_respons c1 n := op2)\<rparr>"
      using Step2 H1_1 bisim_c_elim
      by blast
    show ?Q
      unfolding io_def p_def op_def
      apply(rule exI[where x = "(loop_op (simp_wire wire) buf op3)"])
      apply(rule conjI)
      subgoal
        using Step3 
        apply auto
        using no_wire H1_3
        unfolding c_def conf_loop_def ran_def simp_wire_def
        apply auto
        apply(cases "wire q'"; simp)
        done
      subgoal
        apply(rule bc'_base)
        unfolding op'_def
        apply(rule exI[where x = "wire"])
        apply(rule exI[where x = "buf"])
        apply(rule exI[where x = "buf'"])
        apply(rule exI[where x = "msg'"])
        apply(rule exI[where x = "op3"])
        apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(work_respons c1 n := op2)\<rparr>"])
        apply auto
        subgoal
          using H3
          by simp
        subgoal
          using c1_spec using Step1
          unfolding step_spec_conf.simps[where a = c1]
          apply safe
          apply(erule allE[where x = "q'"])
          apply(erule allE[where x = "n"])
          apply(erule allE[where x = "m"])
          apply(erule allE[where x = "x"])
          apply(erule allE[where x = "work_respons c1 n"])
          apply(erule allE[where x = "op2"])
          apply(erule allE[where x = "op2"])
          apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(work_respons c1 n := op2)\<rparr>)"])
          apply auto
          done
        subgoal
          using H1_2
          unfolding bufs_eq_def p_def
          apply safe
          done
        subgoal
          unfolding c'_def conf_loop_def c_def
          apply(simp only: record_help)
          apply auto
          unfolding op'_def
          by force
        subgoal for p q
          using H1_3
          by blast
        subgoal for p q
          using H1_3
          by blast
        done
      done
  next
    assume io_def: "io = Tau"
    consider "\<exists>op'. c' = c\<lparr>ops := (ops c)(w := op')\<rparr> \<and> step Tau (ops c w) op'" |
      "\<exists>p n m op' q. c' = c\<lparr>ops := (ops c)(work_respons c m := op'),
       msg := (msg c) (work_respons c n := (msg c (work_respons c n))(work_respons c m := BTL (p, n, m) (msg c (work_respons c n) (work_respons c m))))\<rparr> \<and>
       step (Inp (p, n, m) (bhd (msg c (work_respons c n) (work_respons c m) (p, n, m)))) (ops c (work_respons c m)) op' \<and> work_respons c m \<noteq> work_respons c n \<and>
       msg c (work_respons c n) (work_respons c m) (p, n, m) \<noteq> [] \<and> w = work_respons c m \<and> used_wire c q = Some p" |
      "\<exists>q n m x op' p. c' = c\<lparr>ops := (ops c)(work_respons c n := op'),
       msg := (msg c) (work_respons c n := (msg c (work_respons c n))(work_respons c m := BENQ (p, n, m) x (msg c (work_respons c n) (work_respons c m))))\<rparr> \<and>
       step (Out (q, n, m) x) (ops c (work_respons c n)) op' \<and>
       used_wire c q = Some p \<and> work_respons c m \<noteq> work_respons c n \<and> w = work_respons c n"
      using Step'
      unfolding io_def
      apply -
      apply(erule step_dis.cases)
      apply fast+
      done
    then show ?Q
    proof(cases, goal_cases Tau_Tau Tau_Inp Tau_Out)
      case Tau_Tau
      obtain op' where c'_def: "c' = c\<lparr>ops := (ops c)(w := op')\<rparr>" and Step'': "step Tau (ops c w) op'"
        using Tau_Tau
        by fast
      consider "\<exists>op''. op' = loop_op (simp_wire' wire (work_respons c1)) (buf' w) op'' \<and> step Tau (ops c1 w) op''" |
        "\<exists>op'' a aa b. (a, aa, b) \<in> ran (simp_wire' wire (work_respons c1)) \<and>
       op' = loop_op (simp_wire' wire (work_respons c1)) (BTL (a, aa, b) (buf' w)) op'' \<and>
       step (Inp (a, aa, b) (BHD (a, aa, b) (buf' w))) (ops c1 w) op'' \<and>
       buf' w (a, aa, b) \<noteq> []" |
        "\<exists>op'' a aa b ab ac ba x. simp_wire' wire (work_respons c1) (a, aa, b) = Some (ab, ac, ba) \<and>
       op' = loop_op (simp_wire' wire (work_respons c1)) (BENQ (ab, ac, ba) x (buf' w)) op'' \<and>
       step (Out (a, aa, b) x) (ops c1 w) op''"
        using Step''
        apply -
        unfolding c_def conf_loop_def
        apply auto
        apply(erule step_loop_op_elim)
        apply fast+
        done
      then show ?case
      proof(cases, goal_cases Tau_Tau_Tau Tau_Tau_Inp Tau_Tau_Out)
        case Tau_Tau_Tau
        obtain op2 where op'_def: "op' = loop_op (simp_wire' wire (work_respons c1)) (buf' w) op2" and
          Step1: "step Tau (ops c1 w) op2"
          using Tau_Tau_Tau
          by blast
        have Step2: "step_dis' Tau c1 (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"
          using Step1
          apply -
          apply(rule S[where w = w])
          apply(rule SDT[where op' = op2])
           apply auto
          done
        obtain op3 where Step3: "step Tau op1 op3" and H3: "op3 ~d c1\<lparr>ops := (ops c1)(w := op2)\<rparr>"
          using Step2 H1_1 bisim_c_elim
          by blast
        show ?case 
          unfolding io_def op_def
          apply(rule exI[where x = "(loop_op (simp_wire wire) buf op3)"])
          apply(rule conjI)
          subgoal
            using Step3 
            apply auto
            done
          subgoal
            apply(rule bc'_base)
            unfolding op'_def
            apply(rule exI[where x = "wire"])
            apply(rule exI[where x = "buf"])
            apply(rule exI[where x = "buf'"])
            apply(rule exI[where x = "msg'"])
            apply(rule exI[where x = "op3"])
            apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(w := op2)\<rparr>"])
            apply auto
            subgoal
              using H3
              by simp
            subgoal
              using c1_spec using Step1
              unfolding step_spec_conf.simps[where a = c1]
              apply safe
              apply(erule allE[where x = "op2"])
              apply(erule allE[where x = "w"])
              apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"])
              apply auto
              done
            subgoal
              using H1_2
              unfolding bufs_eq_def
              apply safe
              done
            subgoal
              unfolding c'_def conf_loop_def c_def
              apply(simp only: record_help)
              apply auto
              unfolding op'_def
              by force
            subgoal for p q
              using H1_3
              by blast
            subgoal for p q
              using H1_3
              by blast
            done
          done
      next
        case Tau_Tau_Inp
        obtain op2 p n m where some_wire: "(p,n,m) \<in> ran (simp_wire' wire (work_respons c1))" and
          op'_def: "op' = loop_op (simp_wire' wire (work_respons c1)) (BTL (p,n,m) (buf' w)) op2" and
          Step1: "step (Inp (p,n,m) (BHD (p,n,m) (buf' w))) (ops c1 w) op2" and
          buf_nonempty: "buf' w (p,n,m) \<noteq> []"
          using Tau_Tau_Inp
          by blast
        obtain q where some_wire': "wire q = Some p" and work_eq: "work_respons c1 n = work_respons c1 m"
          using some_wire
          unfolding ran_def simp_wire'_def
          apply auto
          subgoal for q' qn qm
            apply(cases "wire q'"; simp)
            apply(cases "work_respons c1 qn = work_respons c1 qm"; simp)
            done
          done
        have no_used_wire: "\<not>(\<exists>q'. used_wire c1 q' = Some p)"
          using H1_3 some_wire'
          apply -
          apply(erule allE[where x = p])
          apply(erule allE[where x = q])
          apply auto
          done
        have w_def: "w = work_respons c1 m" and c1_spec': "step_spec_conf (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"
          using Step1 c1_spec
          unfolding step_spec_conf.simps[where a = c1]
          apply auto
          apply(erule allE[where x = "p"])
          apply(erule allE[where x = "n"])
          apply(erule allE[where x = "m"])
          apply(erule allE[where x = "(BHD (p, n, m) (buf' w))"])
          apply(erule allE[where x = "w"])
          apply(erule allE[where x = "op2"])
          apply(erule allE[where x = "op2"])
          apply safe
          apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(work_respons c1 m := op2)\<rparr>)"])
          by simp
        have Step2: "step_dis' (Inp (p,n,m) (BHD (p,n,m) (buf' w))) c1 (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"
          using Step1 no_used_wire w_def
          apply -
          apply(rule S[where w = w])
          apply(rule SDR[where op' = op2])
           apply auto
          done
        obtain op3 where Step3: "step (Inp (p,n,m) (BHD (p,n,m) (buf' w))) op1 op3" and H3: "op3 ~d c1\<lparr>ops := (ops c1)(w := op2)\<rparr>"
          using Step2 H1_1 bisim_c_elim
          by blast
        show ?case 
          unfolding io_def op_def
          apply(rule exI[where x = "(loop_op (simp_wire wire) (BTL (p, n, m) buf) op3)"])
          apply(rule conjI)
          subgoal
            using Step3 
            apply(rule step_Inp_Tau_loop_op)
               apply auto
            subgoal
              using some_wire'
              unfolding ran_def simp_wire_def
              apply auto
              apply(rule exI[where x = q])
              apply(rule exI[where x = n])
              apply(rule exI[where x = m])
              by auto
            subgoal
              using buf_nonempty H1_2 work_eq
              unfolding bufs_eq_def w_def
              apply -
              apply(erule allE[where x = "(p,n,m)"])
              apply auto
              done
            subgoal
              using buf_nonempty H1_2 work_eq
              unfolding bufs_eq_def w_def BHD_def
              apply -
              apply(erule allE[where x = "(p,n,m)"])
              apply auto
              done
            done
          subgoal
            apply(rule bc'_base)
            unfolding op'_def
            apply(rule exI[where x = "wire"])
            apply(rule exI[where x = "(BTL (p, n, m) buf)"])
            apply(rule exI[where x = "buf'(w := (BTL (p, n, m) (buf' w)))"])
            apply(rule exI[where x = "msg'"])
            apply(rule exI[where x = "op3"])
            apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(w := op2)\<rparr>"])
            apply auto
            subgoal
              using H3
              by simp
            subgoal
              using c1_spec'
              by simp
            subgoal
              using H1_2 work_eq w_def
              unfolding bufs_eq_def BTL_def
              apply safe
              subgoal for a aa b
              apply(erule allE[where x = "(a,aa,b)"])
              apply auto
                done
              done
            subgoal
              unfolding c'_def conf_loop_def c_def
              apply(simp only: record_help)
              apply auto
              unfolding op'_def
              by force
            subgoal for p q
              using H1_3
              by blast
            subgoal for p q
              using H1_3
              by blast
            done
          done
      next
        case Tau_Tau_Out
        obtain op2 q p n m x where some_wire': "wire q = Some p" and work_eq: "work_respons c1 n = work_respons c1 m" and
          op'_def: "op' = loop_op (simp_wire' wire (work_respons c1)) (BENQ (p,n,m) x (buf' w)) op2" and
          Step1: "step (Out (q,n,m) x) (ops c1 w) op2"
          using Tau_Tau_Out
          unfolding simp_wire'_def
          apply auto
          subgoal for op2 q n m p n' m' x
            apply(cases "wire q"; simp)
            apply(cases "work_respons c1 n = work_respons c1 m"; simp)
            done
          done
        have no_used_wire: "used_wire c1 q = None"
          using H1_3 some_wire'
          apply -
          apply(erule allE[where x = p])
          apply(erule allE[where x = q])
          apply auto
          done
        have w_def: "w = work_respons c1 n" and c1_spec': "step_spec_conf (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"
          using Step1 c1_spec
          unfolding step_spec_conf.simps[where a = c1]
          apply auto
          apply(erule allE[where x = "q"])
          apply(erule allE[where x = "n"])
          apply(erule allE[where x = "m"])
          apply(erule allE[where x = "x"])
          apply(erule allE[where x = "w"])
          apply(erule allE[where x = "op2"])
          apply(erule allE[where x = "op2"])
          apply safe
          apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(work_respons c1 n := op2)\<rparr>)"])
          by simp
        have Step2: "step_dis' (Out (q,n,m) x) c1 (c1\<lparr>ops := (ops c1)(w := op2)\<rparr>)"
          using Step1 no_used_wire w_def
          apply -
          apply(rule S[where w = w])
          apply(rule SDW[where op' = op2])
           apply auto
          done
        obtain op3 where Step3: "step (Out (q,n,m) x) op1 op3" and H3: "op3 ~d c1\<lparr>ops := (ops c1)(w := op2)\<rparr>"
          using Step2 H1_1 bisim_c_elim
          by blast
        show ?case 
          unfolding io_def op_def
          apply(rule exI[where x = "(loop_op (simp_wire wire) (BENQ (p, n, m) x buf) op3)"])
          apply(rule conjI)
          subgoal
            using Step3 
            apply(rule step_Out_Tau_loop_op)
               apply auto
            subgoal
              using some_wire'
              unfolding ran_def simp_wire_def
              apply auto
              done
            done
          subgoal
            apply(rule bc'_base)
            unfolding op'_def
            apply(rule exI[where x = "wire"])
            apply(rule exI[where x = "(BENQ (p, n, m) x buf)"])
            apply(rule exI[where x = "buf'(w := (BENQ (p, n, m) x (buf' w)))"])
            apply(rule exI[where x = "msg'"])
            apply(rule exI[where x = "op3"])
            apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(w := op2)\<rparr>"])
            apply auto
            subgoal
              using H3
              by simp
            subgoal
              using c1_spec'
              by simp
            subgoal
              using H1_2 work_eq w_def
              unfolding bufs_eq_def BENQ_def
              apply safe
              subgoal for a aa b
              apply(erule allE[where x = "(a,aa,b)"])
              apply auto
                done
              done
            subgoal
              unfolding c'_def conf_loop_def c_def
              apply(simp only: record_help)
              apply auto
              unfolding op'_def
              by force
            subgoal for p q
              using H1_3
              by blast
            subgoal for p q
              using H1_3
              by blast
            done
          done
      qed
    next
      case Tau_Inp
      obtain p n m op' q where c'_def: "c' = c\<lparr>ops := (ops c)(work_respons c m := op'),
         msg := (msg c) (work_respons c n := (msg c (work_respons c n))
              (work_respons c m := BTL (p, n, m) (msg c (work_respons c n) (work_respons c m))))\<rparr>" and
        Step'': "step (Inp (p, n, m) (bhd (msg c (work_respons c n) (work_respons c m) (p, n, m)))) (ops c (work_respons c m)) op'" and
        work_noteq: "work_respons c1 m \<noteq> work_respons c1 n" and msg_nonempty: "msg c (work_respons c1 n) (work_respons c1 m) (p, n, m) \<noteq> []" and
        w_def: "w = work_respons c1 m" and some_wire: "used_wire c q = Some p"
        using Tau_Inp 
        unfolding c_def conf_loop_def
        by force
      obtain op2 where no_wire: "(p, n, m) \<notin> ran (simp_wire' wire (work_respons c1))" and
       op'_def: "op' = loop_op (simp_wire' wire (work_respons c1)) (buf' (work_respons c1 m)) op2" and
       Step2: "step (Inp (p, n, m) (bhd (if \<exists>q. used_wire c1 q = Some p then msg c1 (work_respons c1 n) (work_respons c1 m) (p, n, m)
           else msg' (work_respons c1 n) (work_respons c1 m) (p, n, m)))) (ops c1 (work_respons c1 m)) op2"
        using Step''
        unfolding c_def conf_loop_def
        apply auto
        apply(erule step_loop_op_elim)
            apply auto
        done
      consider "used_wire c1 q = Some p \<and> wire q = None" | "used_wire c1 q = None \<and> wire q = Some p"
        using some_wire work_noteq
        unfolding c_def conf_loop_def
        apply auto
        apply(cases "used_wire c1 q"; cases "wire q"; simp)
        using H1_3
        subgoal for a aa
          apply -
          apply(erule allE[where x = aa])
          apply(erule allE[where x = q])
          by auto
        done
      then show ?case
      proof(cases, goal_cases internal external)
        case internal
        have some_wire': "used_wire c1 q = Some p" and no_wire': "wire q = None"
          using internal
           apply simp+
          done
        have Step2': "step (Inp (p, n, m) (bhd (msg c1 (work_respons c1 n) (work_respons c1 m) (p, n, m)))) (ops c1 (work_respons c1 m)) op2"
          using Step2 some_wire'
          by presburger
        have Step3: "step_dis' Tau c1 (c1\<lparr>ops := (ops c1)(work_respons c1 m := op2),
               msg := (msg c1) (work_respons c1 n :=
              (msg c1 (work_respons c1 n))(work_respons c1 m := BTL (p, n, m) (msg c1 (work_respons c1 n) (work_respons c1 m))))\<rparr>)"
          using Step2' some_wire' work_noteq msg_nonempty
          apply -
          apply(rule S[where w = "(work_respons c1 m)"])
          apply(rule SDTR[where p = p and n = n and m = m and w = "(work_respons c1 n)" and op' = op2])
                apply auto
          unfolding c_def conf_loop_def
          apply auto
          by presburger
        obtain op3 where Step3': "step Tau op1 op3" and
          H3: "op3 ~d
          c1\<lparr>ops := (ops c1)(work_respons c1 m := op2), msg :=
                 (msg c1) (work_respons c1 n := (msg c1 (work_respons c1 n))
                    (work_respons c1 m := BTL (p, n, m) (msg c1 (work_respons c1 n) (work_respons c1 m))))\<rparr>"
          using Step3 H1_1 bisim_c_elim
          by blast
        show ?case
          unfolding io_def op_def
          apply(rule exI[where x = "(loop_op (simp_wire wire) buf op3)"])
          apply(rule conjI)
          subgoal
            using Step3'
            apply(rule step_Tau_loop_op)
            apply auto
            done
          subgoal
            apply(rule bc'_base)
            unfolding op'_def
            apply(rule exI[where x = "wire"])
            apply(rule exI[where x = "buf"])
            apply(rule exI[where x = "buf'"])
            apply(rule exI[where x = "msg'"])
            apply(rule exI[where x = "op3"])
            apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(work_respons c1 m := op2),
               msg := (msg c1) (work_respons c1 n :=
              (msg c1 (work_respons c1 n))(work_respons c1 m := BTL (p, n, m) (msg c1 (work_respons c1 n) (work_respons c1 m))))\<rparr>"])
            apply auto
            subgoal
              using H3
              by simp
            subgoal
              using c1_spec Step2'
              unfolding step_spec_conf.simps[where a = c1]
              apply safe
              apply(erule allE[where x = "p"])
              apply(erule allE[where x = "n"])
              apply(erule allE[where x = "m"])
              apply(erule allE[where x = "(bhd (msg c1 (work_respons c1 n) (work_respons c1 m) (p, n, m)))"])
              apply(erule allE[where x = "work_respons c1 m"])
              apply(erule allE[where x = "op2"])
              apply(erule allE[where x = "op2"])
              apply(erule allE[where x = "(msg c1)
                  (work_respons c1 n :=
                     (msg c1 (work_respons c1 n))
                     (work_respons c1 m := BTL (p, n, m) (msg c1 (work_respons c1 n) (work_respons c1 m))))"])
              by simp
            subgoal
              using H1_2 work_noteq w_def
              unfolding bufs_eq_def
              apply safe
              done
            subgoal
              using some_wire'
              unfolding c'_def conf_loop_def c_def BTL_def op'_def
              apply(simp only: record_help)
              apply auto
              apply force
              done
            subgoal for p q
              using H1_3
              by blast
            subgoal for p q
              using H1_3
              by blast
            done
          done
      next
        case external
        have no_wire': "used_wire c1 q = None" and some_wire': "wire q = Some p"
          using external
           apply simp+
          done
        have no_used_wire: "\<not>(\<exists>q. used_wire c1 q = Some p)"
          using H1_3 some_wire'
          apply auto
          done
        have Step2': "step (Inp (p, n, m) (bhd (msg' (work_respons c1 n) (work_respons c1 m) (p, n, m)))) (ops c1 (work_respons c1 m)) op2"
          using Step2 no_used_wire
          by fastforce
        have Step3: "step_dis' (Inp (p, n, m) (bhd (msg' (work_respons c1 n) (work_respons c1 m) (p, n, m)))) c1 (c1\<lparr>ops := (ops c1)(work_respons c1 m := op2)\<rparr>)"
          using Step2' work_noteq msg_nonempty no_used_wire
          apply -
          apply(rule S[where w = "(work_respons c1 m)"])
          apply(rule SDR[where op' = op2])
             apply auto
          done
        obtain op3 where Step3': "step (Inp (p, n, m) (bhd (msg' (work_respons c1 n) (work_respons c1 m) (p, n, m)))) op1 op3" and
          H3: "op3 ~d(c1\<lparr>ops := (ops c1)(work_respons c1 m := op2)\<rparr>)"
          using Step3 H1_1 bisim_c_elim
          by blast
        show ?case
          unfolding io_def op_def
          apply(rule exI[where x = "(loop_op (simp_wire wire) (BTL (p, n, m) buf) op3)"])
          apply(rule conjI)
          subgoal
            using Step3'
            apply -
            apply(rule step_Inp_Tau_loop_op[where p = "(p,n,m)" and x= "(bhd (msg' (work_respons c1 n) (work_respons c1 m) (p, n, m)))"])
                apply auto
            subgoal
              using some_wire'
              unfolding ran_def simp_wire_def
              apply auto
              apply(rule exI[where x = q])
              apply(rule exI[where x = n])
              apply(rule exI[where x = m])
              by simp
            subgoal
              using msg_nonempty H1_2 work_noteq no_used_wire
              unfolding bufs_eq_def c_def conf_loop_def
              apply auto
              done
            subgoal
              using H1_2 work_noteq
              unfolding BHD_def bufs_eq_def
              apply auto
              done
            done
          subgoal
            apply(rule bc'_base)
            unfolding op'_def
            apply(rule exI[where x = "wire"])
            apply(rule exI[where x = "(BTL (p, n, m) buf)"])
            apply(rule exI[where x = "buf'"])
            apply(rule exI[where x = "(msg'(work_respons c1 n := (msg' (work_respons c1 n))(work_respons c1 m := BTL (p,n,m) (msg' (work_respons c1 n) (work_respons c1 m)))))"])
            apply(rule exI[where x = "op3"])
            apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(work_respons c1 m := op2)\<rparr>"])
            apply auto
            subgoal
              using H3
              by simp
            subgoal
              using c1_spec Step2'
              unfolding step_spec_conf.simps[where a = c1]
              apply safe
              apply(erule allE[where x = "p"])
              apply(erule allE[where x = "n"])
              apply(erule allE[where x = "m"])
              apply(erule allE[where x = "(bhd (msg' (work_respons c1 n) (work_respons c1 m) (p, n, m)))"])
              apply(erule allE[where x = "work_respons c1 m"])
              apply(erule allE[where x = "op2"])
              apply(erule allE[where x = "op2"])
              apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(work_respons c1 m := op2)\<rparr>)"])
              by simp
            subgoal
              using H1_2 work_noteq w_def
              unfolding bufs_eq_def BTL_def
              apply auto
              done
            subgoal
              using no_used_wire
              unfolding c'_def conf_loop_def c_def BTL_def op'_def
              apply(simp only: record_help)
              apply auto
              by fastforce
            subgoal for p q
              using H1_3
              by blast
            subgoal for p q
              using H1_3
              by blast
            done
          done
      qed
    next
      case Tau_Out
      obtain q n m x op' p where c'_def: "c' = c\<lparr>ops := (ops c)(work_respons c n := op'),
         msg := (msg c) (work_respons c n := (msg c (work_respons c n))
              (work_respons c m := BENQ (p, n, m) x (msg c (work_respons c n) (work_respons c m))))\<rparr>" and
        Step'': "step (Out (q, n, m) x) (ops c (work_respons c n)) op'" and
        work_noteq: "work_respons c1 m \<noteq> work_respons c1 n" and
        w_def: "w = work_respons c1 n" and some_wire: "used_wire c q = Some p"
        using Tau_Out
        unfolding c_def conf_loop_def
        by auto
      obtain op2 where no_wire: "simp_wire' wire (work_respons c1) (q, n, m) = None" and
       op'_def: "op' = loop_op (simp_wire' wire (work_respons c1)) (buf' (work_respons c1 n)) op2" and
       Step2: "step (Out (q, n, m) x) (ops c1 (work_respons c1 n)) op2"
        using Step''
        unfolding c_def conf_loop_def
        apply auto
        apply(erule step_loop_op_elim)
            apply auto
        done
      consider "used_wire c1 q = Some p \<and> wire q = None" | "used_wire c1 q = None \<and> wire q = Some p"
        using some_wire work_noteq
        unfolding c_def conf_loop_def
        apply auto
        apply(cases "used_wire c1 q"; cases "wire q"; simp)
        using H1_3
        subgoal for a aa
          apply -
          apply(erule allE[where x = aa])
          apply(erule allE[where x = q])
          by auto
        done
      then show ?case
      proof(cases, goal_cases internal external)
        case internal
        have some_wire': "used_wire c1 q = Some p" and no_wire': "wire q = None"
          using internal
           apply simp+
          done
        have Step3: "step_dis' Tau c1 (c1\<lparr>ops := (ops c1)(work_respons c1 n := op2),
               msg := (msg c1) (work_respons c1 n :=
              (msg c1 (work_respons c1 n))(work_respons c1 m := BENQ (p, n, m) x (msg c1 (work_respons c1 n) (work_respons c1 m))))\<rparr>)"
          using Step2 some_wire' work_noteq
          apply -
          apply(rule S[where w = "(work_respons c1 n)"])
          apply(rule SDTW[where q = q and n = n and m = m and x = x and op' = op2])
               apply auto
          done
        obtain op3 where Step3': "step Tau op1 op3" and
          H3: "op3 ~d
          c1\<lparr>ops := (ops c1)(work_respons c1 n := op2), msg :=
                 (msg c1) (work_respons c1 n := (msg c1 (work_respons c1 n))
                    (work_respons c1 m := BENQ (p, n, m) x (msg c1 (work_respons c1 n) (work_respons c1 m))))\<rparr>"
          using Step3 H1_1 bisim_c_elim
          by blast
        show ?case
          unfolding io_def op_def
          apply(rule exI[where x = "(loop_op (simp_wire wire) buf op3)"])
          apply(rule conjI)
          subgoal
            using Step3'
            apply(rule step_Tau_loop_op)
            apply auto
            done
          subgoal
            apply(rule bc'_base)
            unfolding op'_def
            apply(rule exI[where x = "wire"])
            apply(rule exI[where x = "buf"])
            apply(rule exI[where x = "buf'"])
            apply(rule exI[where x = "msg'"])
            apply(rule exI[where x = "op3"])
            apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(work_respons c1 n := op2),
               msg := (msg c1) (work_respons c1 n :=
              (msg c1 (work_respons c1 n))(work_respons c1 m := BENQ (p, n, m) x (msg c1 (work_respons c1 n) (work_respons c1 m))))\<rparr>"])
            apply auto
            subgoal
              using H3
              by simp
            subgoal
              using c1_spec Step2
              unfolding step_spec_conf.simps[where a = c1]
              apply safe
              apply(erule allE[where x = "q"])
              apply(erule allE[where x = "n"])
              apply(erule allE[where x = "m"])
              apply(erule allE[where x = "x"])
              apply(erule allE[where x = "work_respons c1 n"])
              apply(erule allE[where x = "op2"])
              apply(erule allE[where x = "op2"])
              apply(erule allE[where x = "(msg c1)
                  (work_respons c1 n :=
                     (msg c1 (work_respons c1 n))(work_respons c1 m := BENQ (p, n, m) x (msg c1 (work_respons c1 n) (work_respons c1 m))))"])
              by simp
            subgoal
              using H1_2 work_noteq w_def
              unfolding bufs_eq_def
              apply safe
              done
            subgoal
              using some_wire'
              unfolding c'_def conf_loop_def c_def BENQ_def op'_def
              apply(simp only: record_help)
              apply auto
              apply force
              done
            subgoal for p q
              using H1_3
              by blast
            subgoal for p q
              using H1_3
              by blast
            done
          done
      next
        case external
        have no_wire': "used_wire c1 q = None" and some_wire': "wire q = Some p"
          using external
           apply simp+
          done
        have no_used_wire: "\<not>(\<exists>q. used_wire c1 q = Some p)"
          using H1_3 some_wire'
          apply auto
          done
        have Step3: "step_dis' (Out (q, n, m) x) c1 (c1\<lparr>ops := (ops c1)(work_respons c1 n := op2)\<rparr>)"
          using Step2 work_noteq no_wire'
          apply -
          apply(rule S[where w = "(work_respons c1 n)"])
          apply(rule SDW[where op' = op2])
             apply auto
          done
        obtain op3 where Step3': "step (Out (q, n, m) x) op1 op3" and
          H3: "op3 ~d(c1\<lparr>ops := (ops c1)(work_respons c1 n := op2)\<rparr>)"
          using Step3 H1_1 bisim_c_elim
          by blast
        show ?case
          unfolding io_def op_def
          apply(rule exI[where x = "(loop_op (simp_wire wire) (BENQ (p, n, m) x buf) op3)"])
          apply(rule conjI)
          subgoal
            using Step3'
            apply -
            apply(rule step_Out_Tau_loop_op[where p = "(q,n,m)" and x = x and q = "(p,n,m)"])
              apply auto
            using some_wire'
            unfolding simp_wire_def
            apply auto
            done
          subgoal
            apply(rule bc'_base)
            unfolding op'_def
            apply(rule exI[where x = "wire"])
            apply(rule exI[where x = "(BENQ (p, n, m) x buf)"])
            apply(rule exI[where x = "buf'"])
            apply(rule exI[where x = "(msg'(work_respons c1 n := (msg' (work_respons c1 n))(work_respons c1 m := BENQ (p,n,m) x (msg' (work_respons c1 n) (work_respons c1 m)))))"])
            apply(rule exI[where x = "op3"])
            apply(rule exI[where x = "c1\<lparr>ops := (ops c1)(work_respons c1 n := op2)\<rparr>"])
            apply auto
            subgoal
              using H3
              by simp
            subgoal
              using c1_spec Step2
              unfolding step_spec_conf.simps[where a = c1]
              apply safe
              apply(erule allE[where x = "q"])
              apply(erule allE[where x = "n"])
              apply(erule allE[where x = "m"])
              apply(erule allE[where x = "x"])
              apply(erule allE[where x = "work_respons c1 n"])
              apply(erule allE[where x = "op2"])
              apply(erule allE[where x = "op2"])
              apply(erule allE[where x = "msg (c1\<lparr>ops := (ops c1)(work_respons c1 n := op2)\<rparr>)"])
              by simp
            subgoal
              using H1_2 work_noteq w_def
              unfolding bufs_eq_def BENQ_def
              apply auto
              done
            subgoal
              using no_used_wire
              unfolding c'_def conf_loop_def c_def BENQ_def op'_def
              apply(simp only: record_help)
              apply auto
              by fastforce
            subgoal for p q
              using H1_3
              by blast
            subgoal for p q
              using H1_3
              by blast
            done
          done
      qed
    qed    
  qed
qed

lemma bisim_example :
  assumes "\<forall>n. n_op1 n = w_n_op1 (work_respons' n) n"
    and "\<forall>n. n_op2 n = w_n_op2 (work_respons' n) n"
  shows  "map_op_comp (comp_op (simp_wire wire) (\<lambda>_. []) (exchange_op \<nat> pact1 n_op1) (exchange_op \<nat> pact2 n_op2)) ~d
          conf_comp wire  (\<lambda>_ _. []) (\<lambda>_ _ _. []) (conf_exchange work_respons' pact1 w_n_op1) (conf_exchange work_respons' pact2 w_n_op2)"
  apply -
  apply(rule comp_bisim)
  subgoal
    using assms
    apply -
    apply(rule exchange_bisim)
    by simp
  subgoal
    using assms
    apply -
    apply(rule exchange_bisim)
    by simp
  subgoal
    apply(rule exchange_spec)
    done
  subgoal
    apply(rule exchange_spec)
    done
  subgoal
    unfolding bufs_eq_def
    by simp
  subgoal
    unfolding conf_exchange_def
    apply auto
    done
  subgoal
    unfolding conf_exchange_def
    apply auto
    done
  done

end
