theory Base_Op_Proofs_Dis

imports
    "HOL-ex.Sketch_and_Explore" 
    Timely_Infrastructure_Dis
    "Examples/Set_op"
    "Examples/Tmap_op"
begin

lemma set_mset_cset[simp]: "rcset (acset (set_mset xs)) = set_mset xs"
  apply(rule acset_inverse)
  using countable_finite by blast


(* set'_op *)

corec set'_op :: "('a \<times> 'b) multiset \<Rightarrow> ('c, 'a, 'b) op \<Rightarrow> ('c, 'a, 'b) op" where
  "set'_op S op = choice2
  (Choice (cimage (\<lambda> op. case op of
     Write op p x \<Rightarrow> Silent (set'_op (add_mset (p, x) S) op) 
   | Silent op \<Rightarrow> Silent (set'_op S op)
   | Read _ _ \<Rightarrow> Code.abort (STR ''Set_op can only output'') (\<lambda> _. \<oslash>)
   ) (choices op))
   )
  (Choice (cimage (\<lambda> (p, x). Write (set'_op (remove1_mset (p, x) S) op) p x) ((acset o set_mset) S)))"

lemma step_set'_op_elim:
  assumes "step io (set'_op S op) op'"
  obtains p x where "io = Out p x" "(p, x) \<in># S" "op' = set'_op (remove1_mset (p, x) S) op"
  | op'' where "io = Tau" "step Tau op op''" "op' = set'_op S op''"
  | p x op'' where "io = Tau" "step (Out p x) op op''" "op' = set'_op (add_mset (p, x) S) op''"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) set'_op.code)
  by (auto del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
     (fastforce+)

lemma step_set'_op_intro_Out[intro]:
  "io = Out p x \<Longrightarrow>
   (p, x) \<in># S \<Longrightarrow>
   op' = set'_op (remove1_mset (p, x) S) op \<Longrightarrow>
   step io (set'_op S op) op'"
  apply (subst set'_op.code)
  apply (clarsimp del: disjCI split: op.splits simp add: comp_def simp flip: cin.rep_eq; hypsubst_thin?)
  apply(rule Write_in_choices_step)
  by(simp add: Bex_def)


lemma step_set'_op_intro_Tau_1[intro]:
  "step (Out p x) op op'' \<Longrightarrow>
   io = Tau \<Longrightarrow>
   op' = set'_op (add_mset (p, x) S) op'' \<Longrightarrow>
   step io (set'_op S op) op'"
  apply (subst set'_op.code)
  apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
  apply(rule Silent_in_choices_step, drule step_choicesE; simp)
  by force

lemma step_set_op_intro_Tau_2[intro]:
  "io = Tau \<Longrightarrow>
   step Tau op op'' \<Longrightarrow>
   op' = set'_op S op'' \<Longrightarrow>
   step io (set'_op S op) op'"
  apply (subst set'_op.code)
  apply (subst set'_op.code)
  apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
  apply (metis (no_types, lifting) IO.distinct(5) IO.simps(6) cimageI cinsertI1 op.simps(20) step.simps step_choicesE)
  done


(* set'_op that can take input
corec set'_op :: "('a \<times> 'b) multiset \<Rightarrow> ('c, 'a, 'b) op \<Rightarrow> ('c, 'a, 'b) op" where
  "set'_op S op = choice2
  (Choice (cimage (\<lambda> op. case op of
     Write op p x \<Rightarrow> Silent (set'_op (add_mset (p, x) S) op) 
   | Silent op \<Rightarrow> Silent (set'_op S op)
   | Read p f \<Rightarrow> Read p ((set'_op S) o f)
   ) (choices op))
   )
  (Choice (cimage (\<lambda> (p, x). Write (set'_op (remove1_mset (p, x) S) op) p x) ((acset o set_mset) S)))"

lemma step_set'_op_elim:
  assumes "step io (set'_op S op) op'"
  obtains p x where "io = Out p x" "(p, x) \<in># S" "op' = set'_op (remove1_mset (p, x) S) op"
  | op'' where "io = Tau" "step Tau op op''" "op' = set'_op S op''"
  | p x op'' where "io = Tau" "step (Out p x) op op''" "op' = set'_op (add_mset (p, x) S) op''"
  | p x op'' where "io = Inp p x" "step (Inp p x) op op''" "op' = set'_op S op''"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) set'_op.code)
  by (auto del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
     (fastforce+)

lemma step_set'_op_intro_Out[intro]:
  "io = Out p x \<Longrightarrow>
   (p, x) \<in># S \<Longrightarrow>
   op' = set'_op (remove1_mset (p, x) S) op \<Longrightarrow>
   step io (set'_op S op) op'"
  apply (subst set'_op.code)
  apply (clarsimp del: disjCI split: op.splits simp add: comp_def simp flip: cin.rep_eq; hypsubst_thin?)
  apply(rule Write_in_choices_step)
  by(simp add: Bex_def)


lemma step_set'_op_intro_Tau_1[intro]:
  "step (Out p x) op op'' \<Longrightarrow>
   io = Tau \<Longrightarrow>
   op' = set'_op (add_mset (p, x) S) op'' \<Longrightarrow>
   step io (set'_op S op) op'"
  apply (subst set'_op.code)
  apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
  apply(rule Silent_in_choices_step, drule step_choicesE; simp)
  by force

lemma step_set_op_intro_Tau_2[intro]:
  "io = Tau \<Longrightarrow>
   step Tau op op'' \<Longrightarrow>
   op' = set'_op S op'' \<Longrightarrow>
   step io (set'_op S op) op'"
  apply (subst set'_op.code)
  apply (subst set'_op.code)
  apply (clarsimp del: disjCI split: op.splits simp flip: cin.rep_eq; hypsubst_thin?)
  apply (metis (no_types, lifting) IO.distinct(5) IO.simps(6) cimageI cinsertI1 op.simps(20) step.simps step_choicesE)
  done
*)

(*source'_op *)

definition source'_op_aux where
  "source'_op_aux inps op = (case op of Read p f \<Rightarrow> cimage (\<lambda> x. (Inl o Inl) (p,f,x)) (acset (set_mset (inps p))) | op' \<Rightarrow> csingle ((Inl o Inr) op'))"

corec source'_op where
  "source'_op inps op = Choice (cimage (case_sum 
    (\<lambda> op'. case op' of
    Inl (p,f,x) \<Rightarrow> Silent (source'_op (inps(p := remove1_mset x (inps p))) (f x))
  | Inr (Write op p x) \<Rightarrow> Write (source'_op inps op) p x
  | Inr (Silent op) \<Rightarrow> Silent (source'_op inps op)) 
    (\<lambda> p. Read p (\<lambda> x. source'_op (inps(p := add_mset x (inps p))) op)))
  (cUn (cim Inr cUNIV) (cUnion (cim (source'_op_aux inps) (choices op)))))"

lemma step_source'_op_intro_Out[intro]:
  "io = Out p x \<Longrightarrow>
   step io op op'' \<Longrightarrow>
   op' = source'_op inps op'' \<Longrightarrow>
   step io (source'_op inps op) op'"
  apply(subst source'_op.corec.code)
  apply(erule step_choicesE; simp)
  apply(rule Write_in_choices_step)
  apply(simp add: source'_op_aux_def Bex_def)
  by fastforce

lemma step_source'_op_intro_Inp[intro]:
  "io = Inp p x \<Longrightarrow>
   op' = source'_op (inps(p := add_mset x (inps p))) op \<Longrightarrow>
   step io (source'_op inps op) op'"
  apply(subst source'_op.corec.code)
  apply simp
  apply(rule Read_in_choices_step)
  apply(simp add: source'_op_aux_def Bex_def)
  by(auto intro!: ext intro: arg_cong[where f = "\<lambda> f. source'_op f _"])

lemma step_source'_op_intro_Tau_Tau[intro]:
  "io = Tau \<Longrightarrow>
   step io op op'' \<Longrightarrow>
   op' = source'_op inps op'' \<Longrightarrow>
   step io (source'_op inps op) op'"
  apply(subst source'_op.corec.code)
  apply(erule step_choicesE; simp)
  apply(rule Silent_in_choices_step)
  apply(simp add: source'_op_aux_def Bex_def)
  by fastforce

lemma step_source'_op_intro_Tau_Inp[intro]:
  "io = Tau \<Longrightarrow>
   step (Inp p x) op op'' \<Longrightarrow>
   op' = source'_op (inps(p := remove1_mset x (inps p))) op'' \<Longrightarrow>
   x \<in># inps p \<Longrightarrow>
   step io (source'_op inps op) op'"
  apply(subst source'_op.corec.code)
  apply(erule step_choicesE; simp)
  apply(rule Silent_in_choices_step)
  apply(simp add: source'_op_aux_def Bex_def)
  by fastforce

lemma step_source'_op_elim:
  assumes "step io (source'_op inps op) op'"
  obtains p x op'' where "io = Out p x" "step (Out p x) op op''" "op' = source'_op inps op''"
  | p x where "io = Inp p x" "op' = source'_op (inps(p := add_mset x (inps p))) op"
  | p x op'' where "io = Tau" "x \<in># inps p" "step (Inp p x) op op''" "op' = source'_op (inps(p := remove1_mset x (inps p))) op''"  
  | op'' where "io = Tau" "step Tau op op''" "op' = source'_op inps op''"
  using assms apply -
  apply atomize_elim
  apply(subst (asm) source'_op.corec.code)
  apply (auto del: disjCI split: op.splits sum.splits dest!: no_Choice_in_choices[simplified cin.rep_eq[symmetric]] Write_in_choices_step  simp flip: cin.rep_eq simp add: source'_op_aux_def ; hypsubst_thin?)
    apply fastforce+
  done


definition op_wrapper where     
  "op_wrapper f_xs S op = set'_op S (source'_op f_xs op)"

lemma step_op_wrapper_elim: 
  assumes "step io (op_wrapper f_xs S op) op'" 
  obtains p x where "io = Out p x" "(p, x) \<in># S" "op' = op_wrapper f_xs (remove1_mset (p, x) S) op" | 
         p x op'' where "io = Tau" "step (Inp p x) op op''" "op' = op_wrapper (f_xs(p := (remove1_mset x (f_xs p)))) S op''" |
         p x op'' where "io = Tau" "step (Out p x) op op''" "op' = op_wrapper f_xs (add_mset (p, x) S) op''" |
         op'' where "io = Tau" "step Tau op op''" "op' = op_wrapper f_xs S op''"
  using assms
  unfolding op_wrapper_def
  apply -
  by(blast elim!: step_set'_op_elim step_source'_op_elim)

lemma step_op_wrapper_intro_Out[intro]:
  "io = Out p x \<Longrightarrow> (p, x) \<in># S \<Longrightarrow>
   op' = (op_wrapper inps (remove1_mset (p, x) S) op) \<Longrightarrow>
   step io (op_wrapper inps S op) op'"
  unfolding op_wrapper_def
  by auto

lemma step_op_wrapper_intro_Tau_Tau[intro]:
  "io = Tau \<Longrightarrow>
   step Tau op op'' \<Longrightarrow>
   op' = op_wrapper inps S op'' \<Longrightarrow>
   step io (op_wrapper inps S op) op'"
  unfolding op_wrapper_def
  by auto

lemma step_op_wrapper_intro_Tau_Inp[intro]:
  "io = Tau \<Longrightarrow>
   x \<in># inps p \<Longrightarrow>
   step (Inp p x) op op'' \<Longrightarrow>
   op' = op_wrapper (inps(p := remove1_mset x (inps p))) S op'' \<Longrightarrow>
   step io (op_wrapper inps S op) op'"
  unfolding op_wrapper_def
  by auto

lemma step_op_wrapper_intro_Tau_Out[intro]:
  "io = Tau \<Longrightarrow>
   step (Out p x) op op'' \<Longrightarrow>
   op' = op_wrapper inps (add_mset (p, x) S) op'' \<Longrightarrow>
   step io (op_wrapper inps S op) op'"
  unfolding op_wrapper_def
  by auto

definition init_conf' where 
  "init_conf' chns f_xs S dt =
  \<lparr> msg = \<lambda> _ _. empty_mset,
    prog_msg = \<lambda> _ _. [],
    ops = \<lambda> w. op_wrapper (f_xs w) (S w) (compile_dataflow_dis w chns dt),
    used_wire = \<lambda> _. None \<rparr>"

abbreviation conf_instance where
  "conf_instance ws f_xs S op \<equiv> (init_conf' ws (\<lambda> w e. case e of Some (Inl e') \<Rightarrow> image_mset Inr (f_xs e' w) | _ \<Rightarrow> empty_mset) (\<lambda> w. (image_mset (\<lambda> (x,y). (Some (w,x), Inr y)) (S w))) op)"

setup_lifting type_definition_multiset

context begin

lemma Finite_Set_bind_help: "finite S \<Longrightarrow> Finite_Set.fold (\<lambda>a. (-+-) (count (f a) x)) 0 (insert s S) = (if s \<in> S then 
  Finite_Set.fold (\<lambda>a. (-+-) (count (f a) x)) 0 S else (\<lambda>a. (-+-) (count (f a) x)) s (Finite_Set.fold (\<lambda>a. (-+-) (count (f a) x)) 0 S))"
  apply(cases "s \<in> S"; simp add: insert_absorb)
  by(rule comp_fun_commute_on.fold_insert[of UNIV]; (auto simp add: comp_fun_commute_on_def))

lift_definition bind_mset :: "('a :: enum) set \<Rightarrow> ('a \<Rightarrow> 'b multiset) \<Rightarrow> 'b multiset" is
  "\<lambda>s M x. Finite_Set.fold (\<lambda> a b. count (M a) x + b) 0 s"
proof -
  have "0 < Finite_Set.fold (\<lambda>(a :: _ :: enum). (-+-) (count (f a) x)) 0 s \<longrightarrow> (\<exists>x'\<in>s. x \<in># f x')" for f s x 
    by(rule finite_subset_induct[of s UNIV]; (simp add: Finite_Set_bind_help))
  then have H: "0 < Finite_Set.fold (\<lambda>(a :: _ :: enum). (-+-) (count (f a) x)) 0 s \<Longrightarrow> (\<exists>x'\<in>s. x \<in># f x')" for f s x 
    by metis
  show "\<And>set fun. finite {x. 0 < Finite_Set.fold (\<lambda>(a :: _ :: enum). (-+-) (count (fun a) x)) 0 set}"
  subgoal for s f
    by(rule finite_subset[where B = "Set.bind s (\<lambda> x. set_mset (f x))"]; (auto simp add: H finite_bind)?)
  done
qed

lift_definition add'_mset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" is
  "\<lambda>M1 M2 a. M1 a + M2 a"
  by fastforce

lemma in_bind_mset[simp]: "x \<in># bind_mset S f = (\<exists> s \<in> S. x \<in># (f s))"
  apply(simp flip: count_greater_zero_iff add: bind_mset.rep_eq)
  by(rule finite_subset_induct[of S UNIV]; simp add: Finite_Set_bind_help)

lemma bind_mset_insert[simp]: "s \<notin> S \<Longrightarrow> bind_mset (insert s S) f = add'_mset (f s) (bind_mset S f)"
  apply(simp flip: count_inject add: bind_mset.rep_eq)
  apply(rule ext)
  by(simp add: bind_mset.rep_eq add'_mset.rep_eq Finite_Set_bind_help)

lemma bind_mset_empty[simp]: "bind_mset {} f = empty_mset"
  by(simp flip: count_inject add: bind_mset.rep_eq zero_multiset.rep_eq)

lemma bind_mset_eq_allmost_everywhere: "(\<forall> s \<in> S. f s = g s) \<Longrightarrow> bind_mset S f = bind_mset S g"
  by(rule finite_subset_induct'[of S S]; simp?)

lemma bind_mset_remove1[simp]: "bind_mset S (f(s := remove1_mset x (f s))) = (if s \<in> S \<and> x \<in># f s then remove1_mset x (bind_mset S f) else bind_mset S f)"
proof -
  have H1: "s \<in> S \<Longrightarrow> x \<in># f s \<Longrightarrow> bind_mset (insert s (S - {s})) (map_entry s (remove1_mset x) f) = add'_mset ((map_entry s (remove1_mset x) f) s) (bind_mset (S - {s}) f)"
    apply(rule trans)
     apply(rule bind_mset_insert; simp)
    apply(rule arg_cong[where f = "add'_mset (map_entry s (remove1_mset x) f s)"])
    by(simp add: bind_mset_eq_allmost_everywhere)
  show ?thesis
  apply(simp flip: count_greater_zero_iff add: bind_mset.rep_eq)
  apply(cases "s \<in> S \<and> x \<in># f s"; (simp add: bind_mset_eq_allmost_everywhere ))
   apply safe
    subgoal
      using H1
      apply(simp add: insert_absorb)
    sorry
  subgoal
    by (metis count_eq_zero_iff)
  done
qed

end

lemma "(op_wrapper (\<lambda> x. bind_mset UNIV (f_xs x)) (bind_mset UNIV S) (compile_dataflow ws (Logic (tmap_op ip op os f) t_msg))) ~d 
      conf_instance ws f_xs S (Logic_Dis (tmap_op ip op os f) t_msg pact)"
proof (coinduction arbitrary: f_xs S os t_msg)
  fix f_xs :: "'a \<times> 'b \<Rightarrow> 'e \<Rightarrow> ('c \<times> 'd) multiset"
    and os :: "('b, 'c, 'f, 'g, 'd, 'h) operator_state_ty2_scheme"
    and t_msg :: "'b \<Rightarrow> 'b \<Rightarrow> 'd buf"
    and S :: "'e \<Rightarrow> (('a \<times> 'b) \<times> 'c \<times> 'd) multiset"
(* TODO try to see if local definition makes things more readable
  define op1 where "op1 = (\<lambda> f_xs S S' os t_msg. op_wrapper (\<lambda>x. bind_mset UNIV (f_xs x)) (cUNION cUNIV S) (cUNION cUNIV S') (compile_dataflow ws (Logic (tmap_op ip op os f) t_msg)))"
*)
  let ?op1 = "\<lambda> f_xs S os t_msg. op_wrapper (\<lambda>x. bind_mset UNIV (f_xs x)) (bind_mset UNIV S) (compile_dataflow ws (Logic (tmap_op ip op os f) t_msg))"
  let ?c1 = "\<lambda> f_xs S os t_msg. conf_instance ws f_xs S (Logic_Dis (tmap_op ip op os f) t_msg pact)"
(*
  let ?c1 = "\<lambda> f_xs S S' os t_msg. init_conf' ws (\<lambda>w. case_option {#} (case_sum (\<lambda>e'. Inr `# f_xs e' w) (\<lambda>b. {#}))) (\<lambda>w. (\<lambda>(x, y). (Some (w, x), Inr y)) |`| S w) (\<lambda>w. (\<lambda>(x, y). (Some (w, x), Inr y)) |`| S' w) (Logic_Dis (tmap_op ip op os f) t_msg pact)"
*)
  have "sim_dis (\<lambda>uu uua. (\<exists>f_xs S (os :: ('b, 'c, 'f, 'g, 'd, 'h) operator_state_ty2_scheme) t_msg. uu = ?op1 f_xs S os t_msg \<and> uua = ?c1 f_xs S os t_msg)) (?op1 f_xs S os t_msg) (?c1 f_xs S os t_msg)"
    unfolding sim_dis_def
    apply simp
    apply safe
    subgoal for io op
      apply(drule step_op_wrapper_elim; simp)
      apply safe
      subgoal for p1 p2 x1 x2 w
        apply(rule exI[where x = "undefined"])
        apply(rule conjI)
        subgoal
          sorry
        subgoal
          apply(rule exI[where x = "f_xs"])
          apply(rule exI[where x = "S(w := remove1_mset ((p1, p2), x1, x2) (S w))"])
          apply(rule exI[where x = "os"])
          apply(rule exI[where x = "t_msg"])
          apply auto

        sorry
      subgoal
        sorry
      subgoal
        sorry
      subgoal for op'
        unfolding compile_dataflow_def dataflow_tree_to_operator_def
        apply simp
        apply(erule step_dataflow_op_elim; simp)
        subgoal for op''
          apply(erule step_map_op_elim)
          apply safe
          apply(erule step_tmap_op_elim; simp?)
          subgoal for io' op''' os'

end
          apply auto
          apply(rule exI[where x = "?c1 f_xs S S' os t_msg"]; simp)
          apply safe
          subgoal for op'''
            sorry
          subgoal for op'''
            apply(rule exI[where x = f_xs])
            apply(rule exI[where x = S])
            apply(rule exI[where x = S'])
            apply(rule exI[where x = os])
            apply(rule exI[where x = t_msg])
            apply auto
            apply(erule step_tmap_op_elim; simp?)
            sorry
          done
        subgoal
          sorry
        subgoal
          sorry
        done
      done
    subgoal for io op
      apply(drule step_dis'_elim, erule exE)
      subgoal for w
        apply(drule step_dis_elim)
      sorry
    done
  done
  then show "\<exists>opa c. ?op1 f_xs S S' os t_msg = opa \<and> ?c1 f_xs S S' os t_msg = c \<and> 
      sim_dis (\<lambda>uu uua. (\<exists>f_xs S S' (os :: ('b, 'c, 'f, 'g, 'd, 'h) operator_state_ty2_scheme) t_msg. uu = ?op1 f_xs S S' os t_msg \<and> uua = ?c1 f_xs S S' os t_msg) \<or> uu ~d uua) opa c"
    apply simp
    apply(rule predicate2D[OF sim_dis_mono, rotated], assumption)
    by blast
  qed




end