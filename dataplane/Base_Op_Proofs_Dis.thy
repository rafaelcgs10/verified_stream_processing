theory Base_Op_Proofs_Dis

imports
    "HOL-ex.Sketch_and_Explore" 
    Timely_Infrastructure_Dis
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

(*source'_op *)

corec source'_op :: "('a \<Rightarrow> 'b llist) \<Rightarrow> ('a, 'c, 'b) op \<Rightarrow> ('a, 'c, 'b) op" where
  "source'_op inps op = Choice (cimage (\<lambda> op'. case op' of
    Read p f \<Rightarrow> Silent (source'_op (inps(p := ltl (inps p))) (f (lhd (inps p))))
  | Write op p x \<Rightarrow> Write (source'_op inps op) p x
  | Silent op \<Rightarrow> Silent (source'_op inps op))
  (cfilter (\<lambda> op. case op of Read p f \<Rightarrow> inps p \<noteq> LNil | _ \<Rightarrow> True) (choices op)))"

lemma step_source'_op_intro_Out[intro]:
  "io = Out p x \<Longrightarrow>
   step io op op'' \<Longrightarrow>
   op' = source'_op inps op'' \<Longrightarrow>
   step io (source'_op inps op) op'"
  apply(subst source'_op.corec.code)
  apply(erule step_choicesE; simp)
  by fastforce

lemma step_source'_op_intro_Tau_Tau[intro]:
  "io = Tau \<Longrightarrow>
   step io op op'' \<Longrightarrow>
   op' = source'_op inps op'' \<Longrightarrow>
   step io (source'_op inps op) op'"
  apply(subst source'_op.corec.code)
  apply(erule step_choicesE; simp)
  by fastforce

lemma x_in_rcset_acset: "x \<in> rcset (acset {y. (p, y) \<in># S}) = (x \<in> {y. (p, y) \<in># S})"
  apply(subgoal_tac "{y. (p, y) \<in># S} \<in> {A. countable A}")
  subgoal
    by simp
  subgoal
    apply(auto intro!: countable_finite simp only: mem_Collect_eq set_mset_def simp add: finite_nonzero_count)
    using finite_nonzero_count[of S, THEN finite_filter[of _ "\<lambda> (p',_). p = p'"], THEN finite_imageI[of _ snd ]]
    apply -
    apply(simp only: mem_Collect_eq Set.filter_eq image_def Bex_def split: sum.split)
    by auto
  done

lemma step_source'_op_intro_Tau_Inp[intro]:
  "io = Tau \<Longrightarrow>
   step (Inp p (lhd (inps p))) op op'' \<Longrightarrow>
   op' = source'_op (inps(p := ltl (inps p))) op'' \<Longrightarrow>
   inps p \<noteq> LNil \<Longrightarrow>
   step io (source'_op inps op) op'"
  apply(subst source'_op.corec.code)
  apply(erule step_choicesE; simp)
  by fastforce

lemma step_source'_op_elim:
  assumes "step io (source'_op inps op) op'"
  obtains p x op'' where "io = Out p x" "step (Out p x) op op''" "op' = source'_op inps op''"
  | p x op'' where "io = Tau" "inps p \<noteq> LNil" "step (Inp p (lhd (inps p))) op op''" "op' = source'_op (inps(p := ltl (inps p))) op''"  
  | op'' where "io = Tau" "step Tau op op''" "op' = source'_op inps op''"
  using assms apply -
  apply atomize_elim
  apply(subst (asm) source'_op.corec.code)
  apply (auto del: disjCI split: op.splits sum.splits dest!: no_Choice_in_choices[simplified cin.rep_eq[symmetric]] Write_in_choices_step  simp flip: cin.rep_eq ; hypsubst_thin?)
                 apply blast+
  done

definition op_wrapper where     
  "op_wrapper inps S op = set'_op S (source'_op inps op)"

lemma step_op_wrapper_elim: 
  assumes "step io (op_wrapper inps S op) op'" 
  obtains p x where "io = Out p x" "(p, x) \<in># S" "op' = op_wrapper inps (remove1_mset (p, x) S) op" | 
         p x op'' where "io = Tau" "step (Inp p (lhd (inps p))) op op''" "inps p \<noteq> LNil" "op' = op_wrapper (inps(p := ltl (inps p))) S op''" |
         p x op'' where "io = Tau" "step (Out p x) op op''" "op' = op_wrapper inps (add_mset (p, x) S) op''" |
         op'' where "io = Tau" "step Tau op op''" "op' = op_wrapper inps S op''"
  using assms
  unfolding op_wrapper_def
  apply -
  by(auto elim!: step_set'_op_elim step_source'_op_elim)

lemma step_op_wrapper_intro_Out:
  "io = Out p x \<Longrightarrow> (p, x) \<in># S \<Longrightarrow>
   op' = (op_wrapper inps (remove1_mset (p, x) S) op) \<Longrightarrow>
   step io (op_wrapper inps S op) op'"
  unfolding op_wrapper_def
  by auto

lemma step_op_wrapper_intro_Tau_Tau:
  "io = Tau \<Longrightarrow>
   step Tau op op'' \<Longrightarrow>
   op' = op_wrapper inps S op'' \<Longrightarrow>
   step io (op_wrapper inps S op) op'"
  unfolding op_wrapper_def
  by auto

lemma step_op_wrapper_intro_Tau_Inp:
  "io = Tau \<Longrightarrow>
   inps p \<noteq> LNil \<Longrightarrow>
   step (Inp p (lhd (inps p))) op op'' \<Longrightarrow>
   op' = op_wrapper (inps(p := ltl (inps p))) S op'' \<Longrightarrow>
   step io (op_wrapper inps S op) op'"
  unfolding op_wrapper_def
  by auto

lemma step_op_wrapper_intro_Tau_Out:
  "io = Tau \<Longrightarrow>
   step (Out p x) op op'' \<Longrightarrow>
   op' = op_wrapper S_in (add_mset (p, x) S_out) op'' \<Longrightarrow>
   step io (op_wrapper S_in S_out op) op'"
  unfolding op_wrapper_def
  by auto

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
(*
lemma Test_case_Out: "io = Out (p1, p2) (x1, x2) \<Longrightarrow>
    op = op_wrapper (bind_mset UNIV S_in) (remove1_mset ((p1, p2), x1, x2) (bind_mset UNIV S_out)) (compile_dataflow ws (dataflow_dis_transfer dt)) \<Longrightarrow>
    ((p1, p2), x1, x2) \<in># S_out w \<Longrightarrow>
    \<exists>c'. step_dis' (Out (p1, p2) (x1, x2)) (conf_instance ws S_in S_out dt) c' \<and>
         (\<exists>S_in' S_out'.
             op_wrapper (bind_mset UNIV S_in) (remove1_mset ((p1, p2), x1, x2) (bind_mset UNIV S_out)) (compile_dataflow ws (dataflow_dis_transfer dt)) =
             op_wrapper (bind_mset UNIV S_in') (bind_mset UNIV S_out') (compile_dataflow ws (dataflow_dis_transfer dt)) \<and>
             c' = conf_instance ws S_in' S_out' dt)"
    apply(rule exI[where x = "conf_instance ws S_in (\<lambda>wa. if wa = w then remove1_mset ((p1, p2), x1, x2) (S_out w) else S_out wa) dt"])
    apply(rule conjI)
    subgoal
      apply(rule step_dis'.intros[of w])
      apply(rule step_dis.intros; (simp add: init_conf'_def))
       apply(rule step_op_wrapper_intro_Out; (simp add: image_def))
      subgoal
        by force
      by(auto split: prod.split simp add: image_mset_remove1_mset_if)
    subgoal
      apply(rule exI[where x = "S_in"])
      apply(rule exI[where x = "S_out(w := remove1_mset ((p1, p2), x1, x2) (S_out w))"])
      by auto
    done

lemma Test_case_Out_Logic: "io = Out (p1, p2) (x1, x2) \<Longrightarrow>
    op = op_wrapper (bind_mset UNIV S_in) (remove1_mset ((p1, p2), x1, x2) (bind_mset UNIV S_out)) (compile_dataflow ws (Logic (dt ipp opp os f) t_msg)) \<Longrightarrow>
    ((p1, p2), x1, x2) \<in># S_out w \<Longrightarrow>
    \<exists>c'. step_dis' (Out (p1, p2) (x1, x2)) (conf_instance ws S_in S_out (Logic_Dis (dt ipp opp os f) t_msg pact)) c' \<and>
         (\<exists>S_in' S_out' os' t_msg'.
             op_wrapper (bind_mset UNIV S_in) (remove1_mset ((p1, p2), x1, x2) (bind_mset UNIV S_out)) (compile_dataflow ws (Logic (dt ipp opp os f) t_msg)) =
             op_wrapper (bind_mset UNIV S_in') (bind_mset UNIV S_out') (compile_dataflow ws (Logic (dt ipp opp os' f) t_msg')) \<and>
             c' = conf_instance ws S_in' S_out' (Logic_Dis (dt ipp opp os' f) t_msg' pact))"
  using Test_case_Out[where dt = "Logic_Dis (dt ipp opp os f) t_msg pact"]
  by fastforce

(*
lemma Test_case_Inp: "io = Tau \<Longrightarrow>
    step (Inp (p1, p2) (x1, x2)) (compile_dataflow ws (Logic (dt ipp opp os f) t_msg)) op' \<Longrightarrow>
    op = op_wrapper (remove1_mset ((p1, p2), x1, x2) (bind_mset UNIV S_in)) (bind_mset UNIV S_out) op' \<Longrightarrow>
    \<exists>c'. step_dis' Tau (conf_instance ws S_in S_out (Logic_Dis (dt ipp opp os f) t_msg pact)) c' \<and>
         (\<exists>S_in' S_out' os' t_msg'.
             op_wrapper (remove1_mset ((p1, p2), x1, x2) (bind_mset UNIV S_in)) (bind_mset UNIV S_out) op' = op_wrapper (bind_mset UNIV S_in') (bind_mset UNIV S_out') (compile_dataflow ws (Logic (dt ipp opp os' f) t_msg')) \<and>
             c' = conf_instance ws S_in' S_out' (Logic_Dis (dt ipp opp os' f) t_msg' pact))"
  apply(rule exI[where x = "conf_instance ws (map_entry undefined (remove1_mset ((p1, p2), x1, x2)) S_out) S_out (Logic_Dis (dt ipp opp os f) t_msg pact)"])
  apply(rule conjI)
  subgoal
    sorry
  subgoal
    unfolding compile_dataflow_def dataflow_tree_to_operator_def
    apply simp
    apply(erule step_dataflow_op_elim; simp)
    apply(erule step_map_op_elim; simp)
    apply(rule exI[where x = "S_in(undefined := remove1_mset ((p1, p2), x1, x2) (S_in undefined))"])
    apply(rule exI[where x = "S_out"])
    apply(rule exI[where x = "os"])
    apply(rule exI[where x = "t_msg"])
    apply auto
    subgoal for io' op''
      apply(cases io'; (auto split: option.splits))
    sorry
  done
*)
*)



(*Not needed by work do it not work*)
instantiation cset :: (enum) enum
begin

definition
  enum_cset :: "'a cset buf" where
    "enum_cset = undefined"

definition
  enum_all_cset :: "('a cset \<Rightarrow> bool) \<Rightarrow> bool" where
    "enum_all_cset f = undefined"

definition
  enum_ex_cset :: "('a cset \<Rightarrow> bool) \<Rightarrow> bool" where
    "enum_ex_cset f = undefined"

instance
  sorry
(*sketch doesn't work ? ?*)
end

lemma csome_elem_single[simp] : "csome_elem {| x |} = x"
  by(auto simp add: csome_elem_def)

definition "init_exchange_conf =
   \<lparr> c_temp = [],
     c_glob = [] \<rparr>"

definition "compile_dataflow_dis w chns dt temp' glob' = (let summary = dataflow_dis_tree_to_graph dt in
                                    let op = snd (dataflow_dis_tree_to_operator w chns dt) in
                                    let sg = init_subgraph summary (map (\<lambda> (nid, p). (Loc nid (Src p), bot, 1)) (List.product Enum.enum Enum.enum)) in
                                    dataflow_dis_op sg (exchange_conf_one.make temp' glob') op)"

definition init_conf' where 
  "init_conf' chns S_in S_out temp' glob' dt =
  \<lparr> msg = \<lambda> _ _. empty_mset,
    prog_msg = \<lambda> _ _. [],
    ops = \<lambda> w. op_wrapper (S_in w) (S_out w) (compile_dataflow_dis w chns (dt w) temp' glob'),
    used_wire = \<lambda> _. None \<rparr>"

abbreviation conf_instance where
  "conf_instance ws inps S temp' glob' op \<equiv> (init_conf' ws  (\<lambda> w. case_option LNil (case_sum (\<lambda> p. lmap Inr (inps w p)) (\<lambda> _. LNil))) (\<lambda> w. (image_mset (\<lambda> (x,y). (Some (w,x), Inr y)) (S w))) temp' glob' op)"

definition "init_subgraph_ext summary pt_tr' upfro' =
   \<lparr> pt_tr = pt_tr',
   edges = graph_to_edges summary,
   summ = summary, upfro = upfro' \<rparr>"

definition "compile_dataflow_ext chns pt_tr' upfro' dt = (let summary = dataflow_tree_to_graph dt in
                                    let op = dataflow_tree_to_operator chns dt in
                                    let sg = init_subgraph_ext summary pt_tr' upfro' in
                                    dataflow_op sg op)"

definition "compile_dataflow_dis_ext w chns dt pt_tr' upfro' temp' glob' = (let summary = dataflow_dis_tree_to_graph dt in
                                    let op = snd (dataflow_dis_tree_to_operator w chns dt) in
                                    let sg = init_subgraph_ext summary pt_tr' upfro' in
                                    dataflow_dis_op sg (exchange_conf_one.make temp' glob') op)"

definition init_conf'_ext where 
  "init_conf'_ext chns S_in S_out dt pt_tr' upfro' temp' glob' =
  \<lparr> msg = \<lambda> _ _. empty_mset,
    prog_msg = \<lambda> _ _. [],
    ops = \<lambda> w. op_wrapper (S_in w) (S_out w) (compile_dataflow_dis_ext w chns (dt w) (pt_tr' w) (upfro' w) temp' glob'),
    used_wire = \<lambda> _. None \<rparr>"

abbreviation conf_instance_ext where
  "conf_instance_ext ws inps S pt_tr' upfro' temp' glob' op \<equiv> 
  (init_conf'_ext ws (\<lambda> w. case_option LNil (case_sum (\<lambda> p. lmap Inr (inps w p)) (\<lambda> _. LNil))) 
  (\<lambda> w. (image_mset (\<lambda> (x,y). (Some (w,x), Inr y)) (S w))) op pt_tr' upfro' temp' glob')"

lemma dataflow_tree_to_graph_op_invariant: "dataflow_tree_to_graph (Logic op t_msg) = dataflow_tree_to_graph (Logic op' t_msg)"
  by(auto simp add: dataflow_tree_to_graph_def)

(* My undefined invariant and all the theorems i want to be true about it *)
definition invar where
  "invar inps inpss S Ss os oss pt_tr' pt_trs' upfro' upfros' temp' glob' in_out_rel = undefined"

(*
lemma invar_theorem1: "invar inps inpss S Ss (os :: (_,_,_) operator_state) (oss :: _ \<Rightarrow> (_,_,_) operator_state) \<Longrightarrow> inps p \<noteq> LNil \<Longrightarrow> lhd (inps (0, ipp)) = (d, t) \<Longrightarrow> invar (inps(p := ltl (inps p))) inpss S Ss (consumes os p t d) oss"
*)
lemma invar_theorem1: "invar inps inpss S Ss os oss pt_tr' pt_trs' upfro' upfros' temp' glob' in_out_rel \<Longrightarrow> inps p \<noteq> LNil \<Longrightarrow> lhd (inps p) = (d, t) \<Longrightarrow> 
                       invar (inps(p := ltl (inps p))) inpss S Ss (consumes os (snd p) t d) oss pt_tr' pt_trs' upfro' upfros' temp' glob' in_out_rel"
  sorry

lemma invar_theorem2: "invar inps inpss S Ss os oss pt_tr' pt_trs' upfro' upfros' temp' glob' in_out_rel \<Longrightarrow> initia os \<Longrightarrow> outpu os (snd p) = x # xs \<Longrightarrow> 
                       invar inps inpss (add_mset (p, x) S) Ss (os\<lparr>outpu := (outpu os)(snd p := xs)\<rparr>) oss pt_tr' pt_trs' upfro' upfros' temp' glob' in_out_rel"
  sorry

lemma invar_theorem3: "invar inps inpss S Ss os oss pt_tr' pt_trs' upfro' upfros' temp' glob' in_out_rel \<Longrightarrow>
    initia os \<Longrightarrow>
    has_progress os \<Longrightarrow>
    (os', st) = obtain_progress os \<Longrightarrow>
    invar inps inpss S Ss os' oss
     (change_multiplicities (dataflow_tree_to_graph (Logic op t_msg))
       (extract_progress nid (graph_to_edges (dataflow_tree_to_graph (Logic op t_msg))) st) pt_tr')
     pt_trs' (\<lambda>_. True) upfros' temp' glob' in_out_rel"
  sorry

lemma invar_theorem4: "
    upfro' n \<Longrightarrow>
    propagate_all
     (dataflow_tree_to_graph
       (Logic (builder_op b ipp opp os (logic ipp opp)) t_msg))
     pt_tr' =
    Some pt_tr_new \<Longrightarrow>
    \<not> initia os \<Longrightarrow>
    invar inps inpss S Ss
     (os\<lparr>front := frontier \<circ> (\<lambda>p. c_imp pt_tr_new (Loc n (Trg p))), initia := True,
           nfron := True\<rparr>)
     oss pt_tr_new pt_trs' (upfro'(n := False)) upfros' temp' glob' in_out_rel"


lemma Case2: "step (Inp p (lhd (inps p))) (compile_dataflow_ext ws pt_tr' upfro' (Logic (builder_op b ipp opp os (logic ipp opp)) t_msg)) op' \<Longrightarrow>
    invar inps inpss S Ss os oss pt_tr' pt_trs' upfro' upfros' temp' glob' in_out_rel \<Longrightarrow> inps p \<noteq> LNil \<Longrightarrow>
    \<exists>c'. wstep_dis Tau (conf_instance_ext ws inpss Ss pt_trs' upfros' temp' glob' (\<lambda>w. Logic_Dis (builder_op b ipp opp (oss w) (logic ipp opp)) t_msg pact)) c' \<and>
         (\<exists>inps' inpss' S' Ss' os' oss' pt_tr'' pt_trs'' upfro'' upfros'' temp'' glob''.
             op_wrapper (inps(p := ltl (inps p))) S op' =
             op_wrapper inps' S' (compile_dataflow_ext ws pt_tr'' upfro'' (Logic (builder_op b ipp opp os' (logic ipp opp)) t_msg)) \<and>
             (c' = conf_instance_ext ws inpss' Ss' pt_trs'' upfros'' temp'' glob'' (\<lambda>w. Logic_Dis (builder_op b ipp opp (oss' w) (logic ipp opp)) t_msg pact) \<and>
                 invar inps' inpss' S' Ss' os' oss' pt_tr'' pt_trs'' upfro'' upfros'' temp'' glob'' in_out_rel))"
  apply(rule exI[where x = "conf_instance_ext ws inpss Ss pt_trs' upfros' temp' glob' (\<lambda>w. Logic_Dis (builder_op b ipp opp (oss w) (logic ipp opp)) t_msg pact)"])
  apply(auto dest!: map_IO_elim elim!: step_builder_op_elim step_map_op_elim step_dataflow_op_elim 
      simp add: compile_dataflow_ext_def wstep_dis_refl dataflow_tree_to_operator_def split: option.splits)
  subgoal for p' x1 x2
    apply(rule exI[where x = "map_entry (0, p') ltl inps"])
    apply(rule exI[where x = "inpss"])
    apply(rule exI[where x = "S"])
    apply(rule exI[where x = "Ss"])
    apply(rule exI[where x = "consumes os p' x2 x1"])
    apply(rule exI[where x = "oss"])
    apply(rule exI[where x = "pt_tr'"])
    apply(rule exI[where x = "pt_trs'"])
    apply(rule exI[where x = "upfro'"])
    apply(rule conjI)
    subgoal
      using dataflow_tree_to_graph_op_invariant
      by metis
    subgoal
      apply(rule exI[where x = "upfros'"])
      apply(rule exI[where x = "temp'"])
      apply(rule exI[where x = "glob'"])
      using invar_theorem1
      by fastforce
    done
  done

lemma Case3: "step (Out p x) (compile_dataflow_ext ws pt_tr' upfro' (Logic (builder_op b ipp opp os (logic ipp opp)) t_msg)) op' \<Longrightarrow>
    invar inps inpss S Ss os oss pt_tr' pt_trs' upfro' upfros' temp' glob' in_out_rel \<Longrightarrow>
    \<exists>c'. wstep_dis Tau
          (conf_instance_ext ws inpss Ss pt_trs' upfros' temp' glob'
            (\<lambda>w. Logic_Dis (builder_op b ipp opp (oss w) (logic ipp opp)) t_msg pact))
          c' \<and>
         (\<exists>inps' inpss' S' Ss' os' oss' pt_tr'' pt_trs'' upfro''.
             op_wrapper inps (add_mset (p, x) S) op' =
             op_wrapper inps' S' (compile_dataflow_ext ws pt_tr'' upfro'' (Logic (builder_op b ipp opp os' (logic ipp opp)) t_msg)) \<and>
             (\<exists>upfros'' temp'' glob''.
                 c' =
                 conf_instance_ext ws inpss' Ss' pt_trs'' upfros'' temp'' glob''
                  (\<lambda>w. Logic_Dis (builder_op b ipp opp (oss' w) (logic ipp opp)) t_msg pact) \<and>
                 invar inps' inpss' S' Ss' os' oss' pt_tr'' pt_trs'' upfro'' upfros'' temp'' glob'' in_out_rel))"
  apply(rule exI[where x = "conf_instance_ext ws inpss Ss pt_trs' upfros' temp' glob' (\<lambda>w. Logic_Dis (builder_op b ipp opp (oss w) (logic ipp opp)) t_msg pact)"])
  apply(auto dest!: map_IO_elim elim!: step_builder_op_elim step_map_op_elim step_dataflow_op_elim 
      simp add: compile_dataflow_ext_def wstep_dis_refl dataflow_tree_to_operator_def split: option.splits)
  subgoal for p' x1 x2 xs
    apply(rule exI[where x = "inps"])
    apply(rule exI[where x = "inpss"])
    apply(rule exI[where x = "add_mset ((0, p'), x1, x2) S"])
    apply(rule exI[where x = "Ss"])
    apply(rule exI[where x = "os\<lparr>outpu := (outpu os)(p' := xs)\<rparr>"])
    apply(rule exI[where x = "oss"])
    apply(rule exI[where x = "pt_tr'"])
    apply(rule exI[where x = "pt_trs'"])
    apply(rule exI[where x = "upfro'"])
    apply(rule conjI)
    subgoal
      using dataflow_tree_to_graph_op_invariant
      by metis
    subgoal
      apply(rule exI[where x = "upfros'"])
      apply(rule exI[where x = "temp'"])
      apply(rule exI[where x = "glob'"])
      using invar_theorem2
      by fastforce
    done
  done

lemma Case4: "step io (builder_op b ipp opp os (logic ipp opp)) op'' \<Longrightarrow>
     map_IO (case_option (Inl 0) (\<lambda>p. Inr (0, p))) (case_option (Inl 0) (\<lambda>p. Inr (0, p))) id io = Out (Inl nid) (Inl (Inl st)) \<Longrightarrow>
    invar inps inpss S Ss os oss (pt_tr' :: (('g :: {enum,minus,one,plus,zero,hashable,linorder}, _) location, _) configuration) pt_trs' upfro' upfros' temp' glob' in_out_rel \<Longrightarrow>
    \<exists>c'. wstep_dis Tau (conf_instance_ext ws inpss Ss pt_trs' upfros' temp' glob' (\<lambda>w. Logic_Dis (builder_op b ipp opp (oss w) (logic ipp opp)) t_msg pact)) c' \<and>
         (\<exists>inps' inpss' S' Ss' os' oss' (pt_tr'' :: (('g, _) location, _) configuration) pt_trs'' upfro''.
             op_wrapper inps S
              (dataflow_op
                (init_subgraph_ext (dataflow_tree_to_graph (Logic (builder_op b ipp opp os (logic ipp opp)) t_msg)) pt_tr' upfro'
                 \<lparr>upfro := \<lambda>_. True,
                    pt_tr :=
                      change_multiplicities (summ (init_subgraph_ext (dataflow_tree_to_graph (Logic (builder_op b ipp opp os (logic ipp opp)) t_msg)) pt_tr' upfro'))
                       (extract_progress nid (edges (init_subgraph_ext (dataflow_tree_to_graph (Logic (builder_op b ipp opp os (logic ipp opp)) t_msg)) pt_tr' upfro')) st)
                       (pt_tr (init_subgraph_ext (dataflow_tree_to_graph (Logic (builder_op b ipp opp os (logic ipp opp)) t_msg)) pt_tr' upfro'))\<rparr>)
                (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, p))) (case_option (Inl 0) (\<lambda>p. Inr (0, p))) op'')) =
             op_wrapper inps' S'
              (dataflow_op (init_subgraph_ext (dataflow_tree_to_graph (Logic (builder_op b ipp opp os' (logic ipp opp)) t_msg)) pt_tr'' upfro'')
                (map_op (case_option (Inl 0) (\<lambda>p. Inr (0, p))) (case_option (Inl 0) (\<lambda>p. Inr (0, p))) (builder_op b ipp opp os' (logic ipp opp)))) \<and>
             (\<exists>upfros'' temp'' glob''.
                 c' = conf_instance_ext ws inpss' Ss' pt_trs'' upfros'' temp'' glob'' (\<lambda>w. Logic_Dis (builder_op b ipp opp (oss' w) (logic ipp opp)) t_msg pact) \<and>
                 invar inps' inpss' S' Ss' os' oss' pt_tr'' pt_trs'' upfro'' upfros'' temp'' glob'' in_out_rel))"
          apply(auto dest!: map_IO_elim elim!: step_builder_op_elim simp add: tmap_op_def split: option.splits)
          subgoal for os'
            apply(rule exI[where x = "conf_instance_ext ws inpss Ss pt_trs' upfros' temp' glob' (\<lambda>w. Logic_Dis (builder_op b ipp opp (oss w) (logic ipp opp)) t_msg pact)"])
            apply(simp add: wstep_dis_refl)
            apply(rule exI[where x = "inps"])
            apply(rule exI[where x = "inpss"])
            apply(rule exI[where x = "S"])
            apply(rule exI[where x = "Ss"])
            apply(rule exI[where x = "os'"])
            apply(rule exI[where x = "oss"])
            apply(rule exI[where x = "change_multiplicities (dataflow_tree_to_graph (Logic (builder_op b ipp opp os (logic ipp opp)) t_msg))
     (extract_progress 0 (graph_to_edges (dataflow_tree_to_graph (Logic (builder_op b ipp opp os (logic ipp opp)) t_msg))) st) pt_tr'"])
            apply(rule exI[where x = "pt_trs'"])
            apply(rule exI[where x = "(\<lambda>_. True)"])
            apply(rule conjI)
            subgoal
              apply(rule arg_cong[where f = "\<lambda> os. op_wrapper _ _ (dataflow_op os _)"])
              unfolding init_subgraph_ext_def
              apply auto
              subgoal
                unfolding obtain_progress_def 
                using dataflow_tree_to_graph_op_invariant
                by metis
              subgoal
                unfolding obtain_progress_def graph_to_edges_def dataflow_tree_to_graph_def
                by fastforce
              done
            apply(rule exI[where x = "upfros'"])
            apply(rule exI[where x = "temp'"])
            apply(rule exI[where x = "glob'"])
            apply auto
            using invar_theorem3
            by fast
          done



(*TODO TODO instead of using bisim_dis use one that uses wstep instead of step, since we want to not take an action (or multiple) TODO TODO*)
(*TODO TODO make a condition between inps and inpss maybe using countable multisets? and for os and oss TODO TODO*)
lemma "invar inps inpss S Ss os oss pt_tr' pt_trs' upfro' upfros' temp' glob' in_out_rel \<Longrightarrow> (op_wrapper inps S (compile_dataflow_ext ws pt_tr' upfro' (Logic (tmap_op ipp opp (os :: (_,_,_,_,_) operator_state_ty2) f) t_msg))) ~dw 
      conf_instance_ext ws inpss Ss pt_trs' upfros' temp' glob' (\<lambda> w. (Logic_Dis (tmap_op ipp opp ((oss :: 'w :: enum \<Rightarrow> (_,_,_,_,_) operator_state_ty2) w) f) t_msg pact)) "
proof (coinduction arbitrary: inps inpss S Ss os oss pt_tr' pt_trs' upfro' upfros' temp' glob')
  fix   inps :: "'a \<times> 'b \<Rightarrow> ('c \<times> 'd) llist"
    and inpss :: "'w \<Rightarrow> 'a \<times> 'b \<Rightarrow> ('c \<times> 'd) llist"
    and S :: "(('a \<times> 'b) \<times> 'c \<times> 'd) multiset"
    and Ss :: "'w \<Rightarrow> (('a \<times> 'b) \<times> 'c \<times> 'd) multiset"
    and os :: "('b, 'c, 'e, 'f, 'd) operator_state_ty2"
    and oss :: "'w \<Rightarrow> ('b, 'c, 'e, 'f, 'd) operator_state_ty2"
    and pt_tr' :: "(('a, 'b) location, 'd) configuration"
    and pt_trs' :: "'w \<Rightarrow> (('a, 'b) location, 'd) configuration"
    and upfro' :: "'a \<Rightarrow> bool"
    and upfros' :: "'w \<Rightarrow> 'a \<Rightarrow> bool"
    and temp' :: "(('a, 'b) location \<times> 'd \<times> int) buf"
    and glob' :: "(('a, 'b) location \<times> 'd \<times> int) buf"
  assume invar: "invar inps inpss S Ss os oss pt_tr' pt_trs' upfro' upfros' temp' glob' in_out_rel"
(* TODO try to see if local definition makes things more readable
  define op1 where "op1 = (\<lambda> f_xs S S' os t_msg. op_wrapper (\<lambda>x. bind_mset UNIV (f_xs x)) (cUNION cUNIV S) (cUNION cUNIV S') (compile_dataflow ws (Logic (tmap_op ip op os f) t_msg)))"
*)
  let ?op1 = "\<lambda> inps S os pt_tr' upfro'. op_wrapper inps S (compile_dataflow_ext ws pt_tr' upfro' (Logic (tmap_op ipp opp (os :: (_,_,_,_,_) operator_state_ty2) f) t_msg))"
  let ?c1 = "\<lambda> inpss Ss oss pt_trs' upfros' temp' glob'. conf_instance_ext ws inpss Ss pt_trs' upfros' temp' glob' (\<lambda> w. (Logic_Dis (tmap_op ipp opp (oss w) f) t_msg pact))"
(*
  let ?c1 = "\<lambda> f_xs S S' os t_msg. init_conf' ws (\<lambda>w. case_option {#} (case_sum (\<lambda>e'. Inr `# f_xs e' w) (\<lambda>b. {#}))) (\<lambda>w. (\<lambda>(x, y). (Some (w, x), Inr y)) |`| S w) (\<lambda>w. (\<lambda>(x, y). (Some (w, x), Inr y)) |`| S' w) (Logic_Dis (tmap_op ip op os f) t_msg pact)"
*)
  have "wsim_dis (\<lambda>op c. (\<exists> inps inpss S Ss (os :: (_,_,_,_,_) operator_state_ty2) (oss :: _ \<Rightarrow> (_,_,_,_,_) operator_state_ty2) pt_tr' pt_trs' upfro' upfros' temp' glob'. 
    op = ?op1 inps S os pt_tr' upfro' \<and> c = ?c1 inpss Ss oss pt_trs' upfros' temp' glob' \<and> invar inps inpss S Ss os oss pt_tr' pt_trs' upfro' upfros' temp' glob' in_out_rel)) (?op1 inps S os pt_tr' upfro') (?c1 inpss Ss oss pt_trs' upfros' temp' glob')"
    unfolding wsim_dis_def
    apply simp
    apply safe
    subgoal for io op
      apply(drule step_op_wrapper_elim; simp)
      apply safe
      (* Case where an element is written from the multiset S, use something like Test_case_Out_Logic*)
      subgoal for p1 p2 d t
        sorry
      (* Case where dataflow_op read an element from inps - Done - Relies on invar_theorem1*)
      subgoal for p1 p2 op'
        using invar Case2
        unfolding tmap_op_def
        by fast
      (* Case where dataflow_op write an element to S - Done - Relies on invar_theorem2*)
      subgoal for p1 p2 x1 x2 op'
        using invar Case3
        unfolding tmap_op_def
        by fastforce
      (* Case where dataflow_op makes a Tau step*)
      subgoal for op'
        apply(simp add: compile_dataflow_ext_def)
        apply(erule step_dataflow_op_elim; simp add: dataflow_tree_to_operator_def; erule step_map_op_elim; simp?)
        (* Case where the build_op's logic is applied*)
(*
        subgoal premises prems for op''
*)
        subgoal for op''
          apply(erule thin_rl)
          apply(erule HOL.cnf.weakening_thm)
          apply(erule HOL.cnf.weakening_thm)
(*
          unfolding tmap_op_def
          apply(erule step_builder_op_elim; simp)
          subgoal for os'
            apply(erule HOL.cnf.weakening_thm[where P = "op'' = _"])
            apply(subst (asm) tmap_logic_def)
            apply simp
            apply(erule HOL.cnf.weakening_thm[where P = "os' = _"])
            apply(rule exI[where x = "conf_instance ws inpss Ss (\<lambda>w. Logic_Dis (builder_op False {|ipp|} {|opp|} (oss w) (tmap_logic ipp opp f)) t_msg pact)"])
            apply(simp add: wstep_dis_refl)
            apply(rule exI[where x = "inps"])
            apply(rule exI[where x = "inpss"])
            apply(rule exI[where x = "S"])
            apply(rule exI[where x = "Ss"])
*)
          sorry
        (* Case where ...*)
        subgoal for nid st io op''
          unfolding tmap_op_def
          using Case4 invar
          by fast
        (* Case where ...*)
        subgoal for nid imp_fron sg' io' op''
          apply(erule HOL.cnf.weakening_thm)
          apply(erule HOL.cnf.weakening_thm)
          apply(erule HOL.cnf.weakening_thm)
          apply(erule HOL.cnf.weakening_thm[where P = "imp_fron = _"])
          apply(erule HOL.cnf.weakening_thm[where P = "op' = _"])
          apply(subst (asm) init_subgraph_ext_def; simp)
          apply(auto dest!: map_IO_elim elim!: step_builder_op_elim simp add: tmap_op_def split: option.splits)
          subgoal for pt_tr_new
            apply(erule HOL.cnf.weakening_thm[where P = "io' = _"])
            apply(erule HOL.cnf.weakening_thm[where P = "nid = _"])
            apply(erule HOL.cnf.weakening_thm[where P = "op'' = _"])
            apply(subst (asm) init_subgraph_ext_def; simp)
            apply(subst (asm) init_subgraph_ext_def; simp)
            unfolding init_subgraph_ext_def
            apply(simp)
            unfolding init_subgraph_ext_def[symmetric]
            apply(rule exI[where x = "conf_instance_ext ws inpss Ss pt_trs' upfros' temp' glob'
            (\<lambda>w. Logic_Dis (builder_op False {|ipp|} {|opp|} (oss w) (tmap_logic ipp opp f))
                   t_msg pact)"])
            apply(simp add: wstep_dis_refl)
            apply(rule exI[where x = "inps"])
            apply(rule exI[where x = "inpss"])
            apply(rule exI[where x = "S"])
            apply(rule exI[where x = "Ss"])
            apply(rule exI[where x = "os\<lparr>front := frontier \<circ> (\<lambda>p. c_imp pt_tr_new (Loc 0 (Trg p))), initia := True,
                    nfron := True\<rparr>"])
            apply(rule exI[where x = "oss"])
            apply(rule exI[where x = "pt_tr_new"])
            apply(rule exI[where x = "pt_trs'"])
            apply(rule exI[where x = "upfro'(0 := False)"])
            apply(rule conjI)
            subgoal
              using dataflow_tree_to_graph_op_invariant
              by metis
            apply(rule exI[where x = "upfros'"])
            apply(rule exI[where x = "temp'"])
            apply(rule exI[where x = "glob'"])
            apply simp

            
            sorry
        done
      done
    subgoal for io op
      sorry
    done
  then show "\<exists>op c. ?op1 inps S os pt_tr' upfro' = op \<and> ?c1 inpss Ss oss pt_trs' upfros' temp' glob' = c \<and>
    wsim_dis (\<lambda>op c. (\<exists>inps inpss S Ss (os :: (_,_,_,_,_) operator_state_ty2) (oss :: _ \<Rightarrow> (_,_,_,_,_) operator_state_ty2) pt_tr' pt_trs' upfro' upfros' temp' glob'.
       op = ?op1 inps S os pt_tr' upfro' \<and> c = ?c1 inpss Ss oss pt_trs' upfros' temp' glob' \<and> invar inps inpss S Ss os oss pt_tr' pt_trs' upfro' upfros' temp' glob' in_out_rel) \<or> op ~dw c) op c"
    apply simp
    apply(rule predicate2D[OF wsim_dis_mono, rotated], assumption)
    by blast
  qed




end