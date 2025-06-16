theory Timely_Operators

imports
  Operator
  BNA_Operators
  Progress_Tracking.Propagate
  Eval
  "HOL-Library.While_Combinator"
  Executable
  Zero_Cyc_Check 
(*    "HOL-Library.Code_Target_Nat" 
  "HOL-Library.Code_Target_Int"   *)
begin 

(*
  TODO:
  Correctness of dataflow compilation
  Loops
  Scopes (change timestamp type)
  Type inference for locations (if it is not so hard)
  Nominal wiring (if it is not so hard)
  Correctness of max_op
  collatz_op
  Correctness of collatz_op
  wcc_op: https://timelydataflow.github.io/differential-dataflow/chapter_4/chapter_4_1.html
  Correctness of wcc_op
*)

(* FIXME: move me *)
lemma zero_one[code]:
  "(0 :: 1) = 1"
  by simp

(* Inspired by timely/src/progress/mod.rs:61 *)
datatype 'p port = Trg (idp: 'p) | Src (idp: 'p)
abbreviation is_Src where "is_Src x \<equiv> (case x of Src _ \<Rightarrow> True | _ \<Rightarrow> False)"
abbreviation is_Trg where "is_Trg x \<equiv> (case x of Trg _ \<Rightarrow> True | _ \<Rightarrow> False)"

(* Inspired by timely/src/progress/mod.rs:19 *)
datatype ('id, 'p) location = Loc (node: 'id) (port: "'p port")

instantiation port :: (enum) enum
begin
definition
  "enum_port = map Trg enum_class.enum @ map Src enum_class.enum"

definition "enum_all_port P \<longleftrightarrow> list_all (\<lambda> x. P (Src x)) enum_class.enum \<and> list_all (\<lambda> x. P (Trg x)) enum_class.enum"

definition "enum_ex_port P \<longleftrightarrow> list_ex (\<lambda> x. P (Src x)) enum_class.enum \<or> list_ex (\<lambda> x. P (Trg x)) enum_class.enum"

instance
  apply standard
  subgoal
    apply (simp add: enum_port_def enum_UNIV)
    apply (metis IntE UNIV_eq_I Un_Int_eq(2,3) port.exhaust rangeI)
    done
  subgoal
    by (auto simp add: enum_class.enum_distinct enum_port_def enum_UNIV distinct_map inj_on_def)
  subgoal
    apply (simp add:  enum_all_port_def enum_UNIV list_all_iff)
    apply (metis port.exhaust)
    done
  subgoal
    apply (simp add:  enum_ex_port_def enum_UNIV list_ex_iff)
    apply (metis port.exhaust)
    done
  done
end

instantiation location :: (enum, enum) enum
begin
definition
  "enum_location = map (\<lambda> (x, y). Loc x y) (List.product enum_class.enum enum_class.enum)"

definition
  "enum_all_location P \<longleftrightarrow> enum_class.enum_all (%x. enum_class.enum_all (%y. P (Loc x y)))"

definition
  "enum_ex_location P = enum_class.enum_ex (%x. enum_class.enum_ex (%y. P (Loc x y)))"

instance
  apply standard
  apply (simp_all add: distinct_map enum_location_def enum_UNIV enum_distinct enum_all_location_def enum_ex_location_def split: prod.splits location.splits)
  apply (metis case_prod_conv location.exhaust surj_def)
  apply (auto simp add: inj_def enum_class.enum_distinct intro!: distinct_product)[1]
  apply (metis location.collapse)+
  done
end

instantiation port :: (ord) ord
begin

fun less_eq_port :: "'a port \<Rightarrow> 'a port \<Rightarrow> bool" where
  "less_eq_port (Trg t) (Trg u) = (t \<le> u)"
| "less_eq_port (Src t) (Src u) = (t \<le> u)"
| "less_eq_port (Trg t) (Src u) = True"
| "less_eq_port _ _ = False"

definition less_port where
  "(x::'a port) < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

instance ..
end

instance port :: (preorder) preorder
proof
  fix x y z :: "'a port"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (rule less_port_def)
  show "x \<le> x"
    apply (cases x)
    apply auto
    done
  assume "x \<le> y" and "y \<le> z" thus "x \<le> z"
    apply (cases x; cases y; cases z)
    apply (auto elim!: order_trans)
    done
qed

instance port :: (order) order
  apply standard
  subgoal for x y
    apply (cases x; cases y)
    apply (auto intro!: antisym elim: less_eq_port.cases)
    done
  done


instantiation location :: (linorder, linorder) linorder
begin
definition
  "less_eq_location = (\<lambda> x y. case (x, y) of (Loc n1 p1, Loc n2 p2) \<Rightarrow> n1 = n2 \<and> p1 \<le> p2 \<or> n1 \<noteq> n2 \<and> n1 < n2)"

definition
  "less_location = (\<lambda> x y. case (x, y) of (Loc n1 p1, Loc n2 p2) \<Rightarrow> n1 = n2 \<and> p1 < p2 \<or> n1 \<noteq> n2 \<and> n1 < n2)"

instance 
  apply standard
  apply (auto intro!: elim!: less_eq_port.cases simp add: less_port_def less_eq_location_def less_location_def split: location.splits port.splits)[4]
  subgoal for x y
    apply (cases x; cases y; simp; hypsubst_thin)
    subgoal for n1 p1 n2 p2
      apply (cases "n1 = n2")
      subgoal
        apply (cases "p1 \<le> p2")
        apply (auto intro!: elim!: less_eq_port.cases simp add: less_port_def less_eq_location_def less_location_def split: location.splits port.splits)
        apply (smt (verit, del_insts) less_eq_port.elims(1) less_eq_port.simps(1) nle_le port.distinct(1) port.inject(2))
        done
      subgoal
        apply (auto intro!: elim!: less_eq_port.cases simp add: less_port_def less_eq_location_def less_location_def split: location.splits port.splits)
        done
      done
    done
  done
end

(* Inspired by timely/src/progress/change_batch.rs:12 *)
type_synonym 'a change_batch = "'a list"

(* Inspired by timely/src/progress/subgraph.rs:237 *)
record ('id, 'p, 't) subgraph =
  pt_tr :: "(('id, 'p) location, 't) configuration"
  (* We consider local_pointstamp and final_pointstamp as the same thing in this non-distributed version *)
  lo_pt :: "(('id, 'p) location \<times> 't \<times> int) change_batch"
  edges :: "('id, 'p) location \<Rightarrow> ('id, 'p) location list"
  summ :: "('id, 'p) location \<Rightarrow> ('id, 'p) location \<Rightarrow> 't antichain"

corec writes where
  "writes op p xs =
    (case xs of [] \<Rightarrow> case_op Read Write Choice Silent op | x #xs \<Rightarrow> Write (writes op p xs) p x)"

lemma foo[friend_of_corec_simps]:
  "(if snd (snd x) = [] then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x)))) else ctor_op (Abs_op_pre_op (Inl (Inr (algrho (fst x, fst (snd x), btl (snd (snd x))), fst (snd x), bhd (snd (snd x))))))) =
         (if snd (snd x) = []
         then if isl (Rep_op_pre_op (dtor_op (fst x))) \<and> isl (projl (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
              else if isl (Rep_op_pre_op (dtor_op (fst x))) \<and> \<not> isl (projl (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
                   else if \<not> isl (Rep_op_pre_op (dtor_op (fst x))) \<and> isl (projr (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
                        else ctor_op
                              (Abs_op_pre_op
                                (Inr (Inr (if isl (Rep_op_pre_op (dtor_op (fst x))) then undefined
                                           else if isl (projr (Rep_op_pre_op (dtor_op (fst x)))) then undefined else projr (projr (Rep_op_pre_op (dtor_op (fst x))))))))
         else ctor_op (Abs_op_pre_op (Inl (Inr (algrho (fst x, fst (snd x), btl (snd (snd x))), fst (snd x), bhd (snd (snd x)))))))"
  by (auto split: if_splits)

friend_of_corec writes where
  "writes op p xs =
    (case xs of [] \<Rightarrow> case_op Read Write Choice Silent op | x #xs \<Rightarrow> Write (writes op p xs) p x)"
  apply (rule writes.code)
  apply transfer_prover
  done

declare zmultiset_of_antichain_def[code]

instantiation "num0" :: hashable
begin
  definition [simp]: "hashcode (n :: num0) = uint32_of_int 0"
  definition "def_hashmap_size = (\<lambda>_ :: num0 itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_num0_def)
end

instantiation "num1" :: hashable
begin
  definition [simp]: "hashcode (n :: num1) = uint32_of_int 1"
  definition "def_hashmap_size = (\<lambda>_ :: num1 itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_num1_def)
end

instantiation "bit0" :: (finite) hashable
begin
  definition [simp]: "hashcode (n :: _ bit0) = uint32_of_int (Rep_bit0 n)"
  definition "def_hashmap_size = (\<lambda>_ :: (_ bit0) itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_bit0_def)
end

instantiation "port" :: (hashable) hashable
begin
  definition [simp]: "hashcode (l :: _ port) = (case l of Src a \<Rightarrow> 2 * hashcode a | Trg b \<Rightarrow> 2 * hashcode b + 1)"
  definition "def_hashmap_size = (\<lambda>_ :: ('a port) itself. def_hashmap_size TYPE('a))"
  instance using def_hashmap_size[where ?'a="'a"]
    by(intro_classes)(simp_all add: bounded_hashcode_bounds def_hashmap_size_port_def split: sum.split)
end

instantiation "location" :: (hashable, hashable) hashable
begin
  definition [simp]: "hashcode (l :: (_, _) location) = (hashcode (node l) * 33 + hashcode (port l))"
  definition "def_hashmap_size = (\<lambda>_ :: (('a, 'b) location) itself. def_hashmap_size TYPE('a) + def_hashmap_size TYPE('b))"
  instance using def_hashmap_size[where ?'a="'a"] def_hashmap_size[where ?'a="'b"]
    by(intro_classes)(simp_all add: def_hashmap_size_location_def)
end

instantiation "bit1" :: (finite) hashable
begin
  definition [simp]: "hashcode (n :: _ bit1) = uint32_of_int (Rep_bit1 n)"
  definition "def_hashmap_size = (\<lambda>_ :: (_ bit1) itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_bit1_def)
end

definition summ_test :: "3 \<Rightarrow> 3 \<Rightarrow> (nat antichain)" where
  "summ_test l1 l2 = 
  (if l1 = 0 \<and> l2 = 1 then frontier {# 0 #}\<^sub>z else
   if l1 = 1 \<and> l2 = 0 then frontier {# 0 #}\<^sub>z else
   frontier {#}\<^sub>z)"


definition mymin_code :: "(nat \<times> ('a :: linorder, 'b  :: linorder) location) set \<Rightarrow> (nat \<times> ('a, 'b) location)" 
  where [code del]: "mymin_code = mymin (<)"

lemma mymin_code[code]: "mymin_code (set (x # xs)) = fold (\<lambda>a b. if t_loc_linord (<) a b then a else b) xs x"
  unfolding mymin_code_def
  apply (rule linorderMin)
  apply unfold_locales
  apply auto
  done

lemma  antichain_sum_empty[simp]:
  "A + {}\<^sub>A = A"
  apply transfer
  apply simp
  apply (smt (verit, ccfv_threshold) in_minimal_antichain incomparable_def order_class.order_eq_iff order_less_imp_not_eq subset_iff)
  done


lift_definition zequal :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> bool" is
  "\<lambda> (M, N) (P, Q). (M-N) = (P-Q) \<and> (N-M) = (Q-P)"
  apply (auto simp: equiv_zmset_def)
  apply (metis (full_types) Multiset.diff_right_commute add_diff_cancel_right')
  apply (metis Multiset.diff_right_commute add_diff_cancel_left')
  apply (metis add_diff_cancel_right' cancel_ab_semigroup_add_class.diff_right_commute)
  by (metis Multiset.diff_right_commute add_diff_cancel_left')

definition "reachable_locations summary \<equiv> { loc . \<exists> loc' .
     \<not> is_empty_antichain (summary loc loc') \<or> \<not> is_empty_antichain (summary loc' loc) }"

definition worklist_is_empty where
  "worklist_is_empty summary c = Set.Ball (reachable_locations summary) (\<lambda> loc. zequal (c_work c loc) {#}\<^sub>z)"

lift_definition is_empty_antichain :: "'a :: order antichain \<Rightarrow> bool" is "Set.is_empty".

lemma set_zmset_code[code]:
  "set_zmset (abs_zmultiset x) = (case x of (A, B) \<Rightarrow> set_mset (A - B) \<union> set_mset (B - A))"
  unfolding set_zmset_def
  by transfer (auto simp: set_mset_def)

lemma frontier_code[code]:
  "set_antichain (frontier x) = minimal_antichain {t \<in> set_zmset x. 0 < zcount x t}"
  by transfer' (auto intro!: arg_cong[of _ _ minimal_antichain] zcount_inI)

abbreviation "has_zero_cyc s \<equiv> cyc_checker_codeT (graph_from_weights s)"

value "has_zero_cyc summ_test"

datatype ('id, 'p, 's, 'd) dataflow_tree = 
   "apply": Logic "('p option, 'p option, 's + 'd) op"
  | Comp "'id \<times> 'p \<Rightarrow> ('id \<times> 'p) option" "('id, 'p, 's, 'd) dataflow_tree" "('id, 'p, 's, 'd) dataflow_tree"

term loop_op

fun compile_dataflow_tree_aux :: "'id :: {minus, plus, one, ord} \<Rightarrow> ('id, 'p, 's, 'd) dataflow_tree \<Rightarrow>
    'id \<times> (('id, 'p) location \<Rightarrow> ('id, 'p) location \<Rightarrow> nat antichain) \<times> ('id + 'id \<times> 'p, 'id + 'id \<times> 'p, 's + 'd) op" where
 "compile_dataflow_tree_aux n (Logic op) = (n + 1,
    (\<lambda> l1 l2. 
    if n = node l1 \<and> n = node l2 \<and> is_Trg (port l1) \<and> is_Src (port l2) 
    then frontier (abs_zmultiset (mset [0], {#})) 
    else frontier {#}\<^sub>z),
    map_op (case_option (Inl n) (\<lambda> p. Inr (n, p))) (case_option (Inl n) (\<lambda> p. Inr (n, p))) op)"
| "compile_dataflow_tree_aux n (Comp wire dt1 dt2) = (
    let (n', summary1, op1) = compile_dataflow_tree_aux n dt1 in
    let (n'', summary2, op2) = compile_dataflow_tree_aux n' dt2 in
    (n'', \<lambda> l1 l2. 
     if node l1 \<ge> n \<and> node l1 < n' \<and> node l2 \<ge> n' \<and> is_Src (port l1) \<and> is_Trg (port l2)
     then (case wire (node l1 - n, idp (port l1)) of 
             None \<Rightarrow> frontier {#}\<^sub>z 
           | Some (offset, q) \<Rightarrow> (if node l2 = n' + offset \<and> q = idp (port l2) then frontier (abs_zmultiset (mset [0], {#})) else frontier {#}\<^sub>z )) 
     else summary1 l1 l2 + summary2 l1 l2,
     map_op (case_sum id id) (case_sum id id)
     (comp_op (case_sum (\<lambda> _. None) ((case_option None (Some o Inr)) o (\<lambda> (nid, p). case wire (nid - n, p) of None \<Rightarrow> None | Some (offset, q) \<Rightarrow> Some (n' + offset, q)))) (\<lambda> _. []) op1 op2))
   )"


value  "(fst o snd) (compile_dataflow_tree_aux (0 :: 4)
       (Comp [ (1, 0) \<mapsto> (3, 0) ]
         (Comp (\<lambda> l. None) (Logic \<oslash>) (Logic \<oslash>))
         (Comp (\<lambda> l. None) (Logic \<oslash>) (Logic \<oslash>))))
      (Loc 1 (Src 1)) (Loc 3 (Trg (1 :: 1)))"

definition "compile_dataflow_tree df = (
  let (_, s, op) = compile_dataflow_tree_aux 0 df in
  if \<not> has_zero_cyc s \<and>
     no_self_loop_checker s \<and>
     implementation_graph_checker (weights_to_graph_fun (remove_non_zero_weights s))
  then (s, op)
  else Code.abort (STR ''Control plane could not be build'') (\<lambda> _. (\<lambda> _ _. frontier {#}\<^sub>z, \<oslash>)))"

abbreviation "df_ex1 \<equiv> (Comp [ (1, 0) \<mapsto> (1, 0) ]
         (Comp (\<lambda> l. None) (Logic \<oslash>) (Logic \<oslash>))
         (Comp (\<lambda> l. None) (Logic \<oslash>) (Logic \<oslash>))) :: (4, 4, unit, nat) dataflow_tree"

value "fst (compile_dataflow_tree
       df_ex1)
       (Loc 1 (Src 0)) (Loc 3 (Trg 0))"

lemma compile_dataflow_tree_aux_same_loc:
  "(n'', summar, op) = compile_dataflow_tree_aux n df \<Longrightarrow>
   summar loc loc = {}\<^sub>A"
  apply (induct df arbitrary: n n'' op summar)
  subgoal for l n n' summar
    by (cases loc; simp add: frontier_empty_zmset split: port.splits if_splits)
  subgoal for wire dt1 dt2 n n'' summar
    apply (cases "compile_dataflow_tree_aux n dt1")
    subgoal for n' summar'
      apply (cases "compile_dataflow_tree_aux n' dt2")
      subgoal for n''' summar''
        apply (drule meta_spec[of _ n])
        apply (drule meta_spec[of _ n'])
        apply (drule meta_spec[of _ n'])
        apply (drule meta_spec[of _ n''])
        apply (drule meta_spec)
        apply (drule meta_spec[of _ summar'])
        apply (drule meta_spec)
        apply (drule meta_spec[of _ summar''])
        apply (drule meta_mp)
        apply simp
        apply (drule meta_mp)
         apply simp
        apply (simp split: if_splits)
        apply safe
        subgoal
          by (auto 0 0 simp add: frontier_empty_zmset port.case_eq_if split: if_splits option.splits)
        done
      done
    done
  done

lemma decide_graph_construction:
  assumes "\<not> cyc_checker_codeT \<lparr>gi_V = \<lambda>x. True, gi_E = weights_to_graph_fun (remove_non_zero_weights summary), gi_V0 = enum_class.enum\<rparr>"
  and "graph.path summary loc loc xs" and "xs \<noteq> []"
  and "graph_checker summary"
    and "implementation_graph_checker (weights_to_graph_fun (remove_non_zero_weights summary))"
  shows "t < t + foldr (+) (map (\<lambda>(s, l, t). l) xs) 0"
proof -
  from assms have G: "Graph.graph summary" 
    using graph_checker_correct by blast
  from assms obtain G Rm where E: "((graph_from_weights summary), G) \<in> \<langle>Rm, Id\<rangle> g_impl_rel_ext" 
    using exists_graph implementation_graph_checker_correct by blast
  with assms have D: "Digraph.graph G"
    using Digraph.graph_def using_enum_is_digraph by blast
  from assms have F: "finite ((g_E G)\<^sup>* `` g_V0 G)" 
    using using_enum_is_finite E by blast
  with assms G D F E have A: "acyclic (g_E G \<inter> (g_E G)\<^sup>* `` g_V0 G \<times> UNIV)"
    using cyc_checker_codeT_correct[of G _ Rm] by blast
  with assms E G show ?thesis
    using acyclic_no_zero_cycle[unfolded graph_enum_def] by fast
qed

lemma empty_graph_no_zero_cyc:
  "graph.path summary loc loc xs \<Longrightarrow>
   summary = (\<lambda>_ _. frontier {#}\<^sub>z)  \<Longrightarrow>
   Graph.graph summary \<Longrightarrow>
   xs \<noteq> [] \<Longrightarrow>
   0 < foldr (+) (map (\<lambda>(s, l, t). l) xs) 0"
  apply (induct xs rule: rev_induct)
   apply simp
  subgoal for x xs'
    apply (simp split: prod.splits)
    apply (cases x)
    apply simp
    apply (erule graph.path_AppendE)
    apply assumption
    using frontier_empty_zmset mem_antichain_nonempty apply blast
    done
  done

lemma enum_dataflow_topology_compile_dataflow[simp]:
  "enum_dataflow_topology (fst (compile_dataflow_tree df)) (+)"
  apply standard
       apply simp_all
  subgoal
    unfolding compile_dataflow_tree_def Let_def
    apply (cases "compile_dataflow_tree_aux 0 df"; simp)
    using compile_dataflow_tree_aux_same_loc eq_snd_iff frontier_empty_zmset apply metis
    done
  subgoal for loc xs s
    unfolding compile_dataflow_tree_def Let_def
    apply (cases "compile_dataflow_tree_aux 0 df")
    apply (simp add: no_self_loop_checker_is_graph_checker split: if_splits)
    subgoal
      apply (rule decide_graph_construction[where t=0, simplified, rotated])
          apply assumption+
      done
    subgoal
      apply (rule empty_graph_no_zero_cyc)
         apply assumption+
        apply simp_all
      apply standard
        apply simp_all
      using frontier_empty_zmset apply blast
      done
    done
  done

global_interpretation dataflow_topology_from_tree: enum_dataflow_topology "fst (compile_dataflow_tree df)" "(+)"
  for df
  defines take_step' = "enum_dataflow_topology.take_step (fst (compile_dataflow_tree df)) (+)"
    and after_summary = "dataflow_topology.after_summary (+) :: nat zmultiset \<Rightarrow> nat antichain \<Rightarrow> nat zmultiset"
  by simp

definition take_step_locale where
  "take_step_locale df = take_step' df (<)"

fun take_step where
 "take_step summary (CM loc t delta) c =
  (let c_pointstamps_old = c_pts c loc; c_pointstamps_new = (c_pts c)(loc := update_zmultiset (c_pts c loc) t delta)
   in c\<lparr>c_pts := c_pointstamps_new, c_work := (c_work c)(loc := c_work c loc + frontier_change_code c_pointstamps_old (c_pointstamps_new loc))\<rparr>)"
| "take_step summary PR c =
   (let (t, loc) = mymin_code (t_loc_pairs c); c_implications_old = c_imp c loc; c_implications_new = (c_imp c)(loc := c_imp c loc + {#t' \<in>#\<^sub>z c_work c loc. t' = t#});
    c_worklist_removed_loc = map_entry loc (filter_zmset (\<lambda>t'. t' \<noteq> t)) (c_work c)
    in c\<lparr>c_work := \<lambda>loc'. c_worklist_removed_loc loc' + after_summary (frontier_change_code c_implications_old (c_implications_new loc)) (summary loc loc'),
        c_imp := c_implications_new\<rparr>)"


definition "propagate_all_locale summary df c0 = (while_option (Not o (worklist_is_empty summary))
                                           (take_step_locale df PR) c0)"


declare dataflow_topology_from_tree.take_step.simps[of _ "((<) :: nat \<Rightarrow> _ \<Rightarrow> _)",  folded take_step_locale_def mymin_code_def, code]

abbreviation empty_conf where
  "empty_conf \<equiv> \<lparr>c_work = (\<lambda> _.  {#}\<^sub>z), c_pts = (\<lambda> _.  {#}\<^sub>z), c_imp = (\<lambda> _. {#}\<^sub>z)\<rparr>"

definition "propagate_all summary c0 = (while_option (Not o (worklist_is_empty summary))
                                        (take_step summary PR) c0)"

lemma take_step_fast_code[simp]:
  "take_step_locale df x = take_step (fst (compile_dataflow_tree df)) x"
  unfolding take_step_locale_def
  apply (cases x)
    apply (auto simp add: fun_eq_iff mymin_code_def)
  done

lemma propagate_all_locale_eq_propagate_all:
  "propagate_all_locale (fst (compile_dataflow_tree df)) df c = propagate_all (fst (compile_dataflow_tree df)) c"
  unfolding propagate_all_locale_def Let_def propagate_all_def by (auto split: prod.splits)

fun print_2 where
  "print_2 n = (if n = 0 then STR ''0'' else STR ''1'')"

definition show_port where
  "show_port p = (case p of Src x \<Rightarrow> STR ''SRC '' + (print_2 x) | Trg x \<Rightarrow> STR ''TRG '' + (print_2 x))"

definition show_loc where
  "show_loc x = STR ''node: '' + print_2 (node x) + STR '', port: '' + show_port (port x)"

abbreviation "print_int n \<equiv> (if n \<ge> 0 then show_nat (Int.nat n) else STR ''-'' + show_nat (Int.nat (abs n)) )"

definition "DEBUG = False"

abbreviation "trace \<equiv> (if DEBUG then Debug.tracing else (\<lambda> x y. y))"

lift_definition Max_antichain :: "nat antichain \<Rightarrow> nat" is "\<lambda> x. if Set.is_empty x then 42 else Max x" .

abbreviation "show_frontier x \<equiv> let f = Max_antichain x in if f = 42 then STR ''{}'' else STR ''{ '' + show_nat (Max_antichain x) + STR '' }''" 

abbreviation "print_frontier x \<equiv> trace ((STR ''Frontier: '') + show_frontier x)" 

abbreviation "show_frontiers impf \<equiv> show_list (show_prod show_loc show_frontier) (map (\<lambda> l. (l, frontier (impf l))) enum_location_inst.enum_location)"

(* Inspired by timely/src/progress/subgraph.rs:453 *)
(* First migrate all change batches to the worklist, then call propagate_all_locale *)
 fun propagate_pointstamps where
  "propagate_pointstamps summary conf [] = (let conf' = propagate_all summary conf in trace (STR ''New frontiers: '' + show_frontiers (c_imp (the conf'))) conf')"
| "propagate_pointstamps summary conf ((l, t, m) # cbs) =
   propagate_pointstamps summary (trace (STR ''CM ==> '' + show_loc l + STR '', t: '' + show_nat t + STR '', m: '' + print_int m) (take_step summary (CM l t m)) conf) cbs"


abbreviation "init_subgraph summary \<equiv>
  trace (STR ''Initializing subgraph'') \<lparr> pt_tr = the (propagate_pointstamps summary empty_conf (concat (map (\<lambda> nid. map (\<lambda> p. (Loc nid (Src p), 0, 1)) enum_class.enum) enum_class.enum))),
   lo_pt = [],
   edges = (\<lambda> l1. [l2 \<leftarrow> enum_location_inst.enum_location. \<not> is_empty_antichain (summary l1 l2) ]),
   summ = summary \<rparr>"

(* Inspired by timely/src/dataflow/operators/generic/builder_rc.rs:29 and timely/src/progress/operate.rs:63 *)
(* This is the shared that the operator exposes to the subgraph *)
record ('p, 't) shared_state =
  cons :: "('p \<times> 't \<times> int) change_batch"
  inte :: "('p \<times> 't \<times> int) change_batch"
  prod :: "('p \<times> 't \<times> int) change_batch"

(* Inspired by timely/src/progress/subgraph.rs:759 *)
definition extract_progress where
  "extract_progress nid edg st =
    map (\<lambda> (p, t, m). (Loc nid (Trg p), t, -m)) (cons st) @ 
    map (\<lambda> (p, t, m). (Loc nid (Src p), t, m)) (inte st) @
    concat (map (\<lambda> (p, t, m). map (\<lambda> l. (l, t, m)) (edg (Loc nid (Src p)))) (prod st))"

(* Inspired by timely/src/dataflow/operators/capability.rs:62 *)
datatype ('p, 't) capability = Cap (time: 't) (out: 'p)

abbreviation "frontier_updating b \<equiv> cfilter (\<lambda> op. case op of Read (Inl _) f \<Rightarrow> b | _ \<Rightarrow> True)"

(* TODO: nid must have a concrete type *)
corec dataflow_op where
  "dataflow_op sg op = Choice (cimage (\<lambda> op. case op of 
     Read (Inl nid) f \<Rightarrow> let imp_fron = (\<lambda> p. c_imp (pt_tr sg) (Loc nid (Trg p))) in Silent (dataflow_op sg (f (Inl (Inr imp_fron))))
   | Read (Inr (nid, p)) f \<Rightarrow> Read (nid, p) (\<lambda> x. dataflow_op sg (f (Inr x)))
   | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow> (case propagate_pointstamps (summ sg) (pt_tr sg) (lo_pt sg @ extract_progress nid (edges sg) st) of
                                              Some conf' \<Rightarrow> Silent (dataflow_op (sg\<lparr> pt_tr := conf', lo_pt := [] \<rparr>) op'))
   | Write op' (Inr (nid, p)) (Inr x) \<Rightarrow> Write (dataflow_op sg op') (nid, p) x
   | Silent op' \<Rightarrow> Silent (dataflow_op sg op')
   | _ \<Rightarrow> Code.abort (STR ''Operator in dataflow_op breaks contract'') undefined) (choices op))"


definition "compile_dataflow dt = (let (summary, op) = compile_dataflow_tree dt in
                                    let sg = init_subgraph summary in
                                    dataflow_op sg op)"

(* Should this be non-deterministic? (e.g. non-deterministically send events and capabilities updates) *)
(* Inspired by timely/src/dataflow/channels/pushers/counter.rs:25 and timely/src/dataflow/channels/mod.rs:49 *)
(* writes maybe could support multiple different ports, then this one also would *)
abbreviation "push op p batch \<equiv> 
  writes (Write op (trace (STR ''Pushing data!'') None) (Inl (Inl \<lparr> cons = [], inte = [], prod = map (\<lambda> (x, c). (p, time c, 1)) batch \<rparr>))) (Some p) (map (\<lambda> (x, c). Inr (x, time c)) batch)"

abbreviation "drop_cap c op \<equiv>
  Write op None (trace (String.implode (''Dropping cap!'')) Inl (Inl \<lparr> cons = [], inte = [(out c, time c, -1)], prod = [] \<rparr>))"

abbreviation "drop_caps cs op \<equiv>
  Write op None (trace (String.implode (''Dropping caps!'')) Inl (Inl \<lparr> cons = [], inte = map (\<lambda> c. (out c, time c, -1)) cs, prod = [] \<rparr>))"

abbreviation "delayed_cap c t \<equiv>
  (Cap (time c + abs t) (out c),
  \<lambda> op. Write op None 
     (Inl (Inl \<lparr> cons = [],
            inte = [(out c, time c, -1), (out c, time c + abs t, 1)],
            prod = [] \<rparr>)))"

(* corec input_op where
  "input_op c inps = (case inps of
    LNil \<Rightarrow> drop_cap 0 c \<odot>
  | LCons xs lxs \<Rightarrow> push 0 c (let (c, f) = delayed_cap 0 c 1 in f (input_op c lxs)) 1 xs)" *)

corec input_op where
  "input_op c inps = (case inps of
    LNil \<Rightarrow> drop_cap c \<oslash>
  | LCons xs lxs \<Rightarrow>
     push 
     (Write (input_op (Cap (time c + 1) (out c)) lxs) (trace (STR ''Delaying cap'') None) (Inl (Inl \<lparr> cons = [], nte = [(out c, time c, -1), (out c, time c + 1, 1)], prod = []\<rparr>)))
      1 (map (\<lambda> x. (x, c)) xs))"

abbreviation "ex1 \<equiv> Logic (input_op (Cap 0 (1 :: 1)) (LCons [Suc 0, 3] (LCons [9] LNil))) :: (2, 1, (1, _) shared_state + 'c, nat \<times> _) dataflow_tree"

value [GHC] "eval 20 (compile_dataflow ex1)"

value [GHC] "cfilter ((\<noteq>) []) (eval 20 (compile_dataflow (Comp [ (0, 0) \<mapsto> (0, 0) ] ex1 (Logic \<I>))))"

(* value [GHC] "eval 17 (dataflow_op True init_subgraph (input_op (Cap (0 :: nat) 0) (LCons [Suc 0, 2, 3, 9] (LCons [8, 1, 0] LNil))))"
value [GHC] "eval 5 (dataflow_op True init_subgraph (input_op (Cap (0 :: nat) 0) (LCons [Suc 0] (LNil))))"
 *)
abbreviation "maxs ft buf \<equiv> [(n, c) \<leftarrow> buf. ft (time c) \<and> n = Max (set (map fst ((filter (\<lambda> (n' :: nat, c'). time c = time c') buf))))]"

(* The minted capability must depend on the internal wiring *)
abbreviation "pull i f \<equiv> (Read ((trace (STR ''Reading data'') Some) i)
  (\<lambda> x. case x of
    (Inr (d, t)) \<Rightarrow> Write (f (d, Cap t 0)) None (Inl (Inl \<lparr>  cons = [(i, t, 1)], inte = [(i, t, 1)], prod = [] \<rparr>))))"

abbreviation
  "less_than_frontier ft t \<equiv> (\<not> is_empty_antichain (filter_antichain (\<lambda> f. t < f) ft))"

term choice2

declare [[unify_search_bound = 100]]

corec max_op' where
  "max_op' buf = choice2
   (Read (trace (STR ''Reading frontier'') None) (\<lambda> st.
    let impf = projr (projl st) in
    let ft = frontier (impf (0 :: 1)) in
    if print_frontier ft  is_empty_antichain ft 
    then trace (STR ''Empty frontier'') \<oslash> 
    else 
    let result = trace (STR ''Non empty frontier'') (maxs (less_than_frontier ft) buf) in
    push (drop_caps (map snd result) (max_op' [(n, c) \<leftarrow> buf. \<not> less_than_frontier ft (time c)])) 0 result))
   (pull (0 :: 1) (\<lambda> x. max_op' (buf @ [x])))"

abbreviation "max_op \<equiv> max_op' []"

abbreviation "ex3 \<equiv> Comp [ (0 :: 2, 0) \<mapsto> (0, 0) ] ex1 (Logic max_op)"

value [GHC] "approx_in 32 [VOut (1, 0) (3, 0), VOut (1, 0) (9, 1)] (compile_dataflow ex3)"

abbreviation "ex4 \<equiv> Comp (\<lambda> _. None) (Logic (input_op (Cap 0 (1 :: 1)) (LCons [0] LNil))) (Logic (input_op (Cap 0 (1 :: 1)) (LCons [Suc 0] LNil)))"

abbreviation "ex5 \<equiv> Comp (\<lambda> _. None) (Logic (\<I> :: (1 option, 1 option, _) op)) (Logic (\<I> :: (1 option, 1 option, _) op))"

abbreviation "ex6 \<equiv> Comp [ (0 :: 4, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex4 ex5"

value [GHC] "approx_in 15 [VOut (3, 0) (0, 0), VOut (2, 0) (1, 0)] (compile_dataflow ex6)"

corec cp_op :: "(1 option, 1 option, 'a) op" where "cp_op = Read (Some 1) (\<lambda>x. Write cp_op (Some 1) x)"

abbreviation "ex7 \<equiv> Comp (\<lambda> _. None) (Logic cp_op) (Logic cp_op)"

abbreviation "ex8 \<equiv> Comp [ (0 :: 4, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex4 ex7"

value [GHC] "approx_in 15 [VOut (3, 0) (0, 0), VOut (2, 0) (1, 0)] (compile_dataflow ex8)"

abbreviation "ex9 \<equiv> Comp [ (0, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex7 ex7"

abbreviation "ex10 \<equiv> Comp [ (0 :: 6, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex4 ex9"

value [GHC] "approx_in 20 [VOut (4, 0) (0, 0), VOut (5, 0) (1, 0)] (compile_dataflow ex10)"


term "c_imp (pt_tr (init_subgraph (fst (compile_dataflow_tree ex3))))"

term "(show_prod show_loc show_frontier)"

term "show_list (show_prod show_loc show_frontier)"


term compile_dataflow_tree_aux




end

(* 
value [GHC] "approx_in 38 [VOut 0 (9, 0), VOut 0 (5, 1), VOut 0 (2, 2)] (dataflow_op True init_subgraph ((input_op (Cap (0 :: nat) (0 :: 2)) (LCons [9, 3] (LCons [Suc 0, 5] (LCons [2] LNil)))) \<bullet>\<^sub>t max_op))"

 *)
fun traceprefix :: "nat \<Rightarrow> ('i, 'o, 'd) VIO list \<Rightarrow> ('i, 'o, 'd :: {countable}) op \<Rightarrow> bool" where
  "traceprefix n [] _ = True"
| "traceprefix n (VInp p x # lxs) (Read q f) = (p = q \<and> traceprefix n lxs (f x))"
| "traceprefix n (VOut p x # lxs) (Write op q y) = (p = q \<and> x = y \<and> traceprefix n lxs op)"
| "traceprefix (Suc n) lxs (Silent op) = traceprefix n lxs op"
| "traceprefix (Suc n) lxs (Choice ops) = (\<not> cis_empty (cfilter (traceprefix n lxs) ops))"
| "traceprefix _ _ _ = False"


definition "tp = traceprefix 1000000 [VOut 0 (9, 0)] (dataflow_op True init_subgraph ((input_op (Cap (0 :: nat) (0 :: 2)) (LCons [9] (LNil))) \<bullet>\<^sub>t max_op))"

definition "tp2 = traceprefix 1000000 [VOut 0 (1, 0), VOut 0 (2, 0), VOut 0 (3, 0), VOut 0 (9, 0), VOut 0 (8, 1), VOut 0 (1, 1), VOut 0 (0, 1)]
  (dataflow_op True init_subgraph (input_op (Cap (0 :: nat) 0) (LCons [Suc 0, 2, 3, 9] (LCons [8, 1, 0] LNil))))"

(* value [GHC] tp
 *)
term "Not (cis_empty (choices op))"

find_consts "_ cset \<Rightarrow> _ llist"

term cset_of_llist

find_theorems cset_of_llist wit_cset


term "\<lambda> (tr, op). while_option (\<lambda> (tr, op). Not (cis_empty (choices op))) (undefined)"

(* 
value [GHC] "(approx_in 40 [VOut 0 (9, 0), VOut 0 (1, 1)] (dataflow_op init_subgraph ((input_op (Cap (0 :: nat) (0 :: 2)) (LCons [0, 9] (LCons [Suc 0] LNil))) \<bullet>\<^sub>t (max_op []))))"
 *)


value [GHC] "cfilter ((\<noteq>) []) (eval 29 (dataflow_op init_subgraph ((input_op (Cap (0 :: nat) (0 :: 2)) (LCons [0, 9] (LCons [Suc 0] LNil))) \<bullet>\<^sub>t (max_op []))))"

term cfilter

end

datatype ('c, 'd) subgraph = 
  "apply": Logic "'c \<Rightarrow> (nat, nat, 'd) op"
  | Comp "nat \<Rightarrow> nat option" "nat \<Rightarrow> 'd buf" "('c, 'd) subgraph" "('c, 'd) subgraph"

fun embed_nat where
  "embed_nat (Inl n) =  2 * n"
| "embed_nat (Inr n) =  2 * n + 1"

fun activate_children where
  "activate_children c (Logic l) = ((\<lambda> op. case op of Write op' p x \<Rightarrow> (send_update_conf c, Write op' p x)) |`| choices (l c))"
  (* | "compile_subgraph c (Comp wire buf sg1 sg2) = (map_op embed_nat embed_nat (comp_op wire buf (compile_subgraph c sg1) (compile_subgraph c sg2)))"
 *)

corec compile_subgraph where
  "compile_subgraph c sg = ((\<lambda> (c', op). undefined) |`| activate_children c sg)"  

inductive activate where
  "wstep io (l c) (l' c') \<Longrightarrow> activate io c (Logic l) c' (Logic l')"
| "activate (Out p x) c sg1 c' sg1' \<Longrightarrow>
   wire p = Some q \<Longrightarrow>
   activate Tau c sg2 c' sg2 \<Longrightarrow>
   activate Tau c (Comp wire buf sg1 sg2) c' (Comp wire (BENQ q x buf) sg1' sg2)"
| "activate (Inp p x) c sg2 c' sg2' \<Longrightarrow>
   BHD p buf = x \<Longrightarrow> buf p \<noteq> [] \<Longrightarrow>
   p \<in> ran wire \<Longrightarrow>
   activate Tau c sg1 c' sg1' \<Longrightarrow>
   activate Tau c (Comp wire buf sg1 sg2) c' (Comp wire (BTL p buf) sg1' sg2')" 
| "activate (Inp p x) c sg1 c' sg1' \<Longrightarrow>
   activate Tau c sg2 c' sg2' \<Longrightarrow>
   activate (Inp (2 * p) x) c (Comp wire buf sg1 sg2) c' (Comp wire buf sg1' sg2')"  



abbreviation "op1_sg \<equiv> Logic op1"
abbreviation "op2_sg \<equiv> Logic (op2 [])"
abbreviation "op1_op2_sg \<equiv> Comp Some (\<lambda> _. []) op1_sg op2_sg"

term "compile_subgraph init_subgraph op1_op2_sg"





end


lemma activate_op1_sg:
  "activate (Out 1 0) init_subgraph op1_sg (init_subgraph\<lparr>lo_pt := (\<lambda> _. {# 1 #}\<^sub>z)(1 := {#}\<^sub>z)\<rparr>) op1_sg"
  apply (rule activate.intros(1))
  apply (subst op1.code)
  apply auto
  done

end

lemma op2_update_internal:
  "op2 \<lparr>pt_tr = C, lo_pt = A\<rparr> = op2 \<lparr>pt_tr = C, lo_pt = B\<rparr>"
  apply (coinduction arbitrary: A B C rule: op.coinduct_upto)
  apply (intro conjI impI)
  apply (subst (1 2) op2.code, simp)
  apply (subst (asm) op2.code, simp)
  apply (subst (asm) op2.code, simp)
  apply (subst (1 2) op2.code, simp)
  apply (subst (asm) op2.code, simp)
  apply (subst (asm) op2.code, simp)
  apply (subst (asm) op2.code, simp)
  apply (subst (1 2) op2.code, simp)
  subgoal
    apply (subst (3 4) op2.code, simp)
    apply (intro rel_setI)
    apply simp_all
    subgoal
      apply (elim disjE)
      subgoal
        apply hypsubst_thin
        apply (smt (verit, ccfv_threshold) transp_op.cong_Silent transp_op.cong_base)        
        done
      subgoal
        apply hypsubst_thin
        apply (rule disjI2)
        apply (rule transp_op.cong_Read)
        apply simp
        apply (smt (verit, del_insts) comp_apply option.simps(5) rel_funI transp_op.cong_Silent transp_op.cong_base transp_op.cong_refl)
        done
      done
    subgoal
      apply (elim disjE)
      subgoal
        apply hypsubst_thin
        apply (smt (verit, ccfv_threshold) transp_op.cong_Silent transp_op.cong_base)        
        done
      subgoal
        apply hypsubst_thin
        apply (rule disjI2)
        apply (rule transp_op.cong_Read)
        apply simp
        apply (smt (verit, del_insts) comp_apply option.simps(5) rel_funI transp_op.cong_Silent transp_op.cong_base transp_op.cong_refl)
        done
      done
    done
  apply (subst (asm) op2.code, simp)
  done

lemma
  "activate Tau init_subgraph op1_op2_sg (init_subgraph\<lparr>lo_pt := (\<lambda> _. {# 1 #}\<^sub>z)(1 := {#}\<^sub>z)\<rparr>) (Comp Some (BENQ 1 0 (\<lambda> _. [])) op1_sg op2_sg)"
  apply (rule activate.intros(2)[where p=1])
  apply (rule activate_op1_sg)
  apply simp
  apply (rule activate.intros(1))
  apply simp
  apply (metis op2_update_internal rtranclp.rtrancl_refl)
  done

lemma
  "activate Tau (init_subgraph\<lparr>lo_pt := (\<lambda> _. {# 1 #}\<^sub>z)(1 := {#}\<^sub>z)\<rparr>) (Comp Some (BENQ 1 0 (\<lambda> _. [])) op1_sg op2_sg)
   (init_subgraph\<lparr>lo_pt := (\<lambda> _. {# 1 #}\<^sub>z)(1 := {#}\<^sub>z)\<rparr>) (Comp Some (BENQ 1 0 (\<lambda> _. [])) op1_sg op2_sg)"


end