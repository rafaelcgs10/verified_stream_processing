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
  Correctness of max_top
  Correctness of dataflow compilation
  Loops
  collatz_op
  Correctness of collatz_op
  unordered_input_top
  wcc_op: https://timelydataflow.github.io/differential-dataflow/chapter_4/chapter_4_1.html
  Correctness of wcc_op
  Scopes (change timestamp type, maybe not now)
  Type inference for locations (if it is not so hard)
  Nominal wiring (if it is not so hard)
  Provide operator builders
*)

value "0 :: 2"

(* FIXME: move me *)
lemma zero_one[code]:
  "(0 :: 1) = 1"
  by simp

(* TODO move *)
simproc_setup num1_eq (\<open>x :: 1\<close>) =
  \<open>K (K (fn ct =>
    if Thm.term_of ct aconv @{term \<open>1 :: 1\<close>} then NONE
    else SOME (mk_meta_eq @{thm num1_eq1})))\<close>

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

lemma step_Out_writes:
  "step io (writes op p buf) op' \<Longrightarrow>
   buf \<noteq> [] \<Longrightarrow>
   op' = writes op p (tl buf) \<and> io = Out p (hd buf)"
  apply (subst (asm) writes.code)
  apply (auto split: op.splits list.splits)
  done

lemma step_writes_reads_buf_empty:
  "step io (writes op p buf) op' \<Longrightarrow> io = Inp p' x \<Longrightarrow> buf = []"
  apply (subst (asm) writes.code)
  apply (auto split: op.splits list.splits)
  done


lemma step_writes_silent_buf_empty:
  "step io (writes op p buf) op' \<Longrightarrow> io = Tau \<Longrightarrow> buf = []"
  apply (subst (asm) writes.code)
  apply (auto split: op.splits list.splits)
  done

lemma step_writes_Out_intro[intro]:
  "buf = x # buf' \<Longrightarrow>
   op' = writes op p buf'\<Longrightarrow>
   step (Out p x) (writes op p buf) op'"
  apply (subst writes.code)
  apply (auto split: op.splits list.splits)
  done

lemma writes_empty_buf_simp[simp]:
  "writes op p [] = op"
  apply (coinduction arbitrary: op rule: op.coinduct_upto)
  apply (intro conjI impI)
           apply (subst writes.code, simp split: op.splits)
          apply (subst writes.code, simp split: op.splits)
         apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
        apply (subst writes.code, simp split: op.splits)
       apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
      apply (subst writes.code, simp split: op.splits)
     apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
    apply (subst writes.code, simp split: op.splits)
   apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
   apply (meson cset.rel_refl rel_cset.rep_eq op.cong_refl)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  done

lemma writes_Cons_simp:
  "writes op p (x # xs) = Write (writes op p xs) p x"
  apply (coinduction arbitrary: op rule: op.coinduct_upto)
  apply (intro conjI impI)
           apply (subst writes.code, simp split: op.splits)
          apply (subst writes.code, simp split: op.splits)
         apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
        apply (subst writes.code, simp split: op.splits)
       apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
      apply (subst writes.code, simp split: op.splits)
     apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
    apply (subst writes.code, simp split: op.splits)
   apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
  apply (subst (asm) writes.code, simp add: op.cong_refl writes.friend.code rel_fun_def split: op.splits)
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

definition "trace = (if DEBUG then Debug.tracing else (\<lambda> x y. y))"

lemma trace_simp[simp]:
  "trace x = id"
  by (auto simp add: trace_def)

declare trace_def[code]

lift_definition Max_antichain :: "nat antichain \<Rightarrow> nat" is "\<lambda> x. if Set.is_empty x then 42 else Max x" .

abbreviation "show_frontier x \<equiv> let f = Max_antichain x in if f = 42 then STR ''{}'' else STR ''{ '' + show_nat (Max_antichain x) + STR '' }''" 

abbreviation "print_frontier x \<equiv> trace ((STR ''Frontier: '') + show_frontier x)" 

abbreviation "show_frontiers impf \<equiv> show_list (show_prod show_loc show_frontier) (map (\<lambda> l. (l, frontier (impf l))) enum_location_inst.enum_location)"

(* Inspired by timely/src/progress/subgraph.rs:453 *)
(* First migrate all change batches to the worklist, then call propagate_all_locale *)
definition "change_multiplicities summary xs conf = fold (\<lambda> (l, t, m) c. take_step summary (CM l t m) c) xs conf"
(* 
 fun change_multiplicities where
  "change_multiplicities summary conf [] = conf"
| "change_multiplicities summary conf ((l, t, m) # cbs) =
   change_multiplicities summary (trace (STR ''CM ==> '' + show_loc l + STR '', t: '' + show_nat t + STR '', m: '' + print_int m) (take_step summary (CM l t m)) conf) cbs"
 *)

definition "propagate_pointstamps summary conf cbs = (
  let conf' = change_multiplicities summary cbs conf in
  let conf'' = propagate_all summary conf' in trace (STR ''New frontiers: '' + show_frontiers (c_imp (the conf''))) conf'')"

abbreviation "init_subgraph summary \<equiv>
  trace (STR ''Initializing subgraph'') \<lparr> pt_tr = the (propagate_pointstamps summary empty_conf (concat (map (\<lambda> nid. map (\<lambda> p. (Loc nid (Src p), 0, 1)) enum_class.enum) enum_class.enum))),
   lo_pt = [],
   edges = (\<lambda> l1. [l2 \<leftarrow> enum_class.enum. \<not> is_empty_antichain (summary l1 l2) \<and> is_Src (port l1) \<and> is_Trg (port l2) ]),
   summ = summary \<rparr>"

(* Inspired by timely/src/dataflow/operators/generic/builder_rc.rs:29 and timely/src/progress/operate.rs:63 *)
(* This is the shared that the operator exposes to the subgraph *)
record ('p, 't) shared_state =
  cons :: "('p \<times> 't \<times> int) change_batch"
  inte :: "('p \<times> 't \<times> int) change_batch"
  prod :: "('p \<times> 't \<times> int) change_batch"

find_consts "_ multiset" name: fol

(* Inspired by timely/src/progress/subgraph.rs:759 *)
definition extract_progress where
  "extract_progress nid edg st =
    map (\<lambda> (p, t, m). (Loc nid (Trg p), t, -m)) (cons st) @ 
    map (\<lambda> (p, t, m). (Loc nid (Src p), t, m)) (inte st) @
    concat (map (\<lambda> (p, t, m). map (\<lambda> l. (l, t, m)) (edg (Loc nid (Src p)))) (prod st))"

(* Inspired by timely/src/dataflow/operators/capability.rs:62 *)
datatype ('p, 't) capability = Cap (time: 't) (out: 'p)

abbreviation "frontier_updating b \<equiv> cfilter (\<lambda> op. case op of Read (Inl _) f \<Rightarrow> b | _ \<Rightarrow> True)"

abbreviation "ifchoice2 b op1 op2 \<equiv> (if b then Choice (cimage (\<lambda>b. if b then op1 else op2) (cinsert True (csingle False))) else op1)"

(* TODO: nid must have a concrete type *)
corec dataflow_op where
  "dataflow_op sg op = Choice (cimage (\<lambda> op. case op of 
     Read (Inl nid) f \<Rightarrow> (case propagate_pointstamps (summ sg) (pt_tr sg) (lo_pt sg) of
         Some conf' \<Rightarrow> let sg' = sg\<lparr> pt_tr := conf', lo_pt := [] \<rparr> in
         let imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) in Silent (dataflow_op sg' (f (Inl (Inr imp_fron)))))
   | Read (Inr (nid, p)) f \<Rightarrow> Read (nid, p) (\<lambda> x. dataflow_op sg (f (Inr x)))
   | Write op' (Inr (nid, p)) (Inr x) \<Rightarrow> Write (dataflow_op sg op') (nid, p) x
   | Silent op' \<Rightarrow> Silent (dataflow_op sg op')
   | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow> Silent (dataflow_op (sg\<lparr> lo_pt := lo_pt sg @ extract_progress nid (edges sg) st \<rparr>) op')
   | _ \<Rightarrow> Code.abort (STR ''Operator in dataflow_op breaks contract'') (\<lambda> _. \<oslash>)) (choices op))"


lemma propagate_all_terminates[simp]:
  "propagate_all a b \<noteq> None"
  sorry

lemma change_multiplicities_terminates[simp]:
  "propagate_pointstamps summary conf cbs \<noteq> None"
  apply (induct cbs arbitrary: conf) 
  apply (auto simp add: propagate_pointstamps_def)
  done

lemma step_dataflow_op_elim:
  assumes "step io (dataflow_op sg op) op'"
  obtains
    nid p op'' x where "io = Inp (nid, p) x" "op' = dataflow_op sg op''" "step (Inp (Inr (nid, p)) (Inr x)) op op''"
  | nid p op'' x where "io = Out (nid, p) x" "op' = dataflow_op sg op''" "step (Out (Inr (nid, p)) (Inr x)) op op''"
  | op'' where "io = Tau" "op' = dataflow_op sg op''" "step Tau op op''"
  | nid op'' st where "io = Tau" "op' = dataflow_op (sg\<lparr> lo_pt := lo_pt sg @ extract_progress nid (edges sg) st \<rparr>) op''" "step (Out (Inl nid) (Inl (Inl st))) op op''"
  | nid op'' imp_fron sg' where "io = Tau" "sg' = (case propagate_pointstamps (summ sg) (pt_tr sg) (lo_pt sg) of Some conf' \<Rightarrow> sg\<lparr> pt_tr := conf', lo_pt := [] \<rparr>)"
    "imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p)))" "op' = dataflow_op sg' op''" "step (Inp (Inl nid) (Inl (Inr imp_fron))) op op''"
  | op'' p p' where "op' = \<oslash>" "op = Write op'' (Inl p) (Inr p')"
  | op'' p p' where "op' = \<oslash>" "op = Write op'' (Inr p) (Inl p')"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) dataflow_op.code)
  apply (simp split: if_splits)
  apply (elim stepChoiceE)
  subgoal for op'
    apply (auto del: disjCI split: op.splits sum.splits option.splits)
        apply fastforce+
    done
  done

lemma step_Tau_dataflow_op_Out_Inl_intro[intro]:
  "step (Out (Inl nid) (Inl (Inl st))) op op' \<Longrightarrow>
   sg' = sg\<lparr> lo_pt := lo_pt sg @ extract_progress nid (edges sg) st \<rparr> \<Longrightarrow>
   step Tau (dataflow_op sg op) (dataflow_op sg' op')"
  apply (subst dataflow_op.code)
    apply (force elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Tau_dataflow_op_Inp_Inl_intro[intro]:
  "step (Inp (Inl nid) (Inl (Inr imp_fron))) op op' \<Longrightarrow>
   conf' = the (propagate_pointstamps (summ sg) (pt_tr sg) (lo_pt sg)) \<Longrightarrow>
   sg' = sg\<lparr> pt_tr := conf', lo_pt := [] \<rparr> \<Longrightarrow>
   imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) \<Longrightarrow>
   step Tau (dataflow_op sg op) (dataflow_op sg' op')"
  apply (subst dataflow_op.code)
    apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Tau_dataflow_op_Tau_intro[intro]:
  "step Tau op op' \<Longrightarrow>
   step Tau (dataflow_op sg op) (dataflow_op sg op')"
  apply (subst dataflow_op.code)
    apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Out_dataflow_op_Out_Inr_intro[intro!]:
  "step (Out (Inr (nid, p)) (Inr x)) op op' \<Longrightarrow>
   step (Out (nid, p) x) (dataflow_op sg op) (dataflow_op sg op')"
  apply (subst dataflow_op.code)
    apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

lemma step_Inp_dataflow_op_Inp_Inr_intro[intro!]:
  "step (Inp (Inr (nid, p)) (Inr x)) op op' \<Longrightarrow>
   step (Inp (nid, p) x) (dataflow_op sg op) (dataflow_op sg op')"
  apply (subst dataflow_op.code)
    apply (fastforce elim: step_choicesE split: sum.splits option.splits)
  done

fun steps where
  "steps [] = (=)"
| "steps (io # ios) = step io OO steps ios"

lemma steps_append[simp]:
  "steps (xs @ ys) = steps xs OO steps ys"
  by (induct xs arbitrary: ys) auto

lemma step_refl[simp]:
  "step io OO (=) = step io"
  by auto

thm step_map_op[no_vars]

lemma steps_map_op[intro!]:
  "steps xs op op' \<Longrightarrow> map (map_IO f g id) xs = xs' \<Longrightarrow>
   f = f' \<Longrightarrow>
   g = g' \<Longrightarrow>
   steps xs' (map_op f g op) (map_op f' g' op')"
  by (induct xs' arbitrary: op op' xs)
    (force simp add: relcompp_apply)+

lemma steps_intro[intro]:
  "step x op op' \<Longrightarrow>
   steps xs op' op'' \<Longrightarrow>
   ys = x # xs \<Longrightarrow>
   steps ys op op''"
  apply auto
  done

lemma steps_Tau_dataflow_op_Out_Inl_intro[intro]:
  "steps (map (\<lambda> st. Out (Inl nid) (Inl (Inl st))) xs) op op' \<Longrightarrow>
   sg' = sg\<lparr> lo_pt := lo_pt sg @ concat (map (\<lambda> st. (extract_progress nid (edges sg) st)) xs) \<rparr> \<Longrightarrow>
   n = length xs \<Longrightarrow>
   (step Tau ^^ n) (dataflow_op sg op) (dataflow_op sg' op')"
  apply (induct xs arbitrary: op' sg op op' sg' n rule: rev_induct)
  subgoal for op' conf' sg
    by simp
  subgoal for a xs op' sg op sg'
    apply simp
    apply (simp add: relcompp_apply)
    apply safe
    apply hypsubst_thin
    apply (drule meta_spec)+
    apply (drule meta_mp)
     apply assumption
    apply (drule meta_mp)
     apply (rule refl)
    apply fastforce
    done
  done


definition "compile_dataflow dt = (let (summary, op) = compile_dataflow_tree dt in
                                    let sg = init_subgraph summary in
                                    dataflow_op sg op)"

(* Should this be non-deterministic? (e.g. non-deterministically send events and capabilities updates) *)
(* Inspired by timely/src/dataflow/channels/pushers/counter.rs:25 and timely/src/dataflow/channels/mod.rs:49 *)
(* writes maybe could support multiple different ports, then this one also would *)
abbreviation "push op p batch \<equiv> 
  writes op (trace (STR ''Pushing data!'') Some p) (map (\<lambda> (x, c). Inr (x, time c)) batch)"

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

(* corec input_top where
  "input_top c inps = (case inps of
    LNil \<Rightarrow> drop_cap 0 c \<odot>
  | LCons xs lxs \<Rightarrow> push 0 c (let (c, f) = delayed_cap 0 c 1 in f (input_top c lxs)) 1 xs)" *)

corec input_top where
  "input_top c inps = (case inps of
    LNil \<Rightarrow> drop_cap c \<oslash>
  | LCons xs lxs \<Rightarrow>
     push 
     (Write (input_top (Cap (time c + 1) (out c)) lxs) (trace (STR ''Managing caps'') None) (Inl (Inl \<lparr> cons = [], inte = [(out c, time c, -1), (out c, time c + 1, 1)], prod = if xs = [] then [] else [(out c, time c, length xs)]\<rparr>)))
      (1 :: 1) (map (\<lambda> x. (x, c)) xs))"

lemma step_input_top_elim:
  assumes "step io (input_top c inps) op'"
  obtains
    op'' x xs where "io = Out (Some 1) (Inr (x, time c))" "lhd inps = xs" "hd xs = x" "inps \<noteq> LNil" "xs \<noteq> []"
    "op' = writes (Write (input_top (Cap (time c + 1) (out c)) (ltl inps)) None (Inl (Inl \<lparr> cons = [], inte = [(out c, time c, -1), (out c, time c + 1, 1)], prod = [(out c, time c, length xs)]\<rparr>))) (Some 1) (map (\<lambda> x. Inr (x, time c)) (tl xs))"
  | "io = Out None (Inl (Inl \<lparr>cons = [], inte = [(out c, time c, - 1), (out c, time c + 1, 1)], prod = []\<rparr>)) " "inps \<noteq> LNil" "lhd inps = []" "op' = input_top (Cap (time c + 1) (out c)) (ltl inps)"
  | "inps = LNil" "io = Out None (Inl (Inl \<lparr> cons = [], inte = [(out c, time c, -1)], prod = [] \<rparr>))" "op' = \<oslash>"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) input_top.code)
  apply (simp split: llist.splits)
   apply force
  subgoal for xs lxs
    apply hypsubst_thin
    apply (cases io; simp)
    subgoal
      using step_writes_reads_buf_empty by fastforce
    subgoal for p x
      apply hypsubst_thin
      apply (cases xs; simp)
      subgoal
        by auto
      subgoal
        apply (drule step_Out_writes)
         apply (auto simp add: comp_def)
        done
      done
    subgoal
      apply (cases xs; simp)
       apply force
      apply (drule step_Out_writes)
       apply auto
      done
    done
  done

lemma step_input_top_Out_Some_intro[intro]:
  "inps = LCons xs inps' \<Longrightarrow>
   xs = x # xs' \<Longrightarrow>
   op = writes (Write (input_top (Cap (time c + 1) (out c)) inps') None (Inl (Inl \<lparr> cons = [], inte = [(out c, time c, -1), (out c, time c + 1, 1)], prod = [(out c, time c, length xs)]\<rparr>))) (Some 1) (map (\<lambda> x. Inr (x, time c)) xs') \<Longrightarrow>
   step (Out (Some 1) (Inr (x, time c))) (input_top c inps) op"
  apply (subst input_top.code)
  apply (auto simp add: comp_def)
  done

lemma step_input_top_Out_None_intro[intro]:
  "inps = LCons [] inps' \<Longrightarrow> 
   step (Out None (Inl (Inl \<lparr> cons = [], inte = [(out c, time c, -1), (out c, Suc (time c), 1)], prod = []\<rparr>))) (input_top c inps) (input_top (Cap (Suc (time c)) (out c)) inps')"
  apply (subst input_top.code)
  apply (auto simp add: comp_def)
  done

lemma ldropWhile_LCons_lfinite_ltakeWhile:
  "ldropWhile ((=) []) inps = LCons (x # xs) inps' \<Longrightarrow> lfinite (ltakeWhile ((=) []) inps)"
  by (metis ldropWhile_eq_LNil_iff lfinite_ltakeWhile llist.simps(2))

lemma ldropWhile_steps_input_top:
  "lfinite (ltakeWhile ((=) []) inps) \<Longrightarrow>
   ldropWhile ((=) []) inps = LCons (x # xs) inps' \<Longrightarrow>
   steps (map (\<lambda> t. Out None (Inl (Inl \<lparr> cons = [], inte = [(out c, t, -1), (out c, Suc t, 1)], prod = []\<rparr>))) [time c..<time c + the_enat (llength (ltakeWhile ((=) []) inps))])
  (input_top c inps) (input_top (Cap (time c + the_enat (llength (ltakeWhile ((=) []) inps))) (out c)) (LCons (x # xs) inps'))"
  apply (induct "ltakeWhile ((=) []) inps"  arbitrary: c inps rule: lfinite_induct)
  subgoal for inps c
    apply (cases "ltakeWhile ((=) []) inps"; simp)
    apply (metis ldropWhile_simps(1,2) ltakeWhile_simps(2) neq_LNil_conv)
    done
  subgoal premises prems for inps c
    using prems(1,2,4-) apply -
    apply (cases inps; simp split: if_splits; hypsubst)
    subgoal for z lxs
      apply (rule steps_intro[where xs="map (\<lambda>t. Out None (Inl (Inl \<lparr>cons = [], inte = [(out c, t, - 1), (out c, Suc t, 1)], prod = []\<rparr>))) [Suc (time c)..<time c + the_enat (eSuc (llength (ltakeWhile ((=) []) lxs)))]"])
      apply (rule step_input_top_Out_None_intro)
        apply (rule refl)+
       defer
      subgoal
       apply simp
      apply (subst map_eq_Cons_conv)
        apply auto
        apply (intro exI conjI[rotated])
         apply (rule refl)
        apply (rule upt_conv_Cons)
        apply (metis dataflow_topology_from_tree.le_plus(1) impossible_Cons le_neq_implies_less length_list_of_conv_the_enat lfinite.simps list_of_LCons llength_LCons nat_add_left_cancel_le)
        done
      subgoal
       apply (subst (1 2) the_enat_eSuc)
        using llength_eq_infty_conv_lfinite apply blast
        using prems(3)[where c="Cap (time c + 1) (out c)" and inps=lxs] apply -
        apply (simp split: if_splits)
        done
      done
    done
  done

abbreviation "ex1 \<equiv> Logic (input_top (Cap 0 (1 :: 1)) (LCons [Suc 0, 3] (LCons [9] LNil))) :: (2, 1, (1, _) shared_state + 'c, nat \<times> _) dataflow_tree"

 value [GHC] "eval 20 (compile_dataflow ex1)"

(*value [GHC] "cfilter ((\<noteq>) []) (eval 20 (compile_dataflow (Comp [ (0, 0) \<mapsto> (0, 0) ] ex1 (Logic \<I>))))" *)

(* value [GHC] "eval 17 (dataflow_op True init_subgraph (input_top (Cap (0 :: nat) 0) (LCons [Suc 0, 2, 3, 9] (LCons [8, 1, 0] LNil))))"
value [GHC] "eval 5 (dataflow_op True init_subgraph (input_top (Cap (0 :: nat) 0) (LCons [Suc 0] (LNil))))"
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

corec max_top' where
  "max_top' buf = choice2
   (Read (trace (STR ''Reading frontier'') None) (\<lambda> st.
    let impf = projr (projl st) in
    let ft = frontier (impf (0 :: 1)) in
    if print_frontier ft  is_empty_antichain ft 
    then trace (STR ''Empty frontier'') \<oslash> 
    else 
    let result = trace (STR ''Non empty frontier'') (maxs (less_than_frontier ft) buf) in
    push (drop_caps (map snd result) (max_top' [(n, c) \<leftarrow> buf. \<not> less_than_frontier ft (time c)])) 0 result))
   (pull (0 :: 1) (\<lambda> x. max_top' (buf @ [x])))"

abbreviation "max_top \<equiv> max_top' []"

abbreviation "ex3 \<equiv> Comp [ (0 :: 2, 0) \<mapsto> (0, 0) ] ex1 (Logic max_top)"

(* value [GHC] "approx_in 32 [VOut (1, 0) (3, 0), VOut (1, 0) (9, 1)] (compile_dataflow ex3)"
 *)
abbreviation "ex4 \<equiv> Comp (\<lambda> _. None) (Logic (input_top (Cap 0 (1 :: 1)) (LCons [0] LNil))) (Logic (input_top (Cap 0 (1 :: 1)) (LCons [Suc 0] LNil)))"

abbreviation "ex5 \<equiv> Comp (\<lambda> _. None) (Logic (\<I> :: (1 option, 1 option, _) op)) (Logic (\<I> :: (1 option, 1 option, _) op))"

abbreviation "ex6 \<equiv> Comp [ (0 :: 4, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex4 ex5"

(* value [GHC] "approx_in 15 [VOut (3, 0) (0, 0), VOut (2, 0) (1, 0)] (compile_dataflow ex6)"
 *)
corec cp_op :: "(1 option, 1 option, 'a) op" where "cp_op = Read (Some 1) (\<lambda>x. Write cp_op (Some 1) x)"

abbreviation "ex7 \<equiv> Comp (\<lambda> _. None) (Logic cp_op) (Logic cp_op)"

abbreviation "ex8 \<equiv> Comp [ (0 :: 4, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex4 ex7"

(* value [GHC] "approx_in 15 [VOut (3, 0) (0, 0), VOut (2, 0) (1, 0)] (compile_dataflow ex8)"
 *)
abbreviation "ex9 \<equiv> Comp [ (0, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex7 ex7"

abbreviation "ex10 \<equiv> Comp [ (0 :: 6, 0) \<mapsto> (1, 0), (1, 0) \<mapsto> (0, 0) ] ex4 ex9"

(* value [GHC] "approx_in 20 [VOut (4, 0) (0, 0), VOut (5, 0) (1, 0)] (compile_dataflow ex10)"
 *)

term "c_imp (pt_tr (init_subgraph (fst (compile_dataflow_tree ex3))))"

term "(show_prod show_loc show_frontier)"

term "show_list (show_prod show_loc show_frontier)"


term compile_dataflow_tree_aux

abbreviation "upd_max S t n \<equiv> (case S t of None \<Rightarrow> S(t \<mapsto> n) | Some n' \<Rightarrow> S(t \<mapsto> max n n'))"

term "compile_dataflow (Logic max_top)"

coinductive dataflow_max_top_spec for nid where
  "dataflow_max_top_spec nid S LNil"
| "dataflow_max_top_spec nid (upd_max S t n) ios \<Longrightarrow> dataflow_max_top_spec nid S (LCons (VInp (nid, 1) (n, t)) ios)"
| "dataflow_max_top_spec nid (S(t := None)) ios \<Longrightarrow>
   \<not> (\<exists> n t'. VInp (1, 1) (n, t') \<in> lset ios \<and> t' \<le> t) \<Longrightarrow> S t = Some m \<Longrightarrow> dataflow_max_top_spec nid S (LCons (VOut (nid, 1) (m, t)) ios)"

lemma
  "compile_dataflow_tree_aux nid (Logic (input_top c inps)) = (nid', summary, op) \<Longrightarrow>
   \<lparr> pt_tr = conf, lo_pt = [],
     edges = (\<lambda> l1. [l2 \<leftarrow> enum_location_inst.enum_location. \<not> is_empty_antichain (summary l1 l2) ]),
     summ = summary \<rparr> = sg \<Longrightarrow>
   wtraced (dataflow_op sg op) ios \<Longrightarrow>
   lprefix ios (lmap (\<lambda> (n, t). VOut (nid, 0) (n, t)) (lconcat (lmap (\<lambda> (xs, t). map (\<lambda> n. (n, t)) xs) (lzip inps (iterates Suc 0)))))"
  apply (coinduction arbitrary: op inps ios)
  subgoal for op inps ios
    apply (cases ios)
     apply simp_all
      apply (elim conjE)
    apply simp
    apply hypsubst_thin
    subgoal for io ios'
      unfolding lnull_def
      apply simp
      oops

lemma
  "compile_dataflow_tree_aux nid (Logic (max_top' buf)) = (nid', summary, op) \<Longrightarrow>
   \<lparr> pt_tr = conf, lo_pt = [],
     edges = (\<lambda> l1. [l2 \<leftarrow> enum_location_inst.enum_location. \<not> is_empty_antichain (summary l1 l2) ]),
     summ = summary \<rparr> = sg \<Longrightarrow>
   wtraced (dataflow_op sg op) ios \<Longrightarrow>
   dataflow_max_top_spec nid (map_of (map (\<lambda> (n, c). (n, time c)) (sort_key fst buf))) ios"
  apply (coinduction arbitrary: buf ios)
  subgoal for buf ios
    apply (cases ios)
    subgoal
      by simp
    subgoal for io ios
      apply hypsubst_thin
      apply simp
      apply (cases io)
      subgoal for p d
        apply simp
        apply (elim conjE)
        apply hypsubst_thin
        apply (erule wtraced.cases)
         apply simp
        subgoal for vio op op' lxs
          apply simp
          apply (elim conjE)
          apply hypsubst_thin
          apply simp
          oops


corec input_op :: "nat \<Rightarrow> 'a buf llist \<Rightarrow> (1, 1, 'a \<times> nat) op" where
  "input_op n inps = (case ldropWhile ((=) []) inps of
     LNil \<Rightarrow> \<oslash>
   | LCons (x # xs) lxs \<Rightarrow> Write (input_op (n + the_enat (llength (ltakeWhile ((=) []) inps))) (LCons xs lxs)) 1 (x, n + the_enat (llength (ltakeWhile ((=) []) inps))))"

abbreviation "ex13 \<equiv> Logic (input_top (Cap 0 (1 :: 1)) (LCons [Suc 0, 3] (LCons [] (LCons [9] (LCons [9] LNil))))) :: (2, 1, (1, _) shared_state + 'c, nat \<times> _) dataflow_tree"


value [GHC] "eval 20 (compile_dataflow ex13)"

value [GHC] "eval 20 (input_op 0 (LCons [Suc 0, 3] (LCons [] (LCons [9] (LCons [9] LNil)))))"

lemma ldropWhile_LConsD:
  "ldropWhile P lxs = LCons x lxs' \<Longrightarrow>
   \<not> P x"
  by (metis lhd_ldropWhile llist.disc(2) llist.sel(1) lnull_ldropWhile)


lemma step_input_op_elim:
  assumes "step io (input_op n inps) op"
  obtains x xs inps' where "io = Out 1 (x, n + the_enat (llength (ltakeWhile ((=) []) inps)))" "ldropWhile ((=) []) inps = LCons (x # xs) inps'" "op = input_op (n + the_enat (llength (ltakeWhile ((=) []) inps))) (LCons xs inps')"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) input_op.code)
  apply (simp split: llist.splits list.splits)
  using ldropWhile_LConsD apply fast
  apply auto
  done


lemma step_input_op_Out_intro[intro]:
  "inps = LCons (x # xs) lxs \<Longrightarrow>
   ys = LCons xs lxs \<Longrightarrow>
   step (Out 1 (x, n)) (input_op n inps) (input_op n ys)"
  apply (subst input_op.code)
  apply (auto split: llist.splits)
  done

lemma step_input_op_not_Tau[simp]:
  "\<not> step Tau (input_op n inps) op"
  apply (subst input_op.code)
  apply (auto split: llist.splits list.splits dest: ldropWhile_LConsD)
  done

lemma step_input_op_not_Inp[simp]:
  "\<not> step (Inp p x) (input_op n inps) op"
  apply (subst input_op.code)
  apply (auto split: llist.splits list.splits dest: ldropWhile_LConsD)
  done

lemma wstep_input_op_simp[simp]:
  "io \<noteq> Tau \<Longrightarrow>
   wstep io (input_op n inps) op = step io (input_op n inps) op"
  unfolding wstep_def
  apply (cases io; simp)
  using converse_rtranclpE apply fastforce
  subgoal
    apply (rule iffI)
    subgoal
      apply clarsimp
      apply (metis converse_rtranclpE step_input_op_elim step_input_op_not_Tau)
      done
    subgoal
      by auto
    done
  done

lemma dataflow_writes_extract_progress_from_push:
  "g = (case_option (Inl nid) (\<lambda>p. Inr (nid, p))) \<Longrightarrow>
   dataflow_op sg
     (map_op f g
       (writes (Write op None (Inl (Inl \<lparr>cons = cs, inte = is, prod = ps\<rparr>))) (Some p) xs)) =
    dataflow_op (sg\<lparr>lo_pt := (lo_pt sg) @ extract_progress nid (edges sg) \<lparr>cons = cs, inte = is, prod = ps\<rparr> \<rparr>)
     (map_op f g
       (writes (Write op None (Inl (Inl \<lparr>cons = [], inte = [], prod = []\<rparr>))) (Some p) xs))"
  apply (induct xs arbitrary: ps "is" cs)
  subgoal 
    apply simp
    apply (subst (1 2) dataflow_op.code)
    apply (auto simp add: extract_progress_def split: if_splits option.splits)
    done
  subgoal for a xs' 
    apply (subst (1 2) writes.code)
    apply simp
    apply (subst (1 2) dataflow_op.code)
    apply (simp add: extract_progress_def split: option.splits sum.splits)
    done
  done

lemma dataflow_extract_progress_from_push:
  "dataflow_op sg
     ((Write op (Inl nid) (Inl (Inl \<lparr>cons = cs, inte = is, prod = ps\<rparr>)))) =
    dataflow_op (sg\<lparr>lo_pt := (lo_pt sg) @ extract_progress nid (edges sg) \<lparr>cons = cs, inte = is, prod = ps\<rparr> \<rparr>)
     ((Write op (Inl nid) (Inl (Inl \<lparr>cons = [], inte = [], prod = []\<rparr>))))"
  apply (subst (1 2) dataflow_op.code)
  apply (auto simp add: extract_progress_def split: if_splits option.splits)
  done


(* FIXME: move me *)
lemma arg_cong3:
  "a = b \<Longrightarrow> c = d \<Longrightarrow> e = g \<Longrightarrow> f a c e = f b d g"
  by fast

lemma update_zmultiset_simps[simp]:
  "update_zmultiset A x 0 = A"
  "update_zmultiset A x (int (Suc n)) = {# x #}\<^sub>z + update_zmultiset A x (int n)"
  "update_zmultiset A x (- (int (Suc n))) = update_zmultiset A x (- (int n)) - {# x #}\<^sub>z"
  subgoal
  apply transfer
   apply (auto simp add: equiv_zmset_def)
    done
 subgoal
  apply transfer
   apply (clarsimp simp add: equiv_zmset_def split: if_splits)
   apply (metis nat_int of_nat_Suc replicate_mset_Suc)
   done
 subgoal
  apply transfer
   apply (clarsimp simp add: equiv_zmset_def split: if_splits)
   apply (metis Suc_as_int replicate_mset_Suc)
   done
  done

lemma update_zmultiset_simps_more[simp]:
  "update_zmultiset A x (int n) = A + zmset_of (replicate_mset n x)"
  "update_zmultiset A x (- (int n)) = A - zmset_of (replicate_mset n x)"
  subgoal
  apply (induct n)
   apply simp_all
  apply (metis Groups.add_ac(2) add_zmset_add_single int_ops(2,5) plus_1_eq_Suc update_zmultiset_simps(2))
    done
  subgoal
  apply (induct n)
     apply simp_all
    apply (metis ab_group_add_class.ab_diff_conv_add_uminus arith_simps(49) diff_add_eq_diff_diff_swap int_Suc union_add_left_zmset
        update_zmultiset_simps(3))
    done
  done

lemma update_zmultiset_replicate:
  "update_zmultiset A x (m :: int) =
  (if m < 0 then A - zmset_of (mset (replicate (nat (abs m)) x)) else A + zmset_of (mset (replicate (nat m) x)))"
  apply (cases m)
   apply clarsimp+
  apply (metis add_uminus_conv_diff int_Suc is_num_normalize(8) nat_int update_zmultiset_simps_more(2))
  done

lemma update_zmultiset_comm:
  "update_zmultiset (update_zmultiset A x m) y n = update_zmultiset (update_zmultiset A y n) x m"
    apply (cases m; cases n)
   apply (clarsimp simp add: update_zmultiset_replicate)+
  apply (simp add: add.commute)
  done

lemma update_zmultiset_plus_pos:
  "A + update_zmultiset B x (int m) = B + update_zmultiset A x (int m)"
  by simp
lemma update_zmultiset_plus_neg:
  "A + update_zmultiset B x (- (int m)) = (A + B) - update_zmultiset {#}\<^sub>z x (int m)"
  apply simp
  using add_diff_eq apply blast
  done

lemma update_zmultiset_plus[simp]:
  "update_zmultiset (update_zmultiset A t n) t m = update_zmultiset A t (n + m)"
  apply transfer
  apply (clarsimp simp add:  nat_add_distrib replicate_mset_plus equiv_zmset_def split: if_splits)
  subgoal by (metis ab_group_add_class.ab_diff_conv_add_uminus diff_add_cancel less_imp_le nat_add_distrib neg_0_le_iff_le not_le replicate_mset_plus)
  subgoal by (smt (verit, del_insts) nat_add_distrib replicate_mset_plus)
  subgoal by (smt (verit, ccfv_threshold) add.commute add.left_commute nat_add_distrib replicate_mset_plus) 
  subgoal by (smt (verit, ccfv_threshold) nat_add_distrib replicate_mset_plus)
  subgoal by (smt (verit, best) nat_add_distrib replicate_mset_plus) 
  done

lemma dataflow_op_simps[simp]:
  "\<not> is_Read (dataflow_op sg op)"
  "\<not> is_Write (dataflow_op sg op)"
  "\<not> is_Silent (dataflow_op sg op)"
  "is_Choice (dataflow_op sg op)"
  by (subst dataflow_op.code; simp)+

lemma rel_set_image:
  "rel_set R (f ` A) B \<longleftrightarrow> rel_set (\<lambda> x. R (f x)) A B"
  "rel_set S A (g ` B) \<longleftrightarrow> rel_set (\<lambda> x y. S x (g y)) A B"
  unfolding rel_set_def
  apply auto
  done

lemma rel_set_reflI:
  "(\<And>x. x \<in> A \<Longrightarrow> R x x) \<Longrightarrow> rel_set R A A"
  unfolding rel_set_def
  apply auto
  done

lemma change_multiplicities_append:
  "change_multiplicities su (xs @ ys) = (\<lambda> c. change_multiplicities su ys (change_multiplicities su xs c))"
  unfolding change_multiplicities_def 
  apply (rule ext)
  apply simp
  done

lemma change_multiplicities_append_comp:
  "change_multiplicities su (xs @ ys) = change_multiplicities su ys o change_multiplicities su xs"
  unfolding change_multiplicities_def
  apply simp
  done

lemma take_step_comm:
  "(take_step su (CM l2 t2 m2) \<circ>\<circ>\<circ> take_step) su (CM l1 t1 m1) = (take_step su (CM l1 t1 m1) \<circ>\<circ>\<circ> take_step) su (CM l2 t2 m2)"
  apply (rule ext)
  apply (auto simp add: fun_upd_twist update_zmultiset_comm)
  done

lemma take_step_plus[simp]:
  "take_step su (CM l t m) (take_step su (CM l t n) c) = take_step su (CM l t (m + n)) c"
  by (cases c; auto simp add: add.commute)

lemma change_multiplicitie_rev[simp]:
  "change_multiplicities su (rev xs) c = change_multiplicities su xs c"
  unfolding change_multiplicities_def
  apply (subst fold_rev)
  apply (clarsimp simp add: take_step_comm)+
  done

lemma change_multiplicities_comm:
  "change_multiplicities su (xs @ ys) c = change_multiplicities su (ys @ xs) c"
  unfolding change_multiplicities_def
  by (metis (mono_tags, lifting) change_multiplicitie_rev change_multiplicities_append change_multiplicities_def rev_append)

lemma change_multiplicities_simps[simp]:
  "change_multiplicities su [] c = c"
  "change_multiplicities su ((l, t, m) # xs) c = change_multiplicities su xs (take_step summary (CM l t m) c)"
  unfolding change_multiplicities_def by simp+

lemma change_multiplicities_simp_alt:
  "change_multiplicities su ((l, t, m) # xs) c = take_step su (CM l t m) (change_multiplicities su xs c)"
proof -
  have "change_multiplicities su ((l, t, m) # xs) c = change_multiplicities su (rev ((l, t, m) # xs)) c" using change_multiplicitie_rev by metis
  also have "\<dots> = take_step su (CM l t m) (change_multiplicities su (rev xs) c)" by (simp add: change_multiplicities_def foldr_conv_fold)
  ultimately show ?thesis by (metis change_multiplicitie_rev)
qed

lemma change_multiplicities_same_pointstamps_aux:
  "(\<forall> x \<in> set xs. \<forall> y \<in> set xs. fst x = fst y \<and> (fst o snd) x = (fst o snd) y) \<Longrightarrow>
   change_multiplicities su xs c = fold (\<lambda> m c. take_step su (CM ((fst o hd) xs) ((fst o snd o hd) xs) m) c) (map (snd o snd) xs) c"
  unfolding change_multiplicities_def
  apply (induct xs arbitrary: c)
   apply simp
  subgoal premises prems for a xs c
    using prems(2-) apply -
    apply (cases a; clarsimp)
    subgoal using prems(1) by (smt (verit) List.fold_cong fold_map fun_comp_eq_conv list.sel(1) list.set_cases list.set_intros(1))
    done
  done

lemma change_multiplicities_same_pointstamps:
  "(\<forall> x \<in> set xs. \<forall> y \<in> set xs. fst x = l \<and> (fst o snd) x = t) \<Longrightarrow>
   m = sum_list (map (snd o snd) xs) \<Longrightarrow>
   change_multiplicities su xs c = take_step su (CM l t m) c"
  apply (induct xs arbitrary: c m)
   apply simp
  subgoal premises prems for x xs c m
    using prems(2-) apply -
    apply hypsubst_thin
    apply (cases x)
    subgoal for l t m
      apply (simp only: change_multiplicities_simp_alt)
      apply (subst prems(1))
        apply force
       apply (rule refl)
      apply clarsimp
      apply (intro conjI impI)
      subgoal by (metis (no_types) group_cancel.sub1 uminus_add_add_uminus update_zmultiset_comm update_zmultiset_plus)
      subgoal
        by blast 
      done
    done
  done
    
lemma dataflow_op_change_multiplicities:
  "change_multiplicities (summ sg) (lo_pt sg) (pt_tr sg) = change_multiplicities (summ sg') (lo_pt sg') (pt_tr sg') \<Longrightarrow>
   summ sg = summ sg' \<Longrightarrow>
   pt_tr sg = pt_tr sg' \<Longrightarrow>
   edges sg = edges sg' \<Longrightarrow>
   dataflow_op sg op = dataflow_op sg' op"
  apply (coinduction arbitrary: sg sg' op rule: op.coinduct_upto)
  subgoal for sg sg' op
    apply simp
    apply (subst (3 4) dataflow_op.code)
    apply (simp add: rel_set_image split: sum.splits option.splits op.splits)
    apply (rule rel_set_reflI)
    apply (auto 0 0 simp add: rel_set_image split: sum.splits option.splits op.splits)
    subgoal for f nid c c'
      apply (subgoal_tac "c = c'")
      subgoal
        apply (rule op.cong_Silent)
        apply (rule op.cong_base)
        apply (rule exI[of _ "sg\<lparr>pt_tr := c, lo_pt := []\<rparr>"])
        apply (rule exI[of _ "sg'\<lparr>pt_tr := c', lo_pt := []\<rparr>"])
        apply (intro conjI exI)
            apply (rule refl)+
           apply simp_all
        done
      subgoal
        unfolding propagate_pointstamps_def Let_def
        apply simp
        done
      done
    subgoal
      by (force intro: op.cong_Read op.cong_base)
    subgoal
        apply (rule op.cong_Silent)
      apply (rule op.cong_base)
      apply (intro conjI exI)
           apply (rule refl)+
      apply (simp_all add: change_multiplicities_append)
      done
    subgoal
      by (simp add: op.cong_intros(2))
   subgoal
     by (simp add: op.cong_intros(2))
   subgoal
     by (simp add: op.cong_intros(2))
   subgoal
     by (force intro: op.cong_Write op.cong_base)
    subgoal
      by (force intro: op.cong_Silent op.cong_base)
    done
  done

lemma input_op_LCons_Nil:
  "input_op i (LCons [] lxs) = input_op (Suc i) lxs"
  apply (cases "llength (ltakeWhile ((=) []) lxs) \<noteq> \<infinity>")
  subgoal
  apply (subst (1 2) input_op.code)
  apply (simp split: llist.splits list.splits)
  apply (subst (1 2) the_enat_eSuc)
     apply simp_all
    done
  subgoal
  apply (subst (1 2) input_op.code)
    apply (simp split: llist.splits list.splits)
    apply (meson ldropWhile_LCons_lfinite_ltakeWhile llength_eq_infty_conv_lfinite)
    done
  done

lemma input_op_LNil:
  "input_op i LNil = \<oslash>"
  apply (subst input_op.code)
  apply simp
  done

lemma dataflow_op_end_op:
  "dataflow_op sg \<oslash> = \<oslash>"
  apply (subst dataflow_op.code)
  apply simp
  done

lemma dataflow_op_input_top_input_op:
  "edges sg = (\<lambda> _. []) \<Longrightarrow>
   dataflow_op sg (map_op (case_option (Inl nid) (\<lambda>p. Inr (nid, p))) (case_option (Inl nid) (\<lambda>p. Inr (nid, p))) (input_top (Cap i (1 :: 1)) inps)) \<approx>
   map_op (\<lambda> p. (nid, p)) (\<lambda> p. (nid, p)) (input_op i inps)"
proof (coinduction arbitrary: inps i sg rule: wbisim_coinduct)
  case SIM1
  then show ?case
    apply -
    apply (elim step_map_op_elim step_dataflow_op_elim step_input_top_elim conjE; simp; hypsubst_thin)
    subgoal for nida op'' io' op''a xa xs
      apply (cases inps)
       apply simp
      subgoal for xs lxs
        apply (cases xs; simp)
        subgoal for x xs'
        apply (intro exI conjI)
           apply (rule step_wstep)
           apply fastforce
          apply hypsubst_thin
          apply (rule wbcr_base)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI[of _ "sg\<lparr> lo_pt := (lo_pt sg) @ extract_progress nid (edges sg) \<lparr>cons = [], inte = [], prod = [(1, i, 1)]\<rparr> \<rparr>"])
          apply (intro conjI[rotated])
          apply simp
           apply (rule refl)
          apply (subst (2) input_top.code)
          apply (simp add: comp_def split: if_splits)
          apply (cases xs')
          subgoal
            apply simp
               apply (subst (1 2) dataflow_op.code)
            apply (auto simp add: extract_progress_def split: if_splits option.splits)
            done
          subgoal
            apply simp
            apply (rule box_equals) 
            defer
            apply (rule dataflow_writes_extract_progress_from_push[symmetric, where p="1 :: 1", simplified])
            apply (rule refl)
             apply (rule dataflow_writes_extract_progress_from_push[symmetric, where p="1 :: 1", simplified])
            apply (rule refl)
          apply (clarsimp simp add: extract_progress_def split: option.splits)
            done
          done
        done
      done
    subgoal 
      apply (cases inps; simp)
      subgoal for x lxs
        apply (intro exI conjI)
        apply (subst input_op_LCons_Nil)
         apply (rule rtranclp.intros(1))
          apply (rule wbcr_base)
          apply (rule exI)
          apply (rule exI)
          apply (rule exI[of _ "sg\<lparr> lo_pt := (lo_pt sg) @ extract_progress nid (edges sg) \<lparr>cons = [], inte = [(1, i, - 1), (1, Suc i, 1)], prod = []\<rparr> \<rparr>"])
          apply (intro conjI[rotated])
      defer
          apply (rule refl)+
         apply simp_all
        done
      done
    subgoal
      apply (auto simp add: dataflow_op_end_op input_op_LNil)
      done
    subgoal   
      apply (rule FalseE)
      apply (subst (asm) input_top.code)
      apply (simp split: llist.splits)
      subgoal for xs lxs
        apply (cases xs; simp add: writes_Cons_simp)
        done
      done
 subgoal   
      apply (rule FalseE)
      apply (subst (asm) input_top.code)
      apply (simp split: llist.splits)
      subgoal for xs lxs
        apply (cases xs; simp add: writes_Cons_simp)
        done
      done
    done
next
  case SIM2
  then show ?case
    apply -
    apply (elim step_map_op_elim step_input_op_elim conjE; simp; hypsubst_thin)
    subgoal for io' op'' x xs inps'
      apply (intro exI conjI)
      unfolding wstep_def
      apply simp
     apply (rule relcomppI[rotated])
     apply (rule relcomppI[rotated])
      apply (rule rtranclp.intros(1))
        apply (rule step_Out_dataflow_op_Out_Inr_intro)
        apply (rule step_map_op[where f="case_option (Inl nid) (\<lambda>p. Inr (nid, 1))" and g="case_option (Inl nid) (\<lambda>p. Inr (nid, 1))"])
         apply simp_all
         apply (rule step_input_top_Out_Some_intro[where c="Cap (i + the_enat (llength (ltakeWhile ((=) []) inps))) 1" and xs="x # xs"])
           apply assumption
          apply (rule refl)+
      apply simp
      apply (rule relpowp_imp_rtranclp) 
      apply (rule steps_Tau_dataflow_op_Out_Inl_intro[where nid=nid and sg=sg and xs="map (\<lambda> t. \<lparr> cons = [], inte = [(1, t, -1), (1, Suc t, 1)], prod = [] \<rparr>) ([i..< i + (the_enat (llength (ltakeWhile ((=) []) inps)))])" ])
         apply (rule steps_map_op)
      apply simp
           apply (rule ldropWhile_steps_input_top[where  c="Cap i 1", simplified])
      apply (meson ldropWhile_LCons_lfinite_ltakeWhile)
           apply simp
      apply simp
         apply (rule refl)+
       apply (intro conjI wbcr_base)
      apply (rule exI[of _ "LCons xs inps'"])
      apply (rule exI[of _ "i + the_enat (llength (ltakeWhile ((=) []) inps))"])
       apply (rule exI[of _ "sg\<lparr> lo_pt := (lo_pt sg) @ extract_progress nid (edges sg) \<lparr>cons = [], inte = concat (map (\<lambda> t. [(1, t, -1), (1, Suc t, 1)]) [i..< i + (the_enat (llength (ltakeWhile ((=) []) inps)))]), prod = [(1, i, 1)]\<rparr> \<rparr>"])
      apply (intro conjI)
      apply simp
      apply (clarsimp simp add: extract_progress_def split: option.splits)
      apply (subst dataflow_writes_extract_progress_from_push[where p="1 :: 1", simplified])
       apply (rule refl)
        apply (clarsimp simp add: extract_progress_def split: option.splits)
        apply simp_all
      apply (cases xs)
      subgoal
        apply (subst (2) input_top.code)
        apply (simp add: comp_def)
        apply (subst (1 2) dataflow_extract_progress_from_push[simplified])
        apply (clarsimp simp add: extract_progress_def split: option.splits)
        apply (rule arg_cong2[where f=dataflow_op])
         apply simp_all
        apply (cases sg; simp)
      apply (simp add: map_concat)
       apply (rule arg_cong[where f=concat])
      apply (rule map_cong)
        apply simp_all
        done
      subgoal
        apply (subst (2) input_top.code)
        apply (simp add: comp_def)
        apply (subst (1 2) dataflow_writes_extract_progress_from_push[simplified])
          apply (clarsimp simp add: extract_progress_def split: option.splits)
          apply (rule refl)+
        apply force
        apply (rule arg_cong2[where f=dataflow_op])
         apply simp_all
        apply (cases sg; simp)
      apply (simp add: map_concat extract_progress_def)
    apply (simp add: map_concat)
       apply (rule arg_cong[where f=concat])
      apply (rule map_cong)
         apply simp_all
        done
      done
    done
qed

(* FIXME: move me *)
lemma is_empty_antichain_simp[simp]:
  "is_empty_antichain {}\<^sub>A"
  apply transfer
  apply (auto simp add: Set.is_empty_def)
  done
lemma is_empty_antichain_empty_list[simp]:
  "is_empty_antichain (antichain_from_list [])"
  apply transfer
  apply (auto simp add: Set.is_empty_def)
  done
lemma is_empty_antichain_not_empty_list[simp]:
  "\<not> is_empty_antichain (antichain_from_list [a])"
  apply transfer
  apply (auto simp add: Set.is_empty_def)
  done

lemma compile_dataflow_tree_aux_Logic_simp[simp]:
  "compile_dataflow_tree_aux n (Logic op) = (n + 1, \<lambda> l1 l2. 
    if n = node l1 \<and> n = node l2 \<and> is_Trg (port l1) \<and> is_Src (port l2) 
    then frontier (abs_zmultiset (mset [0], {#})) 
    else frontier {#}\<^sub>z, map_op (case_option (Inl n) (\<lambda> p. Inr (n, p))) (case_option (Inl n) (\<lambda> p. Inr (n, p))) op)"
  apply auto
  done

lemma compile_dataflow_tree_aux_wellformed:
  "compile_dataflow_tree_aux n op = (n', s, op') \<Longrightarrow>
   \<not> has_zero_cyc s \<and> no_self_loop_checker s \<and> implementation_graph_checker (weights_to_graph_fun (remove_non_zero_weights s))"
  oops
(*   apply (induct op arbitrary: s)
  subgoal for op s
    apply simp
    apply safe
    subgoal
      apply hypsubst_thin
    unfolding compile_dataflow_tree_def Let_def weights_to_graph_fun_def no_self_loop_checker_def implementation_graph_checker_def enum_location_def enum_num1_def enum_port_def 
        apply (clarsimp split: if_splits)
 *)

lemma compile_dataflow_tree_Logic:
  "compile_dataflow_tree (Logic op) = 
  (\<lambda> l1 l2. 
    if 1 = node l1 \<and> (1 :: 1) = node l2 \<and> is_Trg (port l1) \<and> is_Src (port l2) 
    then frontier (abs_zmultiset (mset [0], {#})) 
    else frontier {#}\<^sub>z, map_op (case_option (Inl 1) (\<lambda> p. Inr (1, p))) (case_option (Inl 1) (\<lambda> p :: 1. Inr (1, p))) op)"
  unfolding compile_dataflow_tree_def
  apply (simp only: Let_def compile_dataflow_tree_aux.simps prod.case)
  apply (subst (7) if_P)
   apply eval
  apply simp
  done

(* FIXME: move me *)
lemma wbisim_refl_alt:
  "op = op' \<Longrightarrow> wbisim op op'"
  using wbisim_refl by auto

lemma compile_dataflow_input_top_input_op:
  "(compile_dataflow (Logic (input_top (Cap i 1) inps)) :: (1 \<times> 1, 1 \<times> 1, 'b \<times> nat) op) \<approx> map_op (\<lambda> p. (1, p)) (\<lambda> p. (1, p)) (input_op i inps)"
  unfolding compile_dataflow_def Let_def
  apply (simp split: prod.splits)
  apply (intro conjI allI impI)
  subgoal for su op
    using dataflow_op_input_top_input_op[where sg="init_subgraph su", simplified, where i=i and inps=inps] apply -
    apply (drule meta_mp)
    subgoal
      unfolding compile_dataflow_tree_def Let_def 
      apply (simp split: if_splits)
      subgoal
        unfolding compile_dataflow_tree_def Let_def weights_to_graph_fun_def no_self_loop_checker_def implementation_graph_checker_def enum_location_def enum_num1_def enum_port_def 
        apply (clarsimp split: if_splits)
        done
      subgoal
        unfolding compile_dataflow_tree_def Let_def weights_to_graph_fun_def no_self_loop_checker_def implementation_graph_checker_def enum_location_def enum_num1_def enum_port_def 
        apply (clarsimp split: if_splits)
        done
      done
    subgoal premises prems
      apply (rule wbisim_trans[rotated])
      apply (rule prems(2))
      apply (rule wbisim_refl_alt)
      apply (rule arg_cong2[where f=dataflow_op])
      subgoal
        using prems(1) apply -
        apply (clarsimp simp add: compile_dataflow_tree_Logic)
        subgoal premises
              apply (rule ext)+
        unfolding enum_location_def enum_num1_def enum_port_def 
        apply (auto simp add: compile_dataflow_tree_Logic split: if_splits)
        done
      done
    subgoal
        using prems(1) apply -
        apply (clarsimp simp add: compile_dataflow_tree_Logic)
        done
      done
    done
  done

lemma lhd_concat_ldropWhile:
  "lfinite (ltakeWhile ((=) []) lxs) \<Longrightarrow>
   \<exists> xs lxs'. ldropWhile ((=) []) lxs = LCons (x # xs) lxs' \<Longrightarrow>
   lhd (lconcat lxs) = x"
  apply (induct "ltakeWhile ((=) []) lxs"  arbitrary: lxs rule: lfinite_induct)
  subgoal
  apply (simp add: lconcat_correct split: prod.splits)
      apply (smt (z3) ldropWhile_LNil ldropWhile_simps(2) lhd_LCons lhd_lconcat llist.map_disc_iff llist.map_sel(1) llist_of.simps(2) lnull_def not_lnull_conv)
    done
  subgoal for lxs
    apply (cases lxs; simp split: if_splits)
    done
  done

lemma lhd_concat_ldropWhile_alt:
  "lfinite (ltakeWhile ((=) []) lxs) \<Longrightarrow>
   \<not> lnull (ldropWhile ((=) []) lxs) \<Longrightarrow>
   lhd (lconcat lxs) = hd (lhd (ldropWhile ((=) []) lxs))"
 apply (induct "ltakeWhile ((=) []) lxs"  arbitrary: lxs rule: lfinite_induct)
  subgoal
  apply (simp add: lconcat_correct split: prod.splits)
    apply (smt (z3) Coinductive_List_Auxiliary.lconcat_eq_LNil Coinductive_List_Auxiliary.lconcat_simps(1) lconcat_correct lhd_concat_ldropWhile lhd_ldropWhile list.collapse llist.collapse(2) lnull_imp_lfinite lnull_ldropWhile lset_LNil
        lset_eq_empty ltakeWhile_eq_LNil_iff)
    done
  subgoal for lxs
    apply (cases lxs; simp split: if_splits)
    done
  done

lemma lhd_lconcat_lmap_zip:
  "lfinite (ltakeWhile ((=) []) inps) \<Longrightarrow>
   ldropWhile ((=) []) inps = LCons (x # xs) inps' \<Longrightarrow>
   lhd (lconcat (lmap (\<lambda>(xs, t). map (\<lambda>n. (n, t)) xs) (lzip inps (iterates Suc i)))) = (x, i + (the_enat (llength (ltakeWhile ((=) []) inps))))"
 apply (induct "ltakeWhile ((=) []) inps"  arbitrary: inps i rule: lfinite_induct)
  subgoal
    apply (simp add: lconcat_correct lnull_def split: prod.splits)
    apply (smt (z3) case_prod_conv iterates_lmap lappend_code(1) lappend_ltakeWhile_ldropWhile lhd_LCons lhd_lconcat lhd_llist_of list.map_disc_iff list.map_sel(1) llist.distinct(1) llist.map_disc_iff llist.map_sel(1) llist_of.simps(2)
        llist_of_eq_LNil_conv lzip.ctr(1) lzip.disc_iff(2) lzip.sel(1) lzip_eq_LNil_conv)
    done
  subgoal for lxs i
    apply (cases lxs; simp split: if_splits)
    subgoal for x lxs'
      apply (drule meta_spec[of _ lxs'])
      apply (drule meta_spec[of _ "Suc i"])
      apply simp
      apply (subst iterates.code)
      apply simp
      apply (metis eSuc_enat lfinite_llength_enat the_enat.simps)
      done
    done
  done

lemma ltl_lconcat_lmap_zip:
  "lfinite (ltakeWhile ((=) []) inps) \<Longrightarrow>
   ldropWhile ((=) []) inps = LCons (x # xs) inps' \<Longrightarrow>
   ltl (Coinductive_List_Auxiliary.lconcat (lmap (\<lambda>z. case z of (xs, t) \<Rightarrow> map (\<lambda>n. (n, t)) xs) (lzip inps (iterates Suc i)))) =
   Coinductive_List_Auxiliary.lconcat (lmap (\<lambda>z. case z of (xs, t) \<Rightarrow> map (\<lambda>n. (n, t)) xs) (lzip (LCons xs inps') (iterates Suc (dataflow_topology_from_tree.followed_by i (the_enat (llength (ltakeWhile ((=) []) inps)))))))"
  apply (induct "ltakeWhile ((=) []) inps"  arbitrary: inps i rule: lfinite_induct)
  subgoal
    apply (simp add: lconcat_correct lnull_def split: prod.splits)
    apply (subst ltl_lconcat)
      apply simp_all
      apply (metis (lifting) ldropWhile_LNil llist.distinct(1) lnull_def)
     apply (smt (z3) case_prod_conv ldropWhile_LNil list.map_disc_iff llist.distinct(1) llist.map_disc_iff llist.map_sel(1) llist_of.simps(1) llist_of_inject lnull_def lnull_iterates ltakeWhile_eq_LNil_iff lzip.sel(1)
        lzip_eq_LNil_conv)
    apply (smt (z3) lappend_code(1) lappend_ltakeWhile_ldropWhile lconcat_LCons lhd_LCons lhd_LCons_ltl lhd_lzip list.sel(3) llist.disc(2) llist.map_disc_iff llist.map_sel(1) lnull_iterates ltl_llist_of ltl_lmap ltl_lzip ltl_simps(2)
        lzip.disc(2) map_tl prod.simps(2))
    done
  subgoal for lxs i
    apply (cases lxs; simp split: if_splits)
    subgoal for x lxs'
      apply (drule meta_spec[of _ lxs'])
      apply (drule meta_spec[of _ "Suc i"])
      apply simp
      apply (subst the_enat_eSuc)
      using llength_eq_infty_conv_lfinite apply blast
      apply simp
      apply (subst iterates.code)
      apply simp
      done
    done
  done


lemma input_top_correctness:
  "wtraced (compile_dataflow (Logic (input_top (Cap i 1) inps)) :: (1 \<times> 1, 1 \<times> 1, 'b \<times> nat) op) ios \<Longrightarrow>
   lprefix ios (lmap (\<lambda> (n, t). VOut (1, 0) (n, t)) (lconcat (lmap (\<lambda> (xs, t). map (\<lambda> n. (n, t)) xs) (lzip inps (iterates Suc i)))))"
  apply (drule wbisim_wtraced[OF compile_dataflow_input_top_input_op])
  apply (coinduction arbitrary: ios inps i)
  subgoal for ios inps i
    apply (cases ios)
    subgoal
      by simp
    subgoal for io ios'
      apply simp
      apply (erule wtraced.cases)
       apply simp_all
      apply hypsubst_thin
      apply (elim wstep_map_op_elim)
      apply (subst (asm) wstep_input_op_simp)
       apply force
      apply (elim step_input_op_elim)
      apply (cases io; simp)
      apply hypsubst_thin
      apply safe
      subgoal premises prems
        using prems(2-) apply -
        unfolding lnull_def
        apply (auto simp add: lset_lzip split: prod.splits)
        apply (metis (full_types) in_lset_conv_lnth ldropWhile_eq_LNil_iff llist.distinct(1))
        done
      subgoal premises prems for op' io' op'' x xs inps' a b
        using prems(2-) apply -
        apply (subst lhd_lconcat_lmap_zip)
        apply simp_all
        apply (meson ldropWhile_LCons_lfinite_ltakeWhile)
        done
      subgoal for op' io' op'' x xs inps' a b
        apply (intro conjI[rotated] exI)
         apply assumption
        apply simp
        subgoal premises prems
          using prems(2) apply -
          apply (rule llist.map_cong)
           apply simp_all
          apply (rule ltl_lconcat_lmap_zip)
           apply simp_all
        apply (meson ldropWhile_LCons_lfinite_ltakeWhile)
          done
        done
      done
    done
  done
        find_theorems lmap name: cong

  find_theorems Coinductive_List_Auxiliary.lconcat Coinductive_List.lconcat

end
      

      using prems(1)[unfolded compile_dataflow_tree_def Let_def, simplified]

        unfolding compile_dataflow_tree_def Let_def weights_to_graph_fun_def no_self_loop_checker_def implementation_graph_checker_def enum_location_def enum_num1_def enum_port_def 
        apply simp


        find_theorems enum_location_inst.enum_location

end

(* 
value [GHC] "approx_in 38 [VOut 0 (9, 0), VOut 0 (5, 1), VOut 0 (2, 2)] (dataflow_op True init_subgraph ((input_top (Cap (0 :: nat) (0 :: 2)) (LCons [9, 3] (LCons [Suc 0, 5] (LCons [2] LNil)))) \<bullet>\<^sub>t max_top))"

 *)
fun traceprefix :: "nat \<Rightarrow> ('i, 'o, 'd) VIO list \<Rightarrow> ('i, 'o, 'd :: {countable}) op \<Rightarrow> bool" where
  "traceprefix n [] _ = True"
| "traceprefix n (VInp p x # lxs) (Read q f) = (p = q \<and> traceprefix n lxs (f x))"
| "traceprefix n (VOut p x # lxs) (Write op q y) = (p = q \<and> x = y \<and> traceprefix n lxs op)"
| "traceprefix (Suc n) lxs (Silent op) = traceprefix n lxs op"
| "traceprefix (Suc n) lxs (Choice ops) = (\<not> cis_empty (cfilter (traceprefix n lxs) ops))"
| "traceprefix _ _ _ = False"


definition "tp = traceprefix 1000000 [VOut 0 (9, 0)] (dataflow_op True init_subgraph ((input_top (Cap (0 :: nat) (0 :: 2)) (LCons [9] (LNil))) \<bullet>\<^sub>t max_top))"

definition "tp2 = traceprefix 1000000 [VOut 0 (1, 0), VOut 0 (2, 0), VOut 0 (3, 0), VOut 0 (9, 0), VOut 0 (8, 1), VOut 0 (1, 1), VOut 0 (0, 1)]
  (dataflow_op True init_subgraph (input_top (Cap (0 :: nat) 0) (LCons [Suc 0, 2, 3, 9] (LCons [8, 1, 0] LNil))))"

(* value [GHC] tp
 *)
term "Not (cis_empty (choices op))"

find_consts "_ cset \<Rightarrow> _ llist"

term cset_of_llist

find_theorems cset_of_llist wit_cset


term "\<lambda> (tr, op). while_option (\<lambda> (tr, op). Not (cis_empty (choices op))) (undefined)"

(* 
value [GHC] "(approx_in 40 [VOut 0 (9, 0), VOut 0 (1, 1)] (dataflow_op init_subgraph ((input_top (Cap (0 :: nat) (0 :: 2)) (LCons [0, 9] (LCons [Suc 0] LNil))) \<bullet>\<^sub>t (max_top []))))"
 *)


value [GHC] "cfilter ((\<noteq>) []) (eval 29 (dataflow_op init_subgraph ((input_top (Cap (0 :: nat) (0 :: 2)) (LCons [0, 9] (LCons [Suc 0] LNil))) \<bullet>\<^sub>t (max_top []))))"

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