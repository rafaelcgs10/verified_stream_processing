theory Timely_Operators

imports
  Operator
  BNA_Operators
  Progress_Tracking.Propagate
  Eval
  "HOL-Library.While_Combinator"
  Executable
(*    "HOL-Library.Code_Target_Nat" 
  "HOL-Library.Code_Target_Int"   *)
begin

(* Inspired by timely/src/progress/mod.rs:61 *)
datatype 'loc port = Trg (idp: 'loc) | Src (idp: 'loc)
fun is_Src where "is_Src (Trg _) = False" | "is_Src _ = True"
fun is_Trg where "is_Trg (Trg _) = True" | "is_Trg _ = False"

  (* Inspired by timely/src/progress/mod.rs:19 *)
datatype 'loc location = Loc (node: 'loc) (port: "'loc port")

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

instantiation location :: (enum) enum
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


instantiation location :: (linorder) linorder
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
record ('loc, 't) subgraph =
  pt_tr :: "('loc location, 't) configuration"
  (* We consider local_pointstamp and final_pointstamp as the same thing in this non-distributed version *)
  lo_pt :: "('loc location \<times> 't \<times> int) change_batch"
  edges :: "'loc location \<Rightarrow> 'loc location list"

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

definition summary :: "2 location \<Rightarrow> 2 location \<Rightarrow> (nat antichain)" where
  "summary l1 l2 = 
  (if node l1 = 0 \<and> port l1 = Src 0 \<and> node l2 = 1 \<and> port l2 = Trg 0 then frontier (abs_zmultiset (mset [0], {#})) else
   if node l1 = 1 \<and> port l1 = Trg 0 \<and> node l2 = 1 \<and> port l2 = Src 0 then frontier (abs_zmultiset (mset [0], {#})) else
   frontier {#}\<^sub>z)"

declare zmultiset_of_antichain_def[code]

global_interpretation sum: enum_dataflow_topology
  "summary :: 2 location \<Rightarrow> 2 location \<Rightarrow> nat antichain"
  "(+)"
  defines take_step' = "enum_dataflow_topology.take_step summary (+) :: _ \<Rightarrow> (2 location, nat) Step \<Rightarrow> _ \<Rightarrow> _" and
    after_summary = "dataflow_topology.after_summary (+) :: nat zmultiset \<Rightarrow> nat antichain \<Rightarrow> nat zmultiset"
  sorry

definition mymin_code :: "(nat \<times> ('a :: linorder) location) set \<Rightarrow> (nat \<times> 'a location)" 
  where [code del]: "mymin_code = mymin (<)"

lemma mymin_code[code]: "mymin_code (set (x # xs)) = fold (\<lambda>a b. if t_loc_linord (<) a b then a else b) xs x"
  unfolding mymin_code_def
  apply (rule linorderMin)
  apply unfold_locales
  apply auto
  done

definition take_step where
  "take_step = take_step' (<)"

declare sum.take_step.simps[of "((<) :: nat \<Rightarrow> _ \<Rightarrow> _)",  folded mymin_code_def take_step_def, code]

lift_definition zequal :: "'a zmultiset \<Rightarrow> 'a zmultiset \<Rightarrow> bool" is
  "\<lambda> (M, N) (P, Q). (M-N) = (P-Q) \<and> (N-M) = (Q-P)"
  apply (auto simp: equiv_zmset_def)
  apply (metis (full_types) Multiset.diff_right_commute add_diff_cancel_right')
  apply (metis Multiset.diff_right_commute add_diff_cancel_left')
  apply (metis add_diff_cancel_right' cancel_ab_semigroup_add_class.diff_right_commute)
  by (metis Multiset.diff_right_commute add_diff_cancel_left')

definition "reachable_locations \<equiv> { loc . \<exists> loc' .
     \<not> is_empty_antichain (summary loc loc') \<or> \<not> is_empty_antichain (summary loc' loc) }"

definition worklist_is_empty where
  "worklist_is_empty c = Set.Ball reachable_locations (\<lambda> loc. zequal (c_work c loc) {#}\<^sub>z)"

definition "propagate_all c0 = while_option (Not o worklist_is_empty)
                                            (take_step PR) c0"

fun print_2 where
  "print_2 n = (if n = 0 then STR ''0'' else STR ''1'')"

definition show_port where
  "show_port p = (case p of Src x \<Rightarrow> STR ''SRC '' + (print_2 x) | Trg x \<Rightarrow> STR ''TRG '' + (print_2 x))"

definition show_loc where
  "show_loc x = STR ''node: '' + print_2 (node x) + STR '', port: '' + show_port (port x)"


abbreviation "print_int n \<equiv> (if n \<ge> 0 then show_nat (Int.nat n) else STR ''-'' + show_nat (Int.nat (abs n)) )"

definition "DEBUG = False"

abbreviation "trace \<equiv> (if DEBUG then Debug.tracing else (\<lambda> x y. y))"

(* Inspired by timely/src/progress/subgraph.rs:453 *)
(* First migrate all change batches to the worklist, then call propagate_all *)
fun propagate_pointstamps :: "(2 location, nat) configuration \<Rightarrow> (2 location \<times> nat \<times> int) change_batch \<Rightarrow> (2 location, nat) configuration option"  where
  "propagate_pointstamps conf [] = propagate_all conf"
| "propagate_pointstamps conf ((l, t, m) # cbs) = propagate_pointstamps (trace (STR ''CM ==> '' + show_loc l + STR '', t: '' + show_nat t + STR '', m: '' + print_int m) (take_step (CM l t m)) conf) cbs"

abbreviation empty_conf where
  "empty_conf \<equiv> \<lparr>c_work = (\<lambda> _.  {#}\<^sub>z), c_pts = (\<lambda> _.  {#}\<^sub>z), c_imp = (\<lambda> _. {#}\<^sub>z)\<rparr>"

abbreviation "init_subgraph \<equiv>
  \<lparr> pt_tr = the (propagate_pointstamps empty_conf [(Loc 0 (Src 0), 0, 1)]),
   lo_pt = [],
   edges = (\<lambda> l1. [l2 \<leftarrow> enum_location_inst.enum_location. \<not> is_empty_antichain (summary l1 l2) ]) \<rparr>"

(* Inspired by timely/src/dataflow/operators/generic/builder_rc.rs:29 and timely/src/progress/operate.rs:63 *)
(* This is the shared that the operator exposes to the subgraph *)
record ('loc, 't) shared_state =
  cons :: "('loc \<times> 'loc \<times> 't \<times> int) change_batch"
  inte :: "('loc \<times> 'loc \<times> 't \<times> int) change_batch"
  prod :: "('loc \<times> 'loc \<times> 't \<times> int) change_batch"

(* Inspired by timely/src/progress/subgraph.rs:759 *)
definition extract_progress :: "('loc location \<Rightarrow> 'loc location list) \<Rightarrow> ('loc, 't) shared_state \<Rightarrow> ('loc location \<times> 't \<times> int) change_batch" where
  "extract_progress edg st =
    map (\<lambda> (node, p, t, m). (Loc node (Trg p), t, -m)) (cons st) @ 
    map (\<lambda> (node, p, t, m). (Loc node (Src p), t, m)) (inte st) @
    concat (map (\<lambda> (node, p, t, m). map (\<lambda> l. (l, t, m)) (edg (Loc node (Src p)))) (prod st))"


lift_definition Max_antichain :: "nat antichain \<Rightarrow> nat" is "\<lambda> x. if Set.is_empty x then 0 else Max x" .


abbreviation "print_frontier x \<equiv> trace (show_nat (Max_antichain x))" 

value "c_imp (the (propagate_pointstamps empty_conf [(Loc 0 (Src 0), 0, 1),(Loc 1 (Trg 0), 0, 1), (Loc 1 (Src 0), 0, 1)])) (Loc 1 (Trg 0))"
value "print_frontier (frontier (c_imp (the (propagate_pointstamps (the (propagate_pointstamps empty_conf [(Loc 0 (Src 0), 0, 1), (Loc 1 (Trg 0), 0, 1)]))
       [(Loc 0 (Src 0), 0, -1), (Loc 1 (Trg 0), 0, -1)])) (Loc 1 (Trg 0)))) (1 :: nat)"


(* Inspired by timely/src/dataflow/operators/capability.rs:62 *)
datatype ('loc, 't) capability = Cap (time: 't) (out: 'loc)

definition tscomp_op ::
  "('ip option, 'op1 option, 'd + 's) op \<Rightarrow>
   ('op1 option, 'op option, 'd + 's) op \<Rightarrow>
   ('ip option, 'op option, 'd + 's) op" (infixl "\<bullet>\<^sub>t" 65) where
  "tscomp_op op1 op2 = map_op (case_sum id (\<lambda> _. None)) (case_sum (\<lambda> _. None) id) (comp_op (case_option None (Some o Some)) (\<lambda>_. []) op1 op2)"

lift_definition is_empty_antichain :: "'a :: order antichain \<Rightarrow> bool" is "Set.is_empty".

lemma set_zmset_code[code]:
  "set_zmset (abs_zmultiset x) = (case x of (A, B) \<Rightarrow> set_mset (A - B) \<union> set_mset (B - A))"
  unfolding set_zmset_def
  by transfer (auto simp: set_mset_def)

lemma frontier_code[code]:
  "set_antichain (frontier x) = minimal_antichain {t \<in> set_zmset x. 0 < zcount x t}"
  by transfer' (auto intro!: arg_cong[of _ _ minimal_antichain] zcount_inI)

abbreviation "frontier_updating b \<equiv> cfilter (\<lambda> op. case op of Read None f \<Rightarrow> b | _ \<Rightarrow> True)"

corec dataflow_op where
  "dataflow_op b sg op = Choice (cimage (\<lambda> op. case op of 
     Read None f \<Rightarrow> Silent (dataflow_op False sg (f (Inr (Inr (c_imp (pt_tr sg))))))
   | Read (Some p) f \<Rightarrow> Read p (\<lambda> x. dataflow_op b sg (f (Inl x)))
   | Write op' None (Inr (Inl st)) \<Rightarrow> (case propagate_pointstamps (pt_tr sg) (lo_pt sg @ extract_progress (edges sg) st) of
                                   Some conf' \<Rightarrow> Silent (dataflow_op True (sg\<lparr> pt_tr := conf', lo_pt := [] \<rparr>) op')
                                 | None \<Rightarrow> undefined)
   | Write op' (Some p) (Inl x) \<Rightarrow> Write (dataflow_op b sg op') p x
   | Silent op' \<Rightarrow> Silent (dataflow_op b sg op')) (frontier_updating b (choices op)))"

(* Should this be non-deterministic? (e.g. non-deterministically send events and capabilities updates) *)
(* Inspired by timely/src/dataflow/channels/pushers/counter.rs:25 and timely/src/dataflow/channels/mod.rs:49 *)
(* writes maybe could support multiple different ports, then this one also would *)
abbreviation "push nid op p batch \<equiv> 
  writes (Write op None (Inr (Inl \<lparr> cons = [], inte = [], prod = map (\<lambda> (x, c). (nid, p, time c, 1)) batch \<rparr>))) (Some p) (map (\<lambda> (x, c). Inl (x, time c)) batch)"

abbreviation "drop_cap nid c op \<equiv>
  Write op None (trace (String.implode (''Dropping cap!'')) Inr (Inl \<lparr> cons = [], inte = [(nid, out c, time c, -1)], prod = [] \<rparr>))"

abbreviation "drop_caps nid cs op \<equiv>
  Write op None (trace (String.implode (''Dropping caps!'')) Inr (Inl \<lparr> cons = [], inte = map (\<lambda> c. (nid, out c, time c, -1)) cs, prod = [] \<rparr>))"

abbreviation "delayed_cap nid c t \<equiv>
  (Cap (time c + abs t) (out c),
  \<lambda> op. Write op None 
     (Inr (Inl \<lparr> cons = [],
            inte = [(nid, out c, time c, -1), (nid, out c, time c + abs t, 1)],
            prod = [] \<rparr>)))"

find_consts "_ antichain" name: empty

(* corec input_op where
  "input_op c inps = (case inps of
    LNil \<Rightarrow> drop_cap 0 c \<odot>
  | LCons xs lxs \<Rightarrow> push 0 c (let (c, f) = delayed_cap 0 c 1 in f (input_op c lxs)) 1 xs)" *)

corec input_op :: "('op :: {zero, one}, 't :: {order, plus, one}) capability \<Rightarrow> 'c buf llist \<Rightarrow> (0 option, 'op option, 'c \<times> 't + ('op, 't) shared_state + 'e) op" where
  "input_op c inps = (case inps of
    LNil \<Rightarrow> drop_cap 0 c \<oslash>
  | LCons xs lxs \<Rightarrow> push 0 (Write (input_op (Cap (time c + 1) (out c)) lxs) None 
     (trace (STR ''Delaying capability!'')Inr (Inl \<lparr> cons = [],
            inte = [(0, out c, time c, -1), (0, out c, time c + 1, 1)],
            prod = []\<rparr>))) 0 (map (\<lambda> x. (x, c)) xs))"

abbreviation "try_read i f \<equiv> Choice (cimage (\<lambda> x. if x then f None else Read i (f o Some)) (cinsert True (csingle False)))"

lemma try_read_simp[simp, code]: "try_read i f = Choice ({| Read i (f o Some), f None |})"
  by auto

term "empty_antichain :: nat antichain"

term "dataflow_op True init_subgraph"
term "( (input_op (Cap (0 :: nat) (0 :: 2)) (LCons [Suc 0, 2, 3, 9] (LCons [8, 1, 0] LNil))))"

value [GHC] "eval 17 (dataflow_op True init_subgraph (input_op (Cap (0 :: nat) 0) (LCons [Suc 0, 2, 3, 9] (LCons [8, 1, 0] LNil))))"
value [GHC] "eval 5 (dataflow_op True init_subgraph (input_op (Cap (0 :: nat) 0) (LCons [Suc 0] (LNil))))"

abbreviation "maxs ft buf \<equiv> [(n, c) \<leftarrow> buf. ft (time c) \<and> n = Max (set (map fst ((filter (\<lambda> (n', c'). time c = time c') buf))))]"

(* The minted capability must depend on the internal wiring *)
abbreviation "pull nid i f \<equiv> (Read (Some i) 
  (\<lambda> x. case x of
    (Inl (d, t)) \<Rightarrow> Write (f (d, Cap t 0)) None (Inr (Inl \<lparr>  cons = [(nid, i, t, 1)], inte = [(nid, i, t, 1)], prod = [] \<rparr>))))"

abbreviation
  "less_than_frontier ft t \<equiv> (\<not> is_empty_antichain (filter_antichain (\<lambda> f. t < f) ft))"

term choice2

declare [[unify_search_bound = 100]]

corec max_op' :: "(nat \<times> (2, nat) capability) buf \<Rightarrow> (2 option, 2 option, nat \<times> nat + (2, nat) shared_state + (2 location \<Rightarrow> nat zmultiset)) op" where
  "max_op' buf = choice2
   (Read None (\<lambda> st.
    let impf = projr (projr st) in
    let ft = frontier (impf (Loc 1 (Trg 0))) in
    if is_empty_antichain ft 
    then \<oslash> 
    else 
    let result = (maxs (less_than_frontier ft) buf) in
    push 1 (drop_caps 1 (map snd result) (max_op' [(n, c) \<leftarrow> buf. \<not> less_than_frontier ft (time c)])) 0 result))
   (pull (1 :: 2) (0 :: 2) (\<lambda> x. max_op' (buf @ [x])))"

abbreviation "max_op \<equiv> max_op' []"

(* corec max_op :: "(nat \<times> (2, nat) capability) buf \<Rightarrow> (2 option, 2 option, nat \<times> nat + (2, nat) shared_state + (2 location \<Rightarrow> nat zmultiset)) op" where
  "max_op buf = Read None (\<lambda> st. pull (1 :: 2) (0 :: 2) (case_option
   (let result = (maxs (less_than_frontier 1 0 (projr (projr st))) buf) in
    push 1 (drop_caps 1 (map snd result) (max_op [(n, c) \<leftarrow> buf. \<not> less_than_frontier (1 :: 2) 0 (projr (projr st)) (time c)])) 0 result)
   (\<lambda> x. let result = (maxs (less_than_frontier 1 0 (projr (projr st))) (buf @ [x])) in
    push 1 (drop_caps 1 (map snd result) (max_op [(n, c) \<leftarrow> buf @ [x]. \<not> less_than_frontier 1 0 (projr (projr st)) (time c)])) 0 result)))" *)

value [GHC] "approx_in 36 [VOut 0 (9, 0), VOut 0 (5, 1)] (dataflow_op True init_subgraph ((input_op (Cap (0 :: nat) (0 :: 2)) (LCons [9, 3] (LCons [5] LNil))) \<bullet>\<^sub>t max_op))"

datatype ('loc, 'c, 'd) dataflow_tree = 
   "apply": Logic "'c \<Rightarrow> ('loc, 'loc, 'd) op"
 | Comp "'loc \<times> 'loc \<Rightarrow> ('loc \<times> 'loc) option" "('loc, 'c, 'd) dataflow_tree" "('loc, 'c, 'd) dataflow_tree"

find_consts "_ antichain \<Rightarrow> _ antichain \<Rightarrow> _ antichain"

find_consts "_ port \<Rightarrow> bool"

fun build_summary :: "'loc :: {one,plus, ord, minus} \<Rightarrow> ('loc, 'c, 'd) dataflow_tree \<Rightarrow> 'loc \<times> ('loc location \<Rightarrow> 'loc location \<Rightarrow> nat antichain)" where
  "build_summary n (Comp wire dt1 dt2) = (
    let (n', summary1) = build_summary n dt1 in
    let (n'', summary2) = build_summary n' dt2 in
    (n'', \<lambda> l1 l2. 
     if node l1 \<ge> n \<and> node l1 < n' \<and> node l2 \<ge> n' \<and> is_Src (port l1) \<and> is_Trg (port l2)
     then (case wire (node l1 - n, idp (port l1)) of 
             None \<Rightarrow> frontier {#}\<^sub>z 
           | Some (offset, q) \<Rightarrow> (if node l2 = n' + offset \<and> q = idp (port l2) then frontier (abs_zmultiset (mset [0], {#})) else frontier {#}\<^sub>z )) 
     else summary1 l1 l2 + summary2 l1 l2)
   )"
| "build_summary n (Logic f) = (n + 1, (\<lambda> l1 l2. 
    if n = node l1 \<and> n = node l2 \<and> is_Trg (port l1) \<and> is_Src (port l2) 
    then frontier (abs_zmultiset (mset [0], {#})) 
    else frontier {#}\<^sub>z))"

value "[(Suc 0 , Suc 0) \<mapsto> (Suc 0, Suc 0)](Suc 0, 1)"

value "snd (build_summary (0 :: 4)
       (Comp Some
         (Comp (\<lambda> l. None) (Logic (\<lambda> _. \<oslash>)) (Logic (\<lambda> _. \<oslash>)))
         (Comp (\<lambda> l. None) (Logic (\<lambda> _. \<oslash>)) (Logic (\<lambda> _. \<oslash>)))))
      (Loc 1 (Src 0)) (Loc 3 (Trg 0))"
value "snd (build_summary (0 :: 4)
       (Comp Some
         (Comp (\<lambda> l. None) (Logic (\<lambda> _. \<oslash>)) (Logic (\<lambda> _. \<oslash>)))
         (Comp (\<lambda> l. None) (Logic (\<lambda> _. \<oslash>)) (Logic (\<lambda> _. \<oslash>)))))
      (Loc 1 (Trg 0)) (Loc 1 (Src 0))"

value "snd (build_summary (0 :: 5)
       (Comp Some
         (Comp (\<lambda> l. None) (Comp Some (Logic (\<lambda> _. \<oslash>)) (Logic (\<lambda> _. \<oslash>))) (Logic (\<lambda> _. \<oslash>)))
         (Comp (\<lambda> l. None) (Logic (\<lambda> _. \<oslash>)) (Logic (\<lambda> _. \<oslash>)))))
      (Loc 1 (Src 0)) (Loc 4 (Trg 0))"
value "snd (build_summary (0 :: 5)
       (Comp [(1, 0) \<mapsto> (0, 0), (2, 0) \<mapsto> (1, 0)]
         (Comp (\<lambda> l. None) (Comp Some (Logic (\<lambda> _. \<oslash>)) (Logic (\<lambda> _. \<oslash>))) (Logic (\<lambda> _. \<oslash>)))
         (Comp (\<lambda> l. None) (Logic (\<lambda> _. \<oslash>)) (Logic (\<lambda> _. \<oslash>)))))
      (Loc 2 (Src 0)) (Loc 4 (Trg 0))"

global_interpretation dataflow_topology_from_tree: enum_dataflow_topology
  "build_summary g"
  "(+)"
  for g :: "('p :: {enum,linorder}, 'c, 'd) dataflow_tree "
  defines take_step'' = "\<lambda> g. enum_dataflow_topology.take_step (build_summary g) (+) :: _ \<Rightarrow> (2 location, nat) Step \<Rightarrow> _ \<Rightarrow> _"
  and after_summary' = "dataflow_topology.after_summary (+) :: nat zmultiset \<Rightarrow> nat antichain \<Rightarrow> nat zmultiset"
  apply standard
  sorry

term "take_step''"

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