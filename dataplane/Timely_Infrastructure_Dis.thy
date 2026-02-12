theory Timely_Infrastructure_Dis

imports
    "HOL-ex.Sketch_and_Explore" 
    Timely_Infrastructure
begin

subsection \<open>Extended extension (allows for communication)\<close>

datatype (discs_sels) ('ip, 'op, 'd, 'w :: enum) exchange_op_aux =
  exchange_Read_aux "('ip + 'ip) option" "'d \<Rightarrow> ('ip option, 'op option, 'd) op"
  | exchange_Write_aux "('ip option, 'op option, 'd) op" "('op \<times> 'w) option" 'd
  | exchange_Silent_aux "('ip option, 'op option, 'd) op"

abbreviation eval_exchange_op_aux :: "(('ip option, 'op option, 'd) op \<Rightarrow> (('ip + 'ip) option, ('op \<times> 'w :: enum) option, 'd) op) \<Rightarrow> 
    ('ip, 'op, 'd, 'w) exchange_op_aux \<Rightarrow> (('ip + 'ip) option, ('op \<times> 'w) option, 'd) op" where
  "eval_exchange_op_aux c aux \<equiv> (case aux of
    exchange_Read_aux p f \<Rightarrow> Read p (\<lambda> d. c (f d))
  | exchange_Write_aux op q x \<Rightarrow> Write (c op) q x
  | exchange_Silent_aux op \<Rightarrow> Silent (c op))"

corec exchange_op :: "'w :: enum \<Rightarrow> ('w \<Rightarrow> 'op \<Rightarrow> 'd \<Rightarrow> 'w) \<Rightarrow> ('ip option, 'op option, 'd) op \<Rightarrow> (('ip + 'ip) option, ('op \<times> 'w) option, 'd) op" where
  "exchange_op worker pact op =
     Choice (cimage (eval_exchange_op_aux (exchange_op worker pact)) 
      (cUnion (cimage (\<lambda> op. case op of
     Read (Some p) f \<Rightarrow> cinsert (exchange_Read_aux (Some (Inl p)) f) (csingle (exchange_Read_aux (Some (Inr p)) f))
     | Read None f \<Rightarrow> csingle (exchange_Read_aux None f)
     | Write op' (Some p) x \<Rightarrow> csingle (exchange_Write_aux op' (Some (p, pact worker p x)) x)
     | Write op' None x \<Rightarrow> csingle (exchange_Write_aux op' None x)
     | Silent op' \<Rightarrow> csingle (exchange_Silent_aux op')
     ) ((choices op)))))"

lemma exchange_op_code[code]: "exchange_op worker pact op =
     Choice (cUnion (cimage (\<lambda> op. case op of
     Read (Some p) f \<Rightarrow> cinsert (Read (Some (Inl p)) (\<lambda> d. (exchange_op worker pact (f d)))) (csingle (Read (Some (Inr p)) (\<lambda> d. (exchange_op worker pact (f d)))))
     | Read None f \<Rightarrow> csingle (Read None (\<lambda> d. (exchange_op worker pact (f d))))
     | Write op' (Some p) x \<Rightarrow> csingle (Write (exchange_op worker pact op') (Some (p, pact worker p x)) x)
     | Write op' None x \<Rightarrow> csingle (Write (exchange_op worker pact op') None x)
     | Silent op' \<Rightarrow> csingle (Silent (exchange_op worker pact op'))
     ) ((choices op))))"
  apply (subst exchange_op.code)
  apply (unfold cimage_cUn op.inject)
   apply (auto simp add: cset.map_comp o_def cimage_cUn intro!: arg_cong2[where f = cUn] cimage_cong
      split: exchange_op_aux.splits op.splits option.splits)
  subgoal for f
    unfolding image_def
    by fastforce
  subgoal for f p
    unfolding image_def
    by fastforce
  subgoal for f p
    unfolding image_def
    by fastforce
  subgoal for op x
    unfolding image_def
    by fastforce
  subgoal for op q x
    unfolding image_def
    by fastforce
  subgoal for op
    unfolding image_def
    by fastforce
  done

(*
datatype (discs_sels) ('ip, 'op, 'd, 'w :: enum) exchange_op_aux =
  exchange_Read_aux "'ip + 'ip" "'d \<Rightarrow> ('ip, 'op, 'd) op"
  | exchange_Write_aux "('ip, 'op, 'd) op" "'op \<times> 'w" 'd
  | exchange_Silent_aux "('ip, 'op, 'd) op"

abbreviation eval_exchange_op_aux :: "(('ip, 'op, 'd) op \<Rightarrow> ('ip + 'ip, 'op \<times> 'w :: enum, 'd) op) \<Rightarrow> ('ip, 'op, 'd, 'w) exchange_op_aux \<Rightarrow> ('ip + 'ip, 'op \<times> 'w, 'd) op" where
  "eval_exchange_op_aux c aux \<equiv> (case aux of
    exchange_Read_aux p f \<Rightarrow> Read p (\<lambda> d. c (f d))
  | exchange_Write_aux op q x \<Rightarrow> Write (c op) q x
  | exchange_Silent_aux op \<Rightarrow> Silent (c op))"

corec exchange_op :: "'w :: enum \<Rightarrow> ('w \<Rightarrow> 'op \<Rightarrow> 'd \<Rightarrow> 'w) \<Rightarrow> ('ip, 'op, 'd) op \<Rightarrow> ('ip + 'ip, 'op \<times> 'w, 'd) op" where
  "exchange_op worker pact op =
     Choice (cimage (eval_exchange_op_aux (exchange_op worker pact)) 
      (cUnion (cimage (\<lambda> op. case op of
     Read p f \<Rightarrow> cinsert (exchange_Read_aux (Inl p) f) (csingle (exchange_Read_aux (Inr p) f))
     | Write op' p x \<Rightarrow> csingle (exchange_Write_aux op' (p, pact worker p x) x)
     | Silent op' \<Rightarrow> csingle (exchange_Silent_aux op')
     ) ((choices op)))))"

subsection \<open>Basic simplification properties\<close>
lemma exchange_op_code[code]: "exchange_op worker pact op =
     Choice (cUnion (cimage (\<lambda> op. case op of
     Read p f \<Rightarrow> cinsert (Read (Inl p) (\<lambda> d. (exchange_op worker pact (f d)))) (csingle (Read (Inr p) (\<lambda> d. (exchange_op worker pact (f d)))))
     | Write op' p x \<Rightarrow> csingle (Write (exchange_op worker pact op') (p, pact worker p x) x)
     | Silent op' \<Rightarrow> csingle (Silent (exchange_op worker pact op'))
     ) ((choices op))))"
  apply (subst exchange_op.code)
  apply (unfold cimage_cUn op.inject)
   apply (auto simp add: cset.map_comp o_def cimage_cUn intro!: arg_cong2[where f = cUn] cimage_cong
      split: exchange_op_aux.splits op.splits option.splits)
  subgoal for p f
    unfolding image_def
    by fastforce
  subgoal for p f
    unfolding image_def
    by fastforce
  subgoal for op p x
    unfolding image_def
    by fastforce
  subgoal for op
    unfolding image_def
    by fastforce
  done
*)

datatype ('id, 'p, 's, 'd, 't, 'w :: enum) dataflow_dis_tree = 
  "apply": Logic_Dis "('p option, 'p option, 's + 'd) op" "'p \<Rightarrow> 'p \<Rightarrow> 't list" "'w \<Rightarrow> 'p \<Rightarrow> ('s + 'd) \<Rightarrow> 'w"
  | Comp_Dis "'id \<times> 'p \<Rightarrow> ('id \<times> 'p) option" "('id, 'p, 's, 'd, 't, 'w) dataflow_dis_tree" "('id, 'p, 's, 'd, 't, 'w) dataflow_dis_tree"

fun dataflow_dis_tree_to_operator_aux :: "'w :: enum \<Rightarrow> 'a :: {plus, one, minus} \<Rightarrow> ('a \<times> 'b \<Rightarrow> ('c \<times> 'd) buf)
         \<Rightarrow> ('a, 'b, 'e, 'c \<times> 'd, 'f, 'w) dataflow_dis_tree
            \<Rightarrow> 'a \<times> ('a \<times> 'b \<Rightarrow> ('a \<times> 'b) option) \<times>
               ('a + ('a \<times> 'b + 'a \<times> 'b), 'a + 'a \<times> 'b \<times> 'w,
                'e + 'c \<times> 'd) op" where
  "dataflow_dis_tree_to_operator_aux w n chns (Logic_Dis op su pact) = (n + 1, (\<lambda> _. None), 
    map_op (case_option (Inl n) (case_sum (\<lambda> p. Inr (Inl (n, p))) (\<lambda> p. Inr (Inr (n, p))))) (case_option (Inl n) (\<lambda> p. Inr (n, p))) (exchange_op w pact op))"
| "dataflow_dis_tree_to_operator_aux w n chns (Comp_Dis wire dt1 dt2) = (
    let (n', f, op1) = dataflow_dis_tree_to_operator_aux w n chns dt1 in
    let (n'', f', op2) = dataflow_dis_tree_to_operator_aux w n' chns dt2 in
    (n'', Map.map_add wire (Map.map_add f f'), map_op (case_sum id id) (case_sum id id) 
      (comp_op (case_sum (\<lambda> _. None) ((case_option None (Some o Inr o Inl)) o (\<lambda> (nid, p, w'). case (wire (nid - n, p), w = w') of (Some (offset, q), True) \<Rightarrow> Some (n' + offset, q) | _ \<Rightarrow> None)))
       ((\<lambda> p. case p of Inr (Inl x) \<Rightarrow> map (\<lambda> (d, t). Inr (d, t)) (chns x) | _ \<Rightarrow> [])) op1 op2)))"
definition "dataflow_dis_tree_to_operator w chns df = snd (dataflow_dis_tree_to_operator_aux w 0 chns df)"

fun combined_wire where
  "combined_wire (Logic_Dis _ _ _) = (\<lambda>_. None)"
| "combined_wire (Comp_Dis wire dt1 dt2) = Map.map_add wire (Map.map_add (combined_wire dt1) (combined_wire dt2))"

fun dataflow_dis_tree_to_graph_aux where
  "dataflow_dis_tree_to_graph_aux n (Logic_Dis op su pact) = (n + 1,
    (\<lambda> l1 l2. 
    if n = node l1 \<and> n = node l2 \<and> is_Trg (port l1) \<and> is_Src (port l2) 
    then antichain_from_list (su (idp (port l1)) (idp (port l2)))
    else antichain_from_list []))"
| "dataflow_dis_tree_to_graph_aux n (Comp_Dis wire dt1 dt2) = (
    let (n', summary1) = dataflow_dis_tree_to_graph_aux n dt1 in
    let (n'', summary2) = dataflow_dis_tree_to_graph_aux n' dt2 in
    (n'', \<lambda> l1 l2. 
     if node l1 \<ge> n \<and> node l1 < n' \<and> node l2 \<ge> n' \<and> is_Src (port l1) \<and> is_Trg (port l2)
     then (case wire (node l1 - n, idp (port l1)) of 
             None \<Rightarrow> frontier {#}\<^sub>z 
           | Some (offset, q) \<Rightarrow> (if node l2 = n' + offset \<and> q = idp (port l2) then antichain_from_list [0] else antichain_from_list [])) 
     else summary1 l1 l2 + summary2 l1 l2)
   )"

fun dis_nodes_count where
  "dis_nodes_count (Logic_Dis op su pact) = 1"
| "dis_nodes_count (Comp_Dis wire dt1 dt2) = dis_nodes_count dt1 + dis_nodes_count dt2"

definition "dataflow_dis_tree_to_graph (df :: ('id :: {minus,one,plus,zero,ord,enum,hashable}, _, _, _, _, 'w :: enum) dataflow_dis_tree) = (
  let (_, s) = dataflow_dis_tree_to_graph_aux 0 df in
  if \<not> has_zero_cyc s \<and>
     no_self_loop_checker s \<and>
     implementation_graph_checker (weights_to_graph_fun (remove_non_zero_weights s)) \<and>
     CARD ('id) = dis_nodes_count df
  then s
  else Code.abort (STR ''Control plane could not be build'') (\<lambda> _. (\<lambda> _ _. frontier {#}\<^sub>z)))"


record ('p, 't) exchange_conf_one =
  c_temp :: "('p \<times> 't \<times> int) buf"
  c_glob :: "('p \<times> 't \<times> int) buf"

definition extract_progress_caps where
  "extract_progress_caps nid edg st =
    map (\<lambda> (p, t, m). (Loc nid (Trg p), t, -m)) (cons st) @ 
    map (\<lambda> (p, t, m). (Loc nid (Src p), t, m)) (inte st)"

(* maybe the type of exch should be (('id, 'p) location \<times> 't) exchange_conf_one instead*)
corec dataflow_dis'_op :: "('id :: {enum, linorder}, 'p :: {enum, linorder}, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) subgraph 
  \<Rightarrow> (('id, 'p) location, 't) exchange_conf_one
   \<Rightarrow> ('id + ('e \<times> 'f + 'e \<times> 'f) option, 'id + ('g \<times> 'h \<times> 'w) option, (('p, 't) shared_state + ('p \<Rightarrow> 't antichain)) + ((('id, 'p) location \<times> 't \<times> int) buf + 'j)) op
      \<Rightarrow> (('e \<times> 'f + 'e \<times> 'f) option, ('g \<times> 'h \<times> 'w ) option, (('id, 'p) location \<times> 't \<times> int) buf + 'j) op" where
  "dataflow_dis'_op sg exch op = Choice (cimage (\<lambda> op. case op of 
     Read (Inl nid) f \<Rightarrow> (case propagate_all (summ sg) (pt_tr sg) of
         Some conf' \<Rightarrow> let sg' = sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr> in
         let imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) in Silent (dataflow_dis'_op sg' exch (f (Inl (Inr (frontier o imp_fron))))))

   | Read (Inr (Some p)) f \<Rightarrow> Read (Some p) (\<lambda> x. case x of Inr x' \<Rightarrow> dataflow_dis'_op sg exch (f (Inr (Inr x'))) | Inl _ \<Rightarrow> \<oslash>)
   | Write op' (Inr (Some (nid, p, w))) (Inr (Inr x)) \<Rightarrow> Write (dataflow_dis'_op sg exch op') (Some (nid, p, w)) (Inr x)
   | Silent op' \<Rightarrow> Silent (dataflow_dis'_op sg exch op')

   | Write op' (Inr None) (Inr (Inl x)) \<Rightarrow> Write (dataflow_dis'_op sg (exch\<lparr> c_temp := [] \<rparr>) op') None (Inl x)
   | Read (Inr None) f \<Rightarrow> Read None (\<lambda> x. case x of Inl x' \<Rightarrow> dataflow_dis'_op 
        (sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) x' (pt_tr sg) \<rparr>) 
        (exch\<lparr> c_glob := c_glob exch @ x' \<rparr>) (f (Inr x)) | Inr _ \<Rightarrow> \<oslash>)


   | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow> Silent (dataflow_dis'_op sg (exch\<lparr> c_temp := c_temp exch @ (extract_progress nid (edges sg) st) \<rparr>) op')
   | _ \<Rightarrow> Code.abort (STR ''Operator in dataflow_op breaks contract'') (\<lambda> _. \<oslash>)
) (let C = cUn (cfilter (nop sg) (choices op)) {| Read (Inr None) (\<lambda>_. op), Write op (Inr None) ((Inr o Inl) (c_temp exch)) |} in C))"

corec data_Inr_op :: "('ip, 'op, 'd1 + 'd3) op \<Rightarrow> ('ip, 'op, 'd1 + 'd2 + 'd3) op" where
  "data_Inr_op op = Choice (cimage (\<lambda> op. case op of
    Read p f \<Rightarrow> Read p (\<lambda> x. case x of Inl x' \<Rightarrow> data_Inr_op (f (Inl x')) | Inr (Inl x') \<Rightarrow> \<oslash> | Inr (Inr x') \<Rightarrow>  data_Inr_op (f (Inr x')))
  | Write op' p (Inr x) \<Rightarrow> Write (data_Inr_op op') p (Inr (Inr x))
  | Write op' p (Inl x) \<Rightarrow> Write (data_Inr_op op') p (Inl x)
  | Silent op' \<Rightarrow> Silent (data_Inr_op op')
) (choices op))"


definition dataflow_dis_op :: "('id :: {enum, linorder}, 'p :: {enum, linorder}, 't :: {ccompare,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le,bot}) subgraph 
  \<Rightarrow> (('id, 'p) location, 't) exchange_conf_one
   \<Rightarrow> ('id + 'e \<times> 'f + 'e \<times> 'f, 'id + 'g \<times> 'h \<times> 'w, (('p, 't) shared_state + ('p \<Rightarrow> 't antichain)) + 'j) op
      \<Rightarrow> (('e \<times> 'f + 'e \<times> 'f) option, ('g \<times> 'h \<times> 'w ) option, (('id, 'p) location \<times> 't \<times> int) buf + 'j) op" where
  "dataflow_dis_op sg exch op = dataflow_dis'_op sg exch (map_op (case_sum Inl (Inr o Some)) (case_sum Inl (Inr o Some)) (data_Inr_op op))"


corec data_Inl_op :: "('ip, 'op, 'd1 + 'd2 + 'd3) op \<Rightarrow> ('ip, 'op, 'd1 + 'd3) op" where
  "data_Inl_op op = Choice (cimage (\<lambda> op. case op of
    Read p f \<Rightarrow> Read p (\<lambda> x. case x of Inl x' => data_Inl_op (f (Inl x')) | Inr x' \<Rightarrow> data_Inl_op (f (Inr (Inr x'))))
  | Write op' p (Inl x) \<Rightarrow> Write (data_Inl_op op') p (Inl x)
  | Write op' p (Inr (Inr x)) \<Rightarrow> Write (data_Inl_op op') p (Inr x)
  | Write op' p (Inr (Inl x)) \<Rightarrow> \<oslash>
  | Silent op' \<Rightarrow> Silent (data_Inl_op op')
) (choices op))"

corec filter_op :: "('ip option, 'op option, 'd) op \<Rightarrow> ('ip, 'op, 'd) op" where
  "filter_op op = Choice (cimage (\<lambda> op. case op of
    Read (Some p) f \<Rightarrow> Read p (\<lambda> x. filter_op (f x))
  | Read None f \<Rightarrow> \<oslash>
  | Write op' (Some p) x \<Rightarrow> Write (filter_op op') p x
  | Write op' None x \<Rightarrow> \<oslash>
  | Silent op' \<Rightarrow> Silent (filter_op op')
) (choices op))"

definition data_inv :: "('id + 'ip option, 'id + 'op option, 'd1 + 'd2 + 'd3) op \<Rightarrow> ('id + 'ip, 'id + 'op, 'd1 + 'd3) op" where
  "data_inv op = filter_op (map_op (case_sum (Some o Inl) (case_option None (Some o Inr))) (case_sum (Some o Inl) (case_option None (Some o Inr))) (data_Inl_op op))"

lemma data_Inr_op_elim: "step io (data_Inr_op op) op' \<Longrightarrow> (\<exists> io' op''. step io' op op'' \<and> io = map_IO id id (case_sum Inl (Inr o Inr)) io' \<and> op' = data_Inr_op op'') \<or> (\<exists> p f x. op = Read p f \<and> io = Inp p (Inr (Inl x)) \<and> op' = \<oslash>) \<or>
  (\<exists> ops op'' op''' p f x. op = Choice ops \<and> op''' \<in> rcset ops \<and> Read p f \<in> rcset (choices op''') \<and> op'' = Read p f \<and> io = Inp p (Inr (Inl x)) \<and> op' = \<oslash>)"
  apply(subst (asm) data_Inr_op.code)
  apply auto
    subgoal for op''
      apply(cases op; simp)
      subgoal for p f
        apply(auto simp add: comp_def split: sum.splits)
        by force+
      subgoal for op''' q x
        apply(auto split: sum.splits)
        by force+
      subgoal for ops
        apply safe
        subgoal for op''''
          apply(cases op''; auto split: sum.splits)
          by force+
        done
      subgoal for op'''
        by force
      done
    done


lemma dataflow_dis'_op_code[code]:
  "dataflow_dis'_op sg exch op = Choice (cimage (\<lambda> op. case op of 
     Read (Inl nid) f \<Rightarrow> trace (STR ''Reading from frontier at nid: '' + print_2 nid) (case propagate_all (summ sg) (pt_tr sg) of
         Some conf' \<Rightarrow> let sg' = sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr> in
         let imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p))) in Silent (dataflow_dis'_op sg' exch (f (Inl (Inr (frontier o imp_fron))))))
   | Read (Inr (Some p)) f \<Rightarrow> Read (Some p) (\<lambda> x. case x of Inr x' \<Rightarrow> dataflow_dis'_op sg exch (f (Inr (Inr x'))) | Inl _ \<Rightarrow> \<oslash>)
   | Write op' (Inr (Some (nid, p, w))) (Inr (Inr x)) \<Rightarrow> trace (STR ''Writing out data at location: '' + show_loc (Loc nid (Src p))) (Write (dataflow_dis'_op sg exch op') (Some (nid, p, w)) (Inr x))     
   | Silent op' \<Rightarrow> trace (STR ''Some silent step'') Silent (dataflow_dis'_op sg exch op')
   | Write op' (Inr None) (Inr (Inl x)) \<Rightarrow> Write (dataflow_dis'_op sg (exch\<lparr> c_temp := [] \<rparr>) op') None (Inl x)
   | Read (Inr None) f \<Rightarrow> Read None (\<lambda> x. case x of Inl x' \<Rightarrow> dataflow_dis'_op 
        (sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) x' (pt_tr sg) \<rparr>) 
        (exch\<lparr> c_glob := c_glob exch @ x' \<rparr>) (f (Inr x)) | Inr _ \<Rightarrow> \<oslash>)
   | Write op' (Inl nid) (Inl (Inl st)) \<Rightarrow>
      trace (STR ''Reading progress at nid: '' + print_2 nid + STR '' cgs sizes: ('' + show_nat (length (cons st)) + STR '', '' + show_nat (length (inte st))  + STR '', '' + show_nat (length (prod st)) + STR '')''
   ) (Silent (dataflow_dis'_op sg (exch\<lparr> c_temp := c_temp exch @ (extract_progress nid (edges sg) st) \<rparr>) op'))
   | _ \<Rightarrow> Code.abort (STR ''Operator in dataflow_op breaks contract'') (\<lambda> _. \<oslash>)
) (let C = cUn (cfilter (nop sg) (choices op)) {| Read (Inr None) (\<lambda>_. op), Write op (Inr None) ((Inr o Inl) (c_temp exch)) |} in C))"
  apply (simp only: trace_simp id_def)
  apply (subst dataflow_dis'_op.code[symmetric])
  by simp

lemma step_dataflow_dis'_op_elim:
  assumes "step io (dataflow_dis'_op sg exch op) op'"
  obtains
    nid p op'' x where "io = Inp (Some (Inr (nid, p))) (Inr x)" "op' = dataflow_dis'_op sg exch op''" "step (Inp (Inr (Some (Inr (nid, p)))) (Inr (Inr x))) op op''"
  | nid p op'' x where "io = Inp (Some (Inl (nid, p))) (Inr x)" "op' = dataflow_dis'_op sg exch op''" "step (Inp (Inr (Some (Inl (nid, p)))) (Inr (Inr x))) op op''"
  | nid p x where "io = Inp (Some (Inr (nid, p))) (Inl x)" "op' = \<oslash>"
  | nid p x where "io = Inp (Some (Inl (nid, p))) (Inl x)" "op' = \<oslash>"
  | nid p w op'' x where "io = Out (Some (nid, p, w)) (Inr x)" "op' = dataflow_dis'_op sg exch op''" "step (Out (Inr (Some (nid, p, w))) (Inr (Inr x))) op op''"
  | op'' where "io = Tau" "op' = dataflow_dis'_op sg exch op''" "step Tau op op''"
  | nid op'' imp_fron sg' where "io = Tau" "sg' = (case propagate_all (summ sg) (pt_tr sg) of Some conf' \<Rightarrow> sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr>)" "upfro sg nid"
    "imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p)))" "op' = dataflow_dis'_op sg' exch op''" "step (Inp (Inl nid) (Inl (Inr (frontier o imp_fron)))) op op''"
  | nid op'' st where "io = Tau" "op' = dataflow_dis'_op sg (exch\<lparr> c_temp := c_temp exch @ (extract_progress nid (edges sg) st) \<rparr>) op''" "step (Out (Inl nid) (Inl (Inl st))) op op''"
  | x where "io = Out None (Inl x)" "op' = dataflow_dis'_op sg (exch\<lparr> c_temp := [] \<rparr>) op"
  | x where "io = Inp None (Inl x)" "op' = dataflow_dis'_op (sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) x (pt_tr sg) \<rparr>) (exch\<lparr> c_glob := c_glob exch @ x \<rparr>) op"
  | x where "io = Inp None (Inr x)" "op' = \<oslash>"
  | x op'' where "step (Inp (Inr None) x) op op''"
  | x op'' where "step (Out (Inr None) x) op op''"
  using assms apply -
  apply atomize_elim
  apply (subst (asm) dataflow_dis'_op.code)
  apply (simp split: if_splits)
  apply (elim stepChoiceE)
  subgoal for op'
    apply(simp add: image_def comp_def)
    apply(subst (asm) step.simps)
    apply(erule disjE)
    subgoal
      apply((erule conjE exE disjE)+; simp)
      by(auto split: sum.splits)
    apply(erule disjE[of "op' = Write (dataflow_dis'_op sg (exch\<lparr>c_temp := []\<rparr>) op) None (Inl (c_temp exch))"])
    subgoal
      by((erule conjE exE disjE)+; simp)
    apply(erule conjE exE)+
    subgoal for x
      apply(cases x)
      subgoal for p f
        apply(cases p)
        subgoal for p'
          apply((erule disjE exE conjE)+; cases "propagate_all (summ sg) (pt_tr sg)"; simp add: cin.rep_eq[symmetric] comp_def del: cin.rep_eq)
          apply(drule Read_in_choices_step)
          by fast
        subgoal for p'
          apply(cases p')
          subgoal
            apply((erule disjE exE conjE)+; simp add: cin.rep_eq[symmetric] comp_def del: cin.rep_eq)
            apply(drule Read_in_choices_step)
            by fast
          subgoal for x'
            apply((erule disjE exE conjE)+; simp add: cin.rep_eq[symmetric] comp_def del: cin.rep_eq)
            subgoal for q x''
            apply(cases x'; cases x'')
            subgoal for a aa
              by(cases a; drule Read_in_choices_step; simp)
            subgoal for a aa
              apply(cases a; drule Read_in_choices_step; simp)
              by fast
            subgoal for a aa
              by(cases a; drule Read_in_choices_step; simp)
            subgoal for a aa
              apply(cases a; drule Read_in_choices_step; simp)
              by fast
            done
          done
        done
      done
    subgoal for op q x'
      apply(cases q)
      subgoal for q'
        apply((erule disjE exE conjE)+; cases x'; simp add: cin.rep_eq[symmetric] comp_def del: cin.rep_eq)
        subgoal for p x'' f x'''
          by(cases x'''; simp)
        subgoal for x''
          apply(cases x''; simp add: cin.rep_eq[symmetric] del: cin.rep_eq)
          apply(drule Write_in_choices_step)
          by blast
        done
      subgoal for q'
        apply(cases q')
        subgoal
          apply((erule disjE exE conjE)+; cases x'; simp add: cin.rep_eq[symmetric] comp_def del: cin.rep_eq; drule Write_in_choices_step)
          by metis+
        subgoal for x''
          apply((erule disjE exE conjE)+; cases x'; simp add: cin.rep_eq[symmetric] comp_def del: cin.rep_eq; drule Write_in_choices_step)
          subgoal for p x'' f x'''
            by(cases x'''; simp)
          subgoal for x'''
            apply(cases x''; cases x'''; simp add: cin.rep_eq[symmetric] del: cin.rep_eq)
            by blast
          done
        done
      done
    subgoal
      by force
    subgoal for op
      apply((erule disjE exE conjE)+; simp add: cin.rep_eq[symmetric] comp_def del: cin.rep_eq; drule Silent_in_choices_step)
      by fast
    done
  done
  done

lemma map_IO_elim :
  "map_IO f1 g1 h1 io1 = Inp p1 x1 \<Longrightarrow> (\<exists> p' x'. io1 = Inp p' x' \<and> f1 p' = p1 \<and> h1 x' = x1)"
  "map_IO f2 g2 h2 io2 = Out p2 x2 \<Longrightarrow> (\<exists> p' x'. io2 = Out p' x' \<and> g2 p' = p2 \<and> h2 x' = x2)"
  "map_IO f3 g3 h3 io3 = Tau \<Longrightarrow> io3 = Tau"
  apply(cases io1; simp)
  apply(cases io2; simp)
  apply(cases io3; simp)
  done

lemma step_dataflow_dis_op_elim:
  assumes "step io (dataflow_dis_op sg exch op) op'"
  obtains
    nid p op'' x where "io = Inp (Some (Inr (nid, p))) (Inr x)" "op' = dataflow_dis_op sg exch op''" "step (Inp (Inr (Inr (nid, p))) (Inr x)) op op''"
  | nid p op'' x where "io = Inp (Some (Inl (nid, p))) (Inr x)" "op' = dataflow_dis_op sg exch op''" "step (Inp (Inr (Inl (nid, p))) (Inr x)) op op''"
  | nid p op'' x where "io = Inp (Some (Inr (nid, p))) (Inl x)" "op' = \<oslash>"
  | nid p op'' x where "io = Inp (Some (Inl (nid, p))) (Inl x)" "op' = \<oslash>"
  | nid p w op'' x where "io = Out (Some (nid, p, w)) (Inr x)" "op' = dataflow_dis_op sg exch op''" "step (Out (Inr (nid, p, w)) (Inr x)) op op''"
  | op'' where "io = Tau" "op' = dataflow_dis_op sg exch op''" "step Tau op op''"
  | nid op'' imp_fron sg' where "io = Tau" "sg' = (case propagate_all (summ sg) (pt_tr sg) of Some conf' \<Rightarrow> sg\<lparr> pt_tr := conf', upfro := (upfro sg)(nid := False) \<rparr>)" "upfro sg nid"
    "imp_fron = (\<lambda> p. c_imp (pt_tr sg') (Loc nid (Trg p)))" "op' = dataflow_dis_op sg' exch op''" "step (Inp (Inl nid) (Inl (Inr (frontier o imp_fron)))) op op''"
  | nid op'' st where "io = Tau" "op' = dataflow_dis_op sg (exch\<lparr> c_temp := c_temp exch @ (extract_progress nid (edges sg) st) \<rparr>) op''" "step (Out (Inl nid) (Inl (Inl st))) op op''"
  | x where "io = Out None (Inl x)" "op' = dataflow_dis_op sg (exch\<lparr> c_temp := [] \<rparr>) op"
  | x where "io = Inp None (Inl x)" "op' = dataflow_dis_op (sg\<lparr> upfro := (\<lambda> _. True), pt_tr := change_multiplicities (summ sg) x (pt_tr sg) \<rparr>) (exch\<lparr> c_glob := c_glob exch @ x \<rparr>) op"
  | x where "io = Inp None (Inr x)" "op' = \<oslash>"
  using assms apply -
  apply atomize_elim
  unfolding dataflow_dis_op_def
  apply(erule step_dataflow_dis'_op_elim; simp; drule step_map_op_inv)
  subgoal for nid p op'' x
    by(auto simp add: comp_def dest!: map_IO_elim data_Inr_op_elim sym[of _ "map_IO _ _ _ _"] split: IO.splits sum.splits)
  subgoal for nid p op'' x
    by(auto simp add: comp_def dest!: map_IO_elim data_Inr_op_elim sym[of _ "map_IO _ _ _ _"] split: IO.splits sum.splits)
  subgoal for nid p w op'' x
    by(auto simp add: comp_def dest!: map_IO_elim data_Inr_op_elim sym[of _ "map_IO _ _ _ _"] split: IO.splits sum.splits)
  subgoal for op''
    by(auto simp add: comp_def dest!: map_IO_elim data_Inr_op_elim sym[of _ "map_IO _ _ _ _"] split: IO.splits sum.splits)
  subgoal for nid op'' imp_fron sg'
    by(auto simp add: comp_def dest!: map_IO_elim data_Inr_op_elim sym[of _ "map_IO _ _ _ _"] split: IO.splits sum.splits)
  subgoal for nid op'' st
    by(auto simp add: comp_def dest!: map_IO_elim data_Inr_op_elim sym[of _ "map_IO _ _ _ _"] split: IO.splits sum.splits)
  subgoal for x op''
    apply(rule FalseE)
    by(auto simp add: comp_def dest!: map_IO_elim data_Inr_op_elim sym[of _ "map_IO _ _ _ _"] split: IO.splits sum.splits)
  subgoal for x op''
    apply(rule FalseE)
    by(auto simp add: comp_def dest!: map_IO_elim data_Inr_op_elim sym[of _ "map_IO _ _ _ _"] split: IO.splits sum.splits)
  done



(* 
The options are for the external progress messages (the write does not need 'w sinc the message is broadcasted.
In the paper (Verified progress tracking for TimelyDataflow) there the progress_messages need to, so can buf be a multiset
*)
record ('w :: enum, 'ip, 'op, 'd) conf =
  msg :: "'w \<Rightarrow> 'ip \<Rightarrow> 'd multiset"
  prog_msg :: "'w \<Rightarrow> 'w \<Rightarrow> 'd buf"
  ops :: "'w \<Rightarrow> (('ip + 'ip) option, ('op \<times> 'w) option, 'd) op"
  used_wire :: "'op \<rightharpoonup> 'ip"

inductive step_dis :: "'w :: enum \<Rightarrow> ('ip, 'op, 'd) IO \<Rightarrow> ('w, 'ip, 'op, 'd) conf \<Rightarrow> ('w, 'ip, 'op, 'd) conf \<Rightarrow> bool" where
  SDT: "step Tau (ops c w) op' \<Longrightarrow> c' = c\<lparr> ops := (ops c)(w := op') \<rparr> \<Longrightarrow> step_dis w Tau c c'"
| SDTR: "step (Inp (Some (Inr p)) x) (ops c w) op' \<Longrightarrow> c' = (c\<lparr> ops := (ops c)(w' := op'), msg := (msg c)(w := (msg c w)(p := msg c w p - {# x #}))\<rparr>) \<Longrightarrow> 
    \<exists>q. used_wire c q = Some p \<Longrightarrow> m \<in># msg c w p \<Longrightarrow> step_dis w Tau c c'"
| SDTW: "step (Out (Some (q, w')) x) (ops c w) op' \<Longrightarrow> c' = (c\<lparr> ops := (ops c)(w := op'), msg := (msg c)(w := (msg c w)(p := msg c w' p + {# x #}))\<rparr>) \<Longrightarrow> 
    used_wire c q = Some p \<Longrightarrow> w' \<noteq> w \<Longrightarrow> step_dis w Tau c c'"
| SDR: "step (Inp (Some p) x) (ops c w) op' \<Longrightarrow> c' = (c \<lparr> ops := (ops c)(w := op') \<rparr>) \<Longrightarrow> p = Inl p' \<or> p = Inr p' \<Longrightarrow> \<forall>q. used_wire c q \<noteq> Some p' \<Longrightarrow> step_dis w (Inp p' x) c c'"
| SDW: "step (Out (Some (q, w)) x) (ops c w) op' \<Longrightarrow> c' = (c \<lparr> ops := ((ops c)(w := op')) \<rparr>) \<Longrightarrow> used_wire c q = None \<Longrightarrow> step_dis w (Out q x) c c'"
| SDTUR: "step (Inp None (hd (prog_msg c w' w))) (ops c w) op' \<Longrightarrow> c' = (c \<lparr> ops := (ops c)(w := op'), prog_msg := (prog_msg c)(w' := (prog_msg c w')(w := tl (prog_msg c w' w))) \<rparr>) \<Longrightarrow> step_dis w Tau c c'"
| SDTUW: "step (Out None x) (ops c w) op' \<Longrightarrow> c' = (c \<lparr> ops := (ops c)(w := op'), prog_msg := (prog_msg c)(w := \<lambda> w'. prog_msg c w w' @ [x]) \<rparr>) \<Longrightarrow> step_dis w Tau c c'"

inductive step_dis' :: "('ip, 'op, 'd) IO \<Rightarrow> ('w :: enum, 'ip, 'op, 'd) conf \<Rightarrow> ('w, 'ip, 'op, 'd) conf \<Rightarrow> bool" where
  S: "step_dis w io c c' \<Longrightarrow> step_dis' io c c'"


definition sim_dis :: "(('ip, 'op, 'd) op \<Rightarrow> ('w :: enum, 'ip, 'op, 'd) conf \<Rightarrow> bool) \<Rightarrow> ('ip, 'op, 'd) op \<Rightarrow> ('w, 'ip, 'op, 'd) conf \<Rightarrow> bool" where
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

end