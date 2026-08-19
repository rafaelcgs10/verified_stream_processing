

theory Nop_Step_Lemmas

imports
  Dataflow_Op
begin

section ‹Self-Loop Lemmas for Nop Choices›

text ‹Toolbox for the weak bisimulation between @{const dataflow_op} and its
pruned variant. The pruned choices are (a) frontier reads with a stale
@{const upfro} flag and (b) progress writes without progress. The lemmas
below show that these choices are self-loops: they change nothing except
the @{const upfro} bookkeeping field of the subgraph record.›

subsection ‹Empty progress states›

lemma not_has_progress_empty[simp]:
  "¬ has_progress ⦇ cons = [], inte = [], prod = [] ⦈"
  unfolding has_progress_def by simp

lemma obtain_progress_empty:
  assumes "consu os = []" and "inter os = []" and "produ os = []"
  shows "obtain_progress os = (os, ⦇ cons = [], inte = [], prod = [] ⦈)"
proof -
  have "os⦇ consu := [], inter := [], produ := [] ⦈ =
        os⦇ consu := consu os, inter := inter os, produ := produ os ⦈"
    using assms by simp
  then show ?thesis using assms unfolding obtain_progress_def by simp
qed

subsection ‹Extracted progress and multiplicity changes of empty batches›

lemma extract_progress_empty[simp]:
  "cons st = [] ⟹ inte st = [] ⟹ prod st = [] ⟹ extract_progress nid nt st = []"
  unfolding extract_progress_def by simp

lemma extract_progress_no_progress[simp]:
  "¬ has_progress st ⟹ extract_progress nid nt st = []"
  unfolding has_progress_def by simp

lemma change_multiplicities_Nil[simp]:
  "change_multiplicities summary [] conf = conf"
  unfolding change_multiplicities_def by simp

lemma change_multiplicities_no_progress[simp]:
  "¬ has_progress st ⟹
   change_multiplicities summary (extract_progress nid nt st) conf = conf"
  by simp

subsection ‹Subgraph record identities›

lemma subgraph_progress_write_nop:
  "¬ has_progress st ⟹
   sg⦇ upfro := u, pt_tr := change_multiplicities (summ sg) (extract_progress nid (nxt sg) st) (pt_tr sg) ⦈ =
   sg⦇ upfro := u ⦈"
  by simp

lemma subgraph_frontier_read_nop:
  assumes "¬ upfro sg nid" and "conf' = pt_tr sg"
  shows "sg⦇ pt_tr := conf', upfro := (upfro sg)(nid := False) ⦈ = sg"
proof -
  have "(upfro sg)(nid := False) = upfro sg"
    using assms(1) by (simp add: fun_upd_idem)
  then have "sg⦇ pt_tr := conf', upfro := (upfro sg)(nid := False) ⦈ =
             sg⦇ pt_tr := pt_tr sg, upfro := upfro sg ⦈"
    using assms(2) by simp
  then show ?thesis by simp
qed

subsection ‹Builder self-loops›

lemma builder_op_frontier_read_self_loop:
  "front os = v ⟹ initia os ⟹
   builder_op fb tps sps (os⦇ front := v, initia := True ⦈) logic = builder_op fb tps sps os logic"
  by simp

lemma builder_op_progress_write_self_loop:
  "consu os = [] ⟹ inter os = [] ⟹ produ os = [] ⟹
   (let (os', st) = obtain_progress os in Write (builder_op fb tps sps os' logic) None (Inl (Inl st))) =
   Write (builder_op fb tps sps os logic) None (Inl (Inl ⦇ cons = [], inte = [], prod = [] ⦈))"
  by (simp add: obtain_progress_empty)

subsection ‹Lifting self-loops through composition and mapping›

lemma comp_op_self_loop_right:
  "f v = op2 ⟹ comp_op wire buf op1 (f v) = comp_op wire buf op1 op2"
  by simp

lemma comp_op_self_loop_left:
  "f v = op1 ⟹ comp_op wire buf (f v) op2 = comp_op wire buf op1 op2"
  by simp

lemma comp_op_write_self_loop_right:
  "op2' = op2 ⟹ comp_op wire buf op1 op2' = comp_op wire buf op1 op2"
  by simp

lemma comp_op_write_self_loop_left:
  "op1' = op1 ⟹ comp_op wire buf op1' op2 = comp_op wire buf op1 op2"
  by simp

lemma map_op_self_loop:
  "f v = op ⟹ map_op g h (f v) = map_op g h op"
  by simp

lemma dataflow_op_self_loop:
  "f v = op ⟹ dataflow_op sg (f v) = dataflow_op sg op"
  by simp

end
