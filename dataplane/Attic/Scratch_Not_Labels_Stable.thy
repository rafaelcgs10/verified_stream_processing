theory Scratch_Not_Labels_Stable
  imports Label_Propagation_op
begin

lemma min_label_le_label: "min_label os t v ≤ label os t v"
  unfolding min_label_def by (intro Min_le) auto

lemma not_labels_stable_label_record_updateD:
  fixes t1 t' :: "'t::{order,plus}"
  assumes unstable: "¬ labels_stable (all_edges os' t')
      (min_label (label_prop_label_record_update os' t1 v new_l) t')"
    and ts_eq: "timestamps os' = timestamps os"
    and graph_eq: "graph os' = graph os"
    and vertices_eq: "vertices os' = vertices os"
    and label_eq: "label os' = label os"
    and t'_ts: "t' ∈ set (timestamps os)"
    and dec: "new_l ≤ label os t1 v"
    and sym_graph: "⋀s. sym {(a, b). b ∈ set (graph os s a)}"
  shows "¬ labels_stable (all_edges os t') (min_label os t') ∨
    (∃x ∈ set (neighbors os t' v).
       (en1 os (x, new_l), Cap (MyPair t' (mysnd et)) 1)
         ∈ set (label_prop_label_batch os (label_prop_label_record_update os' t1 v new_l) t1 v new_l et))"
proof (cases "labels_stable (all_edges os t') (min_label os t')")
  case False
  then show ?thesis by blast
next
  case True
  let ?upd = "label_prop_label_record_update os' t1 v new_l"
  let ?E = "all_edges os t'"
  define A where "A = {s ∈ set (timestamps os). s ≤ t'}"
  have finA: "finite A"
    unfolding A_def by simp
  have lab_u: "label ?upd = (label os)(t1 := (label os t1)(v := new_l))"
    using label_eq by (simp add: label_prop_label_record_update_def)
  have ts_u: "timestamps ?upd = timestamps os"
    using ts_eq by (simp add: label_prop_label_record_update_def)
  have all_vertices_eq: "all_vertices os' t' = all_vertices os t'"
    unfolding all_vertices_def using ts_eq vertices_eq by simp
  have neighbors_eq: "⋀w. set (neighbors os' t' w) = set (neighbors os t' w)"
    unfolding set_neighbors using ts_eq graph_eq by simp
  have all_edges_eq: "all_edges os' t' = all_edges os t'"
    unfolding all_edges_def using all_vertices_eq neighbors_eq by auto
  have minl: "min_label os t' w = Min (insert (label os t' w) ((λs. label os s w) ` A))" for w
    by (simp add: min_label_def A_def)
  have minl_u: "min_label ?upd t' w = Min (insert (label ?upd t' w) ((λs. label ?upd s w) ` A))" for w
    by (simp add: min_label_def A_def ts_u ts_eq)
  have upd_other: "min_label ?upd t' w = min_label os t' w" if wv: "w ≠ v" for w
  proof -
    have "label ?upd s w = label os s w" for s
      using wv by (simp add: lab_u)
    then show ?thesis
      by (simp add: minl minl_u)
  qed
  have upd_v_le: "min_label ?upd t' v ≤ min_label os t' v"
  proof -
    have "Min (insert (label os t' v) ((λs. label os s v) ` A)) ∈ insert (label os t' v) ((λs. label os s v) ` A)"
      by (intro Min_in) (use finA in auto)
    then consider "Min (insert (label os t' v) ((λs. label os s v) ` A)) = label os t' v"
      | s where "s ∈ A" "Min (insert (label os t' v) ((λs. label os s v) ` A)) = label os s v"
      by blast
    then show ?thesis
    proof cases
      case 1
      have "min_label ?upd t' v ≤ label ?upd t' v"
        unfolding minl_u by (intro Min_le) (use finA in auto)
      also have "label ?upd t' v ≤ label os t' v"
        using dec by (auto simp add: lab_u)
      finally show ?thesis
        using 1 minl by simp
    next
      case (2 s)
      have "min_label ?upd t' v ≤ label ?upd s v"
        unfolding minl_u by (intro Min_le) (use finA 2 in auto)
      also have "label ?upd s v ≤ label os s v"
        using dec by (auto simp add: lab_u)
      finally show ?thesis
        using 2 minl by simp
    qed
  qed
  have le_upd_v: "c ≤ min_label ?upd t' v" if c_new: "c ≤ new_l" and c_old: "c ≤ min_label os t' v" for c
  proof -
    have le_all: "c ≤ b" if b_in: "b ∈ insert (label ?upd t' v) ((λs. label ?upd s v) ` A)" for b
    proof -
      from b_in have "b = new_l ∨ b ∈ insert (label os t' v) ((λs. label os s v) ` A)"
        by (auto simp add: lab_u split: if_splits)
      then show ?thesis
      proof
        assume "b = new_l"
        then show ?thesis using c_new by simp
      next
        assume "b ∈ insert (label os t' v) ((λs. label os s v) ` A)"
        then have "min_label os t' v ≤ b"
          unfolding minl by (intro Min_le) (use finA in auto)
        then show ?thesis using c_old by simp
      qed
    qed
    show ?thesis
      unfolding minl_u
      by (auto simp add: finA intro: le_all)
  qed
  have upd_v_eq: "min_label ?upd t' v = min_label os t' v" if nle: "¬ t1 ≤ t'"
  proof -
    have t1A: "t1 ∉ A" and t1t': "t' ≠ t1"
      using nle unfolding A_def by auto
    have "(λs. label ?upd s v) ` A = (λs. label os s v) ` A"
      using t1A by (intro image_cong refl) (auto simp add: lab_u)
    moreover have "label ?upd t' v = label os t' v"
      using t1t' by (auto simp add: lab_u)
    ultimately show ?thesis
      by (simp add: minl minl_u)
  qed
  have nb_sym: "a ∈ set (neighbors os t' b)" if "b ∈ set (neighbors os t' a)" for a b
    using that sym_graph[unfolded sym_def] unfolding set_neighbors by fastforce
  have E_sym: "(b, a) ∈ ?E" if "(a, b) ∈ ?E" for a b
    using that nb_sym unfolding all_edges_def by auto
  from unstable obtain x y where edge: "(x, y) ∈ ?E ∪ ?E¯"
    and viol: "¬ min_label ?upd t' x ≤ min_label ?upd t' y"
    unfolding labels_stable_def all_edges_eq by blast
  have old_xy: "min_label os t' x ≤ min_label os t' y"
    using True edge unfolding labels_stable_def by blast
  have x_ne_y: "x ≠ y"
    using viol by auto
  have yv: "y = v"
  proof (rule ccontr)
    assume "y ≠ v"
    then have y_eq: "min_label ?upd t' y = min_label os t' y"
      by (rule upd_other)
    show False
    proof (cases "x = v")
      case True
      then have "min_label ?upd t' x ≤ min_label os t' x"
        using upd_v_le by simp
      then show False
        using old_xy y_eq viol by (metis order_trans)
    next
      case False
      then have "min_label ?upd t' x = min_label os t' x"
        by (rule upd_other)
      then show False
        using old_xy y_eq viol by simp
    qed
  qed
  have xv: "x ≠ v"
    using x_ne_y yv by simp
  have x_eq: "min_label ?upd t' x = min_label os t' x"
    by (rule upd_other[OF xv])
  have old_xv: "min_label os t' x ≤ min_label os t' v"
    using old_xy yv by simp
  have not_le_new: "¬ min_label os t' x ≤ new_l"
  proof
    assume "min_label os t' x ≤ new_l"
    then have "min_label os t' x ≤ min_label ?upd t' v"
      using le_upd_v old_xv by blast
    then show False
      using viol x_eq yv by simp
  qed
  have new_lt_x: "new_l < min_label os t' x"
    using not_le_new by (simp add: not_le)
  have t1_le: "t1 ≤ t'"
  proof (rule ccontr)
    assume "¬ t1 ≤ t'"
    then have "min_label ?upd t' v = min_label os t' v"
      by (rule upd_v_eq)
    then show False
      using viol x_eq yv old_xv by simp
  qed
  have new_lt_v: "new_l < min_label os t' v"
    using new_lt_x old_xv by (rule less_le_trans)
  have x_nb: "x ∈ set (neighbors os t' v)"
  proof -
    from edge yv have "(x, v) ∈ ?E ∨ (v, x) ∈ ?E"
      by auto
    then have "(v, x) ∈ ?E"
      using E_sym by blast
    then show ?thesis
      unfolding all_edges_def by auto
  qed
  have upd_x_gt: "new_l < min_label ?upd t' x"
    using new_lt_x x_eq by simp
  have "(en1 os (x, new_l), Cap (MyPair t' (mysnd et)) 1)
      ∈ set (label_prop_label_batch os ?upd t1 v new_l et)"
    unfolding label_prop_label_batch_def label_prop_neighbor_batch_def Let_def
    using t'_ts t1_le new_lt_v x_nb upd_x_gt by fastforce
  then show ?thesis
    using x_nb by blast
qed

lemma not_labels_stable_record_update_tlD:
  fixes t' :: "'t::{order,plus}"
  assumes unstable: "¬ labels_stable (all_edges (input_tl os_label_prop 1) t')
      (min_label (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v
        (min (min_label os_label_prop (myfst t) v) l)) t')"
    and t'_ts: "t' ∈ set (timestamps os_label_prop)"
    and inv: "label_prop_upd_inv os_label_prop"
  shows "¬ labels_stable (all_edges os_label_prop t') (min_label os_label_prop t') ∨
    (∃x ∈ set (neighbors os_label_prop t' v).
      (en1 os_label_prop (x, min (min_label os_label_prop (myfst t) v) l),
        Cap (MyPair t' (mysnd t)) 1)
        ∈ set (label_prop_label_batch os_label_prop
            (label_prop_label_record_update (input_tl os_label_prop 1) (myfst t) v
              (min (min_label os_label_prop (myfst t) v) l))
            (myfst t) v (min (min_label os_label_prop (myfst t) v) l) t))"
proof (rule not_labels_stable_label_record_updateD[OF unstable])
  show "timestamps (input_tl os_label_prop 1) = timestamps os_label_prop"
    by (simp add: input_tl_def)
  show "graph (input_tl os_label_prop 1) = graph os_label_prop"
    by (simp add: input_tl_def)
  show "vertices (input_tl os_label_prop 1) = vertices os_label_prop"
    by (simp add: input_tl_def)
  show "label (input_tl os_label_prop 1) = label os_label_prop"
    by (simp add: input_tl_def)
  show "t' ∈ set (timestamps os_label_prop)"
    by (rule t'_ts)
  show "min (min_label os_label_prop (myfst t) v) l ≤ label os_label_prop (myfst t) v"
    by (rule min.coboundedI1[OF min_label_le_label])
  show "⋀s. sym {(a, b). b ∈ set (graph os_label_prop s a)}"
    using inv unfolding label_prop_upd_inv_def by blast
qed

end
