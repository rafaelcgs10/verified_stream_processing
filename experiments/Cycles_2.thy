theory Cycles_2

imports "../Llists_Processors"

begin

definition lpartition_sum::"('a + 'b) llist \<Rightarrow> ('a llist \<times> 'b llist)" where
  "lpartition_sum lxs = (lmap projl (lfilter isl lxs), lmap projr (lfilter (Not o isl) lxs))"
definition partition_sum::"('a + 'b) list \<Rightarrow> ('a list \<times> 'b list)" where
  "partition_sum xs = (map projl (filter isl xs), map projr (filter (Not o isl) xs))"

(*
definition "schedule xs lxs = map Inl xs @@- lxs"
*)
definition "prioritize_loop xs lxs = map Inl xs @@- lxs"
primrec alternate where
  "alternate [] lxs = lxs"
| "alternate (x # xs) lxs = (case lxs of LNil \<Rightarrow> llist_of (Inl x # map Inl xs)
   | LCons y lys \<Rightarrow> LCons y (LCons (Inl x) (alternate xs lys)))"

partial_function (option) produce_inner_cycle where
  "produce_inner_cycle schedule op_lxs = (case op_lxs of (op, lxs) \<Rightarrow>
    (case lxs of
        LNil \<Rightarrow> Some (Inr op)
     | LCons h lxs' \<Rightarrow> (let (op', out) = apply op h in
                        let (loop, out') = partition_sum out in
                        case out' of
                         [] \<Rightarrow> produce_inner_cycle schedule (op', schedule loop lxs')
                       | x#xs \<Rightarrow> Some (Inl (op', x, xs, schedule loop lxs')))))"
corec produce_cycle_aux where
  "produce_cycle_aux schedule op lxs =
    (case produce_inner_cycle schedule (op, lxs) of
      None \<Rightarrow> LNil
    | Some (Inr op') \<Rightarrow> snd (lpartition_sum (exit op')) \<comment> \<open>need to think about what to do with the Inl in the exit\<close>
    | Some (Inl (op', x, xs, lxs')) \<Rightarrow> LCons x (xs @@- produce_cycle_aux schedule op' lxs'))"
definition "produce_cycle schedule op = produce_cycle_aux schedule op o lmap Inr"

primcorec left_op :: "('a, 'a') op \<Rightarrow> ('a + 'b, 'a' + 'b) op" where
  "left_op op = Logic (\<lambda>ev. case ev of
       Inl a \<Rightarrow> let (op', out) = apply op a in (left_op op', map Inl out)
     | Inr b \<Rightarrow> (left_op op, [Inr b]))
     (lmap Inl (exit op))"
primcorec right_op :: "('b, 'b') op \<Rightarrow> ('a + 'b, 'a + 'b') op" where
  "right_op op = Logic (\<lambda>ev. case ev of
       Inl a \<Rightarrow> (right_op op, [Inl a])
     | Inr b \<Rightarrow> let (op', out) = apply op b in (right_op op', map Inr out))
     (lmap Inr (exit op))"
primcorec dup_op :: "('a, 'b) op \<Rightarrow> ('a + 'a, 'b) op" where
  "dup_op op = Logic (\<lambda>ev. case ev of
       Inl a \<Rightarrow> let (op', out) = apply op a in (dup_op op', out)
     | Inr b \<Rightarrow> let (op', out) = apply op b in (dup_op op', out))
     (exit op)"

(*left input*)
definition "compose_li_op op1 op2 = compose_op (left_op op1) op2"
(*right input*)
definition "compose_ri_op op1 op2 = compose_op (right_op op1) op2"
(*left output*)
definition "compose_lo_op op1 op2 = compose_op op1 (left_op op2)"
(*right output*)
definition "compose_ro_op op1 op2 = compose_op op1 (right_op op2)"

primcorec collatz_core_op :: "(nat \<times> nat \<times> nat, nat \<times> nat \<times> nat + nat \<times> nat) op" where
  "collatz_core_op = Logic (\<lambda>(a, b, i).
    if b = 1 then (collatz_core_op, [Inr (a, i)]) else (collatz_core_op, [Inl (a, b, i)]))
    LNil"
primcorec collatz_step_op :: "(nat \<times> nat \<times> nat, nat \<times> nat \<times> nat) op" where
  "collatz_step_op = Logic (\<lambda>(a, b, i).
    (collatz_step_op, [(a, if b mod 2 = 0 then b div 2 else 3 * b + 1, i+1)]))
    LNil"
primcorec collatz_init_op :: "(nat, nat \<times> nat \<times> nat) op" where
  "collatz_init_op = Logic (\<lambda>a. (collatz_init_op, [(a, a, 0)])) LNil"

definition collatz where
  "collatz = compose_lo_op (compose_ri_op collatz_init_op (dup_op collatz_core_op)) collatz_step_op"

declare produce_inner_cycle.simps[code]
value "list_of (produce_cycle prioritize_loop collatz (llist_of [1 ..< 100]))"
value "list_of (produce_cycle alternate collatz (llist_of [1 ..< 100]))"
value "set (list_of (produce_cycle prioritize_loop collatz (llist_of [1 ..< 100]))) =
       set (list_of (produce_cycle alternate collatz (llist_of [1 ..< 100])))"
