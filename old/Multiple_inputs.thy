theory Multiple_inputs
  imports
    "Watermarked_Stream"
    "Sum_Order"
begin

codatatype ('o, 'i) op = Logic ("apply": "('i \<Rightarrow> ('o, 'i) op \<times> 'o list)") ("exit": "'o llist")


partial_function (option) produce_inner :: "('a, 'b) op \<times> 'b llist \<Rightarrow> (('a, 'b) op \<times> 'a \<times> 'a list \<times> 'b llist) option option" where
  "produce_inner op_lxs = (case op_lxs of (op, lxs) \<Rightarrow>
    (case lxs of 
        LNil \<Rightarrow> Some None
     | LCons h lxs' \<Rightarrow> (case apply op h of 
                         (lgc', []) \<Rightarrow> produce_inner (lgc', lxs')
                       | (lgc', x#xs) \<Rightarrow> Some (Some (lgc', x, xs, lxs')))))"

corec produce where
  "produce op lxs = 
    (case produce_inner (op, lxs) of
       None \<Rightarrow> LNil
    | Some None \<Rightarrow> exit op
    | Some (Some (lgc', x, xs, lxs')) \<Rightarrow> LCons x (xs @@- produce lgc' lxs'))"

lemma produce_inner_alt:
  assumes "produce_inner op_lxs = Some (Some y)"
  and "\<And>op h lxs' lgc' zs. apply op h = (lgc', []) \<Longrightarrow> Q (lgc', lxs') zs \<Longrightarrow> Q (op, LCons h lxs') zs"
  and "\<And>op h x xs lxs' lgc' . apply op h = (lgc', x # xs) \<Longrightarrow> Q (op, LCons h lxs') (Some (lgc', x, xs, lxs'))"
  and  "\<And>op. Q (op, LNil) None"
  shows "Q op_lxs (Some y)"
  apply (rule produce_inner.raw_induct[OF _ assms(1)])
  apply (auto elim: assms(2,3) split: llist.splits prod.splits list.splits)[1]
  using assms(4) apply blast
  done


primcorec connect where
  "connect lxs = Logic (\<lambda> ev1.
                       case lxs of
                         LNil \<Rightarrow> (connect lxs, [Inr ev1])
                       | LCons ev2 lxs' \<Rightarrow> (connect lxs', [Inr ev1, Inl ev2]))
                 (lmap Inl lxs)"

context fixes join_tuple :: "'tuple \<Rightarrow> 'tuple \<Rightarrow> 'tuple option" begin

primcorec join_op where
  "join_op S W = Logic (\<lambda> ev. case ev of
      Data tt d \<Rightarrow>
        let t = (case tt of Inl x \<Rightarrow> x | Inr x \<Rightarrow> x) in
        let out = List.map_filter (map_option (Data t) o join_tuple d) (S tt)
        in (join_op (if tt \<in> W then S else S(tt := d # S tt)) W, out)
    | Watermark tt \<Rightarrow>
        let t = (case tt of Inl x \<Rightarrow> x | Inr x \<Rightarrow> x) in
        let tt' = (case tt of Inl x \<Rightarrow> Inr x | Inr x \<Rightarrow> Inl x)
        in if tt \<in> W then (join_op (S(tt' := [])) (W - {tt}), [Watermark t])
        else (join_op (S(tt' := [])) (W \<union> {tt}), [])) LNil"

end

primcorec join where
  "join lxs = Logic (\<lambda> ev1.
                       case lxs of
                         LNil \<Rightarrow> (connect lxs, [Inr ev1])
                       | LCons ev2 lxs' \<Rightarrow> (connect lxs', [Inr ev1, Inl ev2]))
                 (lmap Inl lxs)"


primcorec connect_event where
  "connect_event lxs buf = Logic (\<lambda> ev1.
                       case lxs of
                         LNil \<Rightarrow> (connect_event lxs, [Inr ev1])
                       | LCons ev2 lxs' \<Rightarrow> (connect_event lxs', [Inr ev1, Inl ev2]))
                 (lmap Inl lxs)"

primcorec linterleave where
  "linterleave xs ys = (
    case xs of
      LNil \<Rightarrow> ys
    | LCons x xs \<Rightarrow> LCons x (linterleave ys xs) 
  )"


(*
- interleave/connect
- co_flat_map
- join with timestamp parameter
*)

primcorec interleave where
  "interleave lxs = Logic (\<lambda> ev1.
                    case lxs of
                      LNil \<Rightarrow> (interleave lxs, Inl ev1)
                    | LCons ev2 lxs' \<Rightarrow> undefined))"

primcorec multiple_inputs where
  "multiple_inputs op n lxs = Logic (\<lambda> ev.
                             case lxs of
                               LNil \<Rightarrow> undefined
                             | Some (lgc', x, xs, lxs') \<Rightarrow> (multiple_inputs lgc' (ev#buf) lxs', x#xs))"



(* Ideal join: *)
primcorec join where
  "join f buf ev1 = Logic (\<lambda> ev2.
                   let (lgc1', out) = apply lgc1 ev in
                   (round_robin lgc2 lgc1', out))"


end