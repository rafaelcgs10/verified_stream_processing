theory Map_Op
  imports
    "../Watermarked_Stream"
    "../Llists_Processors"
    "../Sum_Order"
    "HOL-Library.Code_Lazy"
begin

section \<open>map_op\<close> 
primcorec map_op where
  "map_op f = Logic (\<lambda> ev. case ev of
                                Watermark wm \<Rightarrow> (map_op f, [Watermark wm])
                              | Data t d \<Rightarrow> (map_op f, [Data t (f t d)])) LNil"

subsection \<open>Correctness\<close> 
lemma produce_map_op_correctness:
  "produce (map_op f) = lmap (\<lambda> ev . case ev of Watermark wm \<Rightarrow> Watermark wm | Data t d \<Rightarrow> Data t (f t d))"
  apply (rule ext)
  subgoal for lxs
    apply (coinduction arbitrary: lxs rule: llist.coinduct)
    apply safe
    subgoal 
      apply (subst (asm) produce.code)
      apply (auto split: option.splits event.splits sum.splits)
       apply (subst (asm) (1) produce_inner.simps)
       apply (auto split: llist.splits event.splits)
      apply (subst (asm) (1) produce_inner.simps)
      apply (auto split: llist.splits event.splits)
      done
    subgoal 
      apply (subst (1) produce.code)
      apply (auto split: option.splits event.splits)
      apply (subst (asm) (1) produce_inner.simps)
      apply (auto split: llist.splits event.splits)
      done
    subgoal 
      apply (subst (1) produce.code)
      apply (auto split: option.splits event.splits)
        apply (subst (asm) (1) produce_inner.simps)
        apply (auto split: llist.splits event.splits)
       apply (subst (asm) (1) produce_inner.simps)
       apply (auto split: llist.splits event.splits)
      done
    subgoal for lxs
      apply (rule exI[of _ "ltl lxs"])
      apply auto
      apply (subst (1 2) produce.code)
      apply (auto split: option.splits)
       apply (subst (asm) (1 2) produce_inner.simps)
       apply (auto split: llist.splits event.splits)
      apply (subst produce.code)
      apply (subst produce_inner.simps)
      apply (auto split: llist.splits event.splits)
      apply (subst produce.code)
      apply (subst produce_inner.simps)
      apply (auto split: llist.splits event.splits)
      apply (subst (asm) (1 2) produce_inner.simps)
      apply (auto split: llist.splits event.splits)
      done
    done
  done

subsection \<open>Strict monotone\<close> 
lemma produce_map_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   produce (map_op f) stream_in = stream_out \<Longrightarrow>
   monotone stream_out WM"
  unfolding produce_map_op_correctness
  apply simp
  apply hypsubst_thin
  apply (coinduction arbitrary: WM f stream_in  rule: monotone.coinduct)
  apply (erule monotone.cases)
    apply auto
  done

subsection \<open>Productive\<close> 
lemma produce_map_op_strict_productive:
  "productive stream_in \<Longrightarrow>
   produce (map_op f) stream_in = stream_out \<Longrightarrow>
   productive stream_out"
  unfolding produce_map_op_correctness productive_alt
  apply simp
  apply hypsubst_thin
  apply (coinduction arbitrary: f stream_in rule: productive'.coinduct)
  apply (erule productive'.cases)
    apply force+
  done

lemma fst_finite_produce_map_op[simp]:
  "fst (finite_produce (map_op f) xs) = map_op f"
  unfolding finite_produce_def
  apply (induct xs arbitrary: )
   apply (auto split: event.splits)
   apply (metis fold_apply_old fst_eqD)+
  done

lemma snd_finite_produce_map_op[simp]:
  "snd (finite_produce (map_op f) xs) = map (\<lambda> ev . case ev of Watermark wm \<Rightarrow> Watermark wm | Data t d \<Rightarrow> Data t (f t d)) xs"
  apply (induct xs arbitrary: )
   apply (auto split: event.splits)
  done

lemma finite_produce_map_op_exit_LNil:
  "finite_produce (map_op f) xs = (op', out) \<Longrightarrow> exit op' = LNil"
  apply (induct xs arbitrary: op' out)
   apply auto
  apply (auto split: event.splits sum.splits if_splits list.splits prod.splits)
  done

end