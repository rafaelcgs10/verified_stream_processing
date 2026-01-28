theory Label_Propagation_op_Correctness

imports
  Label_Propagation_op
begin

(* TODO move *)
lemma num2_cases:
  fixes n :: 2 obtains (0) \<open>n = 0\<close> | (1) \<open>n = 1\<close>
proof (cases n)
  case (of_int z)
  then consider \<open>z = 0\<close> | \<open>z = 1\<close> by fastforce
  thus ?thesis using of_int(1) 0 1 by fastforce
qed

(* Issue: I would like to consider the input and increment operators with only 1 input port and 1
output port, however this is not possible here because the numeral type 2 for ports is the same for
all operators in the graph.  I cannot use map_op to solve this issue because the type parameter for
ports occurs inside the shared_state type, which occurs inside the type of data for the operators,
and this is a dead type parameter. *)

abbreviation cc_edges where
  \<open>cc_edges \<equiv> (\<lambda>l.
  if l = Loc (0 :: 3) (Src (0 :: 2)) then [Loc (1 :: 3) (Trg (0 :: 2))]
  else if l = Loc 1 (Src 1) then [Loc 2 (Trg 0)]
  else if l = Loc 2 (Src 0) then [Loc 1 (Trg 1)]
  else [])\<close>

(* Note: I omit some internal connections of the input and increment operators. *)
abbreviation cc_summary where
  \<open>cc_summary \<equiv> (\<lambda>l1 l2.
  if l1 = Loc (0 :: 3) (Trg (0 :: 2)) \<and> l2 = Loc (0 :: 3) (Src (0 :: 2))
  then antichain {0}
  else if l1 = Loc 0 (Src 0) \<and> l2 = Loc 1 (Trg 0)
  then antichain {0}
  else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 0)
  then antichain {0}
  else if l1 = Loc 1 (Trg 0) \<and> l2 = Loc 1 (Src 1)
  then antichain {0}
  else if l1 = Loc 1 (Trg 1) \<and> l2 = Loc 1 (Src 0)
  then antichain {0}
  else if l1 = Loc 1 (Trg 1) \<and> l2 = Loc 1 (Src 1)
  then antichain {0}
  else if l1 = Loc 1 (Src 1) \<and> l2 = Loc 2 (Trg 0)
  then antichain {0}
  else if l1 = Loc 2 (Trg 0) \<and> l2 = Loc 2 (Src 0)
  then antichain {MyPair 0 1}
  else if l1 = Loc 2 (Src 0) \<and> l2 = Loc 1 (Trg 1)
  then antichain {0}
  else {}\<^sub>A)\<close>

end