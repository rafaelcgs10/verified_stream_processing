theory Concat_Op

imports
  "../Timely/Builder_Op"
begin

definition \<open>concat_op ips p os = builder_op False ips {|p|} os (\<lambda> os. 
    if \<forall> p. ocaps os p = [] then {||} else
    {|
      let result = concat (map (\<lambda> p. input os p) [x <- Enum.enum. x |\<in>| ips]) in
      let os = produces os (map (\<lambda> (d, t). (d, Cap t p)) result) in
      let os = drop_caps os (concat (map (\<lambda> p. map (\<lambda> t. Cap t p) (ocaps os p)) Enum.enum)) in
      trace (STR ''concat_op!'')
      os\<lparr> input := (\<lambda> p. []) \<rparr>
    |}
   )\<close>

lemma nop_leaf_concat_op:
  "nop_leaf None (concat_op ips p os)"
  unfolding concat_op_def
  by (rule nop_leaf_builder_op) simp

end