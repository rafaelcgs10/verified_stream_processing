theory Branch_op

imports
  Dataplane.Timely_Infrastructure
begin

definition \<open>branch_op ip p1 p2 p c os = builder_op False {|ip|} {|p1, p2|} os (\<lambda> os. {|
      let result = input os ip in
      let os = produces os (map (\<lambda> (d, t). (d, Cap t (if c d then p1 else p2))) result) in
      let os = drop_caps os (map (\<lambda> t. Cap t p1) (ocaps os p1) @ map (\<lambda> t. Cap t p2) (ocaps os p2) ) in
      os\<lparr> input := (\<lambda> p. []) \<rparr>
    |}
   )\<close>

end