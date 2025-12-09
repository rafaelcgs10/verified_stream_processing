theory Branch_op

imports
  Dataplane.Timely_Infrastructure
begin

definition \<open>branch_op ip p0 p1 c os = builder_op False {|ip|} {|p0, p1|} os (\<lambda> os. {|
      let result = input os ip in
      let os = produces os (map (\<lambda> (d, t). (d, Cap t (if c (d, t) then trace (STR ''p0!'') p0 else trace (STR ''p1!'') p1))) result) in
      let os = drop_caps os (map (\<lambda> t. Cap t p0) (ocaps os p0) @ map (\<lambda> t. Cap t p1) (ocaps os p1) ) in
      os\<lparr> input := (\<lambda> p. []) \<rparr>
    |}
   )\<close>

end