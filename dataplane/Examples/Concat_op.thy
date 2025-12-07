theory Concat_op

imports
  Dataplane.Timely_Infrastructure
begin

definition \<open>concat_op ips p os = builder_op False ips {|1|} os (\<lambda> os. {|
      let result = concat (map (\<lambda> p. input os p) Enum.enum) in
      let os = produces os (map (\<lambda> (d, t). (d, Cap t 1)) result) in
      let os = drop_caps os (map (\<lambda> t. Cap t 1) (ocaps os 1)) in
      os\<lparr> input := (\<lambda> p. []) \<rparr>
    |}
   )\<close>

end