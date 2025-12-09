theory Concat_op

imports
  Dataplane.Timely_Infrastructure
begin

definition \<open>concat_op ips p os = builder_op False ips {|p|} os (\<lambda> os. {|
      let result = concat (map (\<lambda> p. input os p) [x <- Enum.enum. x |\<in>| ips]) in
      let os = produces os (map (\<lambda> (d, t). (d, Cap t p)) result) in
      let os = drop_caps os (concat (map (\<lambda> p. map (\<lambda> t. Cap t p) (ocaps os p)) Enum.enum)) in
      trace (STR ''concat_op!'')
      os\<lparr> input := (\<lambda> p. []) \<rparr>
    |}
   )\<close>

end