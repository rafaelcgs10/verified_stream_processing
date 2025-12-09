theory Tmap_op

imports
  Dataplane.Timely_Infrastructure
begin

definition \<open>tmap_op ip op os f = builder_op False {|ip|} {|op|} os (\<lambda> os. {|
      let result = map (\<lambda> (d, t). (f (de1 os d), t)) (input os ip) in
      let os =  trace (STR ''producing from tmap op'') (produces os (map (\<lambda> (d, t). (en2 os d, Cap t op)) result)) in
      let os = drop_caps os (concat (map (\<lambda> p. map (\<lambda> t. Cap t p) (ocaps os p)) Enum.enum)) in
      os\<lparr> input := (\<lambda> p. []) \<rparr>
    |}
   )\<close>

end