theory Tmap_op

imports
  Dataplane.Timely_Infrastructure
begin

definition \<open>tmap_op os f = builder_op False {|1|} {|1|} os (\<lambda> os. {|
      let result = map (\<lambda> (d, t). (f (de1 os d), t)) (input os 1) in
      let os =  trace (STR ''producing from tmap op'') (produces os (map (\<lambda> (d, t). (en2 os d, Cap t 1)) result)) in
      let os = drop_caps os (map (\<lambda> t. Cap t 1) (ocaps os 1)) in
      os\<lparr> input := (\<lambda> p. []) \<rparr>
    |}
   )\<close>

end