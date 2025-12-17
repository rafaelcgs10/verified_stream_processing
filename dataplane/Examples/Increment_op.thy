theory Increment_op

imports
  Dataplane.Timely_Infrastructure
  Dataplane.MyProduct_Instances
begin

definition \<open>increment_op_logic ip op inc = (\<lambda>os. {|
      let result = map (\<lambda>(d, t). (d, t + inc)) (input os ip);
          os' = trace (STR ''producing from incr op'') (produces os (map (\<lambda>(d, t). (d, Cap t op)) result));
          os'' = drop_caps os' (concat (map (\<lambda>p. map (\<lambda>t. Cap t p) (ocaps os' p)) Enum.enum))
      in os''\<lparr>input := (\<lambda>_. [])\<rparr>|})\<close>

definition \<open>increment_op ip op inc os = builder_op False {|ip|} {|op|} os (increment_op_logic ip op inc)\<close>

end
