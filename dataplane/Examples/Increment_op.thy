theory Increment_op

imports
  Dataplane.Timely_Infrastructure
  Dataplane.MyProduct_Instances
begin

record ('p, 'd, 'd1, 't) increment_state = \<open>('p, 'd, 'd1, 't) operator_state_ty\<close> + incr :: \<open>'p \<Rightarrow> 't\<close>

definition \<open>increment_op ip op inc os = builder_op False {|ip|} {|op|} os (\<lambda> os. {|
      let result = map (\<lambda> (d, t). (d, t + inc)) (input os ip) in
      let os =  trace (STR ''producing from incr op'') (produces os (map (\<lambda> (d, t). (d, Cap t op)) result)) in
      let os = drop_caps os (concat (map (\<lambda> p. map (\<lambda> t. Cap t p) (ocaps os p)) Enum.enum)) in
      os\<lparr> input := (\<lambda> p. []) \<rparr>
    |}
   )\<close>

end
