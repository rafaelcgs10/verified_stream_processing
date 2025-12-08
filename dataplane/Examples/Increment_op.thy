theory Increment_op

imports
  Dataplane.Timely_Infrastructure
  Dataplane.MyProduct_Instances
begin

record ('p, 'd, 'd1, 't) increment_state = \<open>('p, 'd, 'd1, 't) operator_state_ty\<close> + incr :: \<open>'p \<Rightarrow> 't\<close>

definition increment_op_logic where
  \<open>increment_op_logic ops os = cimage (\<lambda>p. case input os p of (d, t) # xs \<Rightarrow>
    let cap = Cap (t + incr os p) p
    in drop_cap (produce (os\<lparr>input := (input os)(p := xs)\<rparr>) cap [en1 os d]) cap)
    (cfilter (\<lambda>p. input os p \<noteq> []) ops)\<close>

definition increment_op where
  \<open>increment_op ips ops os = builder_op False ips ops os (increment_op_logic ops)\<close>


end
