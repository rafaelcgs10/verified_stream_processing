theory Ooo_Input_op

imports
  Dataplane.Timely_Stream
  Source_op
begin

record ('p, 'd, 't) input_state = "('p, 'd, 't) operator_state" + inps:: "'p \<Rightarrow> ('t, 'd) event llist"

definition ooo_input_op where
  "ooo_input_op ops os = builder_op {||} ops os (\<lambda> os. (cimage (\<lambda>p. case inps os p of
    LCons (Data t d) lxs \<Rightarrow> produce (os\<lparr> inps := (inps os)(p := lxs) \<rparr>) (Cap t p) [d]
  | LCons (Drop t) lxs \<Rightarrow> drop_cap (os\<lparr> inps := (inps os)(p := lxs) \<rparr>) (Cap t p)
  | LCons (Mint t) lxs \<Rightarrow> mint_cap (os\<lparr> inps := (inps os)(p := lxs) \<rparr>) p t)
    (cfilter (\<lambda>p. ocaps os p \<noteq> []) ops)))"

end