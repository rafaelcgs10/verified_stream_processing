theory Timely_Stream
  imports
    "Coinductive.Coinductive_List"
    "HOL-Library.BNF_Corec"
    "HOL-Library.Multiset"
    Nondeterministic_Dataflow.Coinductive_List_Auxiliary
begin

datatype ('t :: order, 'd) event = Data (time: 't) (data: 'd) | Drop (time: 't) | Mint (time: 't)

coinductive timely_monotone :: "('t::order, 'd) event llist \<Rightarrow> 't multiset \<Rightarrow> bool" where
  LNil: "timely_monotone LNil {#}"
| LConsDrop: "\<lbrakk> t \<in># C ; timely_monotone lxs (C - {# t #})\<rbrakk> \<Longrightarrow> timely_monotone (LCons (Drop t) lxs) C"
| LConsMint: "\<lbrakk> t' \<in># C ; t' \<le> t ; timely_monotone lxs (C + {# t #}  )\<rbrakk> \<Longrightarrow> timely_monotone (LCons (Mint t) lxs) C"
| LConsData: "\<lbrakk> t \<in># C  ; timely_monotone lxs C \<rbrakk> \<Longrightarrow> timely_monotone (LCons (Data t d) lxs) C" 

inductive ev_drops for t where
  "ev_drops t 0 lxs"
| "ev_drops t n lxs \<Longrightarrow> ev_drops t (Suc n) (LCons (Drop t) lxs)"
| "ev_drops t (Suc n) lxs \<Longrightarrow> ev_drops t n (LCons (Mint t) lxs)"
| "ev_drops t n lxs \<Longrightarrow> ev_drops t n (LCons (Data t d) lxs)"
| "ev_drops t n lxs \<Longrightarrow> time x \<noteq> t \<Longrightarrow> ev_drops t n (LCons x lxs)"

coinductive timely_productive where
  "lfinite lxs \<Longrightarrow> timely_productive lxs"
| "\<lbrakk>\<not> lfinite lxs; timely_productive lxs\<rbrakk> \<Longrightarrow> timely_productive (LCons (Data t d) lxs)"
| "\<lbrakk>\<not> lfinite lxs; timely_productive lxs; ev_drops t 1 lxs \<rbrakk> \<Longrightarrow> timely_productive (LCons (Mint t) lxs)"
| "\<lbrakk>\<not> lfinite lxs; timely_productive lxs \<rbrakk> \<Longrightarrow> timely_productive (LCons (Drop t) lxs)"


definition "timely_input_stream lxs C =
 (timely_monotone lxs C \<and> (\<forall> t. ev_drops t (count C t) lxs) \<and> timely_productive lxs)"

end