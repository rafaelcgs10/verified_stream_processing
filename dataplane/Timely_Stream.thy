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
| LConsDrop: "\<lbrakk> t \<in># C ; timely_monotone xs (C - {# t #})\<rbrakk> \<Longrightarrow> timely_monotone (LCons (Drop t) xs) C"
| LConsMint: "\<lbrakk> t' \<in># C ; t' \<le> t ; timely_monotone xs (C + {# t #}  )\<rbrakk> \<Longrightarrow> timely_monotone (LCons (Mint t) xs) C"
| LConsData: "\<lbrakk> t \<in># C  ; timely_monotone xs C \<rbrakk> \<Longrightarrow> timely_monotone (LCons (Data t d) xs) C" 

end