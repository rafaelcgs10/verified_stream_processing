theory Timely_Stream
  imports
    "Coinductive.Coinductive_List"
    "HOL-Library.BNF_Corec"
    "HOL-Library.Multiset"
    Nondeterministic_Dataflow.Coinductive_List_Auxiliary
begin

datatype ('t :: order, 'd) event = Data (time: 't) (data: 'd) | Drop (time: 't) | Mint (time: 't)

coinductive monotone :: "('t::order, 'd) event llist \<Rightarrow> 't multiset \<Rightarrow> bool" where
  LNil: "monotone LNil {#}"
| LConsDrop: "\<lbrakk> t \<in># C ; monotone xs (C - {# t #})\<rbrakk> \<Longrightarrow> monotone (LCons (Drop t) xs) C"
| LConsMint: "\<lbrakk> t' \<in># C ; t' \<le> t ; monotone xs (C + {# t #}  )\<rbrakk> \<Longrightarrow> monotone (LCons (Mint t) xs) C"
| LConsData: "\<lbrakk> t \<in># C  ; monotone xs C \<rbrakk> \<Longrightarrow> monotone (LCons (Data t d) xs) C" 

end