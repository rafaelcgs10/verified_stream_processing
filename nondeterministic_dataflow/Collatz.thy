section \<open>The Collatz operator\<close>

theory Collatz

imports
  Loop
  BNA_Operators
begin

locale collatz =
  fixes encode_nat3 :: "nat \<times> nat \<times> nat \<Rightarrow> 'd"
    and decode_nat3 :: "'d \<Rightarrow> nat \<times> nat \<times> nat"
    and encode_nat2 :: "nat \<times> nat \<Rightarrow> 'd"
    and decode_nat2 :: "'d \<Rightarrow> nat \<times> nat"
    and encode_nat1 :: "nat \<Rightarrow> 'd"
    and decode_nat1 :: "'d \<Rightarrow> nat"
  assumes type_definition_nat3: "type_definition encode_nat3 decode_nat3 (range encode_nat3)"
      and type_definition_nat2: "type_definition encode_nat2 decode_nat2 (range encode_nat2)"
      and type_definition_nat1: "type_definition encode_nat1 decode_nat1 (range encode_nat1)"
begin

definition "collatz_op = while_op (\<lambda> _. BEmpty)
      (\<lambda> x. let (n, ni, i) = (decode_nat3 x) in ni = Suc 0)
      (\<lambda> x. let (n, ni, i) = (decode_nat3 x) in encode_nat3 (n, if ni mod 2 = 0 then ni div 2 else 3 * ni + 1, i + 1))"

corec collatz_input where
  "collatz_input = (Read (2::2) (\<lambda>x. case x of
     Observed x \<Rightarrow> let n = decode_nat1 x in Write collatz_input 2 (encode_nat3 (n, n, 0))
   | EOB \<Rightarrow> collatz_input
   | EOS \<Rightarrow> End))"

corec collatz_output where
  "collatz_output = (Read 2 (\<lambda>x. case x of
     Observed x \<Rightarrow> let (n, ni, i) = decode_nat3 x in Write collatz_output (2::2) (encode_nat2 (n,i))
   | EOB \<Rightarrow> collatz_output
   | EOS \<Rightarrow> End))"

abbreviation "collatz_scomp \<equiv> scomp_op collatz_input (scomp_op collatz_op collatz_output)"

definition ccollatz where
  "ccollatz xs = map decode_nat2 (list_of (produce collatz_scomp (\<lambda>_. llist_of (map (encode_nat1) xs)) 2))"
end

abbreviation "(encode_nat3 :: nat \<times> nat \<times> nat \<Rightarrow> nat + nat \<times> nat + nat \<times> nat \<times> nat) \<equiv> Inr o Inr"
abbreviation "(decode_nat3 :: nat + nat \<times> nat + nat \<times> nat \<times> nat \<Rightarrow> nat \<times> nat \<times> nat) \<equiv> projr o projr"

global_interpretation c: collatz
  encode_nat3 decode_nat3 "Inr o Inl" "projl o projr" Inl projl
  defines collatz_op = "collatz.collatz_op encode_nat3 decode_nat3"
  and ccollatz = "collatz.ccollatz encode_nat3 decode_nat3 (Inr o Inl) (projl o projr) Inl projl"
  and collatz_input = "collatz.collatz_input encode_nat3 projl"
  and collatz_output = "collatz.collatz_output decode_nat3 (Inr o Inl)"
  and collatz_scomp = "collatz.collatz_scomp encode_nat3 (projr o projr) (Inr o Inl) projl"
  by standard auto

value "ccollatz [1 ..< 101]"

end