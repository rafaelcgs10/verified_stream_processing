theory Numeral_Conversion

(* Made with GPT-5.3 codex *)

imports
  "HOL-Library.Numeral_Type"
  Nondeterministic_Dataflow.Numeral_Auxiliary
begin

class numeral_conversion =
  fixes to_nat_numeral :: "'a \<Rightarrow> nat"

instantiation num0 :: numeral_conversion
begin

definition to_nat_numeral_num0 :: "0 \<Rightarrow> nat" where
  "to_nat_numeral_num0 _ = 0"

instance ..

end

instantiation num1 :: numeral_conversion
begin

definition to_nat_numeral_num1 :: "1 \<Rightarrow> nat" where
  "to_nat_numeral_num1 _ = 0"

instance ..

end

instantiation bit0 :: (finite) numeral_conversion
begin

definition to_nat_numeral_bit0 :: "'a bit0 \<Rightarrow> nat" where
  "to_nat_numeral_bit0 n = nat (Rep_bit0 n)"

instance ..

end

instantiation bit1 :: (finite) numeral_conversion
begin

definition to_nat_numeral_bit1 :: "'a bit1 \<Rightarrow> nat" where
  "to_nat_numeral_bit1 n = nat (Rep_bit1 n)"

instance ..

end

end
