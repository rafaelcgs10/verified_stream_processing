theory Numeral_Auxiliary

imports
  "HOL-Library.Numeral_Type"
  "HOL-Library.Code_Cardinality"
  "HOL-Library.Countable"
begin 

lemma zero_one[code]:
  "(0 :: 1) = 1"
  by simp

(* TODO move *)
simproc_setup num1_eq (\<open>x :: 1\<close>) =
  \<open>K (K (fn ct =>
    if Thm.term_of ct aconv @{term \<open>1 :: 1\<close>} then NONE
    else SOME (mk_meta_eq @{thm num1_eq1})))\<close>

instantiation num0 :: countable begin
instance proof qed (auto simp: inj_def Rep_num0_inject intro!: exI[of _ Rep_num0])
end


end