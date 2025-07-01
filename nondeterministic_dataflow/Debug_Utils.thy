theory Debug_Utils

imports
  "HOL-Library.Debug"
  "HOL-Library.Numeral_Type"
begin 

fun print_nat where
  "print_nat 0 = ''0''"
| "print_nat (Suc 0) = ''1''"
| "print_nat (Suc (Suc 0)) = ''2''"
| "print_nat (Suc (Suc (Suc 0))) = ''3''"
| "print_nat (Suc (Suc (Suc (Suc 0)))) = ''4''"
| "print_nat (Suc (Suc (Suc (Suc (Suc 0))))) = ''5''"
| "print_nat (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) = ''6''"
| "print_nat (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) = ''7''"
| "print_nat (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) = ''8''"
| "print_nat (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))) = ''9''"
| "print_nat n = print_nat (n div 10) @ print_nat (n mod 10)"

definition show_nat where
  "show_nat x = String.implode (print_nat x)"

definition "enclose s = STR ''('' + s + STR '')''"
find_consts "char list \<Rightarrow> String.literal"
definition show_prod where
  "show_prod show1 show2 x = enclose (show1 (fst x) + STR '','' + show2 (snd x))"
fun show_sum where
  "show_sum show1 show2 (Inl x) = STR ''Inl '' + show1 x"
| "show_sum show1 show2 (Inr x) = STR ''Inr '' + show2 x"
fun show_bool where
  "show_bool True = STR ''T''"
| "show_bool False = STR ''F''"
fun show_list0 where
  "show_list0 show [] = STR ''''"
| "show_list0 show [x] = show x"
| "show_list0 show (x # y # z) = show x + STR '','' + show_list0 show (y # z)"
definition "show_list show xs = enclose (show_list0 show xs)"

fun print_2 where
  "print_2 n = (if n = 0 then STR ''0'' else STR ''1'')"

abbreviation "print_int n \<equiv> (if n \<ge> 0 then show_nat (Int.nat n) else STR ''-'' + show_nat (Int.nat (abs n)) )"

end