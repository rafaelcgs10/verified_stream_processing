theory Operator_Examples

imports
  Operator
begin

corec writes where
  "writes op p xs =
    (case xs of [] \<Rightarrow> case_op Read Write Choice Silent op | x #xs \<Rightarrow> Write (writes op p xs) p x)"

lemma foo[friend_of_corec_simps]:
  "(if snd (snd x) = [] then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x)))) else ctor_op (Abs_op_pre_op (Inl (Inr (algrho (fst x, fst (snd x), btl (snd (snd x))), fst (snd x), bhd (snd (snd x))))))) =
         (if snd (snd x) = []
         then if isl (Rep_op_pre_op (dtor_op (fst x))) \<and> isl (projl (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
              else if isl (Rep_op_pre_op (dtor_op (fst x))) \<and> \<not> isl (projl (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
                   else if \<not> isl (Rep_op_pre_op (dtor_op (fst x))) \<and> isl (projr (Rep_op_pre_op (dtor_op (fst x)))) then ctor_op (Abs_op_pre_op (Rep_op_pre_op (dtor_op (fst x))))
                        else ctor_op
                              (Abs_op_pre_op
                                (Inr (Inr (if isl (Rep_op_pre_op (dtor_op (fst x))) then undefined
                                           else if isl (projr (Rep_op_pre_op (dtor_op (fst x)))) then undefined else projr (projr (Rep_op_pre_op (dtor_op (fst x))))))))
         else ctor_op (Abs_op_pre_op (Inl (Inr (algrho (fst x, fst (snd x), btl (snd (snd x))), fst (snd x), bhd (snd (snd x)))))))"
  by (auto split: if_splits)

friend_of_corec writes where
  "writes op p xs =
    (case xs of [] \<Rightarrow> case_op Read Write Choice Silent op | x #xs \<Rightarrow> Write (writes op p xs) p x)"
  apply (rule writes.code)
  apply transfer_prover
  done

corec window_op where
 "window_op f n buf time =
   Choice (cimage (\<lambda> time. 
     choice2
     (Read (1::1) (\<lambda> x. if n < time then writes (window_op f n [] (time mod n)) (1 :: 1) (f (buf @ [x]) # replicate (time div n - 1) (f [])) else Silent (window_op f n (buf @ [x]) time)))
     (if n < time then writes (window_op f n [] (time mod n)) 1 (f buf # replicate (time div n - 1) (f [])) else Silent (window_op f n buf time))
     ) (cset.acset {Suc time..}))"

corec filter_op where
  "filter_op P buf = choice2 
   (Read (1 :: 1) (\<lambda> x. filter_op P (if P x then buf @ [x] else buf)))
   (writes (filter_op P []) 1 buf)"

term wtraced

thm wbisim'_alt

end