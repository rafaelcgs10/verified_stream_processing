theory Operator_Examples

imports
  Operator
begin


corec writes where
  "writes op p xs =
    (case xs of [] \<Rightarrow> case_op Read Write Choice Silent op | x #xs \<Rightarrow> Write (writes op p xs) p x)"

friend_of_corec writes where
  "writes op p xs =
    (case xs of [] \<Rightarrow> case_op Read Write Choice Silent op | x #xs \<Rightarrow> Write (writes op p xs) p x)"
  sorry

(* 
consts window_op :: "'a buf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (1, 1, 'd) op"  *)


corec window_op where
 "window_op f buf timer time_win =
   Choice (cimage (\<lambda> time. 
     choice2
     (Read (1::1) (\<lambda> x. if time_win < time then writes (window_op f [] (time mod time_win) time_win) 1 (f (buf @ [x]) # replicate 0 (f [])) else Silent (window_op f (buf @ [x]) time time_win)))
     (if buf = [] then Silent (window_op f buf 0 time_win) else (if time_win < time then Write (window_op f [] (time mod time_win) time_win) 1 (f buf) else Silent (window_op f buf time time_win)))
     ) (cset.acset {Suc timer..}))"

lemma window_op_code:
  "window_op buf timer time_win =
   Choice (cimage (\<lambda> time. 
     Choice {|
     Read (1::1) (\<lambda> x. if time_win < time then Write (window_op [] 0 time_win) 1 (encode_output (buf @ [decode_input x])) else Silent (window_op (buf @ [decode_input x]) time time_win)),
     if buf = [] then Silent (window_op buf 0 time_win) else (if time_win < time then Write (window_op [] 0 time_win) 1 (encode_output buf) else Silent (window_op buf time time_win))
     |}) (cset.acset {Suc timer..}))"
  sorry


end

global_interpretation wop: window Inl projl Inr projr
  defines wwindow_op = "wop.window_op"
  by standard auto

term wwindow_op


end