theory Lazy_Issue
  imports
    Coinductive.Coinductive_List
    "HOL-Library.Code_Lazy"
    "HOL-Library.BNF_Corec"
begin

(* value "lhd ((LCons (2::nat) (LCons 3 (repeat 2))))" *)  (* loops, repeat executes too much *)

(* Lets make llist lazy *)
code_lazy_type llist

code_thms ltakeWhile

(* lemma [code]: "ltakeWhile p xs =
   Lazy_llist (delay (\<lambda>uu. case_llist_lazy LNil_Lazy
    (\<lambda>x xs.
        if p x then LCons_Lazy x (ltakeWhile p xs)
        else LNil_Lazy)
    (force (unlazy_llist xs))))"
  apply(cases xs)
   apply(simp_all add: Rep_LNil_Lazy Rep_LCons_Lazy Lazy_llist_def force_delay
      case_llist_lazy_def force_unlazy_llist Abs_llist_lazy_inverse)
  done

lemma if_Lazy_llist [code_unfold]:
   "(if c then Lazy_llist (delay (\<lambda>_. x)) else Lazy_llist (delay (\<lambda>_. y))) = Lazy_llist
(delay (\<lambda>_. if c then x else y))"
   by(simp)

lemma case_lazy_llist_Lazy_llist [code_unfold]:
   "case_llist_lazy (Lazy_llist (delay (\<lambda>_. x))) (\<lambda>x xs. Lazy_llist (delay (\<lambda>_. f x xs))) xs =
    Lazy_llist (delay (\<lambda>_. case_llist_lazy x f xs))"
   by(simp add: Lazy_llist_def force_delay case_llist_lazy_def split: llist.split) *)


value "lhd (LCons (2::nat) (LCons 3 (repeat (hd []))))" (* ok. repeat does not execute *)
value "lhd (ltakeWhile even (LCons (2::nat) (LCons 3 (LCons (hd []) LNil))))" (* ok, takeWhile stops before error. Was it because of 3 or because lhd? *)
value "lhd (ltakeWhile even (LCons (2::nat) (LCons (hd []) LNil)))" (* error, so it was because of 3 *)
value "lhd (ltakeWhile even (LCons (2::nat) (repeat 2)))" (* ok. So it seems repeat does not execute (too much) *)
value "lhd (ltakeWhile even (LCons (2::nat) (LCons 3 (repeat (hd [])))))" (* error. So wait, it executes. This is confusing! *)
value "lhd (ltakeWhile even (repeat (2::nat)))" (* ok *)

code_thms ltakeWhile
(* corecursion guarded by LCons, a lambda and delay *)

lemma [code]: "ltakeWhile p xs =
   Lazy_llist (delay (\<lambda>uu. case_llist_lazy LNil_Lazy
    (\<lambda>x xs.
        if p x then LCons_Lazy x (ltakeWhile p xs)
        else LNil_Lazy)
    (force (unlazy_llist xs))))"
   apply(cases xs)
    apply(simp_all add: Rep_LNil_Lazy Rep_LCons_Lazy Lazy_llist_def force_delay
case_llist_lazy_def force_unlazy_llist Abs_llist_lazy_inverse)
  done


code_thms iterates (* repeat is iterates id *)
(* corecursion guarded by LCons, a lambda and delay *)

(* I define my own lazy list type *)
codatatype (Lazy_lset: 'a) lazy_list =
    lnull: Lazy_LNil
  | Lazy_LCons (Lazy_lhd: "'a") (Lazy_ltl: "unit \<Rightarrow> 'a lazy_list")
for
  map: lmap
  rel: llist_all2
where
  "Lazy_ltl Lazy_LNil = (\<lambda> _. Lazy_LNil)"
| "Lazy_lhd Lazy_LNil = undefined"

(* corecursion inside of a lambda. Lazy_LCons outside of the lambda. *)
primcorec Lazy_iterates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a lazy_list"
  where "Lazy_iterates f x = Lazy_LCons x (\<lambda> _. Lazy_iterates f (f x))"

abbreviation Lazy_repeat :: "'a \<Rightarrow> 'a lazy_list"
where "Lazy_repeat \<equiv> Lazy_iterates (\<lambda>x. x)"

(* corecursion inside of a lambda. Lazy_LCons outside of the lambda. *)
primcorec Lazy_ltakeWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a lazy_list \<Rightarrow> 'a lazy_list"
where
  "Lazy_ltakeWhile P ys = (case ys of Lazy_LNil \<Rightarrow> Lazy_LNil | Lazy_LCons x xs \<Rightarrow> (if P x then Lazy_LCons x (\<lambda> _. Lazy_ltakeWhile P (xs ())) else Lazy_LNil))"

value "Lazy_lhd (Lazy_ltakeWhile even (Lazy_LCons (2::nat) (\<lambda> _. Lazy_repeat (hd []))))" (* ok, so this is more lazy than ltakeWhile *)

(* Trying something non primitive *)
corecursive Lazy_ldropWhile where
  "Lazy_ldropWhile P xs = (if \<forall>x \<in> Lazy_lset xs. P x then
    Lazy_LNil
    else if P (Lazy_lhd xs) then
      Lazy_ldropWhile P (Lazy_ltl xs ())
    else
      xs)"
proof (relation "measure (\<lambda>(P, xs). LEAST n. \<not> P (Lazy_lhd (((\<lambda> x. Lazy_ltl x ()) ^^ n) xs)))", rule wf_measure, clarsimp)
  fix P xs x
  assume "x \<in> Lazy_lset xs" "\<not> P x" "P ((Lazy_lhd xs))"
  from this(1,2) obtain a where "\<not> P (Lazy_lhd (((\<lambda> x. Lazy_ltl x ()) ^^ a) xs))"
    by (atomize_elim, induct x xs rule: lazy_list.set_induct) (auto simp: funpow_Suc_right simp del: funpow.simps(2) intro: exI[of _ 0] exI[of _ "Suc i" for i])
  with \<open> P (Lazy_lhd xs)\<close>
    have "(LEAST n. \<not> P (Lazy_lhd (((\<lambda> x. Lazy_ltl x ()) ^^ n) xs))) = Suc (LEAST n. \<not> P (Lazy_lhd (((\<lambda> x. Lazy_ltl x ()) ^^ Suc n) xs)))"
    by (intro Least_Suc) auto
  then show "(LEAST n. \<not> P (Lazy_lhd (((\<lambda>x. Lazy_ltl x ()) ^^ n) (Lazy_ltl xs ())))) < (LEAST n. \<not> P (Lazy_lhd (((\<lambda>x. Lazy_ltl x ()) ^^ n) xs)))"
    by (simp add: funpow_swap1[of "\<lambda>x. Lazy_ltl x ()"])
qed

lemma ldropWhile_code[code]:
  shows Lazy_ldropWhile_LNil: "Lazy_ldropWhile P Lazy_LNil = Lazy_LNil"
  and Lazy_ldropWhile_LCons: "Lazy_ldropWhile P (Lazy_LCons x xs) = (if P x then Lazy_ldropWhile P (xs ()) else Lazy_LCons x xs)"
  by (subst Lazy_ldropWhile.code; simp)+

value "lhd (ldropWhile even (LCons (3::nat) (LCons 3 (repeat (hd [])))))" (* ok *)
value "lhd (ldropWhile even (LCons 3 (repeat (hd []))))" (* error *)
(* value "lhd (ldropWhile even (LCons (2::nat) (repeat 2)))" *) (* loops *)

value "Lazy_lhd (Lazy_ldropWhile even ( Lazy_LCons (3::nat) (\<lambda> _. Lazy_repeat (hd []))))" (* ok *)
value "Lazy_lhd (Lazy_ldropWhile even (Lazy_LCons (2::nat) (\<lambda> _. Lazy_repeat (hd []))))" (* error, so it stopped because of 3 *)
(* value "Lazy_lhd (Lazy_ldropWhile even (Lazy_LCons (2::nat)  (\<lambda> _. Lazy_repeat 2)))" *) (* loops *)

end