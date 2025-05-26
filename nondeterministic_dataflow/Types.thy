theory Types
  imports Complex_Main
     "HOL-Library.Product_Lexorder"
     "HOL.List"
begin

(*
  Finite datatypes for op_metaerators and ports
*)

definition MAX_OP :: int where "MAX_OP = 100"
definition MAX_PORT :: int where "MAX_PORT = 3"

typedef op_meta = "{0::int.. MAX_OP}"
  morphisms un_Op unsafe_Op
  apply (rule_tac x = 0 in exI)
  apply (simp add: MAX_OP_def)
  done

typedef pnum = "{0::int.. MAX_PORT}"
  morphisms un_Pnum unsafe_Pnum
  apply (rule_tac x = 0 in exI)
  apply (simp add: MAX_PORT_def)
  done

setup_lifting type_definition_op_meta

lift_definition Op :: "int \<Rightarrow> op_meta" is "\<lambda>i. if 0 \<le> i \<and> i \<le> MAX_OP then i else 0"
  by (auto simp: MAX_OP_def)

setup_lifting type_definition_pnum

lift_definition Pnum :: "int \<Rightarrow> pnum" is "\<lambda>i. if 0 \<le> i \<and> i \<le> MAX_PORT then i else 0"
  by (auto simp: MAX_PORT_def)

datatype port = Src pnum | Trg pnum

abbreviation "src n == Src (Pnum n)"
abbreviation "trg n == Trg (Pnum n)"

(* equal on pnum and op_meta *)

instantiation op_meta :: equal
begin
definition "equal_op_meta = (\<lambda> x y. un_Op x = un_Op y)"
instance
  apply standard
  by (simp add: equal_op_meta_def un_Op_inject)
end

instantiation pnum :: equal
begin
definition "equal_pnum = (\<lambda> x y. un_Pnum x = un_Pnum y)"
instance
  apply standard
  by (simp add: equal_pnum_def un_Pnum_inject)
end

(* linorder on port and op_meta *)

instantiation op_meta :: linorder
begin
definition "less_eq_op_meta = (\<lambda> x y. un_Op x \<le> un_Op y)"
definition "less_op_meta = (\<lambda> x y. un_Op x < un_Op y)"
instance
  apply standard
      apply (auto simp: less_eq_op_meta_def less_op_meta_def)
  subgoal using un_Op_inject by auto
  done
end

instantiation pnum :: linorder
begin
definition "less_eq_pnum = (\<lambda> x y. un_Pnum x \<le> un_Pnum y)"
definition "less_pnum = (\<lambda> x y. un_Pnum x < un_Pnum y)"
instance
  apply standard
      apply (auto simp: less_eq_pnum_def less_pnum_def)
  subgoal using un_Pnum_inject by auto
  done
end

lift_definition port_to_int :: "port \<Rightarrow> int" is
  "\<lambda>x. (case x of (Src s) \<Rightarrow> (un_Pnum s) + 1 + MAX_PORT | (Trg t) \<Rightarrow> (un_Pnum t))" .

instantiation port :: linorder
begin
definition "less_eq_port = (\<lambda> x y. port_to_int x \<le> port_to_int y)"
definition less_port :: "port \<Rightarrow> port \<Rightarrow> bool" where
"less_port = (\<lambda> x y. x \<le> y \<and> \<not>y \<le> x)"
instance
  apply standard
  apply (auto simp: less_eq_port_def less_port_def)
  subgoal for x y apply (cases x; cases y)
       apply (simp add: un_Pnum_inject port_to_int.abs_eq)
    subgoal for x y apply (cases x; cases y)
      by (simp add: port_to_int.abs_eq unsafe_Pnum_inverse)
    subgoal for x y apply (cases x; cases y)
      by (simp add: port_to_int.abs_eq unsafe_Pnum_inverse)
    subgoal for x y apply (cases x; cases y)
      by (simp add: port_to_int.abs_eq unsafe_Pnum_inverse)
    done
  done
end

(* enum on port and op_meta *)

instantiation op_meta :: enum
begin
abbreviation "enum' \<equiv> map (Op) [0 .. MAX_OP]"
definition "enum_op_meta = enum'"
definition "enum_all_op_meta P = list_all P enum'"
definition "enum_ex_op_meta P = list_ex P enum'"
instance
  apply standard
  subgoal
    apply (auto simp: enum_op_meta_def)
    subgoal for x by transfer auto
    done
  subgoal
    apply (auto simp: enum_op_meta_def distinct_map inj_on_def)
    by transfer (auto simp add: unsafe_Op_inject)
  subgoal for P
    apply (auto simp: enum_op_meta_def enum_all_op_meta_def list.pred_set)
    subgoal for x
      by (cases x) (auto simp: Op_def)
    done
  subgoal for P
    apply (auto simp: enum_ex_op_meta_def list_ex_iff)
    subgoal for x by (cases x) (auto simp: Op_def)
    done
  done
end

instantiation pnum :: enum
begin
abbreviation "enum_pnum_abb \<equiv> map (Pnum) [0 .. MAX_PORT]"
definition "enum_pnum = enum_pnum_abb"
definition "enum_all_pnum P = list_all P enum_pnum_abb"
definition "enum_ex_pnum P = list_ex P enum_pnum_abb"
instance
  apply standard
  subgoal
    apply (auto simp: enum_pnum_def)
    subgoal for x by transfer auto
    done
  subgoal
    apply (auto simp: enum_pnum_def distinct_map inj_on_def)
    by transfer (auto simp add: unsafe_Pnum_inject)
  subgoal for P
    apply (auto simp: enum_pnum_def enum_all_pnum_def list.pred_set)
    subgoal for x
      by (cases x) (auto simp: Pnum_def)
    done
  subgoal for P
    apply (auto simp: enum_ex_pnum_def list_ex_iff)
    subgoal for x by (cases x) (auto simp: Pnum_def)
    done
  done
end

instantiation port :: enum
begin
abbreviation "enum_port_abb \<equiv> (map (Src \<circ> Pnum) [0..MAX_PORT]) @ (map (Trg \<circ> Pnum) [0..MAX_PORT])"
definition "enum_port = enum_port_abb"
definition "enum_all_port P = list_all P enum_port_abb"
definition "enum_ex_port P = list_ex P enum_port_abb"
instance
  apply standard
     apply (auto simp: enum_port_def enum_all_port_def enum_ex_port_def)
  subgoal for x apply (cases x)
     apply (auto simp: Pnum_def image_iff)
    using unsafe_Pnum_cases apply blast
    using unsafe_Pnum_cases apply blast
    done
  subgoal
    by (auto simp add: Pnum_def o_def distinct_map inj_on_def unsafe_Pnum_inject)
  subgoal
    by (auto simp add: Pnum_def o_def distinct_map inj_on_def unsafe_Pnum_inject)
  subgoal for P x
    apply (cases x)
    subgoal for x1
      apply (cases x1)
      apply (auto simp: Pnum_def o_def list.pred_set)
      done
    subgoal for x2
      apply (cases x2)
      apply (auto simp: Pnum_def o_def list.pred_set)
      done
    done
      apply (simp add: list_all_length)+
  using list_ex_length apply auto
  subgoal for P x
    apply (cases x)
    subgoal for x1
      apply (cases x1)
      apply (auto simp: Pnum_def o_def list_ex_iff)
      done
    subgoal for x2
      apply (cases x2)
      apply (auto simp: Pnum_def o_def list_ex_iff)
      done
    done
  done
end

instantiation prod :: (type, type) zero begin
definition "zero_prod = (0, 0)"
instance
  apply standard
  done
end

instantiation prod :: (monoid_add, monoid_add) monoid_add begin
definition "plus_prod = (\<lambda>(a,b) (c,d). (a+c, b+d))"
instance
  by intro_classes (auto simp: plus_prod_def algebra_simps zero_prod_def)
end

(* linorder (<) definitions on known timestamp/summary types *)

definition linord_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "linord_nat \<equiv> ord_nat_inst.less_nat"

definition linord_nat_prod :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool" where
  "linord_nat_prod \<equiv> Product_Lexorder.ord_prod_inst.less_prod"

type_synonym t = "(nat \<times> nat)"
type_synonym sum = "(nat \<times> nat)"


definition followed_by :: "sum \<Rightarrow> sum \<Rightarrow> sum" where
  "followed_by \<equiv> plus"

definition results_in :: "sum \<Rightarrow> sum \<Rightarrow> sum" where
  "results_in \<equiv> plus"

end