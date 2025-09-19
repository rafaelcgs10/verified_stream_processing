theory Locations

imports
  Main
  Nondeterministic_Dataflow.Numeral_Auxiliary
  "Collections.HashCode"
  Containers.Collection_Order
begin 

(* Inspired by timely/src/progress/mod.rs:61 *)
datatype 'p port = Trg (idp: 'p) | Src (idp: 'p)
abbreviation is_Src where "is_Src x \<equiv> (case x of Src _ \<Rightarrow> True | _ \<Rightarrow> False)"
abbreviation is_Trg where "is_Trg x \<equiv> (case x of Trg _ \<Rightarrow> True | _ \<Rightarrow> False)"

(* Inspired by timely/src/progress/mod.rs:19 *)
datatype ('id, 'p) location = Loc (node: 'id) (port: "'p port")

instantiation port :: (enum) enum
begin
definition
  "enum_port = map Trg enum_class.enum @ map Src enum_class.enum"

definition "enum_all_port P \<longleftrightarrow> list_all (\<lambda> x. P (Src x)) enum_class.enum \<and> list_all (\<lambda> x. P (Trg x)) enum_class.enum"

definition "enum_ex_port P \<longleftrightarrow> list_ex (\<lambda> x. P (Src x)) enum_class.enum \<or> list_ex (\<lambda> x. P (Trg x)) enum_class.enum"

instance
  apply standard
  subgoal
    apply (simp add: enum_port_def enum_UNIV)
    apply (metis IntE UNIV_eq_I Un_Int_eq(2,3) port.exhaust rangeI)
    done
  subgoal
    by (auto simp add: enum_class.enum_distinct enum_port_def enum_UNIV distinct_map inj_on_def)
  subgoal
    apply (simp add:  enum_all_port_def enum_UNIV list_all_iff)
    apply (metis port.exhaust)
    done
  subgoal
    apply (simp add:  enum_ex_port_def enum_UNIV list_ex_iff)
    apply (metis port.exhaust)
    done
  done
end

instantiation location :: (enum, enum) enum
begin
definition
  "enum_location = map (\<lambda> (x, y). Loc x y) (List.product enum_class.enum enum_class.enum)"

definition
  "enum_all_location P \<longleftrightarrow> enum_class.enum_all (%x. enum_class.enum_all (%y. P (Loc x y)))"

definition
  "enum_ex_location P = enum_class.enum_ex (%x. enum_class.enum_ex (%y. P (Loc x y)))"

instance
  apply standard
  apply (simp_all add: distinct_map enum_location_def enum_UNIV enum_distinct enum_all_location_def enum_ex_location_def split: prod.splits location.splits)
  apply (metis case_prod_conv location.exhaust surj_def)
  apply (auto simp add: inj_def enum_class.enum_distinct intro!: distinct_product)[1]
  apply (metis location.collapse)+
  done
end

instantiation port :: (ord) ord
begin

fun less_eq_port :: "'a port \<Rightarrow> 'a port \<Rightarrow> bool" where
  "less_eq_port (Trg t) (Trg u) = (t \<le> u)"
| "less_eq_port (Src t) (Src u) = (t \<le> u)"
| "less_eq_port (Trg t) (Src u) = True"
| "less_eq_port _ _ = False"

definition less_port where
  "(x::'a port) < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

instance ..
end

instance port :: (preorder) preorder
proof
  fix x y z :: "'a port"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (rule less_port_def)
  show "x \<le> x"
    apply (cases x)
    apply auto
    done
  assume "x \<le> y" and "y \<le> z" thus "x \<le> z"
    apply (cases x; cases y; cases z)
    apply (auto elim!: order_trans)
    done
qed

instance port :: (order) order
  apply standard
  subgoal for x y
    apply (cases x; cases y)
    apply (auto intro!: antisym elim: less_eq_port.cases)
    done
  done

instance port :: (linorder) linorder
  apply standard
  subgoal for x y
    apply (cases x; cases y)
    apply (auto intro!: antisym elim: less_eq_port.cases)
    done
  done

instantiation location :: (linorder, linorder) linorder
begin
definition
  "less_eq_location = (\<lambda> x y. case (x, y) of (Loc n1 p1, Loc n2 p2) \<Rightarrow> n1 = n2 \<and> p1 \<le> p2 \<or> n1 \<noteq> n2 \<and> n1 < n2)"

definition
  "less_location = (\<lambda> x y. case (x, y) of (Loc n1 p1, Loc n2 p2) \<Rightarrow> n1 = n2 \<and> p1 < p2 \<or> n1 \<noteq> n2 \<and> n1 < n2)"

instance 
  apply standard
  apply (auto intro!: elim!: less_eq_port.cases simp add: less_port_def less_eq_location_def less_location_def split: location.splits port.splits)[4]
  subgoal for x y
    apply (cases x; cases y; simp; hypsubst_thin)
    subgoal for n1 p1 n2 p2
      apply (cases "n1 = n2")
      subgoal
        apply (cases "p1 \<le> p2")
        apply (auto intro!: elim!: less_eq_port.cases simp add: less_port_def less_eq_location_def less_location_def split: location.splits port.splits)
        done
      subgoal
        apply (auto intro!: elim!: less_eq_port.cases simp add: less_port_def less_eq_location_def less_location_def split: location.splits port.splits)
        done
      done
    done
  done
end

instantiation "num0" :: hashable
begin
  definition [simp]: "hashcode (n :: num0) = uint32_of_int 0"
  definition "def_hashmap_size = (\<lambda>_ :: num0 itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_num0_def)
end

instantiation "num1" :: hashable
begin
  definition [simp]: "hashcode (n :: num1) = uint32_of_int 1"
  definition "def_hashmap_size = (\<lambda>_ :: num1 itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_num1_def)
end

instantiation "bit0" :: (finite) hashable
begin
  definition [simp]: "hashcode (n :: _ bit0) = uint32_of_int (Rep_bit0 n)"
  definition "def_hashmap_size = (\<lambda>_ :: (_ bit0) itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_bit0_def)
end

instantiation "port" :: (hashable) hashable
begin
  definition [simp]: "hashcode (l :: _ port) = (case l of Src a \<Rightarrow> 2 * hashcode a | Trg b \<Rightarrow> 2 * hashcode b + 1)"
  definition "def_hashmap_size = (\<lambda>_ :: ('a port) itself. def_hashmap_size TYPE('a))"
  instance using def_hashmap_size[where ?'a="'a"]
    by(intro_classes)(simp_all add: bounded_hashcode_bounds def_hashmap_size_port_def split: sum.split)
end

instantiation "location" :: (hashable, hashable) hashable
begin
  definition [simp]: "hashcode (l :: (_, _) location) = (hashcode (node l) * 33 + hashcode (port l))"
  definition "def_hashmap_size = (\<lambda>_ :: (('a, 'b) location) itself. def_hashmap_size TYPE('a) + def_hashmap_size TYPE('b))"
  instance using def_hashmap_size[where ?'a="'a"] def_hashmap_size[where ?'a="'b"]
    by(intro_classes)(simp_all add: def_hashmap_size_location_def)
end

instantiation "bit1" :: (finite) hashable
begin
  definition [simp]: "hashcode (n :: _ bit1) = uint32_of_int (Rep_bit1 n)"
  definition "def_hashmap_size = (\<lambda>_ :: (_ bit1) itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_bit1_def)
end

definition t_loc_linord :: "('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('t \<times> 'loc :: linorder ) \<Rightarrow> ('t \<times> 'loc) \<Rightarrow> bool" where
  "t_loc_linord t_less p1 p2 = (case (p1, p2) of ((t1, l1), (t2, l2)) \<Rightarrow>
    (t_less t1 t2) \<or> (t1 = t2 \<and> l1 \<le> l2))"

lemma linorder_t_loc_linord:
  assumes H1: "class.linorder (\<lambda>t u. less_t t u \<or> t = u) less_t"
  shows "class.linorder (t_loc_linord less_t) (\<lambda>t u. t_loc_linord less_t t u \<and> t \<noteq> u)"
proof -
  from H1 interpret A: linorder "(\<lambda>t u. less_t t u \<or> t = u)" less_t by auto
  show ?thesis 
  apply unfold_locales
  subgoal  by (smt (z3) A.dual_order.asym Pair_inject case_prodE t_loc_linord_def verit_la_disequality)
  subgoal by (simp add: case_prodI2 t_loc_linord_def)
  subgoal by (smt (z3) A.order.strict_trans1 case_prodE order_trans prod.simps(2) t_loc_linord_def)
  subgoal using \<open>\<And>y x. (t_loc_linord less_t x y \<and> x \<noteq> y) = (t_loc_linord less_t x y \<and> \<not> t_loc_linord less_t y x)\<close> by blast
  subgoal by (smt (verit, best) A.antisym_conv3 case_prodI case_prodI2 nle_le t_loc_linord_def)
  done
qed

definition mymin :: "('t \<Rightarrow> 't \<Rightarrow> bool) => ('t \<times> 'loc :: linorder) set \<Rightarrow> ('t \<times> 'loc)"
  where "mymin t_less = linorder.Min (t_loc_linord t_less)"

lemma linorderMin:
  assumes "class.linorder (\<lambda>t u. less_t t u \<or> t = u) less_t"
  shows "mymin less_t (set (x # xs)) = fold (\<lambda>a b. if t_loc_linord less_t a b then a else b) xs x"
proof -
  interpret B: linorder "t_loc_linord less_t" "\<lambda>t u. t_loc_linord less_t t u \<and> t \<noteq> u"
    by (rule linorder_t_loc_linord[OF assms])
  have H2: "B.Min (insert x (set xs)) = fold B.min xs x" by (metis B.Min.set_eq_fold list.simps(15))
  have H3: "B.min = (\<lambda>a b. if t_loc_linord less_t a b then a else b)" using B.min_def by blast
  show ?thesis
    unfolding mymin_def
    by (auto simp: H2 H3)
qed

definition mymin_code :: "('t :: ccompare \<times> 'loc :: linorder) set \<Rightarrow> ('t \<times> 'loc)"
  where [code del]: "mymin_code = mymin cless"

lemma mymin_code[code]: "mymin_code (set ((x :: 't :: ccompare \<times> 'loc :: linorder) # xs)) = (case ID CCOMPARE('t) of
  None \<Rightarrow> Code.abort (STR ''mymin_code: ccompare = None'') (\<lambda>_. mymin_code (set (x # xs)))
| Some c \<Rightarrow> fold (\<lambda>a b. if t_loc_linord (lt_of_comp c) a b then a else b) xs x)"
  unfolding mymin_code_def
  apply (cases \<open>ID (CCOMPARE('t))\<close>; simp)
  apply (rule linorderMin[simplified])
  apply (frule ID_ccompare)
  apply (erule arg_cong2[where ?f=class.linorder, THEN iffD1, rotated 2])
   apply (auto simp add: le_of_comp_def lt_of_comp_def fun_eq_iff split: order.splits)
   apply (meson ID_ccompare' comparator.nEq_neq_conv)
  apply (simp add: ID_code ccompare comparator.comp_same)
  done

fun print_2 where
  "print_2 n = (if n = 0 then STR ''0'' else STR ''1'')"

definition show_port where
  "show_port p = (case p of Src x \<Rightarrow> STR ''SRC '' + (print_2 x) | Trg x \<Rightarrow> STR ''TRG '' + (print_2 x))"

definition show_loc where
  "show_loc x = STR ''node: '' + print_2 (node x) + STR '', port: '' + show_port (port x)"


lemma loc_2_1_cases:
  "l = Loc (0 :: 2) (Trg (1 :: 1)) \<or> l = Loc 0 (Src 1) \<or> l = Loc 1 (Src 1) \<or> l = Loc 1 (Trg 1)"
  apply (cases l; simp)
  subgoal for nid p
    apply (cases nid; cases p; simp)
     apply (smt (verit, ccfv_SIG) of_int_0 of_int_1)+
    done
  done

end