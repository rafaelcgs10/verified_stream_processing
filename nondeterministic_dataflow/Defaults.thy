text \<open>defaultss setup\<close>

theory Defaults
  imports "HOL-Library.Numeral_Type"
begin

class defaults = fixes defaults :: "'a set"
begin

definition "\<UU> = (UNIV - defaults)"

lemma \<UU>_I[simp, intro]: "p \<notin> defaults \<Longrightarrow> p \<in> \<UU>"
  unfolding \<UU>_def by auto

lemma \<UU>_E[elim!]: "p \<in> \<UU> \<Longrightarrow> (p \<notin> defaults \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding \<UU>_def by auto

end

instantiation sum :: (defaults, type) defaults
begin
definition defaults_sum where "defaults_sum = Inl ` defaults \<union> Inr ` defaults"
instance
proof qed
end

lemma case_sum_defaults[intro]:
  "p \<notin> defaults \<Longrightarrow> case_sum Inr Inl p \<notin> defaults"
  apply (cases p)
  apply (auto simp add: defaults_sum_def image_iff)
  done

lemma Inl_in_defaults[simp]:
  "Inl x \<in> (defaults :: ('a :: defaults + 'b :: defaults) set) \<longleftrightarrow> x \<in> defaults"
  by (auto simp add: defaults_sum_def)

lemma Inr_in_defaults[simp]:
  "Inr x \<in> (defaults :: ('a :: defaults + 'b :: defaults) set) \<longleftrightarrow> x \<in> defaults"
  by (auto simp add: defaults_sum_def)

lemma sum_in_defaults[intro]:
  "(isl x \<and> projl x \<in> defaults \<or> (\<not> isl x \<and> projr x \<in> defaults)) \<Longrightarrow> x \<in> (defaults :: ('a :: defaults + 'b :: defaults) set)"
  by (cases x; auto simp add: defaults_sum_def)

lemma Inl_not_in_defaults[dest]:
  "Inl x \<in> (defaults :: ('a :: defaults + 'b :: defaults) set) \<Longrightarrow> x \<in> defaults"
  by (auto simp add: defaults_sum_def)
lemma Inr_not_in_defaults[dest]:
  "Inr x \<in> (defaults :: ('a :: defaults + 'b :: defaults) set) \<Longrightarrow> x \<in> defaults"
  by auto


instantiation unit :: defaults
begin
definition defaults_unit where "defaults_unit = {()}"
instance
proof qed
end 

class no_defaults = defaults +
  assumes no_defaults: "defaults = {}"

subclass (in no_defaults) defaults.



setup_lifting type_definition_num0
instantiation num0 :: defaults begin
lift_definition defaults_num0 :: "num0 set" is "UNIV" .
instance ..
end
setup_lifting type_definition_num1
instantiation num1 :: defaults begin
lift_definition defaults_num1 :: "num1 set" is "{}" .
instance ..
end
setup_lifting type_definition_bit0
instantiation bit0 :: (finite) defaults begin
lift_definition defaults_bit0 :: "'a bit0 set" is "{}" by simp
instance ..
end
setup_lifting type_definition_bit1
instantiation bit1 :: (finite) defaults begin
lift_definition defaults_bit1 :: "'a bit1 set" is "{}" by simp
instance ..
end


end