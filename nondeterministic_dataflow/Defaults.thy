text \<open>defaultss setup\<close>

theory Defaults
  imports Main
begin

class defaults = fixes defaults :: "'a set"

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


end