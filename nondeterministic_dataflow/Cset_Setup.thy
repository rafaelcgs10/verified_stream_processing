text \<open>cset setup\<close>

theory Cset_Setup
imports
  "HOL-Library.Countable_Set_Type"
  Defaults
begin

section \<open>cset Syntax\<close>
syntax
  "_insert_fset"     :: "args => 'a cset"  ("{|(_)|}")

notation cempty ("{||}")

translations
  "{|x, xs|}" == "CONST cinsert x {|xs|}"
  "{|x|}"     == "CONST csingle x"

abbreviation cmember :: "'a \<Rightarrow> 'a cset \<Rightarrow> bool" (infix "|\<in>|" 50) where
  "x |\<in>| X \<equiv> cin x X"

abbreviation cim :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a cset \<Rightarrow> 'b cset" (infix "|`|" 50) where
  "f |`| X \<equiv> cimage f X"

section \<open>cset lifts\<close>
context includes cset.lifting begin
lift_definition cUNIV :: "'m :: countable cset" is UNIV by auto
lift_definition cproduct :: "'a cset \<Rightarrow> 'b cset \<Rightarrow> ('a \<times> 'b) cset" is "(\<times>)" by auto
lift_definition cfilter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a cset \<Rightarrow> 'a cset" is Set.filter by (simp add: Set.filter_def)
lift_definition c\<UU> :: "('m :: {countable, defaults}) cset" is "\<UU>" by auto

end

declare cBall.rep_eq[simp] cinsert.rep_eq[simp] bot_cset.rep_eq[simp] sup_cset.rep_eq[simp] cimage.rep_eq[simp] cUnion.rep_eq[simp] rel_cset.rep_eq[simp]
  cfilter.rep_eq[simp] c\<UU>.rep_eq[simp]

declare ranI[simp]

lemma cfilter_eq[simp]:
  "cfilter P A = B \<longleftrightarrow>
   Set.filter P (cset.rcset A) = (cset.rcset B)"
  by (auto simp add: cin.rep_eq)

lemma cin_cfilter[simp]:
  "x |\<in>| cfilter P A \<longleftrightarrow> x |\<in>| A \<and> P x"
  by (metis cfilter.rep_eq cin.rep_eq member_filter)


lemma cin_cimage_cfilter[simp]:
  "x |\<in>| cimage f (cfilter P A) \<longleftrightarrow> (\<exists> y. y |\<in>| A \<and> P y \<and> x = f y)"
  by auto

lemma cUnion_cempty[simp]:
  "cUnion {||} = {||}"
  using cUN_empty by auto

lemma cfilter_cempty[simp]:
  "cfilter P {||} = {||}"
  by auto

lemma cfilter_cfilter[simp]:
  "cfilter P (cfilter P S) = cfilter P S"
  by force

lemma cUnion_cinsert[simp]:
  "cUnion (cinsert x A) = cUn x (cUnion A)"
  apply (subst (3 8) cset.map_id[symmetric])
  apply (metis cUN_cinsert eq_id_iff)
  done

end