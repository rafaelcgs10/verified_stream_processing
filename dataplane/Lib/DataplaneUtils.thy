theory DataplaneUtils

imports
  ZmsetUtils
begin

abbreviation "isr x \<equiv> \<not> (isl x)"

section \<open>General-Purpose Facts\<close>

text \<open>Congruence rules, lazy list shifts, and relational sets.\<close>

lemma ldropWhile_LConsD:
  "ldropWhile P lxs = LCons x lxs' \<Longrightarrow>
   \<not> P x"
  by (metis lhd_ldropWhile llist.disc(2) llist.sel(1) lnull_ldropWhile)

lemma arg_cong3:
  "a = b \<Longrightarrow> c = d \<Longrightarrow> e = g \<Longrightarrow> f a c e = f b d g"
  by fast

lemma arg_cong4:
  "a = b \<Longrightarrow> c = d \<Longrightarrow> e = g \<Longrightarrow> h = i \<Longrightarrow> f a c e h  = f b d g i"
  by fast

lemma arg_cong5:
  "a = b \<Longrightarrow> c = d \<Longrightarrow> e = g \<Longrightarrow> h = i \<Longrightarrow> j = k \<Longrightarrow> f a c e h j  = f b d g i k"
  by fast

lemma lmap_lshift[simp]:
  "lmap f (xs @@- lxs) = map f xs @@- lmap f lxs"
  by (metis lappend_llist_of lmap_lappend_distrib lmap_llist_of)

lemma lfinite_lshift[simp]:
  "lfinite (xs @@- lxs) = lfinite lxs"
  by (metis lappend_llist_of lfinite_lappend lfinite_llist_of)


lemma rel_set_image:
  "rel_set R (f ` A) B \<longleftrightarrow> rel_set (\<lambda> x. R (f x)) A B"
  "rel_set S A (g ` B) \<longleftrightarrow> rel_set (\<lambda> x y. S x (g y)) A B"
  unfolding rel_set_def
  apply auto
  done


section \<open>Buffer Heads and Enqueues\<close>

text \<open>How BHD and BENQ interact with appending.\<close>

lemma BAPPEND_BENQ_BHD':
  "buf1 p \<noteq> [] \<Longrightarrow> BHD p buf1 = x \<Longrightarrow> (BTL p buf1) >> (BENQ p x buf2) = buf1 >> buf2"
  unfolding BULK_BENQ_def BTL_def BENQ_def BHD_def by force

lemma BHD_map[simp]:
  "buf p \<noteq> [] \<Longrightarrow>
   BHD p (\<lambda>x. map f (buf x)) = f (BHD p buf)"
  unfolding BHD_def
  apply (auto simp add: hd_map)
  done


section \<open>Concatenations of Lazy Lists\<close>

text \<open>Heads and tails of concatenated, zipped lazy lists.\<close>






end

