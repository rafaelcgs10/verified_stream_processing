theory Lifted

imports
  BNA_Operators
  "table_1/B1"
  "table_1/B3"
  "table_1/B4"
  "table_1/B5"
  "table_1/B6"
  "table_1/R1"
  "table_1/R2"
  "HOL-ex.Sketch_and_Explore"
begin

no_notation Sublist.parallel (infixl "\<parallel>" 50)
no_notation nth (infixl "!" 100)

section \<open>Axioms for split_op surrounded by identities\<close>


section \<open>Properties of compositions and feedback surrounded by identities\<close>

lemma scomp_op_move_vdash:
  "\<stileturn>((op1 \<bullet> op2)\<turnstile>) \<approx> \<stileturn>op1 \<bullet> op2\<turnstile>"
  by (smt (verit, del_insts) bisim_wbisim B3.B3 scomp_op_id_id wbisim_scomp_op_cong wbisim_sym wbisim_trans)

lemma pcomp_op_move_vdash_left:
  "\<stileturn>(op1 \<parallel> op2) \<approx> \<stileturn>op1 \<parallel> \<stileturn>op2"
    by (smt (verit, del_insts) bisim_comp_op_cong bisim_scomp_op_cong bisim_trans bisim_wbisim choices_Choice_bisim pcomp_op_def B5 B6 wbisim_sym wbisim_trans)

lemma pcomp_op_move_vdash_right:
 "(op1 \<parallel> op2)\<turnstile> \<approx> op1\<turnstile> \<parallel> op2\<turnstile>"
    by (smt (verit, del_insts) bisim_comp_op_cong bisim_scomp_op_cong bisim_trans bisim_wbisim choices_Choice_bisim pcomp_op_def B5 B6 wbisim_sym wbisim_trans)

lemma pcomp_op_move_vdash:
  "\<stileturn>((op1 \<parallel> op2)\<turnstile>) \<approx> \<stileturn>(op1\<turnstile>) \<parallel> \<stileturn>(op2\<turnstile>)"
proof -
  have "(\<stileturn>(op1 \<parallel> op2))\<turnstile> \<approx> (\<stileturn>op1 \<parallel> \<stileturn>op2)\<turnstile>" (is "?a \<approx> ?b")
    using pcomp_op_move_vdash_left wbisim_refl wbisim_scomp_op_cong by blast
  moreover have "?b \<approx> \<stileturn>(op1\<turnstile>) \<parallel> \<stileturn>(op2\<turnstile>)" 
    using pcomp_op_move_vdash_right wbisim_refl wbisim_scomp_op_cong 
    by (smt (verit, best) bisim_wbisim pcomp_op_def B3.B3 wbisim_comp_op_cong wbisim_trans)
  ultimately show ?thesis
    by (meson bisim_wbisim B3.B3 wbisim_sym wbisim_trans)
qed

lemma feedback_op_move_left_vdash:
  assumes "Inr -` inputs op \<inter> defaults = {}"
    and "Inr -` outputs op \<inter> defaults = {}"
  shows  "\<stileturn>(op\<up>) \<approx> \<stileturn>op\<up>"
  using assms apply -
  apply (rule wbisim_trans[OF R1])
  apply (simp_all add: bisim_wbisim B6 wbisim_loop_op_cong wbisim_refl wbisim_scomp_op_cong)
  done

lemma feedback_op_move_right_vdash:
  assumes "Inr -` inputs op \<inter> defaults = {}"
    and "Inr -` outputs op \<inter> defaults = {}"
  shows  "(op\<up>)\<turnstile> \<approx> op\<turnstile>\<up>"
  using assms apply -
  apply (rule wbisim_trans[OF R2])
  apply (simp_all add: bisim_wbisim B6 wbisim_loop_op_cong wbisim_refl wbisim_scomp_op_cong)
  done

lemma feedback_op_move_vdash:
  assumes "Inr -` inputs op \<inter> defaults = {}"
    and "Inr -` outputs op \<inter> defaults = {}"
  shows  "(\<stileturn>(op\<up>))\<turnstile> \<approx> (\<stileturn>op)\<turnstile>\<up>"
  using assms apply -
  apply (rule wbisim_trans[OF wbisim_scomp_op_cong])
    apply (rule feedback_op_move_left_vdash)
     apply assumption+
   apply (rule wbisim_refl)
  apply (rule feedback_op_move_right_vdash)
   apply (auto simp add: scomp_op_def image_iff disjoint_iff op.set_map ran_def)
  done


section \<open>Axioms for aeq_op surrounded by identities\<close>

lemma aeq_vdash_absorb:
  "\<Q>' \<approx> (\<stileturn>(\<Q>'))"
  using aeq_id_absorb using bisim_wbisim B3.B3 wbisim_refl wbisim_scomp_op_cong wbisim_trans by blast

lemma aeq_double_vdash_absorb:
  "\<Q>' \<approx> (\<stileturn>(\<Q>'\<turnstile>))"
  using aeq_vdash_absorb using B4.B4_1 wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by blast

section \<open>Axioms for split_op surrounded by identities\<close>

lemma split'_id_absorb_right:
  \<open>\<Lambda>' \<approx> \<Lambda>'\<turnstile>\<close>
  using split_id_absorb_right bisim_wbisim B3.B3 wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by blast

lemma split'_id_absorb:
  \<open>\<Lambda>' \<approx> (\<stileturn>\<Lambda>')\<turnstile>\<close>
  using split'_id_absorb_right B4.B4_2 wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by blast

section \<open>Axioms for merge_op surrounded by identities\<close>

lemma merge'_id_absorb_left:
  \<open>\<V>' \<approx> \<stileturn>\<V>'\<close>
  using merge_id_absorb_left bisim_wbisim B3.B3 wbisim_refl wbisim_scomp_op_cong wbisim_trans by blast

lemma merge'_id_absorb:
  \<open>\<V>' \<approx> (\<stileturn>\<V>')\<turnstile>\<close>
  using merge'_id_absorb_left B4.B4_1 wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans by blast

section \<open>Axioms for sink surrounded by identities\<close>
lemma sink_vdash_absorb:
  "\<stileturn>((! :: ('m :: {countable, defaults}, 0, 'd) op)\<turnstile>) \<approx> !"
  sorry


section \<open>Typedef and lifting\<close>

context notes [[typedef_overloaded]] begin
typedef ('ip, 'op, 'd) operator = 
  "{op :: ('ip :: {countable,defaults}, 'op :: {countable,defaults}, 'd) op. \<exists> op' :: ('ip, 'op, 'd) op. op \<approx> \<stileturn>(op'\<turnstile>)}" morphisms from_operator top_operator
  apply (rule exI[of _ "\<stileturn>(\<oslash>\<turnstile>)"])
  apply simp
  apply (rule exI[of _ "\<stileturn>\<oslash>"])
  apply (smt (verit, ccfv_SIG) bisim_wbisim B3.B3 B4.B4_2 scomp_op_move_vdash wbisim_sym wbisim_trans)
  done

setup_lifting type_definition_operator

lemma intersect_empty_iff:
  "A \<inter> B = {} \<longleftrightarrow> (\<forall> x \<in> A. x \<notin> B \<and> (\<forall> x \<in> B. x \<notin> A))"
  by blast

(* FIXME: move me *)
lemma wbisim_double_vdash:
  assumes "op \<approx> \<stileturn>(op'\<turnstile>)"
  shows "op \<approx> \<stileturn>(op\<turnstile>)"
proof -
  have "\<stileturn>(op'\<turnstile>) \<approx> \<stileturn>\<stileturn>(op'\<turnstile>)" using B4.B4_2 wbisim_sym by blast
  also have "\<dots> \<approx> \<stileturn>\<stileturn>(op'\<turnstile>\<turnstile>)" by (simp add: B4.B4_1 wbisim_refl wbisim_scomp_op_cong wbisim_sym)
  also have "\<dots> \<approx> \<stileturn>(op\<turnstile>)" by (smt (verit, del_insts) assms bisim_wbisim B3.B3 wbisim_refl wbisim_scomp_op_cong wbisim_sym wbisim_trans)
  finally show ?thesis using assms wbisim_trans by blast
qed

no_notation scomp_op (infixl "\<bullet>" 65)
lift_definition 
  scomp_operator :: "('ip1 :: {countable,defaults}, 'op1  :: {countable,defaults}, 'd) operator \<Rightarrow> ('op1, 'op2  :: {countable,defaults}, 'd) operator \<Rightarrow>
  ('ip1, 'op2, 'd) operator" (infixl "\<bullet>" 65) is "scomp_op"
  apply (clarsimp simp add: intersect_empty_iff)
  subgoal for op1 op2 op1' op2'
    apply (intro exI[of _ "scomp_op (op1'\<turnstile>) (\<stileturn>op2')"])
      apply (rule wbisim_trans)
       apply (rule wbisim_scomp_op_cong)
        apply assumption+
      apply (rule wbisim_trans[rotated])
       apply (rule wbisim_sym)
     apply (rule scomp_op_move_vdash)
    using bisim_wbisim B3.B3 wbisim_refl wbisim_scomp_op_cong wbisim_sym apply blast
    done
  done

(* FIXME: move me *)
lemma wbisim_pcomp_op_cong:
  "op1 \<approx> op1' \<Longrightarrow>
   op2 \<approx> op2' \<Longrightarrow>
   op1 \<parallel> op2 \<approx> op1' \<parallel> op2'"
  unfolding pcomp_op_def using wbisim_comp_op_cong wbisim_map_op by blast

no_notation pcomp_op (infixl "\<parallel>" 64)
lift_definition 
  pcomp_operator :: "('ip1, 'op1, 'd) operator \<Rightarrow> ('ip2, 'op2, 'd) operator \<Rightarrow>
  ('ip1  :: {countable,defaults} + 'ip2 :: {countable,defaults}, 'op1 :: {countable,defaults} + 'op2 :: {countable,defaults}, 'd) operator" (infixl "\<parallel>" 64) is "pcomp_op"
  apply (clarsimp simp add: intersect_empty_iff)
  subgoal for op1 op2 op1' op2'
    apply (intro exI[of _ "pcomp_op op1' op2'"])
    apply (rule wbisim_trans)
       apply (rule wbisim_pcomp_op_cong)
      apply assumption+
    apply (smt (verit, best) pcomp_op_move_vdash_left pcomp_op_move_vdash_right scomp_op_id_id wbisim_scomp_op_cong wbisim_sym wbisim_trans)
    done
  done

lemma feedback_op_move_vdash_alt:
  assumes "Inr -` inputs op \<inter> defaults = {}"
    and "Inr -` outputs op \<inter> defaults = {}"
  shows  "\<stileturn>((op\<up>)\<turnstile>) \<approx> (\<stileturn>op)\<turnstile>\<up>"
  by (smt (verit) assms(1) assms(2) bisim_wbisim feedback_op_move_vdash B3.B3 wbisim_sym wbisim_trans)

lift_definition
  feedback_operator :: 
  "('ip :: {countable, defaults} + 'p :: {countable, defaults}, 'op :: {countable, defaults} + 'p, 'd) operator \<Rightarrow> ('ip, 'op, 'd) operator" ( "_ \<up>" [66] 65) is feedback_op
  apply safe
  subgoal for op op'
    apply (rule exI[of _ "\<stileturn>(op\<turnstile>) \<up>"])
    apply (rule wbisim_trans)
     apply (rule wbisim_loop_op_cong)
    apply assumption
    apply (rule wbisim_trans[rotated])
     apply (rule wbisim_sym)
    apply (rule feedback_op_move_vdash_alt)
       apply (auto simp add: scomp_op_def image_iff disjoint_iff op.set_map ran_def)[1]
       apply (auto simp add: scomp_op_def image_iff disjoint_iff op.set_map ran_def)[1]
    apply (smt (verit, ccfv_threshold) bisim_wbisim B3.B3 wbisim_double_vdash wbisim_loop_op_cong wbisim_sym wbisim_trans)
    done
  done
no_notation feedback_op ( "_ \<up>" [66] 65)

lemma
  "inj_on f \<UU> \<Longrightarrow>
   (\<forall> p \<in> \<UU>. f p \<notin> defaults) \<Longrightarrow>
   (\<forall> p \<in> defaults. f p \<in> defaults) \<Longrightarrow>
   p \<notin> defaults \<Longrightarrow>
   BENQ p x (buf \<circ> f) = (BENQ (f p) x buf) o f"
  nitpick [eval = " BENQ p x (  buf \<circ> f)" "(BENQ (f p) x buf) o f"]
  oops

lemma map_op_vdash_gen:
  "inj_on f (inputs op) \<Longrightarrow>
   inj_on g (outputs op) \<Longrightarrow>
   \<forall>x. f x \<in> defaults \<longrightarrow> x \<in> defaults \<Longrightarrow>
   \<forall>x. g x \<in> defaults \<longrightarrow> x \<in> defaults \<Longrightarrow>
   map_op f g (map_op projl projr (comp_op Some (B o f) (id_op (A o f)) (map_op projl projr (comp_op Some (C o g) op (id_op (D o g)))))) ~
   map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D))))"
proof (coinduction arbitrary: A B C D op rule: bisim_coinduct_upto'')
  case SIM1
  then show ?case 
    apply -
    explore (auto 0 0 elim!: step_map_op_elim step_comp_op_elim step_id_op_cases split: if_splits; hypsubst_thin?)
  proof -
    have "\<exists>op2'. step (Inp (f p) x) (map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D))))) op2' \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>A B C D op. op1xx = map_op f g (map_op projl projr (comp_op Some (B \<circ> f) (id_op (A \<circ> f)) (map_op projl projr (comp_op Some (C \<circ> g) op (id_op (D \<circ> g)))))) \<and> op2xx = map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D)))) \<and> inj_on f (inputs op) \<and> inj_on g (outputs op)) (map_op f g (map_op projl projr (comp_op Some (B \<circ> f) (id_op (BENQ p x (A \<circ> f))) (map_op projl projr (comp_op Some (C \<circ> g) op (id_op (D \<circ> g))))))) op2'"
      if "inj_on f (inputs op)"
        and "inj_on g (outputs op)"
        and "\<forall>x. f x \<in> defaults \<longrightarrow> x \<in> defaults"
        and "\<forall>x. g x \<in> defaults \<longrightarrow> x \<in> defaults"
        and "p \<notin> defaults"
      for p :: 'a
        and x :: 'd
      using that 
      apply -
      apply (intro conjI[rotated] exI)
       defer
         apply (rule step_map_op)
      apply (rule step_comp_op_L_Inp)
      apply (rule step_id_op_Read[where p="f p"])
             apply blast
            apply (rule refl)+
       apply blast
      apply (rule bc_base)
      apply (intro exI conjI)
      defer
      apply (rule refl)+
        apply blast
      apply blast
(* 
      apply (rule bc_bisim)


end
    moreover have "\<exists>op2'. step (Out (g p) (BHD p (D \<circ> g))) (map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D))))) op2' \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>A B C D op. op1xx = map_op f g (map_op projl projr (comp_op Some (B \<circ> f) (id_op (A \<circ> f)) (map_op projl projr (comp_op Some (C \<circ> g) op (id_op (D \<circ> g)))))) \<and> op2xx = map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D)))) \<and> inj_on f (inputs op) \<and> inj_on g (outputs op)) (map_op f g (map_op projl projr (comp_op Some (B \<circ> f) (id_op (A \<circ> f)) (map_op projl projr (comp_op Some (C \<circ> g) op (id_op (BTL p (D \<circ> g)))))))) op2'"
      if "inj_on f (inputs op)"
        and "inj_on g (outputs op)"
        and "\<forall>x. f x \<in> defaults \<longrightarrow> x \<in> defaults"
        and "\<forall>x. g x \<in> defaults \<longrightarrow> x \<in> defaults"
        and "p \<notin> defaults"
        and "D (g p) \<noteq> []"
      for p :: 'c
      using that sorry
    moreover have "\<exists>op2'. step Tau (map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D))))) op2' \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>A B C D op. op1xx = map_op f g (map_op projl projr (comp_op Some (B \<circ> f) (id_op (A \<circ> f)) (map_op projl projr (comp_op Some (C \<circ> g) op (id_op (D \<circ> g)))))) \<and> op2xx = map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D)))) \<and> inj_on f (inputs op) \<and> inj_on g (outputs op)) (map_op f g (map_op projl projr (comp_op Some (BENQ pa (BHD pa (A \<circ> f)) (B \<circ> f)) (id_op (BTL pa (A \<circ> f))) (map_op projl projr (comp_op Some (C \<circ> g) op (id_op (D \<circ> g))))))) op2'"
      if "inj_on f (inputs op)"
        and "inj_on g (outputs op)"
        and "\<forall>x. f x \<in> defaults \<longrightarrow> x \<in> defaults"
        and "\<forall>x. g x \<in> defaults \<longrightarrow> x \<in> defaults"
        and "pa \<notin> defaults"
        and "A (f pa) \<noteq> []"
      for pa :: 'a
      using that sorry
    moreover have "\<exists>op2'. step Tau (map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D))))) op2' \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>A B C D op. op1xx = map_op f g (map_op projl projr (comp_op Some (B \<circ> f) (id_op (A \<circ> f)) (map_op projl projr (comp_op Some (C \<circ> g) op (id_op (D \<circ> g)))))) \<and> op2xx = map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D)))) \<and> inj_on f (inputs op) \<and> inj_on g (outputs op)) (map_op f g (map_op projl projr (comp_op Some (BTL p (B \<circ> f)) (id_op (A \<circ> f)) (map_op projl projr (comp_op Some (C \<circ> g) op1' (id_op (D \<circ> g))))))) op2'"
      if "inj_on f (inputs op)"
        and "inj_on g (outputs op)"
        and "\<forall>x. f x \<in> defaults \<longrightarrow> x \<in> defaults"
        and "\<forall>x. g x \<in> defaults \<longrightarrow> x \<in> defaults"
        and "B (f p) \<noteq> []"
        and "step (Inp p (BHD p (B \<circ> f))) op op1'"
      for p :: 'a
        and op1' :: "('a, 'c, 'd) op"
      using that sorry
    moreover have "\<exists>op2'. step Tau (map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D))))) op2' \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>A B C D op. op1xx = map_op f g (map_op projl projr (comp_op Some (B \<circ> f) (id_op (A \<circ> f)) (map_op projl projr (comp_op Some (C \<circ> g) op (id_op (D \<circ> g)))))) \<and> op2xx = map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D)))) \<and> inj_on f (inputs op) \<and> inj_on g (outputs op)) (map_op f g (map_op projl projr (comp_op Some (B \<circ> f) (id_op (A \<circ> f)) (map_op projl projr (comp_op Some (BENQ q xa (C \<circ> g)) op1' (id_op (D \<circ> g))))))) op2'"
      if "inj_on f (inputs op)"
        and "inj_on g (outputs op)"
        and "\<forall>x. f x \<in> defaults \<longrightarrow> x \<in> defaults"
        and "\<forall>x. g x \<in> defaults \<longrightarrow> x \<in> defaults"
        and "step (Out q xa) op op1'"
      for xa :: 'd
        and op1' :: "('a, 'c, 'd) op"
        and q :: 'c
      using that sorry
    moreover have "\<exists>op2'. step Tau (map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D))))) op2' \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>A B C D op. op1xx = map_op f g (map_op projl projr (comp_op Some (B \<circ> f) (id_op (A \<circ> f)) (map_op projl projr (comp_op Some (C \<circ> g) op (id_op (D \<circ> g)))))) \<and> op2xx = map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D)))) \<and> inj_on f (inputs op) \<and> inj_on g (outputs op)) (map_op f g (map_op projl projr (comp_op Some (B \<circ> f) (id_op (A \<circ> f)) (map_op projl projr (comp_op Some (BTL pb (C \<circ> g)) op (id_op (BENQ pb (BHD pb (C \<circ> g)) (D \<circ> g)))))))) op2'"
      if "inj_on f (inputs op)"
        and "inj_on g (outputs op)"
        and "\<forall>x. f x \<in> defaults \<longrightarrow> x \<in> defaults"
        and "\<forall>x. g x \<in> defaults \<longrightarrow> x \<in> defaults"
        and "C (g pb) \<noteq> []"
        and "pb \<notin> defaults"
      for pb :: 'c
      using that sorry
    moreover have "\<exists>op2'. step Tau (map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D))))) op2' \<and> bisim_cong (\<lambda>op1xx op2xx. \<exists>A B C D op. op1xx = map_op f g (map_op projl projr (comp_op Some (B \<circ> f) (id_op (A \<circ> f)) (map_op projl projr (comp_op Some (C \<circ> g) op (id_op (D \<circ> g)))))) \<and> op2xx = map_op projl projr (comp_op Some B (id_op A) (map_op projl projr (comp_op Some C (map_op f g op) (id_op D)))) \<and> inj_on f (inputs op) \<and> inj_on g (outputs op)) (map_op f g (map_op projl projr (comp_op Some (B \<circ> f) (id_op (A \<circ> f)) (map_op projl projr (comp_op Some (C \<circ> g) op1' (id_op (D \<circ> g))))))) op2'"
      if "inj_on f (inputs op)"
        and "inj_on g (outputs op)"
        and "\<forall>x. f x \<in> defaults \<longrightarrow> x \<in> defaults"
        and "\<forall>x. g x \<in> defaults \<longrightarrow> x \<in> defaults"
        and "step Tau op op1'"
      for op1' :: "('a, 'c, 'd) op"
      using that sorry
    ultimately show ?thesis
      by (auto 0 0 elim !: step_map_op_elim step_comp_op_elim step_id_op_cases split: if_splits ; hypsubst_thin ?)
  qed
 
end
next
  case SIM2
  then show ?case sorry
qed

 *)
      oops

lemma map_op_vdash:
  "inj_on f (inputs op) \<Longrightarrow>
   inj_on g (outputs op) \<Longrightarrow>
   (\<forall> x. f x \<in> defaults \<longrightarrow> x \<in> defaults) \<Longrightarrow>
   (\<forall> x. g x \<in> defaults \<longrightarrow> x \<in> defaults) \<Longrightarrow>
   map_op f g (\<stileturn>(op\<turnstile>)) \<approx> \<stileturn>(map_op f g op\<turnstile>)"
  oops
(*   unfolding scomp_op_def using map_op_vdash_gen[of f op g "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []", unfolded comp_def, simplified] by auto 
 *)


lift_definition
  map_operator :: "('a :: {countable,defaults} \<Rightarrow> 'b :: {countable,defaults}) \<Rightarrow> ('c :: {countable,defaults} \<Rightarrow> 'd :: {countable,defaults}) \<Rightarrow> ('a, 'c, 'e) operator \<Rightarrow> ('b, 'd, 'e) operator" is 
  "\<lambda> f g op. (if inj f \<and> inj g \<and> (\<forall> x. f x \<in> defaults \<longrightarrow> x \<in> defaults) \<and> (\<forall> x. g x \<in> defaults \<longrightarrow> x \<in> defaults) then map_op f g op else \<stileturn>(end_op\<turnstile>))"

(*   "\<lambda> f g op. (if inj_on f (inputs op) \<and> inj_on g (outputs op) \<and> (\<forall> x. f x \<in> defaults \<longrightarrow> x \<in> defaults) \<and> (\<forall> x. g x \<in> defaults \<longrightarrow> x \<in> defaults) then map_op f g op else \<stileturn>(end_op\<turnstile>))"
 *)
  apply (simp add: op.set_map split: if_splits)
  apply (intro allI conjI impI)
  subgoal for f g op
    apply safe
    subgoal for op'
      apply (rule exI[of _ "map_op f g op"])
sorry
(*       apply (rule wbisim_trans[OF _ map_op_vdash])
      using wbisim_double_vdash wbisim_map_op apply blast
      apply assumption+ done *)
      
    done
  subgoal
    sorry
  done

no_notation id_empty_op ("\<I>")
lift_definition id_empty_operator :: "('a :: {countable, defaults}, 'a, 'b) operator"  ("\<I>") is id_empty_op
  subgoal 
    apply (rule exI[of _ id_empty_op])
    unfolding scomp_op_def
    apply (rule wbisim_sym)
    using id_id_gen[of "\<lambda> _. []" "\<lambda> _. []" "\<lambda> _. []", simplified] apply (smt (verit) BULK_BENQ_left_neutral id_id_gen wbisim_comp_op_cong wbisim_map_op wbisim_sym wbisim_trans) 
    done
  done

no_notation wbisim (infix "\<approx>"40)
lift_definition wbisim_operator :: "('a :: {countable, defaults}, 'b :: {countable, defaults}, 'c) operator \<Rightarrow> ('a, 'b, 'c) operator \<Rightarrow> bool" (infix "\<approx>"40) is wbisim.



no_notation aeq_empty_op ("\<Q>")
lift_definition aeq_empty_operator :: "('a :: {countable, defaults} + 'a, 'a, 'b) operator"  ("\<Q>") is "aeq_empty_op\<turnstile>"
  apply (rule exI[of _ "aeq_empty_op"])
  using aeq_vdash_absorb apply blast
  done

no_notation transp_empty_op ("\<X>")
lift_definition transp_empty_operator :: "('a :: {countable, defaults} + 'b :: {countable, defaults}, 'b + 'a, 'd) operator"  ("\<X>") is "transp_empty_op"
  apply (rule exI[of _ "transp_empty_op"])
  using bisim_wbisim B3.B3 transp_id_absorb wbisim_trans apply blast
  done

abbreviation "sink_op_0 :: ('a :: {countable, defaults}, 0, 'c) op \<equiv> sink_op"

no_notation sink_op ("!")
lift_definition sink_op_0_operator :: "('a :: {countable, defaults}, 0, 'b) operator"  ("!") is "sink_op_0"
  apply (rule exI[of _ "sink_op"])
  using sink_vdash_absorb wbisim_sym apply blast
  done


lemma wbisim_vdash_inputs_no_defaults[dest]:
  "wbisim op1 (\<stileturn>(op'\<turnstile>)) \<Longrightarrow> Inr -` inputs op1 \<inter> defaults = {}"
  apply (drule wbisim_double_vdash)
  apply (auto simp add: scomp_op_def image_iff disjoint_iff op.set_map ran_def dest!: wbisim_inputs)[1]
  done

lemma wbisim_vdash_outputs_no_defaults[dest]:
  "wbisim op1 (\<stileturn>(op'\<turnstile>)) \<Longrightarrow> Inr -` outputs op1 \<inter> defaults = {}"
  apply (drule wbisim_double_vdash)
  apply (auto simp add: scomp_op_def image_iff disjoint_iff op.set_map ran_def dest!: wbisim_outputs)[1]
  done


lemma inj_on_case_sum_Inr_Inl_inputs_scomp_op[simp]:
  "inj_on (case_sum Inr Inl) (inputs (scomp_op op1 op2))"
  unfolding scomp_op_def
  apply (metis (mono_tags, lifting) Inl_Inr_False inj_onI old.sum.inject(2) sum.case_eq_if sum.expand sum.inject(1))
  done

lemma reassoc_defaults[simp]:
  "reassoc (x :: ('a :: {countable,defaults} + 'b :: {countable,defaults}) + 'c :: {countable,defaults}) \<in> defaults \<longleftrightarrow> x \<in> defaults"
  by (cases x; simp split: sum.splits)


end
end