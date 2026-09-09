theory Increment_Op

imports
  "../Timely/Builder_Op"
begin

definition \<open>incr_op_logic ip op inc = (\<lambda>os. 
    if ocaps os op = [] then {||} else
    {|
      let result = map (\<lambda>(d, t). (d, t + inc)) (input os ip);
          os' = produces os (map (\<lambda>(d, t). (d, Cap t op)) result);
          os'' = drop_caps os' (map (\<lambda>t. Cap t op) (ocaps os' op))
      in os''\<lparr>input := (input os)(op := [])\<rparr>|})\<close>

definition \<open>incr_op ip op inc os = builder_op False {|ip|} {|op|} os (incr_op_logic ip op inc)\<close>

lemma incr_op_logic_front_initia:
  "os' |\<in>| incr_op_logic ip op inc os \<Longrightarrow> front os' = front os"
  "os' |\<in>| incr_op_logic ip op inc os \<Longrightarrow> initia os' = initia os"
  unfolding incr_op_logic_def
  by (auto simp add: Let_def split: if_splits simp flip: cin.rep_eq)

lemma nop_leaf_incr_op:
  "nop_leaf None (incr_op ip op inc os)"
  unfolding incr_op_def
  by (rule nop_leaf_builder_op) simp

section \<open>Inputs of incr_op\<close>

lemma inputs_incr_op:
  assumes \<open>sub_op (Read p f) (incr_op ip op inc os) n\<close>
  shows \<open>p = Some ip\<close>
  using assms
proof (induct p \<open>incr_op ip op inc os\<close> arbitrary: os rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case
    unfolding incr_op_def
    by (subst (asm) builder_op.code) (auto split: if_splits option.splits list.splits sum.splits)
next
  case (Read2 p p' f x d g)
  then show ?case
    unfolding incr_op_def
    by (subst (asm) builder_op.code) (auto split: if_splits option.splits list.splits sum.splits)
next
  case (Write p p' op' x d g)
  then show ?case
    unfolding incr_op_def
    by (subst (asm) builder_op.code) (auto split: if_splits option.splits list.splits sum.splits)
next
  case (Silent p op' d)
  then show ?case
    unfolding incr_op_def
    by (subst (asm) builder_op.code) (auto split: if_splits option.splits list.splits sum.splits)
next
  case (Choice p choices d g)
  then show ?case
    unfolding incr_op_def
    apply -
    apply (subst (asm) (2) builder_op.code)
    apply (auto 0 0 simp add: obtain_progress_def
        simp del: incr_op_logic_front_initia
        operator_state_front_initia_upd_collapse
        split: if_splits list.splits sum.splits prod.splits)
    apply (meson Suc_lessD lessI)+
    done
qed

lemma inputs_incr_op_le:
  \<open>inputs (incr_op ip op inc os) \<subseteq> {Some ip}\<close>
  by (auto dest!: inputs_sub_op_Read inputs_incr_op)


lemma inputs_incr_op_le_alt[dest!]:
  \<open>p \<in> inputs (incr_op ip op inc os) \<Longrightarrow> p = Some ip\<close>
  using set_mp[OF inputs_incr_op_le] by blast


section \<open>Introduction rules for incr_op steps\<close>

lemma step_incr_op_Write_None[intro]:
  assumes \<open>io = Out None (Inl (Inl st))\<close>
    and \<open>(os', st) = obtain_progress os\<close>
    and \<open>op' = incr_op ip op inc os'\<close>
  shows \<open>step io (incr_op ip op inc os) op'\<close>
  using assms unfolding incr_op_def by auto

lemma step_incr_op_Write_None_alt[intro]:
  assumes \<open>io = Out None (Inl (Inl (snd (obtain_progress os))))\<close>
    and \<open>op' = incr_op ip op inc (fst (obtain_progress os))\<close>
  shows \<open>step io (incr_op ip op inc os) op'\<close>
  by (rule step_incr_op_Write_None[OF assms(1) _ assms(2)]) (rule prod.collapse)

lemma steps_incr_op_Write_Some[intro]:
  assumes \<open>outpu os op = xs @ ys\<close>
    and \<open>op' = incr_op ip op inc (os\<lparr>outpu := (outpu os)(op := ys)\<rparr>)\<close>
    and \<open>zs = map (\<lambda>x. Out (Some op) (Inr x)) xs\<close>
  shows \<open>steps zs (incr_op ip op inc os) op'\<close>
  using assms unfolding incr_op_def by auto

lemma steps_incr_op_Read_Some[intro]:
  assumes \<open>op' = incr_op ip op inc (fold (\<lambda>(d, t) os. consumes os ip t d) xs os)\<close>
    and \<open>ys = map (\<lambda>x. Inp (Some ip) (Inr x)) xs\<close>
  shows \<open>steps ys (incr_op ip op inc os) op'\<close>
  using assms unfolding incr_op_def by auto

lemma step_incr_op_Silent[intro]:
  assumes \<open>ocaps os op \<noteq> []\<close>
    and \<open>result = map (\<lambda>(d, t). (d, t + inc)) (input os ip)\<close>
    and \<open>os_produced = produces os (map (\<lambda>(d, t). (d, Cap t op)) result)\<close>
    and \<open>caps = map (\<lambda>t. Cap t op) (ocaps os_produced op)\<close>
    and \<open>os_dropped = drop_caps os_produced caps\<close>
    and \<open>os_next = os_dropped\<lparr>input := (input os_dropped)(op := [])\<rparr>\<close>
    and \<open>initia os\<close>
    and \<open>op' = incr_op ip op inc os_next\<close>
  shows \<open>step Tau (incr_op ip op inc os) op'\<close>
  unfolding assms(8) incr_op_def
  apply (rule step_builder_op_Silent)
     apply (rule refl)
    apply (rule assms(7))
   apply (unfold incr_op_logic_def)
   apply (simp add: assms(1-6))
  apply (simp add: assms(2-6) incr_op_logic_front_initia
      operator_state_front_initia_upd_collapse)
  done


end
