theory Increment_op

imports
  Dataplane.Timely_Builder_Op
begin

definition \<open>increment_op_logic ip op inc = (\<lambda>os. 
    if ocaps os op = [] then {||} else
    {|
      let result = map (\<lambda>(d, t). (d, t + inc)) (input os ip);
          os' = produces os (map (\<lambda>(d, t). (d, Cap t op)) result);
          os'' = drop_caps os' (map (\<lambda>t. Cap t op) (ocaps os' op))
      in os''\<lparr>input := (input os)(op := [])\<rparr>|})\<close>

definition \<open>increment_op ip op inc os = builder_op False {|ip|} {|op|} os (increment_op_logic ip op inc)\<close>

section \<open>Inputs of increment_op\<close>

lemma inputs_increment_op:
  assumes \<open>sub_op (Read p f) (increment_op ip op inc os) n\<close>
  shows \<open>p = Some ip\<close>
  using assms
proof (induct p \<open>increment_op ip op inc os\<close> arbitrary: os rule: sub_op_Read_induct)
  case (Read1 f p)
  then show ?case
    unfolding increment_op_def
    by (subst (asm) builder_op.code) (auto split: if_splits option.splits list.splits sum.splits)
next
  case (Read2 p p' f x d g)
  then show ?case
    unfolding increment_op_def
    by (subst (asm) builder_op.code) (auto split: if_splits option.splits list.splits sum.splits)
next
  case (Write p p' op' x d g)
  then show ?case
    unfolding increment_op_def
    by (subst (asm) builder_op.code) (auto split: if_splits option.splits list.splits sum.splits)
next
  case (Silent p op' d)
  then show ?case
    unfolding increment_op_def
    by (subst (asm) builder_op.code) (auto split: if_splits option.splits list.splits sum.splits)
next
  case (Choice p choices d g)
  then show ?case
    unfolding increment_op_def
    apply -
    apply (subst (asm) (2) builder_op.code)
    apply (auto 0 0 simp add: obtain_progress_def split: if_splits list.splits sum.splits prod.splits)
    apply (meson Suc_lessD lessI)+
    done
qed

lemma inputs_increment_op_le:
  \<open>inputs (increment_op ip op inc os) \<subseteq> {Some ip}\<close>
  by (auto dest!: inputs_sub_op_Read inputs_increment_op)


lemma inputs_increment_op_le_alt[dest!]:
  \<open>p \<in> inputs (increment_op ip op inc os) \<Longrightarrow> p = Some ip\<close>
  using set_mp[OF inputs_increment_op_le] by blast


section \<open>Introduction rules for increment_op steps\<close>

lemma step_increment_op_Read_Some[intro]:
  assumes \<open>io = Inp (Some ip) (Inr (d, t))\<close>
    and \<open>op' = increment_op ip op inc (consumes os ip t d)\<close>
  shows \<open>step io (increment_op ip op inc os) op'\<close>
  using assms unfolding increment_op_def by auto

lemma step_increment_op_Write_None[intro]:
  assumes \<open>io = Out None (Inl (Inl st))\<close>
    and \<open>(os', st) = obtain_progress os\<close>
    and \<open>op' = increment_op ip op inc os'\<close>
  shows \<open>step io (increment_op ip op inc os) op'\<close>
  using assms unfolding increment_op_def by auto

lemma step_increment_op_Write_None_alt[intro]:
  assumes \<open>io = Out None (Inl (Inl (snd (obtain_progress os))))\<close>
    and \<open>op' = increment_op ip op inc (fst (obtain_progress os))\<close>
  shows \<open>step io (increment_op ip op inc os) op'\<close>
  by (rule step_increment_op_Write_None[OF assms(1) _ assms(2)]) (rule prod.collapse)

lemma step_increment_op_Write_Some[intro]:
  assumes \<open>io = Out (Some op) (Inr x)\<close>
    and \<open>outpu os op = x # xs\<close>
    and \<open>op' = increment_op ip op inc (os\<lparr>outpu := (outpu os)(op := xs)\<rparr>)\<close>
  shows \<open>step io (increment_op ip op inc os) op'\<close>
  using assms unfolding increment_op_def by auto

lemma steps_increment_op_Write_Some[intro]:
  assumes \<open>outpu os op = xs @ ys\<close>
    and \<open>op' = increment_op ip op inc (os\<lparr>outpu := (outpu os)(op := ys)\<rparr>)\<close>
    and \<open>zs = map (\<lambda>x. Out (Some op) (Inr x)) xs\<close>
  shows \<open>steps zs (increment_op ip op inc os) op'\<close>
  using assms unfolding increment_op_def by auto

lemma steps_increment_op_Read_Some[intro]:
  assumes \<open>op' = increment_op ip op inc (fold (\<lambda>(d, t) os. consumes os ip t d) xs os)\<close>
    and \<open>ys = map (\<lambda>x. Inp (Some ip) (Inr x)) xs\<close>
  shows \<open>steps ys (increment_op ip op inc os) op'\<close>
  using assms unfolding increment_op_def by auto

lemma step_increment_op_Silent[intro]:
  assumes \<open>ocaps os op \<noteq> []\<close>
    and \<open>result = map (\<lambda>(d, t). (d, t + inc)) (input os ip)\<close>
    and \<open>os_produced = produces os (map (\<lambda>(d, t). (d, Cap t op)) result)\<close>
    and \<open>caps = map (\<lambda>t. Cap t op) (ocaps os_produced op)\<close>
    and \<open>os_dropped = drop_caps os_produced caps\<close>
    and \<open>os_next = os_dropped\<lparr>input := (input os_dropped)(op := [])\<rparr>\<close>
    and \<open>initia os\<close>
    and \<open>op' = increment_op ip op inc os_next\<close>
  shows \<open>step Tau (increment_op ip op inc os) op'\<close>
  using assms unfolding increment_op_def increment_op_logic_def by auto

end
