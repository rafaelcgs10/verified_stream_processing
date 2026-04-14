theory Tmap_op

imports
  Dataplane.Timely_Infrastructure
begin

definition tmap_logic where
  "tmap_logic ip op f os = {|
      let result = map (\<lambda> (d, t). (f (de1 os d), t)) (input os ip) in
      let os =  trace (STR ''producing from tmap op'') (produces os (map (\<lambda> (d, t). (en2 os d, Cap t op)) result)) in
      let os = drop_caps os (concat (map (\<lambda> p. map (\<lambda> t. Cap t p) (ocaps os p)) Enum.enum)) in
      os\<lparr> input := (\<lambda> p. []) \<rparr>
    |}"
                                   
definition \<open>tmap_op ip op os f = builder_op False {|ip|} {|op|} os (tmap_logic ip op f)\<close>

lemma is_Inl_alt: "is_Inl x = (\<exists>x'. x = Inl x')"
  by(cases x; simp)

lemma is_Inr_alt: "is_Inr x \<Longrightarrow> \<exists>x'. x = Inr x'"
  by(cases x; simp)

lemma step_tmap_op_elim: 
  assumes "step io (tmap_op ip op os f) op'"
  obtains x where "io = Inp None (Inl (Inl x))" "op' = \<oslash>" |
        x where "io = Inp None (Inr x)" "op' = \<oslash>" |
        fa where "io = Inp None (Inl (Inr fa))" "\<not> initia os" "op' = tmap_op ip op (os\<lparr>front := fa, initia := True, nfron := True\<rparr>) f" |
        x where "io = Inp (Some ip) (Inl x)" "initia os" "op' = \<oslash>" |
        p d t where "io = Inp (Some ip) (Inr (d, t))" "initia os" "op' = tmap_op ip op (consumes os p t d) f" |
        os' st where "io = Out None (Inl (Inl st))" "initia os" "has_progress os" "(os', st) = obtain_progress os" "op' = tmap_op ip op os' f" |
        p x xs where "io = Out (Some op) (Inr x)" "initia os" "outpu os op = x # xs" "op' = tmap_op ip op (os\<lparr>outpu := (outpu os)(p := xs)\<rparr>) f" |
        os' where "io = Tau" "initia os" "\<exists>p. ocaps os p \<noteq> []" 
            "os' |\<in>| {|let result = map (\<lambda>(d, y). (f (de1 os d), y)) (input os ip); os = trace STR ''producing from tmap op'' (produces os (map (\<lambda>(d, t). (en2 os d, Cap t op)) result))
             in Let (drop_caps os (concat (map (\<lambda>p. map (\<lambda>t. Cap t p) (ocaps os p)) enum_class.enum))) (input_update (\<lambda>_ p. []))|}"
             "op' = tmap_op ip op os' f"
  using assms
  apply -
  unfolding tmap_op_def tmap_logic_def
  apply(drule step_builder_op_elim; (simp only: is_Inr_alt is_Inl_alt tmap_op_def[symmetric])?)
      apply (metis (lifting) is_Inl.simps(2) is_Inr.simps(2) reassoc.cases sum.sel(1))
     apply(blast)+
  done



end