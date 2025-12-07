theory Batch_op

imports
  Dataplane.Timely_Stream
  Dataplane.Timely_Infrastructure
  "../MyProduct_Instances"
begin

term "show_list show_nat"

abbreviation "show_myprod \<equiv> (\<lambda> s1 s2. show_prod s1 s2 o to_prod)"

definition batch_op where
  "batch_op ips ops comb os logic = notifier_op ips ops os 
   (\<lambda> os compl_caps.
    let comb_caps = comb compl_caps in
    if (\<forall> p. comb_caps p = []) then trace (STR ''No capabilities'') {||} else
    let compl_batches = (\<lambda> p t. map (de1 os o fst) (filter (\<lambda> (d, t'). t' = t \<and> t \<in> set (comb_caps p)) (input os p))) in
    let ts = (\<lambda> p. rmdups {} (map snd (filter (\<lambda> (d, t). t \<in> set (comb_caps p)) (input os p)))) in
    let os = os\<lparr> input := (\<lambda> p. filter (\<lambda> (d, t). t \<notin> set (comb_caps p)) (input os p)) \<rparr> in
    let outs_drops = logic compl_batches ts comb_caps in
    cimage (\<lambda> (outs, drops). drop_caps (produces os (map (\<lambda> (d, cap). (en2 os d, cap)) outs)) drops) outs_drops)"


definition batch_fun_op where
  "batch_fun_op os f = batch_op {|(1 :: 1)|} {|(1 :: 1)|} id os
   (\<lambda> compl_batches ts caps. {| (concat (map (\<lambda> t. map (\<lambda> x. (x, Cap t 1)) (f (compl_batches 1 t))) (ts 1)), map (\<lambda> t. Cap t 1) (caps 1)) |})"


(*
definition diff_op where
  "diff_op os = batch_op {|(1 :: 2), 2|} {|1|} 
   (\<lambda> compl_caps p. if p = 1 then filter (\<lambda> t. t \<in> set (compl_caps 2)) (compl_caps 1) else filter (\<lambda> t. t \<in> set (compl_caps 1)) (compl_caps 2))
   (os\<lparr> de1 := projl, en2 := Inr \<rparr>)
   (\<lambda> compl_batches ts caps. 
   {| (map (\<lambda> t. (mset (compl_batches 1 t) - mset (compl_batches 2 t), Cap t 1)) (rmdups {} (caps 1)),
       map (\<lambda> t. Cap t 1) (caps 1) @ map (\<lambda> t. Cap t 2) (caps 2)) |})"

definition batch_ty2_op where
  "batch_ty2_op ips ops comb os logic = notifier_op ips ops os 
   (\<lambda> os compl_caps.
    let comb_caps = comb compl_caps in
    let compl_batches = (\<lambda> p t. map (de1 os o fst) (filter (\<lambda> (d, t'). t' = t \<and> t \<in> set (comb_caps p)) (input os p))) in
    let os = os\<lparr> input := (\<lambda> p. filter (\<lambda> (d, t). t \<notin> set (comb_caps p)) (input os p)) \<rparr> in
    let outs_drops = logic compl_batches comb_caps in
    cimage (\<lambda> (outs, drops). drop_caps (produces os (map (\<lambda> (d, cap). (en2 os d, cap)) outs)) drops) outs_drops)"

 *)
end