theory Batch_op

imports
  Dataplane.Timely_Stream
  Source_op
begin

definition batch_op where
  "batch_op ips ops os comb logic = notifier_op ips ops os 
   (\<lambda> os compl_caps.
    let comb_caps = comb compl_caps in
    let compl_batches = (\<lambda> p t. map fst (filter (\<lambda> (d, t'). t' = t \<and> t \<in> set (comb_caps p)) (input os p))) in
    let os = os\<lparr> input := (\<lambda> p. filter (\<lambda> (d, t). t \<notin> set (comb_caps p)) (input os p)) \<rparr> in
    let outs_drops = logic compl_batches comb_caps in
    cimage (\<lambda> (outs, drops). drop_caps (produces os outs) drops) outs_drops)"

definition max_op where
  "max_op os = batch_op {|(1 :: 1)|} {|(1 :: 1)|} os id 
   (\<lambda> compl_batches caps. {| (map (\<lambda> t. (Max (set (compl_batches 1 t)), Cap t 1)) (caps 1), map (\<lambda> t. Cap t 1) (caps 1)) |})"

definition diff_op where
  "diff_op os f = batch_op {|(1 :: 2), 2|} {|1|} os 
   (\<lambda> compl_caps p. if p = 1 then filter (\<lambda> t. t \<in> set (compl_caps 2)) (compl_caps 1) else filter (\<lambda> t. t \<in> set (compl_caps 1)) (compl_caps 2))
   (\<lambda> compl_batches caps. {| (map (\<lambda> t. (mset (compl_batches 1 t), Cap t 1)) (caps 1), map (\<lambda> t. Cap t 1) (caps 1) @ map (\<lambda> t. Cap t 2) (caps 2)) |})"


end