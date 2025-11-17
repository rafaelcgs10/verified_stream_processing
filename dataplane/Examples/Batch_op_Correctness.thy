theory Batch_op_Correctness

imports
  Dataplane.Timely_Stream
  Source_op
  Ooo_Input_op
  Batch_op
begin

partial_function (llist) batch_fun_spec where
 "batch_fun_spec f lxs buf caps = (case lxs of
    LNil \<Rightarrow> (
    let compl_batches = (\<lambda> t. filter (\<lambda> (d, t'). t' = t) buf) in
    let outs = concat (map (\<lambda> t. map (\<lambda> x. (x, t)) (f (compl_batches t))) (rmdups {} caps)) in
    LCons outs LNil)
  | LCons (Data t d) lxs' \<Rightarrow> batch_fun_spec f lxs' (buf @ [(t, d)]) caps
  | LCons (Mint t) lxs' \<Rightarrow> batch_fun_spec f lxs' buf (caps @ [t])
  | LCons (Drop t) lxs' \<Rightarrow> (
    let below_caps = filter (\<lambda> t. \<not> frontier_less_equal (frontier (zmset_of (mset caps - {# t #}))) t) caps in
    let compl_batches = (\<lambda> t. filter (\<lambda> (d, t'). t' = t \<and> t' \<in> set below_caps) buf) in
    let outs = concat (map (\<lambda> t. map (\<lambda> x. (x, t)) (f (compl_batches t))) ((rmdups {} (map snd buf)))) in
    let buf' = filter (\<lambda> (d, t). t \<notin> set below_caps) buf in
    LCons outs (batch_fun_spec f lxs' buf' (remove_last t caps))))"



abbreviation "inp_top os inps \<equiv> map_op (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (case_option (Inl (0 :: 2)) (\<lambda> p. Inr (0, p))) (ooo_input_op os inps)"

abbreviation "b_op os f \<equiv> map_op (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (case_option (Inl (1 :: 2)) (\<lambda> p. Inr (1, p))) (batch_fun_op os f)"

abbreviation "inp_m_top os1 inps buf os2 f \<equiv>
   map_op (case_sum id id) (case_sum id id)
   (comp_op [Inr (0 :: 2, 0 :: 1) \<mapsto> Inr (1 :: 2, 0 :: 1)] buf (inp_top os1 inps) (b_op os2 f))"


term "inp_m_top os1 inps buf os2 f"

term "source_op (\<lambda> p. lconcat (batch_fun_spec f lxs buf caps))"

end
