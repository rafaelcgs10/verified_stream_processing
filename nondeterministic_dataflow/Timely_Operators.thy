theory Timely_Operators

imports
  Operator
  BNA_Operators
begin

datatype 'd flow = 
  Node "(nat, nat, 'd) op"
  | Seq "'d flow" "'d flow"
  | Par "'d flow" "'d flow"
  | Loop "'d flow"

term "Seq (Node ex1_op) (Node !)"

term "Seq
      (Node (map_op (case_sum ((*) 2) (\<lambda> x. 2 * x + 1)) id \<oslash>))
      (Node (map_op id (case_sum ((*) 2) (\<lambda> x. 2 * x + 1)) \<Lambda>))"


term "()"
term "\<lambda> x. if x = 1 then Some (Inl \<V>) else None"
   
end