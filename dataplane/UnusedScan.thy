theory UnusedScan

imports
  "Examples/Label_Propagation/Label_Propagation_op_Correctness"
  "Examples/Batch_op_Correctness"
  "Examples/Increment_op_Correctness"
  "Examples/Collatz"
begin

unused_thms Operator - Label_Propagation_op_Correctness Batch_op_Correctness Increment_op_Correctness Collatz

end
