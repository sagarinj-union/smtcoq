Add Rec LoadPath "../../../../../src/" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "PEQ020_size5.smt2" "PEQ020_size5_cvc5.pf".
End Benchmark.
