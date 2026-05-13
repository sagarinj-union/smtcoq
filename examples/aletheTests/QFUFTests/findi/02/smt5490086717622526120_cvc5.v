Add Rec LoadPath "../../../../../src/" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "smt5490086717622526120.smt2" "smt5490086717622526120_cvc5.pf".
End Benchmark.
