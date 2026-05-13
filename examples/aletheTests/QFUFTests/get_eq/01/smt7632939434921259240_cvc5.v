Add Rec LoadPath "../../../../../src/" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "smt7632939434921259240.smt2" "smt7632939434921259240_cvc5.pf".
End Benchmark.
