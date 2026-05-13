Add Rec LoadPath "../../../../../src/" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "smt4057580428149921510.smt2" "smt4057580428149921510_cvc5.pf".
End Benchmark.
