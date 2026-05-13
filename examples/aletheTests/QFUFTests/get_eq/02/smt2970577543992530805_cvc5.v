Add Rec LoadPath "../../../../../src/" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "smt2970577543992530805.smt2" "smt2970577543992530805_cvc5.pf".
End Benchmark.
