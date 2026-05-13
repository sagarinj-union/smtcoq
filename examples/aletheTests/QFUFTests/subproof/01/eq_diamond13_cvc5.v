Add Rec LoadPath "../../../../../src/" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "eq_diamond13.smt2" "eq_diamond13_cvc5.pf".
End Benchmark.
