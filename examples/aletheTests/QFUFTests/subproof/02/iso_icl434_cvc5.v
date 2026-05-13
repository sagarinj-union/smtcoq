Add Rec LoadPath "../../../../../src/" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "iso_icl434.smt2" "iso_icl434_cvc5.pf".
End Benchmark.
