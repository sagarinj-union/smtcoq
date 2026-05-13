Add Rec LoadPath "../../../../../src/" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "iso_icl902.smt2" "iso_icl902_cvc5.pf".
End Benchmark.
