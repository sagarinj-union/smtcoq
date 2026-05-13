Add Rec LoadPath "../../../../../src/" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "iso_icl073.smt2" "loops6/iso_icl073_cvc5.pf".
End Benchmark.
