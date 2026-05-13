Add Rec LoadPath "../../../../../src/" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "smt2080745738819601301.smt2" "smt2080745738819601301_veritnew.pf".
End Benchmark.
