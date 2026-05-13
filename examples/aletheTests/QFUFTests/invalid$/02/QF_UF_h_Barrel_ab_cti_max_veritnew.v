Add Rec LoadPath "../../../../../src/" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "QF_UF_h_Barrel_ab_cti_max.smt2" "QF_UF_h_Barrel_ab_cti_max_veritnew.pf".
End Benchmark.
