Add Rec LoadPath "../../../../../src/" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "QF_UF_lifts.4.prop1_ab_reg_max.smt2" "QF_UF_lifts.4.prop1_ab_reg_max_cvc5.pf".
End Benchmark.
