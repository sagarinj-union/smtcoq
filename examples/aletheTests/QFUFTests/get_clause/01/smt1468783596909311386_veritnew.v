Add Rec LoadPath "../../../../../src/" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "smt1468783596909311386.smt2" "smt1468783596909311386_veritnew.pf".
End Benchmark.
