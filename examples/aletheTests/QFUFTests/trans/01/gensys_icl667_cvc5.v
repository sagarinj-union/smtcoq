Add Rec LoadPath "../../../../../src/" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "gensys_icl667.smt2" "gensys_icl667_cvc5.pf".
End Benchmark.
