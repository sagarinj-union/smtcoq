(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.9, replace it with:
     Require Import SMTCoq.
   *)
   Add Rec LoadPath "../../../src" as SMTCoq.

   Require Import SMTCoq.SMTCoq.
   Require Import Bool.
   
   Require Import ZArith.
   Require Import Int31.
   
   (*Local Open Scope int63_scope.*)
   Local Open Scope int31_scope.
   Local Open Scope array_scope.
   Local Open Scope int63_scope.
   
   Section CongP.
     Verit_Checker "congand.smt2" "congand.pf".
   End CongP.