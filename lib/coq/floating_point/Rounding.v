(* This file is generated by Why3's Coq-realize driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.

(* This file is generated by Why3's Coq-realize driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.

(* Why3 assumption *)
Inductive mode :=
  | NearestTiesToEven : mode
  | ToZero : mode
  | Up : mode
  | Down : mode
  | NearestTiesToAway : mode.
Axiom mode_WhyType : WhyType mode.
Existing Instance mode_WhyType.

