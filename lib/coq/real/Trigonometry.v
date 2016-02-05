(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* This file is generated by Why3's Coq-realize driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require Reals.R_sqrt.
Require Reals.Rbasic_fun.
Require Reals.Rtrigo_def.
Require Reals.Rtrigo1.
Require Reals.Ratan.
Require BuiltIn.
Require real.Real.
Require real.Abs.
Require real.Square.

Require Import Reals.

(* Why3 comment *)
(* cos is replaced with (Reals.Rtrigo_def.cos x) by the coq driver *)

(* Why3 comment *)
(* sin is replaced with (Reals.Rtrigo_def.sin x) by the coq driver *)

(* Why3 goal *)
Lemma Pythagorean_identity : forall (x:R),
  (((Reals.RIneq.Rsqr (Reals.Rtrigo_def.cos x)) + (Reals.RIneq.Rsqr (Reals.Rtrigo_def.sin x)))%R = 1%R).
Proof.
intros x.
rewrite Rplus_comm.
apply sin2_cos2.
Qed.

(* Why3 goal *)
Lemma Cos_le_one : forall (x:R),
  ((Reals.Rbasic_fun.Rabs (Reals.Rtrigo_def.cos x)) <= 1%R)%R.
Proof.
intros x.
apply Abs.Abs_le.
apply COS_bound.
Qed.

(* Why3 goal *)
Lemma Sin_le_one : forall (x:R),
  ((Reals.Rbasic_fun.Rabs (Reals.Rtrigo_def.sin x)) <= 1%R)%R.
Proof.
intros x.
apply Abs.Abs_le.
apply SIN_bound.
Qed.

(* Why3 goal *)
Lemma Cos_0 : ((Reals.Rtrigo_def.cos 0%R) = 1%R).
Proof.
apply cos_0.
Qed.

(* Why3 goal *)
Lemma Sin_0 : ((Reals.Rtrigo_def.sin 0%R) = 0%R).
Proof.
apply sin_0.
Qed.

(* Why3 comment *)
(* pi is replaced with Reals.Rtrigo1.PI by the coq driver *)

(* Why3 goal *)
Lemma Pi_interval : ((314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)%R < Reals.Rtrigo1.PI)%R /\
  (Reals.Rtrigo1.PI < (314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038197 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)%R)%R.
Proof.
replace PI with (4 * (PI / 4))%R by field.
rewrite <- atan_1.
admit. (* to avoid a dependency on CoqInterval *)
(* split ; interval with (i_prec 680). *)
Admitted.

(* Why3 goal *)
Lemma Cos_pi : ((Reals.Rtrigo_def.cos Reals.Rtrigo1.PI) = (-1%R)%R).
Proof.
apply cos_PI.
Qed.

(* Why3 goal *)
Lemma Sin_pi : ((Reals.Rtrigo_def.sin Reals.Rtrigo1.PI) = 0%R).
Proof.
apply sin_PI.
Qed.

(* Why3 goal *)
Lemma Cos_pi2 : ((Reals.Rtrigo_def.cos ((05 / 10)%R * Reals.Rtrigo1.PI)%R) = 0%R).
Proof.
replace (5 / 10 * PI)%R with (PI / 2)%R by field.
apply cos_PI2.
Qed.

(* Why3 goal *)
Lemma Sin_pi2 : ((Reals.Rtrigo_def.sin ((05 / 10)%R * Reals.Rtrigo1.PI)%R) = 1%R).
Proof.
replace (5 / 10 * PI)%R with (PI / 2)%R by field.
apply sin_PI2.
Qed.

(* Why3 goal *)
Lemma Cos_plus_pi : forall (x:R),
  ((Reals.Rtrigo_def.cos (x + Reals.Rtrigo1.PI)%R) = (-(Reals.Rtrigo_def.cos x))%R).
Proof.
intros x.
apply neg_cos.
Qed.

(* Why3 goal *)
Lemma Sin_plus_pi : forall (x:R),
  ((Reals.Rtrigo_def.sin (x + Reals.Rtrigo1.PI)%R) = (-(Reals.Rtrigo_def.sin x))%R).
Proof.
intros x.
apply neg_sin.
Qed.

(* Why3 goal *)
Lemma Cos_plus_pi2 : forall (x:R),
  ((Reals.Rtrigo_def.cos (x + ((05 / 10)%R * Reals.Rtrigo1.PI)%R)%R) = (-(Reals.Rtrigo_def.sin x))%R).
Proof.
intros x.
rewrite cos_sin.
replace (PI / 2 + (x + 5 / 10 * PI))%R with (x + PI)%R by field.
apply neg_sin.
Qed.

(* Why3 goal *)
Lemma Sin_plus_pi2 : forall (x:R),
  ((Reals.Rtrigo_def.sin (x + ((05 / 10)%R * Reals.Rtrigo1.PI)%R)%R) = (Reals.Rtrigo_def.cos x)).
Proof.
intros x.
rewrite cos_sin.
apply f_equal.
field.
Qed.

(* Why3 goal *)
Lemma Cos_neg : forall (x:R),
  ((Reals.Rtrigo_def.cos (-x)%R) = (Reals.Rtrigo_def.cos x)).
Proof.
intros x.
apply cos_neg.
Qed.

(* Why3 goal *)
Lemma Sin_neg : forall (x:R),
  ((Reals.Rtrigo_def.sin (-x)%R) = (-(Reals.Rtrigo_def.sin x))%R).
Proof.
intros x.
apply sin_neg.
Qed.

(* Why3 goal *)
Lemma Cos_sum : forall (x:R) (y:R),
  ((Reals.Rtrigo_def.cos (x + y)%R) = (((Reals.Rtrigo_def.cos x) * (Reals.Rtrigo_def.cos y))%R - ((Reals.Rtrigo_def.sin x) * (Reals.Rtrigo_def.sin y))%R)%R).
Proof.
intros x y.
apply cos_plus.
Qed.

(* Why3 goal *)
Lemma Sin_sum : forall (x:R) (y:R),
  ((Reals.Rtrigo_def.sin (x + y)%R) = (((Reals.Rtrigo_def.sin x) * (Reals.Rtrigo_def.cos y))%R + ((Reals.Rtrigo_def.cos x) * (Reals.Rtrigo_def.sin y))%R)%R).
Proof.
intros x y.
apply sin_plus.
Qed.

(* Why3 goal *)
Lemma tan_def : forall (x:R),
  ((Reals.Rtrigo1.tan x) = ((Reals.Rtrigo_def.sin x) / (Reals.Rtrigo_def.cos x))%R).
Proof.
intros x.
apply eq_refl.
Qed.

(* Why3 comment *)
(* atan is replaced with (Reals.Ratan.atan x) by the coq driver *)

(* Why3 goal *)
Lemma Tan_atan : forall (x:R),
  ((Reals.Rtrigo1.tan (Reals.Ratan.atan x)) = x).
Proof.
intros x.
apply atan_right_inv.
Qed.

