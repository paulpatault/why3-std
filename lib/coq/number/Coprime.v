(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* This file is generated by Why3's Coq-realize driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.
Require int.Abs.
Require int.EuclideanDivision.
Require int.ComputerDivision.
Require number.Parity.
Require number.Divisibility.
Require number.Gcd.
Require number.Prime.

(* Why3 assumption *)
Definition coprime (a:Z) (b:Z): Prop := ((number.Gcd.gcd a b) = 1%Z).

Lemma coprime_is_Zrel_prime :
  forall a b, coprime a b <-> Znumtheory.rel_prime a b.
intros.
unfold coprime.
unfold Znumtheory.rel_prime.
split; intro h.
rewrite <- h; apply Znumtheory.Zgcd_is_gcd.
apply Znumtheory.Zis_gcd_gcd; auto with zarith.
Qed.

(* Why3 goal *)
Lemma prime_coprime : forall (p:Z), (number.Prime.prime p) <->
  ((2%Z <= p)%Z /\ forall (n:Z), ((1%Z <= n)%Z /\ (n < p)%Z) -> (coprime n
  p)).
intros p.
(*
Znumtheory.prime_intro:
  forall p : int,
  (1 < p)%Z ->
  (forall n : int, (1 <= n < p)%Z -> Znumtheory.rel_prime n p) ->
  Znumtheory.prime p
*)
rewrite Prime.prime_is_Zprime.
split.
intro h; inversion h; clear h.
split; auto with zarith.
intros n h.
rewrite coprime_is_Zrel_prime.
apply H0; auto.
intros (h1,h2).
constructor; auto with zarith.
intros n h.
rewrite <- coprime_is_Zrel_prime.
apply h2; auto.
Qed.

(* Why3 goal *)
Lemma Gauss : forall (a:Z) (b:Z) (c:Z), ((number.Divisibility.divides a
  (b * c)%Z) /\ (coprime a b)) -> (number.Divisibility.divides a c).
intros a b c (h1,h2).
apply Znumtheory.Gauss with b; auto.
rewrite <- coprime_is_Zrel_prime; auto.
Qed.

(* Why3 goal *)
Lemma Euclid : forall (p:Z) (a:Z) (b:Z), ((number.Prime.prime p) /\
  (number.Divisibility.divides p (a * b)%Z)) -> ((number.Divisibility.divides
  p a) \/ (number.Divisibility.divides p b)).
intros p a b (h1,h2).
apply Znumtheory.prime_mult; auto.
now rewrite <- Prime.prime_is_Zprime.
Qed.

(* Why3 goal *)
Lemma gcd_coprime : forall (a:Z) (b:Z) (c:Z), (coprime a b) ->
  ((number.Gcd.gcd a (b * c)%Z) = (number.Gcd.gcd a c)).
intros a b c h1.
apply Z.gcd_unique.
- apply Z.gcd_nonneg.
- apply Gcd.gcd_def1.
- apply Divisibility.divides_multl.
  apply Gcd.gcd_def2.
- intros q h2 h3.
  apply Gcd.gcd_def3.
  trivial.
  apply Gauss with b; split; auto.
  rewrite coprime_is_Zrel_prime.
  rewrite coprime_is_Zrel_prime in h1.
  now apply Znumtheory.rel_prime_div with (2:=h2).
Qed.

