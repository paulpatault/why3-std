(* This file is generated by Why3's Coq-realize driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.

(* This file is generated by Why3's Coq-realize driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.

Require Import Exponentiation.

(* Why3 goal *)
Notation power := Zpower.

Lemma power_is_exponentiation :
  forall x n, (0 <= n)%Z -> power x n = Exponentiation.power _ 1%Z Zmult x n.
Proof.
intros x [|n|n] H.
easy.
2: now elim H.
unfold Exponentiation.power, power, Zpower_pos.
now rewrite iter_nat_of_P.
Qed.

(* Why3 goal *)
Lemma Power_0 : forall (x:Z), ((power x 0%Z) = 1%Z).
Proof.
intros x.
apply refl_equal.
Qed.

(* Why3 goal *)
Lemma Power_s : forall (x:Z) (n:Z), (0%Z <= n)%Z -> ((power x
  (n + 1%Z)%Z) = (x * (power x n))%Z).
Proof.
intros x n h1.
rewrite Zpower_exp.
change (power x 1) with (x * 1)%Z.
ring.
now apply Zle_ge.
easy.
Qed.

(* Why3 goal *)
Lemma Power_s_alt : forall (x:Z) (n:Z), (0%Z < n)%Z -> ((power x
  n) = (x * (power x (n - 1%Z)%Z))%Z).
intros x n h1.
rewrite <- Power_s.
f_equal; auto with zarith.
omega.
Qed.

(* Why3 goal *)
Lemma Power_1 : forall (x:Z), ((power x 1%Z) = x).
Proof.
exact Zmult_1_r.
Qed.

(* Why3 goal *)
Lemma Power_sum : forall (x:Z) (n:Z) (m:Z), (0%Z <= n)%Z -> ((0%Z <= m)%Z ->
  ((power x (n + m)%Z) = ((power x n) * (power x m))%Z)).
Proof.
intros x n m Hn Hm.
now apply Zpower_exp; apply Zle_ge.
Qed.

(* Why3 goal *)
Lemma Power_mult : forall (x:Z) (n:Z) (m:Z), (0%Z <= n)%Z -> ((0%Z <= m)%Z ->
  ((power x (n * m)%Z) = (power (power x n) m))).
Proof.
intros x n m Hn Hm.
rewrite 3!power_is_exponentiation ; auto with zarith.
apply Power_mult ; auto with zarith.
Qed.

(* Why3 goal *)
Lemma Power_mult2 : forall (x:Z) (y:Z) (n:Z), (0%Z <= n)%Z ->
  ((power (x * y)%Z n) = ((power x n) * (power y n))%Z).
Proof.
intros x y n Hn.
rewrite 3!power_is_exponentiation ; auto with zarith.
apply Power_mult2 ; auto with zarith.
Qed.

(* Why3 goal *)
Lemma Power_non_neg : forall (x:Z) (y:Z), ((0%Z <= x)%Z /\ (0%Z <= y)%Z) ->
  (0%Z <= (power x y))%Z.
intros x y (h1,h2).
now apply Z.pow_nonneg.
Qed.

Open Scope Z_scope.

(* Why3 goal *)
Lemma Power_monotonic : forall (x:Z) (n:Z) (m:Z), ((0%Z < x)%Z /\
  ((0%Z <= n)%Z /\ (n <= m)%Z)) -> ((power x n) <= (power x m))%Z.
intros.
apply Z.pow_le_mono_r; auto with zarith.
Qed.

