(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.
Require int.Abs.
Require int.EuclideanDivision.

(* Why3 assumption *)
Definition unit  := unit.

Parameter fib: Z -> Z.

Axiom fib0 : ((fib 0%Z) = 0%Z).

Axiom fib1 : ((fib 1%Z) = 1%Z).

Axiom fibn : forall (n:Z), (2%Z <= n)%Z ->
  ((fib n) = ((fib (n - 1%Z)%Z) + (fib (n - 2%Z)%Z))%Z).

(* Why3 assumption *)
Inductive t  :=
  | mk_t : Z -> Z -> Z -> Z -> t .
Axiom t_WhyType : WhyType t.
Existing Instance t_WhyType.

(* Why3 assumption *)
Definition a22(v:t): Z := match v with
  | (mk_t x x1 x2 x3) => x3
  end.

(* Why3 assumption *)
Definition a21(v:t): Z := match v with
  | (mk_t x x1 x2 x3) => x2
  end.

(* Why3 assumption *)
Definition a12(v:t): Z := match v with
  | (mk_t x x1 x2 x3) => x1
  end.

(* Why3 assumption *)
Definition a11(v:t): Z := match v with
  | (mk_t x x1 x2 x3) => x
  end.

(* Why3 assumption *)
Definition mult(x:t) (y:t): t :=
  (mk_t (((a11 x) * (a11 y))%Z + ((a12 x) * (a21 y))%Z)%Z
  (((a11 x) * (a12 y))%Z + ((a12 x) * (a22 y))%Z)%Z
  (((a21 x) * (a11 y))%Z + ((a22 x) * (a21 y))%Z)%Z
  (((a21 x) * (a12 y))%Z + ((a22 x) * (a22 y))%Z)%Z).

Axiom Assoc : forall (x:t) (y:t) (z:t), ((mult (mult x y) z) = (mult x
  (mult y z))).

Axiom Unit_def_l : forall (x:t), ((mult (mk_t 1%Z 0%Z 0%Z 1%Z) x) = x).

Axiom Unit_def_r : forall (x:t), ((mult x (mk_t 1%Z 0%Z 0%Z 1%Z)) = x).

Axiom Comm : forall (x:t) (y:t), ((mult x y) = (mult y x)).

Parameter power: t -> Z -> t.

Axiom Power_0 : forall (x:t), ((power x 0%Z) = (mk_t 1%Z 0%Z 0%Z 1%Z)).

Axiom Power_s : forall (x:t) (n:Z), (0%Z <= n)%Z -> ((power x
  (n + 1%Z)%Z) = (mult x (power x n))).

Axiom Power_s_alt : forall (x:t) (n:Z), (0%Z < n)%Z -> ((power x n) = (mult x
  (power x (n - 1%Z)%Z))).

Axiom Power_1 : forall (x:t), ((power x 1%Z) = x).

Axiom Power_sum : forall (x:t) (n:Z) (m:Z), (0%Z <= n)%Z -> ((0%Z <= m)%Z ->
  ((power x (n + m)%Z) = (mult (power x n) (power x m)))).

Axiom Power_mult : forall (x:t) (n:Z) (m:Z), (0%Z <= n)%Z -> ((0%Z <= m)%Z ->
  ((power x (n * m)%Z) = (power (power x n) m))).

Axiom Power_mult2 : forall (x:t) (y:t) (n:Z), (0%Z <= n)%Z -> ((power (mult x
  y) n) = (mult (power x n) (power y n))).

(* Why3 goal *)
Theorem WP_parameter_logfib : forall (n:Z), (0%Z <= n)%Z -> ((~ (n = 0%Z)) ->
  ((0%Z <= (int.EuclideanDivision.div n 2%Z))%Z -> forall (result:Z)
  (result1:Z), ((power (mk_t 1%Z 1%Z 1%Z 0%Z) (int.EuclideanDivision.div n
  2%Z)) = (mk_t (result + result1)%Z result1 result1 result)) ->
  ((((int.EuclideanDivision.mod1 n 2%Z) = 0%Z) -> let a :=
  ((result * result)%Z + (result1 * result1)%Z)%Z in let b :=
  (result1 * (result + (result + result1)%Z)%Z)%Z in ((power (mk_t 1%Z 1%Z
  1%Z 0%Z) n) = (mk_t (a + b)%Z b b a))) /\
  ((~ ((int.EuclideanDivision.mod1 n 2%Z) = 0%Z)) -> let a :=
  (result1 * (result + (result + result1)%Z)%Z)%Z in let b :=
  (((result + result1)%Z * (result + result1)%Z)%Z + (result1 * result1)%Z)%Z in
  ((power (mk_t 1%Z 1%Z 1%Z 0%Z) n) = (mk_t (a + b)%Z b b a)))))).
(* YOU MAY EDIT THE PROOF BELOW *)
Import EuclideanDivision.
intros.
assert (h: (2 <> 0)%Z) by omega.
generalize (Div_mod n 2 h)%Z.
intuition.
rewrite H4 in H3.
rewrite H3.
replace (2 * div n 2 + 0)%Z with (div n 2 + div n 2)%Z by omega.
rewrite Power_sum by exact H1.
rewrite H2; simpl.
unfold mult; simpl.
apply f_equal4; ring.

generalize (Mod_bound n 2 h)%Z.
simpl.
intro.
assert (h': (mod1 n 2 = 1)%Z) by omega.
rewrite h' in H3.
rewrite H3.
replace (2 * div n 2 + 1)%Z with ((div n 2 + div n 2) + 1)%Z by omega.
rewrite Power_s.
rewrite Power_sum by exact H1.
rewrite H2; simpl.
unfold mult at 2; simpl.
unfold mult.
apply f_equal4; unfold a11, a12, a21, a22; try ring.
intuition.
Qed.


