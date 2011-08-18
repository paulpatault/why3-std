(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import ZArith.
Require Import Rbase.
Require Import ZOdiv.
Require Import Zdiv.
Definition unit  := unit.

Parameter mark : Type.

Parameter at1: forall (a:Type), a -> mark  -> a.

Implicit Arguments at1.

Parameter old: forall (a:Type), a  -> a.

Implicit Arguments old.

Axiom Abs_pos : forall (x:Z), (0%Z <= (Zabs x))%Z.

Axiom Div_mod : forall (x:Z) (y:Z), (~ (y = 0%Z)) ->
  (x = ((y * (ZOdiv x y))%Z + (ZOmod x y))%Z).

Axiom Div_bound : forall (x:Z) (y:Z), ((0%Z <= x)%Z /\ (0%Z <  y)%Z) ->
  ((0%Z <= (ZOdiv x y))%Z /\ ((ZOdiv x y) <= x)%Z).

Axiom Mod_bound : forall (x:Z) (y:Z), (~ (y = 0%Z)) ->
  (((-(Zabs y))%Z <  (ZOmod x y))%Z /\ ((ZOmod x y) <  (Zabs y))%Z).

Axiom Div_sign_pos : forall (x:Z) (y:Z), ((0%Z <= x)%Z /\ (0%Z <  y)%Z) ->
  (0%Z <= (ZOdiv x y))%Z.

Axiom Div_sign_neg : forall (x:Z) (y:Z), ((x <= 0%Z)%Z /\ (0%Z <  y)%Z) ->
  ((ZOdiv x y) <= 0%Z)%Z.

Axiom Mod_sign_pos : forall (x:Z) (y:Z), ((0%Z <= x)%Z /\ ~ (y = 0%Z)) ->
  (0%Z <= (ZOmod x y))%Z.

Axiom Mod_sign_neg : forall (x:Z) (y:Z), ((x <= 0%Z)%Z /\ ~ (y = 0%Z)) ->
  ((ZOmod x y) <= 0%Z)%Z.

Axiom Rounds_toward_zero : forall (x:Z) (y:Z), (~ (y = 0%Z)) ->
  ((Zabs ((ZOdiv x y) * y)%Z) <= (Zabs x))%Z.

Axiom Div_1 : forall (x:Z), ((ZOdiv x 1%Z) = x).

Axiom Mod_1 : forall (x:Z), ((ZOmod x 1%Z) = 0%Z).

Axiom Div_inf : forall (x:Z) (y:Z), ((0%Z <= x)%Z /\ (x <  y)%Z) ->
  ((ZOdiv x y) = 0%Z).

Axiom Mod_inf : forall (x:Z) (y:Z), ((0%Z <= x)%Z /\ (x <  y)%Z) ->
  ((ZOmod x y) = x).

Axiom Div_mult : forall (x:Z) (y:Z) (z:Z), ((0%Z <  x)%Z /\ ((0%Z <= y)%Z /\
  (0%Z <= z)%Z)) -> ((ZOdiv ((x * y)%Z + z)%Z x) = (y + (ZOdiv z x))%Z).

Axiom Mod_mult : forall (x:Z) (y:Z) (z:Z), ((0%Z <  x)%Z /\ ((0%Z <= y)%Z /\
  (0%Z <= z)%Z)) -> ((ZOmod ((x * y)%Z + z)%Z x) = (ZOmod z x)).

Definition lt_nat(x:Z) (y:Z): Prop := (0%Z <= y)%Z /\ (x <  y)%Z.

Inductive lex : (Z* Z)%type -> (Z* Z)%type -> Prop :=
  | Lex_1 : forall (x1:Z) (x2:Z) (y1:Z) (y2:Z), (lt_nat x1 x2) -> (lex (x1,
      y1) (x2, y2))
  | Lex_2 : forall (x:Z) (y1:Z) (y2:Z), (lt_nat y1 y2) -> (lex (x, y1) (x,
      y2)).

Definition even(n:Z): Prop := exists k:Z, (n = (2%Z * k)%Z).

Definition odd(n:Z): Prop := exists k:Z, (n = ((2%Z * k)%Z + 1%Z)%Z).

Axiom even_or_odd : forall (n:Z), (even n) \/ (odd n).

Axiom even_not_odd : forall (n:Z), (even n) -> ~ (odd n).

Axiom odd_not_even : forall (n:Z), (odd n) -> ~ (even n).

Axiom even_odd : forall (n:Z), (even n) -> (odd (n + 1%Z)%Z).

Axiom odd_even : forall (n:Z), (odd n) -> (even (n + 1%Z)%Z).

Axiom even_even : forall (n:Z), (even n) -> (even (n + 2%Z)%Z).

Axiom odd_odd : forall (n:Z), (odd n) -> (odd (n + 2%Z)%Z).

Axiom even_2k : forall (k:Z), (even (2%Z * k)%Z).

Axiom odd_2k1 : forall (k:Z), (odd ((2%Z * k)%Z + 1%Z)%Z).

Definition divides(d:Z) (n:Z): Prop := exists q:Z, (n = (q * d)%Z).

Axiom divides_refl : forall (n:Z), (divides n n).

Axiom divides_1_n : forall (n:Z), (divides 1%Z n).

Axiom divides_0 : forall (n:Z), (divides n 0%Z).

Axiom divides_left : forall (a:Z) (b:Z) (c:Z), (divides a b) ->
  (divides (c * a)%Z (c * b)%Z).

Axiom divides_right : forall (a:Z) (b:Z) (c:Z), (divides a b) ->
  (divides (a * c)%Z (b * c)%Z).

Axiom divides_oppr : forall (a:Z) (b:Z), (divides a b) -> (divides a (-b)%Z).

Axiom divides_oppl : forall (a:Z) (b:Z), (divides a b) -> (divides (-a)%Z b).

Axiom divides_oppr_rev : forall (a:Z) (b:Z), (divides (-a)%Z b) -> (divides a
  b).

Axiom divides_oppl_rev : forall (a:Z) (b:Z), (divides a (-b)%Z) -> (divides a
  b).

Axiom divides_plusr : forall (a:Z) (b:Z) (c:Z), (divides a b) -> ((divides a
  c) -> (divides a (b + c)%Z)).

Axiom divides_minusr : forall (a:Z) (b:Z) (c:Z), (divides a b) -> ((divides a
  c) -> (divides a (b - c)%Z)).

Axiom divides_multl : forall (a:Z) (b:Z) (c:Z), (divides a b) -> (divides a
  (c * b)%Z).

Axiom divides_multr : forall (a:Z) (b:Z) (c:Z), (divides a b) -> (divides a
  (b * c)%Z).

Axiom divides_factorl : forall (a:Z) (b:Z), (divides a (b * a)%Z).

Axiom divides_factorr : forall (a:Z) (b:Z), (divides a (a * b)%Z).

Axiom divides_n_1 : forall (n:Z), (divides n 1%Z) -> ((n = 1%Z) \/
  (n = (-1%Z)%Z)).

Axiom divides_antisym : forall (a:Z) (b:Z), (divides a b) -> ((divides b
  a) -> ((a = b) \/ (a = (-b)%Z))).

Axiom divides_trans : forall (a:Z) (b:Z) (c:Z), (divides a b) -> ((divides b
  c) -> (divides a c)).

Axiom divides_bounds : forall (a:Z) (b:Z), (divides a b) -> ((~ (b = 0%Z)) ->
  ((Zabs a) <= (Zabs b))%Z).

Axiom Div_mod1 : forall (x:Z) (y:Z), (~ (y = 0%Z)) ->
  (x = ((y * (Zdiv x y))%Z + (Zmod x y))%Z).

Axiom Div_bound1 : forall (x:Z) (y:Z), ((0%Z <= x)%Z /\ (0%Z <  y)%Z) ->
  ((0%Z <= (Zdiv x y))%Z /\ ((Zdiv x y) <= x)%Z).

Axiom Mod_bound1 : forall (x:Z) (y:Z), (~ (y = 0%Z)) ->
  ((0%Z <= (Zmod x y))%Z /\ ((Zmod x y) <  (Zabs y))%Z).

Axiom Mod_11 : forall (x:Z), ((Zmod x 1%Z) = 0%Z).

Axiom Div_11 : forall (x:Z), ((Zdiv x 1%Z) = x).

Axiom mod_divides_euclidean : forall (a:Z) (b:Z), (~ (b = 0%Z)) ->
  (((Zmod a b) = 0%Z) -> (divides b a)).

Axiom divides_mod_euclidean : forall (a:Z) (b:Z), (~ (b = 0%Z)) ->
  ((divides b a) -> ((Zmod a b) = 0%Z)).

Axiom mod_divides_computer : forall (a:Z) (b:Z), (~ (b = 0%Z)) ->
  (((ZOmod a b) = 0%Z) -> (divides b a)).

Axiom divides_mod_computer : forall (a:Z) (b:Z), (~ (b = 0%Z)) -> ((divides b
  a) -> ((ZOmod a b) = 0%Z)).

Axiom even_divides : forall (a:Z), (even a) <-> (divides 2%Z a).

Axiom odd_divides : forall (a:Z), (odd a) <-> ~ (divides 2%Z a).

Definition prime(p:Z): Prop := (2%Z <= p)%Z /\ forall (n:Z), ((1%Z <  n)%Z /\
  (n <  p)%Z) -> ~ (divides n p).

Axiom not_prime_1 : ~ (prime 1%Z).

Axiom prime_2 : (prime 2%Z).

Axiom prime_3 : (prime 3%Z).

Axiom prime_divisors : forall (p:Z), (prime p) -> forall (d:Z), (divides d
  p) -> ((d = 1%Z) \/ ((d = (-1%Z)%Z) \/ ((d = p) \/ (d = (-p)%Z)))).

Axiom small_divisors : forall (p:Z), (2%Z <= p)%Z -> ((forall (d:Z),
  (2%Z <= d)%Z -> ((prime d) -> (((1%Z <  (d * d)%Z)%Z /\
  ((d * d)%Z <= p)%Z) -> ~ (divides d p)))) -> (prime p)).

Axiom even_prime : forall (p:Z), (prime p) -> ((even p) -> (p = 2%Z)).

Axiom odd_prime : forall (p:Z), (prime p) -> ((3%Z <= p)%Z -> (odd p)).

Inductive ref (a:Type) :=
  | mk_ref : a -> ref a.
Implicit Arguments mk_ref.

Definition contents (a:Type)(u:(ref a)): a :=
  match u with
  | mk_ref contents1 => contents1
  end.
Implicit Arguments contents.

Parameter map : forall (a:Type) (b:Type), Type.

Parameter get: forall (a:Type) (b:Type), (map a b) -> a  -> b.

Implicit Arguments get.

Parameter set: forall (a:Type) (b:Type), (map a b) -> a -> b  -> (map a b).

Implicit Arguments set.

Axiom Select_eq : forall (a:Type) (b:Type), forall (m:(map a b)),
  forall (a1:a) (a2:a), forall (b1:b), (a1 = a2) -> ((get (set m a1 b1)
  a2) = b1).

Axiom Select_neq : forall (a:Type) (b:Type), forall (m:(map a b)),
  forall (a1:a) (a2:a), forall (b1:b), (~ (a1 = a2)) -> ((get (set m a1 b1)
  a2) = (get m a2)).

Parameter const: forall (b:Type) (a:Type), b  -> (map a b).

Set Contextual Implicit.
Implicit Arguments const.
Unset Contextual Implicit.

Axiom Const : forall (b:Type) (a:Type), forall (b1:b) (a1:a), ((get (const(
  b1):(map a b)) a1) = b1).

Inductive array (a:Type) :=
  | mk_array : Z -> (map Z a) -> array a.
Implicit Arguments mk_array.

Definition elts (a:Type)(u:(array a)): (map Z a) :=
  match u with
  | mk_array _ elts1 => elts1
  end.
Implicit Arguments elts.

Definition length (a:Type)(u:(array a)): Z :=
  match u with
  | mk_array length1 _ => length1
  end.
Implicit Arguments length.

Definition get1 (a:Type)(a1:(array a)) (i:Z): a := (get (elts a1) i).
Implicit Arguments get1.

Definition set1 (a:Type)(a1:(array a)) (i:Z) (v:a): (array a) :=
  match a1 with
  | mk_array xcl0 _ => (mk_array xcl0 (set (elts a1) i v))
  end.
Implicit Arguments set1.

Definition no_prime_in(l:Z) (u:Z): Prop := forall (x:Z), ((l <  x)%Z /\
  (x <  u)%Z) -> ~ (prime x).

Definition first_primes(p:(array Z)) (u:Z): Prop := ((get1 p 0%Z) = 2%Z) /\
  ((forall (i:Z) (j:Z), (((0%Z <= i)%Z /\ (i <  j)%Z) /\ (j <  u)%Z) ->
  ((get1 p i) <  (get1 p j))%Z) /\ ((forall (i:Z), ((0%Z <= i)%Z /\
  (i <  u)%Z) -> (prime (get1 p i))) /\ forall (i:Z), ((0%Z <= i)%Z /\
  (i <  (u - 1%Z)%Z)%Z) -> (no_prime_in (get1 p i) (get1 p (i + 1%Z)%Z)))).

Axiom exists_prime : forall (p:(array Z)) (u:Z), (1%Z <= u)%Z ->
  ((first_primes p u) -> forall (d:Z), ((2%Z <= d)%Z /\ (d <= (get1 p
  (u - 1%Z)%Z))%Z) -> ((prime d) -> exists i:Z, ((0%Z <= i)%Z /\
  (i <  u)%Z) /\ (d = (get1 p i)))).

Axiom Bertrand_postulate : forall (p:Z), (prime p) -> ~ (no_prime_in p
  (2%Z * p)%Z).

(* YOU MAY EDIT THE CONTEXT BELOW *)

(* DO NOT EDIT BELOW *)

Theorem WP_parameter_prime_numbers : forall (m:Z), (2%Z <= m)%Z ->
  ((0%Z <= m)%Z -> (((0%Z <= 0%Z)%Z /\ (0%Z <  m)%Z) -> forall (p:(map Z Z)),
  (p = (set (const(0%Z):(map Z Z)) 0%Z 2%Z)) -> (((0%Z <= 1%Z)%Z /\
  (1%Z <  m)%Z) -> forall (p1:(map Z Z)), (p1 = (set p 1%Z 3%Z)) ->
  ((2%Z <= (m - 1%Z)%Z)%Z -> forall (n:Z), forall (p2:(map Z Z)),
  forall (j:Z), ((2%Z <= j)%Z /\ (j <= (m - 1%Z)%Z)%Z) ->
  (((first_primes (mk_array m p2) j) /\ ((((get p2 (j - 1%Z)%Z) <  n)%Z /\
  (n <  (2%Z * (get p2 (j - 1%Z)%Z))%Z)%Z) /\ ((odd n) /\
  (no_prime_in (get p2 (j - 1%Z)%Z) n)))) -> forall (k:Z), forall (n1:Z),
  forall (p3:(map Z Z)), (((1%Z <= k)%Z /\ (k <  j)%Z) /\
  ((first_primes (mk_array m p3) j) /\ ((((get p3 (j - 1%Z)%Z) <  n1)%Z /\
  (n1 <  (2%Z * (get p3 (j - 1%Z)%Z))%Z)%Z) /\ ((odd n1) /\
  ((no_prime_in (get p3 (j - 1%Z)%Z) n1) /\ forall (i:Z), ((0%Z <= i)%Z /\
  (i <  k)%Z) -> ~ (divides (get p3 i) n1)))))) -> (((0%Z <= k)%Z /\
  (k <  m)%Z) -> ((~ ((ZOmod n1 (get p3 k)) = 0%Z)) -> (((0%Z <= k)%Z /\
  (k <  m)%Z) -> (((0%Z <= k)%Z /\ (k <  m)%Z) -> (((get p3
  k) <  (ZOdiv n1 (get p3 k)))%Z -> ((k + 1%Z)%Z <  j)%Z)))))))))).
(* YOU MAY EDIT THE PROOF BELOW *)
intuition.
intros. clear H9.
assert (case: (k = j-1 \/ k+1<j)%Z) by omega. destruct case. 2: auto.
apply False_ind.
subst k.
assert (2 < get p3 (j-1))%Z.
red in H21. destruct H21 as (h1, (h2, _)).
rewrite <- h1. apply h2; omega.
assert (ne0: (get p3 (j-1) <> 0)%Z) by omega.
generalize (Div_mod n1 (get p3 (j-1))%Z ne0). intro div.
assert (ne1: (0 <= n1 /\ get p3 (j-1) <> 0)%Z) by omega.
generalize (Mod_sign_pos n1 (get p3 (j-1))%Z ne1). intro mod_.
assert (n1 > get p3 (j - 1) * get p3 (j-1))%Z.
assert (get p3 (j - 1) * (ZOdiv n1 (get p3 (j - 1))) > get p3 (j - 1) * get p3 (j-1))%Z.
apply Zmult_gt_compat_l.
omega.
apply Zlt_gt.
assumption.
omega.
assert (n1 < get p3 (j - 1) * get p3 (j - 1)%Z).
assert (2 * get p3 (j - 1) < get p3 (j - 1) * get p3 (j - 1))%Z.
apply Zmult_lt_compat_r; omega.
omega.
omega.
Qed.
(* DO NOT EDIT BELOW *)


