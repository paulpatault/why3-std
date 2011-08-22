(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import ZArith.
Require Import Rbase.
Definition unit  := unit.

Parameter mark : Type.

Parameter at1: forall (a:Type), a -> mark  -> a.

Implicit Arguments at1.

Parameter old: forall (a:Type), a  -> a.

Implicit Arguments old.

Parameter set : forall (a:Type), Type.

Parameter mem: forall (a:Type), a -> (set a)  -> Prop.

Implicit Arguments mem.

Definition infix_eqeq (a:Type)(s1:(set a)) (s2:(set a)): Prop :=
  forall (x:a), (mem x s1) <-> (mem x s2).
Implicit Arguments infix_eqeq.

Axiom extensionality : forall (a:Type), forall (s1:(set a)) (s2:(set a)),
  (infix_eqeq s1 s2) -> (s1 = s2).

Definition subset (a:Type)(s1:(set a)) (s2:(set a)): Prop := forall (x:a),
  (mem x s1) -> (mem x s2).
Implicit Arguments subset.

Axiom subset_trans : forall (a:Type), forall (s1:(set a)) (s2:(set a))
  (s3:(set a)), (subset s1 s2) -> ((subset s2 s3) -> (subset s1 s3)).

Parameter empty: forall (a:Type),  (set a).

Set Contextual Implicit.
Implicit Arguments empty.
Unset Contextual Implicit.

Definition is_empty (a:Type)(s:(set a)): Prop := forall (x:a), ~ (mem x s).
Implicit Arguments is_empty.

Axiom empty_def1 : forall (a:Type), (is_empty (empty:(set a))).

Parameter add: forall (a:Type), a -> (set a)  -> (set a).

Implicit Arguments add.

Axiom add_def1 : forall (a:Type), forall (x:a) (y:a), forall (s:(set a)),
  (mem x (add y s)) <-> ((x = y) \/ (mem x s)).

Parameter remove: forall (a:Type), a -> (set a)  -> (set a).

Implicit Arguments remove.

Axiom remove_def1 : forall (a:Type), forall (x:a) (y:a) (s:(set a)), (mem x
  (remove y s)) <-> ((~ (x = y)) /\ (mem x s)).

Axiom subset_remove : forall (a:Type), forall (x:a) (s:(set a)),
  (subset (remove x s) s).

Parameter union: forall (a:Type), (set a) -> (set a)  -> (set a).

Implicit Arguments union.

Axiom union_def1 : forall (a:Type), forall (s1:(set a)) (s2:(set a)) (x:a),
  (mem x (union s1 s2)) <-> ((mem x s1) \/ (mem x s2)).

Parameter inter: forall (a:Type), (set a) -> (set a)  -> (set a).

Implicit Arguments inter.

Axiom inter_def1 : forall (a:Type), forall (s1:(set a)) (s2:(set a)) (x:a),
  (mem x (inter s1 s2)) <-> ((mem x s1) /\ (mem x s2)).

Parameter diff: forall (a:Type), (set a) -> (set a)  -> (set a).

Implicit Arguments diff.

Axiom diff_def1 : forall (a:Type), forall (s1:(set a)) (s2:(set a)) (x:a),
  (mem x (diff s1 s2)) <-> ((mem x s1) /\ ~ (mem x s2)).

Axiom subset_diff : forall (a:Type), forall (s1:(set a)) (s2:(set a)),
  (subset (diff s1 s2) s1).

Parameter cardinal: forall (a:Type), (set a)  -> Z.

Implicit Arguments cardinal.

Axiom cardinal_nonneg : forall (a:Type), forall (s:(set a)),
  (0%Z <= (cardinal s))%Z.

Axiom cardinal_empty : forall (a:Type), forall (s:(set a)),
  ((cardinal s) = 0%Z) <-> (is_empty s).

Axiom cardinal_add : forall (a:Type), forall (x:a), forall (s:(set a)),
  (~ (mem x s)) -> ((cardinal (add x s)) = (1%Z + (cardinal s))%Z).

Axiom cardinal_remove : forall (a:Type), forall (x:a), forall (s:(set a)),
  (mem x s) -> ((cardinal s) = (1%Z + (cardinal (remove x s)))%Z).

Axiom cardinal_subset : forall (a:Type), forall (s1:(set a)) (s2:(set a)),
  (subset s1 s2) -> ((cardinal s1) <= (cardinal s2))%Z.

Parameter min_elt: (set Z)  -> Z.


Axiom min_elt_def1 : forall (s:(set Z)), (~ (is_empty s)) -> (mem (min_elt s)
  s).

Axiom min_elt_def2 : forall (s:(set Z)), (~ (is_empty s)) -> forall (x:Z),
  (mem x s) -> ((min_elt s) <= x)%Z.

Parameter max_elt: (set Z)  -> Z.


Axiom max_elt_def1 : forall (s:(set Z)), (~ (is_empty s)) -> (mem (max_elt s)
  s).

Axiom max_elt_def2 : forall (s:(set Z)), (~ (is_empty s)) -> forall (x:Z),
  (mem x s) -> (x <= (max_elt s))%Z.

Parameter below: Z  -> (set Z).


Axiom below_def : forall (x:Z) (n:Z), (mem x (below n)) <-> ((0%Z <= x)%Z /\
  (x <  n)%Z).

Axiom cardinal_below : forall (n:Z), ((0%Z <= n)%Z ->
  ((cardinal (below n)) = n)) /\ ((~ (0%Z <= n)%Z) ->
  ((cardinal (below n)) = 0%Z)).

Parameter succ: (set Z)  -> (set Z).


Axiom succ_def : forall (s:(set Z)) (i:Z), (mem i (succ s)) <->
  ((1%Z <= i)%Z /\ (mem (i - 1%Z)%Z s)).

Parameter pred: (set Z)  -> (set Z).


Axiom pred_def : forall (s:(set Z)) (i:Z), (mem i (pred s)) <->
  ((0%Z <= i)%Z /\ (mem (i + 1%Z)%Z s)).

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

Parameter set1: forall (a:Type) (b:Type), (map a b) -> a -> b  -> (map a b).

Implicit Arguments set1.

Axiom Select_eq : forall (a:Type) (b:Type), forall (m:(map a b)),
  forall (a1:a) (a2:a), forall (b1:b), (a1 = a2) -> ((get (set1 m a1 b1)
  a2) = b1).

Axiom Select_neq : forall (a:Type) (b:Type), forall (m:(map a b)),
  forall (a1:a) (a2:a), forall (b1:b), (~ (a1 = a2)) -> ((get (set1 m a1 b1)
  a2) = (get m a2)).

Parameter const: forall (b:Type) (a:Type), b  -> (map a b).

Set Contextual Implicit.
Implicit Arguments const.
Unset Contextual Implicit.

Axiom Const : forall (b:Type) (a:Type), forall (b1:b) (a1:a), ((get (const(
  b1):(map a b)) a1) = b1).

Parameter n:  Z.


Definition solution  := (map Z Z).

Definition eq_prefix (a:Type)(t:(map Z a)) (u:(map Z a)) (i:Z): Prop :=
  forall (k:Z), ((0%Z <= k)%Z /\ (k <  i)%Z) -> ((get t k) = (get u k)).
Implicit Arguments eq_prefix.

Definition partial_solution(k:Z) (s:(map Z Z)): Prop := forall (i:Z),
  ((0%Z <= i)%Z /\ (i <  k)%Z) -> (((0%Z <= (get s i))%Z /\ ((get s
  i) <  (n ))%Z) /\ forall (j:Z), ((0%Z <= j)%Z /\ (j <  i)%Z) -> ((~ ((get s
  i) = (get s j))) /\ ((~ (((get s i) - (get s j))%Z = (i - j)%Z)) /\
  ~ (((get s i) - (get s j))%Z = (j - i)%Z)))).

Axiom partial_solution_eq_prefix : forall (u:(map Z Z)) (t:(map Z Z)) (k:Z),
  (partial_solution k t) -> ((eq_prefix t u k) -> (partial_solution k u)).

Definition lt_sol(s1:(map Z Z)) (s2:(map Z Z)): Prop := exists i:Z,
  ((0%Z <= i)%Z /\ (i <  (n ))%Z) /\ ((eq_prefix s1 s2 i) /\ ((get s1
  i) <  (get s2 i))%Z).

Definition solutions  := (map Z (map Z Z)).

Definition sorted(s:(map Z (map Z Z))) (a:Z) (b:Z): Prop := forall (i:Z)
  (j:Z), (((a <= i)%Z /\ (i <  j)%Z) /\ (j <  b)%Z) -> (lt_sol (get s i)
  (get s j)).

Parameter col:  (ref (map Z Z)).


Parameter k:  (ref Z).


Parameter sol:  (ref (map Z (map Z Z))).


Parameter s:  (ref Z).


(* YOU MAY EDIT THE CONTEXT BELOW *)

(* DO NOT EDIT BELOW *)

Theorem WP_parameter_t3 : forall (a:(set Z)), forall (b:(set Z)),
  forall (c:(set Z)), forall (s1:Z), forall (sol1:(map Z (map Z Z))),
  forall (k1:Z), forall (col1:(map Z Z)), ((0%Z <= k1)%Z /\
  (((k1 + (cardinal a))%Z = (n )) /\ ((0%Z <= s1)%Z /\ ((forall (i:Z), (mem i
  a) <-> (((0%Z <= i)%Z /\ (i <  (n ))%Z) /\ forall (j:Z), ((0%Z <= j)%Z /\
  (j <  k1)%Z) -> ~ ((get col1 j) = i))) /\ ((forall (i:Z), (0%Z <= i)%Z ->
  ((~ (mem i b)) <-> forall (j:Z), ((0%Z <= j)%Z /\ (j <  k1)%Z) ->
  ~ ((get col1 j) = ((i + j)%Z - k1)%Z))) /\ ((forall (i:Z), (0%Z <= i)%Z ->
  ((~ (mem i c)) <-> forall (j:Z), ((0%Z <= j)%Z /\ (j <  k1)%Z) ->
  ~ ((get col1 j) = ((i + k1)%Z - j)%Z))) /\ (partial_solution k1
  col1))))))) -> ((~ (is_empty a)) -> forall (f:Z), forall (e:(set Z)),
  forall (s2:Z), forall (sol2:(map Z (map Z Z))), forall (k2:Z),
  forall (col2:(map Z Z)), (((f = (s2 - s1)%Z) /\ (0%Z <= (s2 - s1)%Z)%Z) /\
  ((k2 = k1) /\ ((subset e (diff (diff a b) c)) /\ ((partial_solution k2
  col2) /\ ((sorted sol2 s1 s2) /\ ((forall (i:Z) (j:Z), (mem i
  (diff (diff (diff a b) c) e)) -> ((mem j e) -> (i <  j)%Z)) /\
  ((forall (t:(map Z Z)), ((partial_solution (n ) t) /\ ((eq_prefix col2 t
  k2) /\ (mem (get t k2) (diff (diff (diff a b) c) e)))) <-> exists i:Z,
  ((s1 <= i)%Z /\ (i <  s2)%Z) /\ (eq_prefix t (get sol2 i) (n ))) /\
  ((eq_prefix col1 col2 k1) /\ (eq_prefix sol1 sol2 s1))))))))) ->
  ((~ (is_empty e)) -> forall (col3:(map Z Z)), (col3 = (set1 col2 k2
  (min_elt e))) -> forall (k3:Z), (k3 = (k2 + 1%Z)%Z) ->
  ((((0%Z <= (cardinal a))%Z /\ ((cardinal (remove (min_elt e)
  a)) <  (cardinal a))%Z) /\ ((0%Z <= k3)%Z /\
  (((k3 + (cardinal (remove (min_elt e) a)))%Z = (n )) /\ ((0%Z <= s2)%Z /\
  ((forall (i:Z), (mem i (remove (min_elt e) a)) <-> (((0%Z <= i)%Z /\
  (i <  (n ))%Z) /\ forall (j:Z), ((0%Z <= j)%Z /\ (j <  k3)%Z) ->
  ~ ((get col3 j) = i))) /\ ((forall (i:Z), (0%Z <= i)%Z -> ((~ (mem i
  (succ (add (min_elt e) b)))) <-> forall (j:Z), ((0%Z <= j)%Z /\
  (j <  k3)%Z) -> ~ ((get col3 j) = ((i + j)%Z - k3)%Z))) /\ ((forall (i:Z),
  (0%Z <= i)%Z -> ((~ (mem i (pred (add (min_elt e) c)))) <-> forall (j:Z),
  ((0%Z <= j)%Z /\ (j <  k3)%Z) -> ~ ((get col3 j) = ((i + k3)%Z - j)%Z))) /\
  (partial_solution k3 col3)))))))) -> forall (s3:Z), forall (sol3:(map Z
  (map Z Z))), forall (k4:Z), forall (col4:(map Z Z)), forall (result:Z),
  (((result = (s3 - s2)%Z) /\ (0%Z <= (s3 - s2)%Z)%Z) /\ ((k4 = k3) /\
  ((sorted sol3 s2 s3) /\ ((forall (t:(map Z Z)), ((partial_solution (n )
  t) /\ (eq_prefix col4 t k4)) <-> exists i:Z, ((s2 <= i)%Z /\
  (i <  s3)%Z) /\ (eq_prefix t (get sol3 i) (n ))) /\ ((eq_prefix col3 col4
  k4) /\ (eq_prefix sol2 sol3 s2)))))) -> forall (f1:Z),
  (f1 = (f + result)%Z) -> forall (k5:Z), (k5 = (k4 - 1%Z)%Z) ->
  forall (e1:(set Z)), (e1 = (remove (min_elt e) e)) -> forall (i:Z) (j:Z),
  (mem i (diff (diff (diff a b) c) e1)) -> ((mem j e1) -> (i <  j)%Z)))).
(* YOU MAY EDIT THE PROOF BELOW *)
intros a b c. generalize (diff (diff a b) c) as abc.
intuition.
clear H3 H4 H5 H33 H15 H25 H26 H27.
assert (not (mem i e1)).
generalize (diff_def1 _ abc e1 i); intuition.
subst e1.
generalize (remove_def1 _ i (min_elt e) e).
intros (h1, h2).
assert (case: i = min_elt e \/ i <> min_elt e) by omega. destruct case.
subst i.
assert (min_elt e <= j)%Z.
apply min_elt_def2; auto.
generalize (remove_def1 _ j (min_elt e) e). intuition.
assert (j <> min_elt e)%Z.
generalize (remove_def1 _ j (min_elt e) e). intuition.
omega.
apply H14.
generalize (diff_def1 _ abc e i); intuition.
generalize (diff_def1 _ abc (remove (min_elt e) e) i); intuition.
generalize (remove_def1 _ j (min_elt e) e). intuition.
Qed.
(* DO NOT EDIT BELOW *)


