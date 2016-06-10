(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require map.Map.
Require int.Int.
Require list.List.
Require list.Length.
Require list.Mem.
Require list.Append.

(* Why3 assumption *)
Definition unit := unit.

(* Why3 assumption *)
Inductive color :=
  | White : color
  | Black : color.
Axiom color_WhyType : WhyType color.
Existing Instance color_WhyType.

(* Why3 assumption *)
Inductive forest :=
  | E : forest
  | N : Z -> forest -> forest -> forest.
Axiom forest_WhyType : WhyType forest.
Existing Instance forest_WhyType.

(* Why3 assumption *)
Definition coloring := (map.Map.map Z color).

(* Why3 assumption *)
Fixpoint size_forest (f:forest) {struct f}: Z :=
  match f with
  | E => 0%Z
  | (N _ f1 f2) => ((1%Z + (size_forest f1))%Z + (size_forest f2))%Z
  end.

Axiom size_forest_nonneg : forall (f:forest), (0%Z <= (size_forest f))%Z.

(* Why3 assumption *)
Fixpoint mem_forest (n:Z) (f:forest) {struct f}: Prop :=
  match f with
  | E => False
  | (N i f1 f2) => (i = n) \/ ((mem_forest n f1) \/ (mem_forest n f2))
  end.

(* Why3 assumption *)
Definition between_range_forest (i:Z) (j:Z) (f:forest): Prop := forall (n:Z),
  (mem_forest n f) -> ((i <= n)%Z /\ (n < j)%Z).

(* Why3 assumption *)
Definition disjoint (f1:forest) (f2:forest): Prop := forall (x:Z),
  (mem_forest x f1) -> ~ (mem_forest x f2).

(* Why3 assumption *)
Fixpoint no_repeated_forest (f:forest) {struct f}: Prop :=
  match f with
  | E => True
  | (N i f1 f2) => (no_repeated_forest f1) /\ ((no_repeated_forest f2) /\
      ((~ (mem_forest i f1)) /\ ((~ (mem_forest i f2)) /\ (disjoint f1 f2))))
  end.

(* Why3 assumption *)
Definition valid_nums_forest (f:forest) (n:Z): Prop := (between_range_forest
  0%Z n f) /\ (no_repeated_forest f).

(* Why3 assumption *)
Fixpoint white_forest (f:forest) (c:(map.Map.map Z
  color)) {struct f}: Prop :=
  match f with
  | E => True
  | (N i f1 f2) => ((map.Map.get c i) = White) /\ ((white_forest f1 c) /\
      (white_forest f2 c))
  end.

(* Why3 assumption *)
Fixpoint valid_coloring (f:forest) (c:(map.Map.map Z
  color)) {struct f}: Prop :=
  match f with
  | E => True
  | (N i f1 f2) => (valid_coloring f2 c) /\ match (map.Map.get c
      i) with
      | White => (white_forest f1 c)
      | Black => (valid_coloring f1 c)
      end
  end.

(* Why3 assumption *)
Fixpoint count_forest (f:forest) {struct f}: Z :=
  match f with
  | E => 1%Z
  | (N _ f1 f2) => ((1%Z + (count_forest f1))%Z * (count_forest f2))%Z
  end.

Axiom count_forest_nonneg : forall (f:forest), (1%Z <= (count_forest f))%Z.

(* Why3 assumption *)
Definition eq_coloring (n:Z) (c1:(map.Map.map Z color)) (c2:(map.Map.map Z
  color)): Prop := forall (i:Z), ((0%Z <= i)%Z /\ (i < n)%Z) ->
  ((map.Map.get c1 i) = (map.Map.get c2 i)).

(* Why3 assumption *)
Definition stack := (list forest).

(* Why3 assumption *)
Fixpoint mem_stack (n:Z) (st:(list forest)) {struct st}: Prop :=
  match st with
  | Init.Datatypes.nil => False
  | (Init.Datatypes.cons f tl) => (mem_forest n f) \/ (mem_stack n tl)
  end.

Axiom mem_app : forall (n:Z) (st1:(list forest)) (st2:(list forest)),
  (mem_stack n (Init.Datatypes.app st1 st2)) -> ((mem_stack n st1) \/
  (mem_stack n st2)).

(* Why3 assumption *)
Fixpoint size_stack (st:(list forest)) {struct st}: Z :=
  match st with
  | Init.Datatypes.nil => 0%Z
  | (Init.Datatypes.cons f st1) => ((size_forest f) + (size_stack st1))%Z
  end.

Axiom size_stack_nonneg : forall (st:(list forest)),
  (0%Z <= (size_stack st))%Z.

Axiom white_forest_equiv : forall (f:forest) (c:(map.Map.map Z color)),
  (white_forest f c) <-> forall (i:Z), (mem_forest i f) -> ((map.Map.get c
  i) = White).

(* Why3 assumption *)
Fixpoint even_forest (f:forest) {struct f}: Prop :=
  match f with
  | E => False
  | (N _ f1 f2) => (~ (even_forest f1)) \/ (even_forest f2)
  end.

(* Why3 assumption *)
Fixpoint final_forest (f:forest) (c:(map.Map.map Z
  color)) {struct f}: Prop :=
  match f with
  | E => True
  | (N i f1 f2) => ((map.Map.get c i) = Black) /\ ((final_forest f1 c) /\
      (((~ (even_forest f1)) -> (white_forest f2 c)) /\ ((even_forest f1) ->
      (final_forest f2 c))))
  end.

(* Why3 assumption *)
Definition any_forest (f:forest) (c:(map.Map.map Z color)): Prop :=
  (white_forest f c) \/ (final_forest f c).

Axiom any_forest_frame : forall (f:forest) (c1:(map.Map.map Z color))
  (c2:(map.Map.map Z color)), (forall (i:Z), (mem_forest i f) ->
  ((map.Map.get c1 i) = (map.Map.get c2 i))) -> (((final_forest f c1) ->
  (final_forest f c2)) /\ ((white_forest f c1) -> (white_forest f c2))).

(* Why3 assumption *)
Definition unchanged (st:(list forest)) (c1:(map.Map.map Z color))
  (c2:(map.Map.map Z color)): Prop := forall (i:Z), (mem_stack i st) ->
  ((map.Map.get c1 i) = (map.Map.get c2 i)).

(* Why3 assumption *)
Fixpoint inverse (st:(list forest)) (c1:(map.Map.map Z color))
  (c2:(map.Map.map Z color)) {struct st}: Prop :=
  match st with
  | Init.Datatypes.nil => True
  | (Init.Datatypes.cons f st') => (((white_forest f c1) /\ (final_forest f
      c2)) \/ ((final_forest f c1) /\ (white_forest f c2))) /\ (((even_forest
      f) -> (unchanged st' c1 c2)) /\ ((~ (even_forest f)) -> (inverse st' c1
      c2)))
  end.

(* Why3 assumption *)
Fixpoint any_stack (st:(list forest)) (c:(map.Map.map Z
  color)) {struct st}: Prop :=
  match st with
  | Init.Datatypes.nil => True
  | (Init.Datatypes.cons f st1) => ((white_forest f c) \/ (final_forest f
      c)) /\ (any_stack st1 c)
  end.

Axiom any_stack_frame : forall (st:(list forest)) (c1:(map.Map.map Z color))
  (c2:(map.Map.map Z color)), (unchanged st c1 c2) -> ((any_stack st c1) ->
  (any_stack st c2)).

Axiom inverse_frame : forall (st:(list forest)) (c1:(map.Map.map Z color))
  (c2:(map.Map.map Z color)) (c3:(map.Map.map Z color)), (inverse st c1
  c2) -> ((unchanged st c2 c3) -> (inverse st c1 c3)).

Axiom inverse_frame2 : forall (st:(list forest)) (c1:(map.Map.map Z color))
  (c2:(map.Map.map Z color)) (c3:(map.Map.map Z color)), (unchanged st c1
  c2) -> ((inverse st c2 c3) -> (inverse st c1 c3)).

Axiom inverse_any : forall (st:(list forest)) (c1:(map.Map.map Z color))
  (c2:(map.Map.map Z color)), ((any_stack st c1) /\ (inverse st c1 c2)) ->
  (any_stack st c2).

Axiom inverse_final : forall (f:forest) (st:(list forest)) (c1:(map.Map.map Z
  color)) (c2:(map.Map.map Z color)), (final_forest f c1) -> ((inverse
  (Init.Datatypes.cons f st) c1 c2) -> (white_forest f c2)).

Axiom inverse_white : forall (f:forest) (st:(list forest)) (c1:(map.Map.map Z
  color)) (c2:(map.Map.map Z color)), (white_forest f c1) -> ((inverse
  (Init.Datatypes.cons f st) c1 c2) -> (final_forest f c2)).

Axiom white_final_exclusive : forall (f:forest) (c:(map.Map.map Z color)),
  (~ (f = E)) -> ((white_forest f c) -> ~ (final_forest f c)).

Axiom final_unique : forall (f:forest) (c1:(map.Map.map Z color))
  (c2:(map.Map.map Z color)), (final_forest f c1) -> ((final_forest f c2) ->
  forall (i:Z), (mem_forest i f) -> ((map.Map.get c1 i) = (map.Map.get c2
  i))).

Axiom inverse_inverse : forall (st:(list forest)) (c1:(map.Map.map Z color))
  (c2:(map.Map.map Z color)) (c3:(map.Map.map Z color)), ((inverse st c1
  c2) /\ (inverse st c2 c3)) -> (unchanged st c1 c3).

(* Why3 assumption *)
Inductive sub: (list forest) -> forest -> (map.Map.map Z color) -> Prop :=
  | Sub_reflex : forall (f:forest) (c:(map.Map.map Z color)), (sub
      (Init.Datatypes.cons f Init.Datatypes.nil) f c)
  | Sub_brother : forall (st:(list forest)) (i:Z) (f1:forest) (f2:forest)
      (c:(map.Map.map Z color)), (sub st f2 c) -> (sub st (N i f1 f2) c)
  | Sub_append : forall (st:(list forest)) (i:Z) (f1:forest) (f2:forest)
      (c:(map.Map.map Z color)), (sub st f1 c) -> (((map.Map.get c
      i) = Black) -> (sub
      (Init.Datatypes.app st (Init.Datatypes.cons f2 Init.Datatypes.nil))
      (N i f1 f2) c)).

Axiom sub_not_nil : forall (f:forest) (c:(map.Map.map Z color)), ~ (sub
  Init.Datatypes.nil f c).

Axiom sub_empty : forall (st:(list forest)) (f0:forest) (c:(map.Map.map Z
  color)), (~ (st = Init.Datatypes.nil)) -> ((sub (Init.Datatypes.cons E st)
  f0 c) -> (sub st f0 c)).

Axiom sub_mem : forall (n:Z) (st:(list forest)) (f:forest) (c:(map.Map.map Z
  color)), (mem_stack n st) -> ((sub st f c) -> (mem_forest n f)).

Axiom sub_weaken1 : forall (st:(list forest)) (i:Z) (f1:forest) (f2:forest)
  (f0:forest) (c:(map.Map.map Z color)), (sub (Init.Datatypes.cons (N i f1
  f2) st) f0 c) -> (sub (Init.Datatypes.cons f2 st) f0 c).

Axiom sub_weaken2 : forall (st:(list forest)) (i:Z) (f1:forest) (f2:forest)
  (f0:forest) (c:(map.Map.map Z color)), (sub (Init.Datatypes.cons (N i f1
  f2) st) f0 c) -> (((map.Map.get c i) = Black) -> (sub
  (Init.Datatypes.cons f1 (Init.Datatypes.cons f2 st)) f0 c)).

Axiom not_mem_st : forall (i:Z) (f:forest) (st:(list forest)) (c:(map.Map.map
  Z color)), (~ (mem_forest i f)) -> ((sub st f c) -> ~ (mem_stack i st)).

Axiom sub_frame : forall (st:(list forest)) (f0:forest) (c:(map.Map.map Z
  color)) (c':(map.Map.map Z color)), (no_repeated_forest f0) ->
  ((forall (i:Z), (~ (mem_stack i st)) -> ((mem_forest i f0) ->
  ((map.Map.get c' i) = (map.Map.get c i)))) -> ((sub st f0 c) -> (sub st f0
  c'))).

(* Why3 assumption *)
Definition disjoint_stack (f:forest) (st:(list forest)): Prop :=
  forall (i:Z), (mem_forest i f) -> ~ (mem_stack i st).

Axiom sub_no_rep : forall (f:forest) (st':(list forest)) (f0:forest)
  (c:(map.Map.map Z color)), (sub (Init.Datatypes.cons f st') f0 c) ->
  ((no_repeated_forest f0) -> (no_repeated_forest f)).

Axiom sub_no_rep2 : forall (f:forest) (st':(list forest)) (f0:forest)
  (c:(map.Map.map Z color)), (sub (Init.Datatypes.cons f st') f0 c) ->
  ((no_repeated_forest f0) -> (disjoint_stack f st')).

Axiom white_valid : forall (f:forest) (c:(map.Map.map Z color)),
  (white_forest f c) -> (valid_coloring f c).

Axiom final_valid : forall (f:forest) (c:(map.Map.map Z color)),
  (final_forest f c) -> (valid_coloring f c).

Axiom valid_coloring_frame : forall (f:forest) (c1:(map.Map.map Z color))
  (c2:(map.Map.map Z color)), (valid_coloring f c1) -> ((forall (i:Z),
  (mem_forest i f) -> ((map.Map.get c2 i) = (map.Map.get c1 i))) ->
  (valid_coloring f c2)).

Axiom valid_coloring_set : forall (f:forest) (i:Z) (c:(map.Map.map Z color)),
  (valid_coloring f c) -> ((~ (mem_forest i f)) -> (valid_coloring f
  (map.Map.set c i Black))).

Axiom head_and_tail : forall {a:Type} {a_WT:WhyType a}, forall (f1:a) (f2:a)
  (st1:(list a)) (st2:(list a)),
  ((Init.Datatypes.cons f1 st1) = (Init.Datatypes.app st2 (Init.Datatypes.cons f2 Init.Datatypes.nil))) ->
  ((~ (st2 = Init.Datatypes.nil)) -> exists st:(list a),
  (st1 = (Init.Datatypes.app st (Init.Datatypes.cons f2 Init.Datatypes.nil))) /\
  (st2 = (Init.Datatypes.cons f1 st))).

Axiom sub_valid_coloring_f1 : forall (i:Z) (f1:forest) (f2:forest)
  (c:(map.Map.map Z color)) (i1:Z), (no_repeated_forest (N i f1 f2)) ->
  ((valid_coloring (N i f1 f2) c) -> (((map.Map.get c i) = Black) ->
  ((mem_forest i1 f1) -> ((valid_coloring f1 (map.Map.set c i1 Black)) ->
  (valid_coloring (N i f1 f2) (map.Map.set c i1 Black)))))).

Parameter st: (list forest).

Parameter i: Z.

Parameter f1: forest.

Parameter f2: forest.

Parameter c: (map.Map.map Z color).

Axiom H : (sub st f1 c).

Axiom H1 : forall (i1:Z) (f11:forest) (f21:forest) (st1:(list forest)),
  ((Init.Datatypes.cons (N i1 f11 f21) st1) = st) -> ((no_repeated_forest
  f1) -> ((valid_coloring f1 c) -> (valid_coloring f1 (map.Map.set c i1
  Black)))).

Axiom H2 : ((map.Map.get c i) = Black).

Parameter f0: forest.

Parameter i1: Z.

Parameter f11: forest.

Parameter f21: forest.

Parameter st1: (list forest).

Parameter c1: (map.Map.map Z color).

Axiom H3 : (c1 = c).

Axiom H4 : (f0 = (N i f1 f2)).

Axiom H5 : ((Init.Datatypes.cons (N i1 f11
  f21) st1) = (Init.Datatypes.app st (Init.Datatypes.cons f2 Init.Datatypes.nil))).

Axiom H6 : (no_repeated_forest f0).

Axiom H7 : (valid_coloring f0 c1).

Require Import Why3.
Ltac ae := why3 "alt-ergo" timelimit 15.
Ltac cvc4 := why3 "cvc4" timelimit 15.

(* Why3 goal *)
Theorem sub_valid_coloring : forall (x:Z) (x1:forest) (x2:forest), (f0 = (N x
  x1 x2)) -> (valid_coloring x2 (map.Map.set c1 i1 Black)).
(* Why3 intros x x1 x2 h1. *)
intros x x1 x2 h1.
rewrite H4 in *.
injection h1.
intros; subst.
apply valid_coloring_set.
generalize H7. rewrite H4. inversion 1. trivial.
destruct (head_and_tail (N i1 f11 f21) f2 st1 st). apply H5.
red; intro. generalize H. rewrite H0. apply sub_not_nil.
generalize H6. rewrite H4. inversion 1.
cvc4.
Qed.

