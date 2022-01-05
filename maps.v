
Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.



Inductive Map (A : Type) : Type :=
| MEmpty : Map A
| MCons : string -> A -> Map A -> Map A
.

Arguments MEmpty {A}.
Arguments MCons {A}.

Notation "v |=> T ; M" := (MCons v T M) (at level 40).


Ltac breakStrDec :=
  repeat match goal with
  | [ |- context [string_dec ?v ?v'] ] =>
      destruct (string_dec v v'); subst; try easy
  | [ H: context [string_dec ?v ?v'] |- _ ] =>
      destruct (string_dec v v') in H; subst; try easy
end.


Fixpoint In {A} M var : option A :=
  match M with
  | MEmpty => None
  | var' |=> T; M' => if string_dec var var' then Some T else In M' var
  end.


Lemma InEq' : forall A (M : Map A) var r r',
    In (var |=> r; M) var = Some r' -> r = r'.
Proof. intros. simpl in *. breakStrDec.
       congruence.
Qed.


Lemma InEq : forall A (M : Map A) var r, In (var |=> r; M) var = Some r.
Proof. intros. simpl. breakStrDec. Qed.


Lemma InNotEq : forall A (M : Map A) var var' r r',
    var <> var' -> In (var' |=> r; M) var = r' -> In M var = r'.
Proof. intros. simpl in *. breakStrDec. Qed.


Lemma InNotEq' : forall A (M : Map A) var var' r,
    var <> var' -> In (var' |=> r; M) var = In M var.
Proof. intros. simpl in *. breakStrDec. Qed.


Definition inclusion {A} (M : Map A) M' :=
  forall x v, In M x = Some v -> In M' x = Some v.


Lemma inclusion_empty : forall A (M : Map A), inclusion MEmpty M.
Proof.
  unfold inclusion. intros A M x v H. inversion H.
Qed.


Lemma inclusion_refl : forall A (M : Map A), inclusion M M.
Proof. unfold inclusion. trivial. Qed.

Lemma inclusion_update : forall A (M : Map A) M' var tvar,
  inclusion M M' -> inclusion (var |=> tvar ; M) (var |=> tvar ; M').
Proof.
  intros A M M' var tvar Hinc.
  unfold inclusion; intros v tv Hin.
  simpl in *; breakStrDec; auto.
Qed.


Lemma inclusion_shadow : forall A (M : Map A) var t1 t2,
  inclusion (var |=> t1; (var |=> t2; M)) (var |=> t1; M).
Proof.
  unfold inclusion.
  intros A M var t1 t2 var' t' Hin.
  simpl. breakStrDec.
  - rewrite InEq in Hin. congruence with InEq.
  - eauto using InNotEq.
Qed.


Lemma inclusion_shadow' : forall A (M : Map A) var t1 t2,
  inclusion (var |=> t1; M) (var |=> t1; (var |=> t2; M)).
Proof.
  unfold inclusion.
  intros A M var t1 t2 var' t' Hin.
  simpl in *; breakStrDec.
Qed.


Lemma inclusion_permute : forall A (M : Map A) var1 var2 t1 t2,
  var1 <> var2 ->
  inclusion (var1 |=> t1; (var2 |=> t2; M))
            (var2 |=> t2; (var1 |=> t1; M)).
Proof.
  unfold inclusion. simpl.
  intros A M var1 var2 t1 t2 Hneq var' t' HIn.
  breakStrDec.
Qed.


Lemma InInclusionEq : forall A (M M' : Map A) var t, 
    inclusion (var |=> t; M) M' ->
    In M' var = Some t.
Proof.
  intros * HI.
  unfold inclusion in HI.
  apply HI.
  eauto using InEq.
Qed.


Lemma InInclusion : forall A (M M' : Map A) var t, 
    inclusion (var |=> t; M) M' ->
    In M' var = Some t.
Proof.
  intros * HI.
  unfold inclusion in HI.
  apply HI.
  eauto using InEq.
Qed.


Definition map_eq {A} (M M' : Map A) := forall var, In M var = In M' var.


Lemma eq_shadow : forall A (M : Map A) var t1 t2,
   map_eq (var |=> t1; M) (var |=> t1; (var |=> t2; M)).
Proof.
  intros A M var t1 t2.
  intros var'.
  simpl.
  breakStrDec.
Qed.


