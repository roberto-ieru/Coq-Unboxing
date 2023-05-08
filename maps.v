(*
** Maps used to represent environments in all three languages.
*)


Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.


(*
** A Map maps strings to A.
*)
Inductive Map (A : Type) : Type :=
| MEmpty : Map A
| MCons : string -> A -> Map A -> Map A
.

Arguments MEmpty {A}.
Arguments MCons {A}.

Notation "v |=> T ; M" := (MCons v T M) (at level 40).


Ltac breakStrDec :=
  simpl in *;
  repeat match goal with
  | [ |- context [string_dec ?v ?v'] ] =>
      destruct (string_dec v v'); subst; try easy
  | [ H: context [string_dec ?v ?v'] |- _ ] =>
      destruct (string_dec v v') in H; subst; try easy
end.


(*
** Return 'M[var]' (None if absent)
*)
Fixpoint In {A} M var : option A :=
  match M with
  | MEmpty => None
  | var' |=> T; M' => if string_dec var var' then Some T else In M' var
  end.


Lemma InEq : forall A (M : Map A) var r, In (var |=> r; M) var = Some r.
Proof. intros; breakStrDec. Qed.


Lemma InEq' : forall A (M : Map A) var r r',
    In (var |=> r; M) var = Some r' -> r = r'.
Proof. intros * H. rewrite InEq in H. injection H. trivial. Qed.


Lemma InNotEq' : forall A (M : Map A) var var' r,
    var <> var' -> In (var' |=> r; M) var = In M var.
Proof. intros; breakStrDec. Qed.


Lemma InNotEq : forall A (M : Map A) var var' r r',
    var <> var' -> In (var' |=> r; M) var = r' -> In M var = r'.
Proof. intros * HNeq Heq. rewrite InNotEq' in Heq; trivial. Qed.


Definition inclusion {A} (M : Map A) M' :=
  forall x v, In M x = Some v -> In M' x = Some v.


Lemma inclusion_empty : forall A (M : Map A), inclusion MEmpty M.
Proof. unfold inclusion. inversion 1. Qed.


Lemma inclusion_refl : forall A (M : Map A), inclusion M M.
Proof. unfold inclusion. trivial. Qed.


Lemma inclusion_update : forall A (M : Map A) M' var tvar,
  inclusion M M' -> inclusion (var |=> tvar ; M) (var |=> tvar ; M').
Proof.
  unfold inclusion; intros; breakStrDec; auto.
Qed.


Lemma inclusion_shadow : forall A (M : Map A) var t1 t2,
  inclusion (var |=> t1; (var |=> t2; M)) (var |=> t1; M).
Proof.
  unfold inclusion; intros; breakStrDec.
Qed.


Lemma inclusion_shadow' : forall A (M : Map A) var t1 t2,
  inclusion (var |=> t1; M) (var |=> t1; (var |=> t2; M)).
Proof.
  unfold inclusion; intros; breakStrDec.
Qed.


Lemma inclusion_permute : forall A (M : Map A) var1 var2 t1 t2,
  var1 <> var2 ->
  inclusion (var1 |=> t1; (var2 |=> t2; M))
            (var2 |=> t2; (var1 |=> t1; M)).
Proof.
  unfold inclusion; intros; breakStrDec.
Qed.


Lemma InInclusionEq : forall A (M M' : Map A) var t,
    inclusion (var |=> t; M) M' ->
    In M' var = Some t.
Proof.
  unfold inclusion; eauto using InEq.
Qed.


Lemma InInclusion : forall A (M M' : Map A) var t,
    inclusion (var |=> t; M) M' ->
    In M' var = Some t.
Proof.
  unfold inclusion; intros; eauto using InEq.
Qed.


Definition map_eq {A} (M M' : Map A) := forall var, In M var = In M' var.


Lemma map_eq_In : forall {A} (M M': Map A) var v v',
    In M' var = Some v ->
    map_eq (var |=> v'; M) M' ->
    v = v'.
Proof.
  intros * HI HEq.
  replace (In M' var) with (Some v') in *; try congruence.
  specialize (HEq var). rewrite InEq in HEq. congruence.
Qed.


Lemma map_eq_incl : forall {A} (M M': Map A),
    map_eq M M' -> inclusion M M'.
Proof.
  unfold inclusion; unfold map_eq; intros; congruence.
Qed.


(* map_eq is an equivalence relation *)

Lemma map_eq_refl : forall A (M : Map A), map_eq M M.
Proof. unfold map_eq; trivial. Qed.

Lemma map_eq_sym : forall A (M M': Map A), map_eq M M' -> map_eq M' M.
Proof. unfold map_eq; auto. Qed.

Lemma map_eq_trans : forall A (M M' M'': Map A),
    map_eq M M' ->
    map_eq M' M'' ->
    map_eq M M''.
Proof. unfold map_eq; intros; congruence. Qed.


Lemma eqeq_shadow : forall A (M M' : Map A) var v v',
   map_eq (var |=> v'; M) M' ->
   map_eq (var |=> v; M) (var |=> v; M').
Proof.
  intros * H1.
  intros var'.
  breakStrDec.
  specialize (H1 var').
  rewrite InNotEq' in H1; trivial.
Qed.


Lemma eq_shadow : forall A (M : Map A) var v v',
   map_eq (var |=> v; M) (var |=> v; (var |=> v'; M)).
Proof.
  intros; eauto using eqeq_shadow, map_eq_refl.
Qed.


Lemma eqeq_permute : forall A (M M' : Map A) var var' v v',
   map_eq (var |=> v; M) M' ->
   var <> var' ->
   map_eq (var |=> v; (var' |=> v'; M)) (var' |=> v'; M').
Proof.
  intros * H ?.
  intros var0.
  specialize (H var0).
  breakStrDec.
Qed.


