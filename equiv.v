Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.


Require Import LIR.pallene.
Require Import LIR.lir.
Require Import LIR.dyn.
Require Import LIR.biglir.


Definition dynEq (e1 e2 : IRE) := dyn e1 = dyn e2.


Infix "~~" := dynEq  (at level 80, no associativity).


Lemma eqRefl : forall e, e ~~ e.
Proof. unfold dynEq. trivial. Qed.


Lemma eqDyn : forall e, e ~~ dyn e.
Proof. unfold dynEq. auto using dynIdempotent. Qed.


Lemma eqSubst : forall e1 e2 e1' e2' var,
    e1 ~~ e1' ->
    e2 ~~ e2' ->
    ([var := e1]e2) ~~ ([var := e1']e2').
Proof.
  unfold dynEq.
  intros e1 e2 e1' e2' var H1 H2.
  rewrite <- dynSubst; rewrite <- dynSubst; congruence.
Qed.


Definition dynEqMem (m1 m2 : Mem) := dynMem m1 = dynMem m2.


Infix "~M~" := dynEqMem  (at level 80, no associativity).


Lemma eqIndex : forall e1 e2, e1 ~~ e2 -> ToIndex e1 = ToIndex e2.
Proof. unfold dynEq. intros e1 e2 H.
  rewrite DynIndex. rewrite (DynIndex e2). congruence.
Qed.


Lemma eqQuery : forall m1 m2 a idx,
  m1 ~M~ m2 -> query a idx m1 ~~ query a idx m2.
Proof.
  unfold dynEq. unfold dynEqMem.
  induction m1; intros ? ? ? ?; destruct m2; try easy.
  simpl in H. inversion H; subst.
  rewrite dynQuery.
  rewrite dynQuery.
  f_equal. simpl. congruence.
Qed.
  

Lemma eqUpdate : forall m1 m2 e1 e2 a idx,
  m1 ~M~ m2 -> e1 ~~ e2 -> Update a idx e1 m1 ~M~ Update a idx e2 m2.
Proof.
  unfold dynEq. unfold dynEqMem.
  intros. simpl. congruence.
Qed.


Theorem eqSym : forall m1 m2 e t m' e',
  m1 / e ==> m' / e' ->
  MEmpty |= e : t -> mem_correct m1 ->
  m1 ~M~ m2 ->
  exists dm' de', m2 / dyn e ==> dm' / de' /\ m' ~M~ dm' /\ de' ~~ e'.
Proof.
  unfold dynEq. unfold dynEqMem.
  intros m1 m2 e t m' e' Hstep.
  generalize dependent m2.
  generalize dependent t.
  induction Hstep; intros ? ? Hty HMC HM2.
  - exists m2. exists (dyn e). split; (only 2: split).
    + eauto using BStValue, dynValue.
    + congruence.
    + eauto using dynIdempotent.
  - inversion Hty; subst.
    specialize (IHHstep1 _ m2 H2 HMC HM2) as [? [? [? [? ?]]]]. 
    assert (mem_correct m') by (eapply BPreservation; eauto).
    specialize (IHHstep2 _ x H4 H3 H0) as [? [? [? [? ?]]]].
    eexists. eexists. split; (only 2: split).
    + simpl. eapply BStBox. eapply BStPlus.
      * eapply BStUnbox. eauto.
  



