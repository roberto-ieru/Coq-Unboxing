Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.

Require Import LIR.lir.

Require Import LIR.dyn.


Reserved Notation "m '/' e ==> m1 '/' e1"
(at level 40, e at level 39, m1 at level 39, e1 at level 39).
Reserved Notation "m '/' e ==> 'fail'"
(at level 40, e at level 39).

Inductive bigStep : Mem -> IRE -> Mem -> IRE -> Prop :=
| BStValue : forall m e, Value e -> m / e ==> m / e
| BStPlus : forall m e1 m' n1 e2 m'' n2,
    m / e1 ==> m' / IRENum n1 ->
    m'/ e2 ==> m'' / IRENum n2 ->
    m / IREPlus e1 e2 ==> m'' / IRENum (n1 + n2)
| BStCstr : forall m m' free,
    (free, m') = fresh m ->
    m / IRECnst ==> m' / IREAddr free
| BStGet : forall m e1 m' a e2 m'' v idx,
    m / e1 ==> m' / IREAddr a ->
    m'/ e2 ==> m'' / idx ->
    v = query a idx m'' ->
    m / IREGet e1 e2 ==> m'' / v
| BStSet : forall m e1 m' a e2 m'' idx m''' e3 val,
    m / e1 ==> m' / IREAddr a ->
    m'/ e2 ==> m'' / idx ->
    m''/ e3 ==> m''' / val ->
    m / IRESet e1 e2 e3 ==> Update a (ToIndex idx) val m''' / val
| BStLet : forall m exp m' v1 var t body m'' res,
     m / exp ==> m' / v1 ->
     m' / ([var := v1] body) ==> m'' / res ->
     m / IRELet var t exp body ==> m'' / res
| BStFunapp : forall m e1 m' var body e2 m'' v2 m''' res,
    m / e1 ==> m' / IREFun var body ->
    m' / e2 ==> m'' / v2 ->
    m'' / ([var := v2] body) ==> m''' / res ->
    m / IREFunApp e1 e2 ==> m''' / res
| BStBox : forall m e m' e' t,
    m / e ==> m' / e' ->
    m / IREBox t e ==> m' / IREBox t e'
| BStUnbox : forall m e m' t e',
    m / e ==> m' / IREBox t e' ->
    m / IREUnbox t e ==> m' / e'

where "m / e ==> m1 / e1" := (bigStep m e m1 e1)
.

Inductive bigStepF : Mem -> IRE -> Prop :=
| BStPlus1F : forall m e1 e2,
    m / e1 ==> fail ->
    m / IREPlus e1 e2 ==> fail
| BStPlus2F : forall m e1 m' n1 e2,
    m / e1 ==> m' / IRENum n1 ->
    m' / e2 ==> fail ->
    m / IREPlus e1 e2 ==> fail
| BStGet1F : forall m e1 e2,
    m / e1 ==> fail ->
    m / IREGet e1 e2 ==> fail
| BStGet2F : forall m e1 m' a e2,
    m / e1 ==> m' / IREAddr a ->
    m' / e2 ==> fail ->
    m / IREGet e1 e2 ==> fail
| BStSet1F : forall m e1 e2 e3,
    m / e1 ==> fail ->
    m / IRESet e1 e2 e3 ==> fail
| BStSet2F : forall m e1 m' a e2 e3,
    m / e1 ==> m' / IREAddr a ->
    m'/ e2 ==> fail ->
    m / IRESet e1 e2 e3 ==> fail
| BStSet3F : forall m e1 m' a e2 m'' idx e3,
    m / e1 ==> m' / IREAddr a ->
    m'/ e2 ==> m'' / IRENum idx ->
    m''/ e3 ==> fail ->
    m / IRESet e1 e2 e3 ==> fail
| BStLet1F : forall m exp var t body,
     m / exp ==> fail ->
     m / IRELet var t exp body ==> fail
| BStLet2F : forall m exp m' v1 var t body,
     m / exp ==> m' / v1 ->
     m' / ([var := v1] body) ==> fail ->
     m / IRELet var t exp body ==> fail
| BStFunapp1F : forall m e1 e2,
    m / e1 ==> fail ->
    m / IREFunApp e1 e2 ==> fail
| BStFunapp2F : forall m e1 m' v1 e2,
    m / e1 ==> m' / v1 ->
    m' / e2 ==> fail ->
    m / IREFunApp e1 e2 ==> fail
| BStFunapp3F : forall m e1 m' var body e2 m'' v2,
    m / e1 ==> m' / IREFun var body ->
    m' / e2 ==> m'' / v2 ->
    m'' / ([var := v2] body) ==> fail ->
    m / IREFunApp e1 e2 ==> fail
| BStBox1F : forall m e t,
    m / e ==> fail ->
    m / IREBox t e ==> fail
| BStUnboxF : forall m e m' t t' e',
    m / e ==> m' / IREBox t e' ->
    t <> t' ->
    m / IREUnbox t' e ==> fail
| BStUnbox1F : forall m e t,
    m / e ==> fail ->
    m / IREUnbox t e ==> fail

where "m / e ==> 'fail'" := (bigStepF m e)
.


Lemma splitAnd : forall A B C,
    (A -> (B /\ C)) -> (A -> B) /\ (A -> C).
Proof. intros. intuition. Qed.


Ltac splitAnd :=
  repeat match goal with
  [ H: _ -> _ /\ _ |- _ ] => apply splitAnd in H; destruct H end.


Lemma valueNormal : forall m e m' res,
    bigStep m e m' res -> Value e -> m = m' /\ res = e.
Proof.
  intros m e m' res HB HV.
  induction HB; inversion HV; subst; eauto using Value;
  splitAnd;
  intuition congruence.
Qed.


Lemma BPreservation : forall (m m' : Mem) e e' t,
  m / e ==> m' / e' ->
  mem_correct m ->
  MEmpty |= e : t ->
     mem_correct m' /\ MEmpty |= e' : t /\ Value e'.
Proof.
  intros m m' e e' t Hst HMC HTy.
  remember MEmpty as Γ.
  generalize dependent t.
  induction Hst; intros ? HTy;
  (* apply type judgment and break 'and's *)
  inversion HTy; subst; split;
  (* instantiate induction hypotheses when possible *)
  repeat match goal with
  | [ HM : mem_correct ?M,
      HT : _ |= ?E : _,
      IH : mem_correct ?M -> _ -> _ |= ?E : _ -> _ |- _] =>
        specialize (IH HM _ HT) as [? [? ?]]
  end;
  eauto using IRTyping,Value,mem_correct_fresh,mem_correct_update;
  (* handle substitutions inside FUN (not pretty yet) *)
  try (assert (MEmpty |= [var := v2] body : IRTStar) by (
      inversion H0; inversion H9; subst; eauto using subst_typing);
    eapply IHHst3; eauto).
  - (* use mem_correct for queries *)
    split; auto using MCTy, MCValue.
  - eapply IHHst2; eauto.
    inversion HTy; subst. eauto using subst_typing.
  - eapply IHHst2; eauto.
    inversion HTy; subst. eauto using subst_typing.
  - (* Unboxing step needs an extra inversion on type judgment
       and value to get inside the boxed value *)
    split.
    * inversion H0; trivial.
    * inversion H1; trivial.
Qed.


Lemma BstepValue : forall (m m' : Mem) e e' t,
  m / e ==> m' / e' ->
  mem_correct m ->
  MEmpty |= e : t ->
  Value e'.
Proof. apply BPreservation. Qed.


Lemma BstepTy : forall (m m' : Mem) e e' t,
  m / e ==> m' / e' ->
  mem_correct m ->
  MEmpty |= e : t ->
  MEmpty |= e' : t.
Proof. apply BPreservation. Qed.


(* Propagate 'mem_correct' to all memories *)
Ltac memC :=
  match goal with
    | [ M : Mem |- _] =>  (* for all memories *)
      match goal with
      | [ H : mem_correct M |- _] => fail 1  (* already done *)
      | [ |- _] =>  (* else *)
         assert(mem_correct M) by (eapply BPreservation; eauto)
      end
    end.

(*
** {==================================================================
** Equivalence big step - small step
** ===================================================================
*)

Lemma stepBigstep : forall m e m' e' m'' e'',
    mem_correct m ->
    m / e --> m' / e' -> m' / e' ==> m'' / e'' -> m / e ==> m'' / e''.
Proof.
  intros m e m' e' m'' e'' HM HSt HB.
  remember (Some e') as E eqn:HEq.
  generalize dependent e'.
  generalize dependent m''.
  generalize dependent e''.
  induction HSt; intros ? ? ? HEq HB; inversion HEq; clear HEq; subst;
  inversion HB; subst;
  (* ~half cases values are not values *)
  try match goal with
  | [ H: Value _ |- _ ] =>
      inversion H; subst; eauto using bigStep,Value; fail
  end;
  (* rewrite queries to its real values in the step *)
  repeat match goal with
  | [ H: _ = query _ _ _ |- _ ] => rewrite <- H in HB end;
  (* extract equalities from "value" steps *)
  repeat match goal with
  | [ HB: bigStep _ _ _ _ |- _] =>
    eapply valueNormal in HB; only 2: (eauto using Value; fail);
    intuition; subst
  end;
  (* extract equalities from injections *)
  repeat match goal with
  | [H: Some _ = Some _ |- _] => idtac H; injection H as H; subst
  end;
  (* clear useless equalities *)
  repeat match goal with | [H: ?E = ?E |- _] => clear H end;
  eauto using bigStep,Value;
  (* contradictions about query not being a value *)
  try match goal with
    |[H: ?E = query _ _ _ |- _] =>
        assert (HC: Value E) by (rewrite H; apply HM); inversion HC
    end; subst.
  - (* queries being complex values (fun and lambdas which must be
     broken to extract some equalities *)
    eapply valueNormal in HB as [? ?]; subst; trivial;
    eapply BStGet; eauto using bigStep, Value; congruence.
  - inversion H3; subst.
    eapply BStSet; eauto using bigStep, Value; congruence.
Qed.


Theorem smallBig : forall m e t m' e',
    mem_correct m ->
    MEmpty |= e : t ->
    m / e -->* m' / e' ->
    Value e' ->
    m / e ==> m' / e'.
Proof.
  intros m e t m' e' MC MTy MSt.
  remember (Some e') as E'.
  generalize dependent e'.
  induction MSt; intros ? HEq HV; inversion HEq; subst; clear HEq;
  eauto using bigStep, stepBigstep, PresMC, PresTy.
Qed.


Ltac finishmExp :=
  intros m e m' e' Hmt;
  remember (Some e') as E' eqn:Heq;
  generalize dependent e';
  induction Hmt; intros ? Heq; inversion Heq; subst;
  eauto using step,multistep.


Lemma mPlus1 : forall e2 m e m' e',
    m / e -->* m' / e' ->  m / IREPlus e e2 -->* m' / IREPlus e' e2.
Proof. intros e2; finishmExp. Qed.

Lemma mPlus2 : forall e1, Value e1 -> forall m e m' e',
    m / e -->* m' / e' ->  m / IREPlus e1 e -->* m' / IREPlus e1 e'.
Proof. intros e1 HV; finishmExp. Qed.

Lemma mGet1 : forall e2 m e m' e',
    m / e -->* m' / e' ->  m / IREGet e e2 -->* m' / IREGet e' e2.
Proof. intros e2; finishmExp. Qed.

Lemma mGet2 : forall e1, Value e1 -> forall m e m' e',
    m / e -->* m' / e' ->  m / IREGet e1 e -->* m' / IREGet e1 e'.
Proof. intros e1 HV; finishmExp. Qed.

Lemma mSet1 : forall e2 e3 m e m' e',
    m / e -->* m' / e' ->  m / IRESet e e2 e3 -->* m' / IRESet e' e2 e3.
Proof. intros e2 e3; finishmExp. Qed.

Lemma mSet2 : forall e1, Value e1 -> forall e3 m e m' e',
    m / e -->* m' / e' ->  m / IRESet e1 e e3 -->* m' / IRESet e1 e' e3.
Proof. intros e1 HV e3; finishmExp. Qed.

Lemma mSet3 : forall e1 e2, Value e1 -> Value e2 -> forall m e m' e',
    m / e -->* m' / e' ->  m / IRESet e1 e2 e -->* m' / IRESet e1 e2 e'.
Proof. intros e1 e2 HV1 HV2; finishmExp. Qed.

Lemma mLet1 : forall var t body m e m' e',
    m / e -->* m' / e' ->
    m / IRELet var t e body -->* m' / IRELet var t e' body.
Proof. intros var t body; finishmExp. Qed.

Lemma mFunapp1 : forall e2 m e m' e',
    m / e -->* m' / e' ->  m / IREFunApp e e2 -->* m' / IREFunApp e' e2.
Proof. intros e2; finishmExp. Qed.

Lemma mFunapp2 : forall e1, Value e1 -> forall m e m' e',
    m / e -->* m' / e' ->  m / IREFunApp e1 e -->* m' / IREFunApp e1 e'.
Proof. intros e1 HV; finishmExp. Qed.

Lemma mBox1 : forall t m e m' e',
    m / e -->* m' / e' ->  m / IREBox t e -->* m' / IREBox t e'.
Proof.
  intros t; finishmExp. Qed.

Lemma mUnbox1 : forall t m e m' e',
    m / e -->* m' / e' ->  m / IREUnbox t e -->* m' / IREUnbox t e'.
Proof. intros t; finishmExp. Qed.


Lemma invertTyBox : forall t e, Value (IREBox t e) -> Value e.
Proof. intros t e H. inversion H. trivial. Qed.


Theorem bigSmall : forall m e t m' e',
    mem_correct m ->
    MEmpty |= e : t ->
    m / e ==> m' / e' ->
    m / e -->* m' / e'.
Proof.
  intros m e t m' e' HM ? HSt.
  generalize dependent t.
  induction HSt; intros ? HTy;
  inversion HTy; subst;
  repeat memC;
  repeat match goal with
    [ IH: mem_correct ?M  -> _ -> IRTyping _ ?E _ -> _,
      HM: mem_correct ?M,
      HT: IRTyping _ ?E _ |- _] =>
        specialize (IH HM _ HT)
    end;
    eauto using multistep.
  - eauto 6 using mPlus1, mPlus2, Value, multistep1, step, multiRefl.
  - eauto using multistep1, step.
  - eauto 8 using mGet1, mGet2, Value, multistep1, step, multiRefl,
                  BstepValue.
  - eauto 12 using mSet1, mSet2, mSet3,  Value, multistep1, step, multiRefl,
                  BstepValue.
  - eapply multiRefl.
    * eauto using mLet1.
    * eapply multiRefl.
      ** eauto using multistep1, StLet, BstepValue.
      ** eauto using subst_typing, BstepValue, BstepTy.
  - eapply multiRefl.
    + eauto using mFunapp1.
    + eapply multiRefl.
      ** eauto using mFunapp2, Value.
      ** eapply multiRefl.
         *** eauto using multistep1, StFunapp, Value, BstepValue.
         *** eapply IHHSt3; eauto.
             assert (HTyF : MEmpty |= IREFun var body : TgFun)
                by (eapply BPreservation; eauto).
             inversion HTyF; subst.
             eapply subst_typing; eauto.
             eapply BPreservation; eauto.
  - auto using mBox1.
  - eauto 8 using multiRefl, mUnbox1, multistep1,
      StUnbox, invertTyBox, BstepValue.
Qed.


(* }================================================================== *)


Theorem bigDyn : forall e t m e' m',
   m / e ==> m' / e' -> MEmpty |= e : t -> mem_correct m ->
   dynMem m / dyn e ==> dynMem m' / dyn e'.
Proof.
  intros e t m e' m' HB HTy HM.
  remember MEmpty as Γ eqn:Heq.
  generalize dependent t.
  induction HB; intros ? HTy;
  inversion Heq; inversion HTy; subst; simpl;
  try match goal with [H : Value _ |- _] => inversion H end;
  repeat memC;
  simpl;
  try (eapply BStValue; eauto using Value; fail);
  eauto using Value,BStValue,dynValue,dynFresh,bigStep;
  repeat match goal with
    | [ MC: mem_correct ?M,
        HT: MEmpty |= ?E : _,
        IH: mem_correct ?M -> forall _, MEmpty |= ?E : _ -> _
         |- _] =>
        specialize (IH MC _ HT); simpl in IH
    end; eauto using bigStep.
  - rewrite dynQuery. eauto using bigStep.
  - rewrite DynIndex. eauto using bigStep.
  - eapply BStLet; eauto. rewrite dynSubst.
    eapply IHHB2; eauto.
    eapply subst_typing; eauto. eauto using BstepTy.
  - eapply BStFunapp; eauto.
    + eapply BStUnbox. eauto.
    + rewrite dynSubst. eapply IHHB3; eauto.
      eapply subst_typing; eauto using BstepTy.
      assert (HTyF: MEmpty |= IREFun var body : TgFun).
      { eapply BPreservation; eauto. }
      inversion HTyF; subst. eauto.
Qed.


