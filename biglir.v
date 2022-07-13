Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.

Require Import LIR.lir.


(*
** Bigstep semantics for Lir; regular case
*)
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
    (free, m') = freshT m ->
    m / IRENew ==> m' / IRETAddr free
| BStGet : forall m e1 m' a e2 m'' v idx,
    m / e1 ==> m' / IRETAddr a ->
    m'/ e2 ==> m'' / idx ->
    v = queryT a idx m'' ->
    m / IREGet e1 e2 ==> m'' / v
| BStSet : forall m e1 m' a e2 m'' idx m''' e3 val vval,
    m / e1 ==> m' / IRETAddr a ->
    m'/ e2 ==> m'' / idx ->
    val = EV2Val vval ->
    m''/ e3 ==> m''' / val ->
    m / IRESet e1 e2 e3 ==> UpdateT a (ToIndex idx) vval m''' / IRENil
| BStLet : forall m exp m' v1 var t body m'' res,
     m / exp ==> m' / v1 ->
     m' / ([var := v1] body) ==> m'' / res ->
     m / IRELet var t exp body ==> m'' / res
| BStFun : forall m m' v b free,
    (free, m') = freshF m v b ->
    m / IREFun v b ==> m' / IREFAddr free
| BStApp : forall m e1 m' a var body e2 m'' v2 m''' res,
    m / e1 ==> m' / IREFAddr a ->
    m' / e2 ==> m'' / v2 ->
    (var, body) = queryF a m'' ->
    m'' / ([var := v2] body) ==> m''' / res ->
    m / IREApp e1 e2 ==> m''' / res
| BStBox : forall m e m' e' t,
    m / e ==> m' / e' ->
    m / IREBox t e ==> m' / IREBox t e'
| BStUnbox : forall m e m' t e',
    m / e ==> m' / IREBox t e' ->
    m / IREUnbox t e ==> m' / e'

where "m / e ==> m1 / e1" := (bigStep m e m1 e1)
.

(*
** Bigstep semantics for Lir; error case
*)
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
    m / e1 ==> m' / IRETAddr a ->
    m' / e2 ==> fail ->
    m / IREGet e1 e2 ==> fail
| BStSet1F : forall m e1 e2 e3,
    m / e1 ==> fail ->
    m / IRESet e1 e2 e3 ==> fail
| BStSet2F : forall m e1 m' a e2 e3,
    m / e1 ==> m' / IRETAddr a ->
    m'/ e2 ==> fail ->
    m / IRESet e1 e2 e3 ==> fail
| BStSet3F : forall m e1 m' a e2 m'' idx e3,
    m / e1 ==> m' / IRETAddr a ->
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
| BStApp1F : forall m e1 e2,
    m / e1 ==> fail ->
    m / IREApp e1 e2 ==> fail
| BStApp2F : forall m e1 m' v1 e2,
    m / e1 ==> m' / v1 ->
    m' / e2 ==> fail ->
    m / IREApp e1 e2 ==> fail
| BStApp3F : forall m e1 m' var body e2 m'' v2,
    m / e1 ==> m' / IREFun var body ->
    m' / e2 ==> m'' / v2 ->
    m'' / ([var := v2] body) ==> fail ->
    m / IREApp e1 e2 ==> fail
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


(*
** Big step of a value means zero steps
*)
Lemma valueNormal : forall m e m' res,
    bigStep m e m' res -> Value e -> m = m' /\ res = e.
Proof.
  intros m e m' res HB HV.
  induction HB; inversion HV; subst; eauto using Value;
  splitAnd;
  intuition congruence.
Qed.


(*
** Big steps preserve typing and result in values
*)
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
  eauto using IRTyping,Value,mem_correct,mem_correct_freshT,
              mem_correct_freshF;
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
  - eapply MCTyF in H; auto.
    eapply IHHst3 in H4.
    + destruct H4; eauto.
    + eauto using subst_typing.
  - eapply MCTyF in H; auto.
    eapply IHHst3 in H4.
    + destruct H4; eauto.
    + eauto using subst_typing.
  - (* Unboxing step needs an extra inversion on type judgment
       and value to get inside the boxed value *)
    split.
    * inversion H0; trivial.
    * inversion H1; trivial.
Qed.


(*
** Big steps produce values
*)
Lemma BstepValue : forall (m m' : Mem) e e' t,
  m / e ==> m' / e' ->
  mem_correct m ->
  MEmpty |= e : t ->
  Value e'.
Proof. apply BPreservation. Qed.


(*
** Big steps preserve types
*)
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
    m / e --> m' / e' ->
    m' / e' ==> m'' / e'' ->
    m / e ==> m'' / e''.
Proof.
  intros * HM HSt HB.
  generalize dependent m''.
  generalize dependent e''.
  induction HSt; intros * HB; subst;
  inversion HB; subst;
  (* ~half cases values are not values *)
  try match goal with
  | [ H: Value _ |- _ ] =>
      inversion H; subst; eauto using bigStep,Value; fail
  end;
  (* rewrite queries to its real values in the step *)
  repeat match goal with
  | [ H: _ = queryT _ _ _ |- _ ] => rewrite <- H in HB end;
  (* extract equalities from "value" steps *)
  repeat match goal with
  | [ HB: bigStep _ _ _ _ |- _] =>
    eapply valueNormal in HB; only 2: (eauto using Value; fail);
    intuition; subst
  end;
  (* clear useless equalities *)
  repeat match goal with | [H: ?E = ?E |- _] => clear H end;
  (* extract equalities from injections *)
  repeat match goal with
  | [H: IREBox _ _ = IREBox _ _ |- _] => injection H as H; subst
  end;
  eauto using bigStep,Value;
  (* contradictions about query not being a value *)
  try match goal with
    |[H: ?E = queryT _ _ _ |- _] =>
        assert (HC: Value E) by (rewrite H; eauto using MCValue); inversion HC
    end; subst.

  - (* queries being complex values (fun and lambdas which must be
     broken to extract some equalities *)
    eapply valueNormal in HB as [? ?]; subst; trivial;
    eapply BStGet; eauto using bigStep, Value; congruence.
Qed.


Theorem smallBig : forall m e t m' e',
    mem_correct m ->
    MEmpty |= e : t ->
    m / e -->* m' / e' ->
    Value e' ->
    m / e ==> m' / e'.
Proof.
  intros * MC MTy MSt.
  induction MSt; intros HV;
  eauto using bigStep, stepBigstep, memPreservation, expPreservation.
Qed.


Lemma invertTyBox : forall t e, Value (IREBox t e) -> Value e.
Proof. intros t e H. inversion H. trivial. Qed.


Lemma auxTySubst : forall m m' var t t' exp v body,
    MEmpty |= exp : t ->
    m / exp ==> m' / v ->
    mem_correct m ->
    (var |=> t; MEmpty) |= body : t' ->
    MEmpty |= [var := v] body : t'.
Proof.
  intros. eauto using BstepTy, subst_typing.
Qed.


Lemma auxTyFun : forall m' m'' var body a e2 v2,
    (var, body) = queryF a m'' ->
    MEmpty |= e2 : IRTStar ->
    m' / e2 ==> m'' / v2 ->
    mem_correct m' ->
    mem_correct m'' ->
    MEmpty |= [var := v2] body : IRTStar.
Proof.
  intros.
  eapply subst_typing.
  - eauto 10 using subst_typing, MCTyF, BPreservation.
  - eapply BPreservation; eauto.
Qed.


Lemma StSet' : forall m a idx val,
    Value idx ->
    m / IRESet (IRETAddr a) idx (EV2Val val) -->
    UpdateT a (ToIndex idx) val m / IRENil.
Proof.
  intros *.
  destruct val.
  eauto using StSet.
Qed.


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

  (* Propagate 'mem_correct' to all memories *)
  repeat memC;

  (* instantiate inductive hypothesis *)
  repeat match goal with
    [ IH: mem_correct ?M  -> _ -> IRTyping _ ?E _ -> _,
      HM: mem_correct ?M,
      HT: IRTyping _ ?E _ |- _] =>
        specialize (IH HM _ HT)
    end;

    (* handle the trivial cases *)
    eauto using MStRefl;

    (* this eauto cannot include MStRefl, as it will solve several
       cases the wrong way *)
    unshelve (eauto 11 using
      CongPlus1, CongPlus2, CongGet1, CongGet2,
      CongSet1, CongSet2, CongSet3,
      CongApp1, CongApp2, CongLet,
      CongBox, CongUnbox,
      Value, multistep1, step, multiTrans,
      BstepValue, BstepTy,  StSet', auxTyFun, invertTyBox);
    try apply TgNil.

   (* Let is still going the wrong way... *)
   eapply multiTrans.
   2: { eauto using auxTySubst. }
   eauto 6 using multiTrans, CongLet, multistep1, step, BstepValue.

Qed.


(* }================================================================== *)



