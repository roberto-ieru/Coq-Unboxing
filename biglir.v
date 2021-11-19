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

Inductive bigStep : Mem -> IRE -> Mem -> option IRE -> Prop :=
| BStValue : forall m e, Value e -> m / e ==> m / e
| BStPlus : forall m e1 m' n1 e2 m'' n2,
    m / e1 ==> m' / IRENum n1 ->
    m'/ e2 ==> m'' / IRENum n2 ->
    m / IREPlus e1 e2 ==> m'' / IRENum (n1 + n2)
| BStPlus1F : forall m e1 e2,
    m / e1 ==> fail ->
    m / IREPlus e1 e2 ==> fail
| BStPlus2F : forall m e1 m' n1 e2,
    m / e1 ==> m' / IRENum n1 ->
    m' / e2 ==> fail ->
    m / IREPlus e1 e2 ==> fail
| BStCstr : forall m m' free,
    (free, m') = fresh m ->
    m / IRECnst ==> m' / IREAddr free
| BStGet : forall m e1 m' a e2 m'' v idx,
    m / e1 ==> m' / IREAddr a ->
    m'/ e2 ==> m'' / idx ->
    v = query a idx m'' ->
    m / IREGet e1 e2 ==> m'' / v
| BStGet1F : forall m e1 e2,
    m / e1 ==> fail ->
    m / IREGet e1 e2 ==> fail
| BStGet2F : forall m e1 m' a e2,
    m / e1 ==> m' / IREAddr a ->
    m' / e2 ==> fail ->
    m / IREGet e1 e2 ==> fail
| BStSet : forall m e1 m' a e2 m'' idx m''' e3 val,
    m / e1 ==> m' / IREAddr a ->
    m'/ e2 ==> m'' / idx ->
    m''/ e3 ==> m''' / val ->
    m / IRESet e1 e2 e3 ==> Update a (ToIndex idx) val m''' / val
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
| BStFun : forall m e m' var body,
    m / e ==> m' / IRELamb var IRTStar body ->
    m / IREFun e ==> m' / IREFun (IRELamb var IRTStar body)
| BStFun1F : forall m e,
    m / e ==> fail ->
    m / IREFun e ==> fail
| BStLambapp : forall m e1 m' var t body e2 m'' v2 m''' res,
     m / e1 ==> m' / IRELamb var t body ->
     m' / e2 ==> m'' / v2 ->
     m'' / ([var := v2] body) ==> m''' / res ->
     m / IRELambApp e1 e2 ==> m''' / res
| BStLambapp1F : forall m e1 e2,
     m / e1 ==> fail ->
     m / IRELambApp e1 e2 ==> fail
| BStLambapp2F : forall m e1 m' var t body e2,
     m / e1 ==> m' / IRELamb var t body ->
     m' / e2 ==> fail ->
     m / IRELambApp e1 e2 ==> fail
| BStLambapp3F : forall m e1 m' var t body e2 m'' v2,
     m / e1 ==> m' / IRELamb var t body ->
     m' / e2 ==> m'' / v2 ->
     m'' / ([var := v2] body) ==> fail ->
     m / IRELambApp e1 e2 ==> fail
| BStFunapp : forall m e1 m' var body e2 m'' v2 m''' res,
    m / e1 ==> m' / IREFun (IRELamb var IRTStar body) ->
    m' / e2 ==> m'' / v2 ->
    m'' / ([var := v2] body) ==> m''' / res ->
    m / IREFunApp e1 e2 ==> m''' / res
| BStFunapp1F : forall m e1 e2,
    m / e1 ==> fail ->
    m / IREFunApp e1 e2 ==> fail
| BStFunapp2F : forall m e1 m' v1 e2,
    m / e1 ==> m' / v1 ->
    m' / e2 ==> fail ->
    m / IREFunApp e1 e2 ==> fail
| BStFunapp3F : forall m e1 m' var body e2 m'' v2,
    m / e1 ==> m' / IREFun (IRELamb var IRTStar body) ->
    m' / e2 ==> m'' / v2 ->
    m'' / ([var := v2] body) ==> fail ->
    m / IREFunApp e1 e2 ==> fail
| BStBox : forall m e m' e' t,
    m / e ==> m' / e' ->
    m / IREBox t e ==> m' / IREBox t e'
| BStBox1F : forall m e t,
    m / e ==> fail ->
    m / IREBox t e ==> fail
| BStUnbox : forall m e m' t e',
    m / e ==> m' / IREBox t e' ->
    m / IREUnbox t e ==> m' / e'
| BStUnboxF : forall m e m' t t' e',
    m / e ==> m' / IREBox t e' ->
    t <> t' ->
    m / IREUnbox t' e ==> fail
| BStUnbox1F : forall m e t,
    m / e ==> fail ->
    m / IREUnbox t e ==> fail


where "m / e ==> m1 / e1" := (bigStep m e m1 (Some e1))
  and "m / e ==> 'fail'" := (bigStep m e m None)
.


Lemma valueNormal : forall m e m' res,
    bigStep m e m' res -> Value e -> m = m' /\ res = Some e.
Proof.
  intros m e m' res HB HV.
  induction HB; inversion HV; subst; eauto using Value;
  try specialize (IHHB (Vlam _ _ _));
  try intuition congruence.
Qed.


Lemma BPreservation : forall (m m' : Mem) e e' t,
  m / e ==> m' / e' ->
  mem_correct m ->
  MEmpty |= e : t ->
     mem_correct m' /\ MEmpty |= e' : t /\ Value e'.
Proof.
  intros m m' e e' t Hst HMC HTy.
  remember MEmpty as Γ.
  remember (Some e') as E'.
  generalize dependent e'.
  generalize dependent t.
  induction Hst; intros ? HTy ? HE';
  (* impossible cases *)
  inversion HE'; subst;
  (* apply type judgment and break 'and's *)
  inversion HTy; subst; (split; only 2: split);
  repeat (
  (* instantiate induction hypotheses when possible *)
  match goal with
  | [ HM : mem_correct ?M,
      HT : _ |= ?E : _,
      IH : mem_correct ?M -> _ -> _ |= ?E : _ -> _ |- _] =>
        specialize (IH HM _ HT _ eq_refl) as [? [? ?]]
  end;
  (* handle cases that need substitution *)
  try match goal with
    | [HT: MEmpty |= IRELamb ?V _ ?B : ETLamb ?T1 ?T2,
       HTV: MEmpty |= ?Arg : (ETn ?T1) |- _] =>
        assert (MEmpty |= [V := Arg] B : T2) by
      (inversion HT; subst; eauto using subst_typing)
    end
  );
  eauto using IRTyping,Value,mem_correct_fresh,mem_correct_update;
  (* handle substitutions inside FUN (not pretty yet) *)
  try (assert (MEmpty |= [var := v2] body : IRTStar) by (
      inversion H0; inversion H9; subst; eauto using subst_typing);
    eapply IHHst3; eauto).
  - (* use mem_correct for queries *)
    unfold mem_correct in H3. split; eapply H3.
  - (* Unboxing step needs an extra inversion on type judgment
       and value to get inside the boxed value *)
    split.
    * inversion H0; trivial.
    * inversion H1; trivial.
Qed.


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
  | [H: Some _ = Some _ |- _] => injection H as H; subst
  end;
  (* clear useless equalities *)
  repeat match goal with | [H: ?E = ?E |- _] => clear H end;
  eauto using bigStep,Value;
  (* contradictions about query not being a value *)
  try match goal with
    |[H: ?E = query _ _ _ |- _] =>
        assert (HC: Value E) by (rewrite H; apply HM); inversion HC
    end;
  (* queries being complex values (fun and lambdas which must be
     broken to extract some equalities *)
  (
    eapply valueNormal in HB as [? HB1]; eauto using Value;
    inversion HB1; subst;
    eapply BStGet; eauto using bigStep,Value; congruence
  ).
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
  induction MSt; intros ? HEq HV; inversion HEq; subst; clear HEq.
  - eauto using bigStep.
  - eapply stepBigstep; eauto.
    eapply IHMSt; eauto; eapply Preservation; eauto.
Qed.


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


Theorem bigDyn : forall e t m e' m',
   m / e ==> m' / e' -> MEmpty |= e : t -> mem_correct m ->
   dynMem m / dyn e ==> dynMem m' / dyn e'.
Proof.
  intros e t m e' m' HB HTy HM.
  remember MEmpty as Γ eqn:Heq.
  remember (Some e') as E'.
  generalize dependent e'.
  generalize dependent t.
  induction HB; intros ? HTy ? Heq1;
  inversion Heq1; clear Heq1;
  inversion Heq; inversion HTy; subst; simpl;
  try match goal with [H : Value _ |- _] => inversion H end;
  repeat memC;
  simpl;
  try (eapply BStValue; eauto using Value; fail);
  eauto using Value,BStValue,dynValue,dynFresh,bigStep;
  repeat match goal with
    | [ MC: mem_correct ?M,
        HT: MEmpty |= ?E : _ |- _] =>
      match goal with
      | [ IH: mem_correct M -> forall _, MEmpty |= E : _ ->
        forall _, Some ?E' = Some _ -> _
         |- _] =>
        specialize (IH MC _ HT E' eq_refl); simpl in IH
      end
    end; eauto using bigStep.
  - rewrite dynQuery. eauto using bigStep.
  - rewrite DynIndex. eauto using bigStep.
  - apply (BStLambapp _ _ (dynMem m') var IRTStar (dyn body) _
                          (dynMem m'') (dyn v2)); eauto.
    + rewrite dynSubst. eapply IHHB3; eauto.
      assert (MEmpty |= IRELamb var t body : ETLamb t1 t0).
      { eapply BPreservation; eauto. }
      eapply subst_typing; inversion H2; eauto.
      eapply BPreservation; eauto.
  - eapply (BStFunapp _ _ (dynMem m') var (dyn body) _ (dynMem m'')
            (dyn v2)); eauto using bigStep.
    + rewrite dynSubst. eapply IHHB3; eauto.
      assert (HTF: MEmpty |= IREFun (IRELamb var IRTStar body) : TgFun).
      { eapply BPreservation; eauto. }
      inversion HTF; subst.
      eapply subst_typing.
      * inversion H5; eauto.
      * eapply BPreservation; eauto.
Qed.


