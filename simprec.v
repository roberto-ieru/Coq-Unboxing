Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.
Require Import LIR.lir.
Require Import LIR.precision.
Require Import LIR.dyn.

Set Implicit Arguments.

(*
** Precision relation for memories: implies that memory is correct,
** because the precision relation needs the types of the expressions
** being compared.
*)
Inductive PrecMem : Mem -> Mem -> Prop :=
| PrecMemE : PrecMem EmptyMem EmptyMem
| PrecMemUD : forall addr idx v1 v2 m1 m2,
    Precision PEmpty (EV2Val v1) IRTStar (EV2Val v2) IRTStar ->
    PrecMem m1 m2 ->
    PrecMem (UpdateT addr idx v1 m1) (UpdateT addr idx v2 m2)
| PrecMemUDF : forall addr var b1 b2 m1 m2,
    Precision (Env2P  (var |=> IRTStar; MEmpty)) b1 IRTStar b2 IRTStar ->
    PrecMem m1 m2 ->
    PrecMem (UpdateF addr var b1 m1) (UpdateF addr var b2 m2)
.


Infix "<M|" := PrecMem (at level 80).


(*
** Memory precision is reflexive
*)
Lemma PrecMemRefl : forall m,
    mem_correct m -> m <M| m.
Proof.
  intros m Hm.
  induction Hm; constructor; trivial;
  eapply PrecisionRefl; eauto.
Qed.


(*
** Memory precision implies that memory 1 is correct.
*)
Lemma PrecCorrect1 : forall m1 m2, m1 <M| m2 -> mem_correct m1.
Proof.
  intros * H.
  induction H; intros *; simpl;
  eauto using mem_correct, PrecisionType1Empty.
  eapply PrecisionType1 in H. simpl in H.
  eauto using mem_correct, PrecisionType1Empty.
Qed.


(*
** Memory precision implies that memory 2 is correct.
*)
Lemma PrecCorrect2 : forall m1 m2, m1 <M| m2 -> mem_correct m2.
Proof.
  intros * H.
  induction H; intros *; simpl;
  eauto using mem_correct, PrecisionType2Empty.
  eapply PrecisionType2 in H. simpl in H.
  eauto using mem_correct, PrecisionType2Empty.
Qed.


(*
** Expressions equal "up to precision" generate the same indices
*)
Lemma PrecIndex : forall e1 e2,
    Precision PEmpty e1 IRTStar e2 IRTStar ->
    ToIndex e1 = ToIndex e2.
Proof. intros * HP. induction HP; eauto. Qed.


(*
** Memories in a precision relation generate equal "fresh" addresses
*)
Lemma PrecFreshaux : forall m1 m2,
    m1 <M| m2 -> freshaux m1 = freshaux m2.
Proof.
  intros * HOM.
  induction HOM; simpl; eauto.
Qed.


(*
** Creating a new table entry preserves memory precision and
** results in equal addresses.
*)
Lemma PrecFreshT : forall m1 m2 free m1',
    m1 <M| m2 ->
    (free, m1') = freshT m1 ->
    exists m2', m1' <M| m2' /\ (free, m2') = freshT m2.
Proof.
  unfold freshT.
  intros * HOM HF.
  injection HF; intros; subst; clear HF.
  replace (freshaux m2) with (freshaux m1) by auto using PrecFreshaux.
  eexists. split; only 2: trivial;
  eauto using PrecMem, Precision.
Qed.


(*
** Creating a new closure preserves memory precision and
** results in equal addresses.
*)
Lemma PrecFreshF : forall m1 m2 var d1 d2 free m1',
    m1 <M| m2 ->
    Precision
       (ExpandPEnv PEmpty var IRTStar IRTStar (TPrecisionRefl IRTStar)) d1
       IRTStar d2 IRTStar ->
    (free, m1') = freshF m1 var d1 ->
    exists m2', m1' <M| m2' /\ (free, m2') = freshF m2 var d2.
Proof.
  unfold freshF.
  intros * HOM HP HF.
  injection HF; intros; subst; clear HF.
  replace (freshaux m2) with (freshaux m1) by auto using PrecFreshaux.
  replace PEmpty with (Env2P MEmpty) in HP by trivial.
  eexists;
  eauto using PrecMemUDF, PrecisionIrrel, PEquivSym, Expand2P.
Qed.


Lemma PrecQueryT : forall m1 m2 a i1 i2,
    m1 <M| m2 ->
    Precision PEmpty i1 IRTStar i2 IRTStar ->
    Precision PEmpty (queryT a i1 m1) IRTStar (queryT a i2 m2) IRTStar.
Proof.
  intros * HOM HP.
  induction HOM; simpl; eauto using Precision.
  rewrite <- (PrecIndex HP).
  breakIndexDec; trivial.
Qed.


Lemma PrecQueryF : forall m1 m2 a var var' body body',
    m1 <M| m2 ->
    (var, body) = queryF a m1 ->
    (var', body') = queryF a m2 ->
    var = var' /\
      Precision
         (ExpandPEnv PEmpty var IRTStar IRTStar (TPrecisionRefl IRTStar))
          body IRTStar body' IRTStar.
Proof.
  intros * HM HEq1 HEq2.
  induction HM; simpl; eauto.
  - inversion HEq1; inversion HEq2; subst.
    unshelve (split; eauto using Precision, PrecisionIrrel);
      eauto using TPrecision.
  - simpl in *.
    breakIndexDec; eauto.
    injection HEq1; injection HEq2; intros; subst.
    clear HEq1 HEq2. split; trivial.
    eapply PrecisionIrrel; eauto.
    eapply Expand2P.
Qed.


Lemma PrecUpdate : forall m1 m2 a i1 i2 v1 v2,
    m1 <M| m2 ->
    forall (vv1 : Value v1) (vv2 : Value v2),
    Precision PEmpty i1 IRTStar i2 IRTStar ->
    Precision PEmpty v1 IRTStar v2 IRTStar ->
    UpdateT a (ToIndex i1) (EV v1 vv1) m1 <M|
    UpdateT a (ToIndex i2) (EV v2 vv2) m2.
Proof.
  intros * HOM HV1 HV2 HP1 HP2.
  rewrite <- (PrecIndex HP1).
  auto using PrecMem.
Qed.


(*
** Substitution preserves precision
*)
Lemma PrecSubs : forall body Γ Γ' var  body' v1 v2 t1 t2 t1' t2'
                        (H12: t1 <| t2),
    Precision PEmpty v1 t1 v2 t2 ->
    PEquiv (ExpandPEnv Γ var t1 t2 H12) Γ' ->
    Precision Γ' body t1' body' t2' ->
    Precision Γ ([var := v1] body) t1' ([var := v2] body') t2'.
Proof.
  intros * HPV HPE HPB.
  generalize dependent Γ.
  induction HPB; intros ? HPE; eauto using Precision;
  try ( simpl;
    breakStrDec;
      unshelve (econstructor;
      eauto using PrecisionIrrel, PEquivTrans, PEquivShadow, PEquivPermute,
                  ExpandEquiv, PEquivSym);
      auto using TPrecisionRefl; fail).

  - (* variable *)
    simpl.
    destruct HPE.
    specialize (H1 var0).
    specialize (H2 var0).
    rewrite Expand1 in H1.
    rewrite Expand2 in H2.
    breakStrDec.
    + replace t0 with t1 by congruence.
      replace t3 with t2 by congruence.
      eauto using PrecisionInclusion, PinclusionEmpty.
    + apply PVar; congruence.
Qed.


(*
** Substitution applied to function bodies
*)
Lemma PrecSubs' : forall var body body' v1 v2,
    Precision PEmpty (IREFun var body) IRTFun
                     (IREFun var body') IRTFun ->
    Precision PEmpty v1 IRTStar v2 IRTStar ->
    Precision PEmpty ([var := v1] body) IRTStar ([var := v2] body') IRTStar.
Proof.
  intros * HPF HPV.
  inversion HPF; subst.
  eauto using PrecSubs, ExpandEquiv, PEquivRefl.
Qed.


Ltac ContraTags :=
  try match goal with
    [H: IRTStar <| Tag2Type _ |- _] =>
      apply NoneBiggerThanStar in H
  end;
  try match goal with
    [H: IRTStar = Tag2Type ?g |- _] =>
      destruct g; discriminate
  end.


Lemma GroundFlat': forall g g', (Tag2Type g) <| (Tag2Type g') -> g = g'.
Proof.
  intros * H. apply GroundFlat in H. injection H; trivial.
Qed.


Lemma GroundType: forall g t g',
    t <| Tag2Type g -> Type2Tag t = Some g' -> g = g'.
Proof.
  intros * HT Heq.
  destruct t eqn:Heq';
  ContraTags;
  injection Heq; intros;
    rewrite <- Heq' in HT;
    replace t with (Tag2Type g') in HT by (subst; trivial);
    symmetry;
    subst; eauto using GroundFlat'.
Qed.


(*
** About "catch-up": when e1 ⊑ e2 and e1 is a value, e2 may not be
** a value (e.g., (unbox (box 10))). But we can guarantee that e2
** reduces to a value (nor errors or infinite loops) in a somewhat
** restricted way. This property is called "catch-up", and several
** of the following lemmas help its proof.
*)

(*
** Catch-up steps do not change the memory
*)
Lemma stepValueMem : forall e1 e2 e2' t1 t2 m m',
    Precision PEmpty e1 t1 e2 t2 ->
    Value e1 ->
    m / e2 --> m' / e2' -> m = m'.
Proof.
  intros * HP HV HStep.
  remember PEmpty as Γ.
  generalize dependent m'.
  generalize dependent m.
  generalize dependent e2'.
  induction HP; intros * HStep; inversion HV;
  inversion HStep; subst; eauto using Precision.
Qed.


(*
** Catch-up steps preserve precision
*)
Lemma PrecisionPreservation : forall e1 e2 e2' t1 t2 m m',
    Precision PEmpty e1 t1 e2 t2 ->
    Value e1 ->
    m / e2 --> m' / e2' ->
    Precision PEmpty e1 t1 e2' t2.
Proof.
  intros * HP HV HStep.
  remember PEmpty as Γ.
  generalize dependent m'.
  generalize dependent m.
  generalize dependent e2'.
  induction HP; intros * HStep; inversion HV; subst;
  inversion HStep; subst; eauto using Precision;
  inversion HStep; subst;
  try (inversion H5;
       inversion HP; subst; trivial).
  - inversion H6.
  - inversion HP; subst; trivial.
    ContraTags.
Qed.


(*
** Catch-up multi-steps preserve precision
*)
Lemma PrecisionPreservationMult : forall e1 e2 e2' t1 t2 m m',
    Precision PEmpty e1 t1 e2 t2 ->
    Value e1 ->
    m / e2 -->* m' / e2' ->
    Precision PEmpty e1 t1 e2' t2.
Proof.
  intros * HP HV HStep.
  induction HStep; eauto using PrecisionPreservation.
Qed.


(*
** Catch-up applied to boxes: if the term "catching-up" is a box,
** it remains a box.
*)
Lemma BoxPreservePrecision : forall e m m' b tg v t,
  m / IREBox tg e -->* m' / b ->
  Precision PEmpty v t (IREBox tg e) IRTStar ->
  Value v ->
  exists o, b = IREBox tg o /\ Precision PEmpty v t b IRTStar.
Proof.
  intros * Hst.
  remember (IREBox tg e) as E.
  generalize dependent e.
  induction Hst; intros * HEq HP HV.
  - exists e0. auto.
  - subst.
    replace m' with m in * by (eapply stepValueMem; eauto).
    inversion H; subst.
    eauto using PrecisionPreservation.
Qed.


(*
** If the term "catching-up" has type '*', it converges to a box.
*)
Lemma ValueStarP : forall tg t v e m e',
    Precision PEmpty v t e IRTStar ->
    t <| Tag2Type tg ->
    Value v ->
    m / e -->* m / e' ->
    Value e' ->
      exists o,
        e' = IREBox tg o /\ Precision PEmpty v t e' IRTStar.
Proof.
  intros * HP HSty HVP HStep HV.
  inversion HP; subst; try (inversion HVP; fail);
  ContraTags.
  replace g with tg in * by (
    apply PPT in H;
    eauto using GroundTop).
  eauto using BoxPreservePrecision.
Qed.


(*
** Obs: reduction uses only unbox(box x); it does not change memory
*)
Theorem CatchUp : forall e1 t1 e2 t2 m,
  Precision PEmpty e1 t1 e2 t2 ->
  Value e1 ->
  exists e2', m / e2 -->* m / e2' /\ Value e2'.
Proof.
  intros * HP HV.
  remember PEmpty as Γ eqn:Heq.
  induction HP; subst Γ; inversion HV; subst;
  (* instanciate and break induction hypothesis *)
  try match goal with
  [IH: _ -> Value ?E -> _ ,
   HV: Value ?E |- _] =>
     specialize (IH eq_refl HV) as [? [? ?]]
  end;
  try (eexists; split; eauto using MStRefl, Value; fail);
  try (eexists; split; eauto using CongBox, Value; fail);

  pose proof HP as HP';
  apply PrecisionType1 in HP';
  inversion HP'; subst; clear HP';
  ContraTags;

  specialize (ValueStarP HP H HV H0 H1) as [? [? _]];
      subst;

  try (eapply GroundType in H; only 2: (simpl; trivial);
    apply valBoxVal in H1;
    exists x0; split;
    eauto using multiTrans, CongUnbox, StUnbox, multistep).
Qed.


Ltac BreakIH :=
  match goal with
    [IH: context [_ / ?E --> _ / _ -> (PrecMem _ _) -> _] ,
     HSt: ?M / ?E --> _ / _ ,
     HM: ?M <M| ?M' |- _ ] =>
       specialize (IH eq_refl _ _ _ _ HSt HM) as [? [? [? [? ?]]]]
  end.


Lemma NoValueUnbox : forall tg e (C : Type),
    Value (IREUnbox tg e) -> C.
Proof.
  intros * H.
  exfalso.
  inversion H.
Qed.


Ltac NoValueUnbox :=
  match goal with [H: Value (IREUnbox _ _) |- _] =>
    eapply NoValueUnbox; eauto
  end.


(* Try to instantiate CatchUp. First, find a precision relation HP.
   If its E' already progresses, there is nothing to be done. (Probably
   the tactic already handled that case.) Otherwise, try to prove
   that E is a value. If so, instantiate CatchUp. *)
Ltac doCatchUp :=
  match goal with
  [ HP: Precision _ ?E _ ?E' _ |- context [?M / _ -->* _ / _] ] =>
      match goal with
      | [ H: _ / E' -->* _ / _  |- _ ] => fail 1  (* already done *)
      | [ |- _ ] =>  (* otherwise *)
        assert (HXX: Value E) by eauto using Value;
        specialize (CatchUp M HP HXX) as [? [? ?]];
        clear HXX
      end
  end.


(*
** Main simulation lemma
*)
Theorem Sim : forall m1 e1 t1 e2 m2 t2 m1' e1',
  Precision PEmpty e1 t1 e2 t2 ->
  m1 / e1 --> m1' / e1'   ->
  m1 <M| m2 ->
  exists e2' m2',
    m2 / e2 -->* m2' / e2' /\ m1' <M| m2' /\ Precision PEmpty e1' t1 e2' t2.
Proof.
  intros * HP.
  generalize dependent m2.
  generalize dependent e1'.
  generalize dependent m1'.
  generalize dependent m1.
  remember PEmpty as Γ.
  induction HP; intros * Hstep HM;

  (* Handle BoxR and UnboxR, which should not invert step *)
  try (subst; BreakIH;
    eexists; eexists; split; try split;
    eauto using Precision, CongBox, CongUnbox;
    fail);

  inversion Hstep; subst; repeat BreakIH;
  (* Handle all "first" cases *)
  try (eexists; eexists; split; try split;
    eauto using Precision, CongPlus1, CongGet1, CongSet1, CongLet,
                CongApp1;
    fail);

    repeat doCatchUp.

  - (* StPlus2 *)
    clear IHHP1.
    eexists; exists x0; split; try split;
      eauto using multiTrans, CongPlus1, CongPlus2,
                  Precision, PrecisionPreservationMult.

  - (* StPlus *)
    clear IHHP1 IHHP2.

    assert (N1: x = IRENum n1). {
      specialize (PrecisionPreservationMult HP1 (Vnum n1) H) as NH1.
      inversion NH1; subst; trivial; NoValueUnbox.
    }

    assert (N2: x0 = IRENum n2). {
      specialize (PrecisionPreservationMult HP2 (Vnum n2) H1) as NH2.
      inversion NH2; subst; trivial; NoValueUnbox.
    }

    subst.
    exists (IRENum (n1 + n2)). exists m2. split; try split;
    eauto 7 using multiTrans, CongPlus1, CongPlus2, multistep1, step,
         Precision.


  - (* StCstr *)
    specialize (PrecFreshT HM H) as [? [? ?]].
    eexists; eexists; split; try split;
    eauto using multistep1, step, Precision.


  - (* StGet2 *)
    eexists; exists x0; split; try split;
      eauto using multiTrans, CongGet1, CongGet2,
                  Precision, PrecisionPreservationMult.

  - (* StGet *)
    clear IHHP1 IHHP2.

    assert (N1: x = IRETAddr a). {
      specialize (PrecisionPreservationMult HP1 (Vtbl a) H) as NH1.
      inversion NH1; subst; trivial; NoValueUnbox.
    } subst.

    exists (queryT a x0 m2). exists m2. split; try split;
      eauto 7 using multiTrans, CongGet1, CongGet2, multistep1, step,
         Precision, PrecQueryT, PrecisionPreservationMult.

  - (* StSet2 *)
    eexists; exists x0; split; try split;
      eauto using multiTrans, CongSet1, CongSet2,
                  Precision, PrecisionPreservationMult.

  - (* StSet3 *)
   clear IHHP1 IHHP2.
    eexists; exists x0; split; try split;
      eauto 6 using multiTrans, CongSet1, CongSet2, CongSet3,
                  Precision, PrecisionPreservationMult.

  - (* StSet *)
    clear IHHP1 IHHP2 IHHP3.

    assert (N1: x = IRETAddr a). {
      specialize (PrecisionPreservationMult HP1 (Vtbl a) H) as NH1.
      inversion NH1; subst; trivial; NoValueUnbox.
    } subst.

    exists IRENil. eexists (UpdateT _ _ (EV x1 H4) _).
    split; try split;
      eauto 9 using multiTrans, CongSet1, CongSet2, CongSet3,
        multistep1, step, Precision, PrecQueryT, PrecisionPreservationMult,
        PrecUpdate.

  - (* StLet *)
    clear IHHP1 IHHP2.
    eexists ([var := x] b2); exists m2; split; try split;
      eauto using multiTrans, CongLet, multistep1, step,
                  PrecSubs, PrecisionPreservationMult, PEquivRefl.

  - (* StFun *)
    clear IHHP.
    specialize (PrecFreshF HM HP H4) as [? [? ?]].
    eexists. eexists. repeat split;
    eauto using multistep1, step, Precision.

  - (* StApp2 *)
    eexists; exists x0; split; try split;
      eauto using multiTrans, CongApp1, CongApp2,
                  Precision, PrecisionPreservationMult.

  - (* StApp *)
    clear IHHP1 IHHP2.

    assert (N1: x0 = IREFAddr a). {
      specialize (PrecisionPreservationMult HP2 (Vfun a) H1) as NH1.
      inversion NH1; subst. eauto. NoValueUnbox.
    }
    subst.

    destruct (queryF a m2) as [var' body'] eqn:HEq2. symmetry in HEq2.
    specialize (PrecQueryF _ HM H5 HEq2) as [? ?]; subst.
    exists (IRELet var' IRTStar x body').
    exists m2. repeat split;
    eauto 7 using multiTrans, CongApp1, CongApp2, multistep1, step,
         Precision, PrecisionPreservationMult.

  - (* StUnbox *)
    clear IHHP.
    inversion HP; subst; ContraTags.
    * exfalso. apply PPT in H1. ContraTags.
    * specialize (ValueStarP H3 (TPrecisionRefl (Tag2Type g))
        H5 H H0) as [? [? ?]].
      subst.
      eexists; eexists; split; try split; eauto.

Qed.


(*
** Simulation theorem
*)
Theorem SimMult : forall m1 e1 t1 e2 m2 t2 m1' e1',
  m1 / e1 -->* m1' / e1'   ->
  Value e1' ->
  Precision PEmpty e1 t1 e2 t2 ->
  m1 <M| m2 ->
  exists e2' m2',
    m2 / e2 -->* m2' / e2' /\
    Precision PEmpty e1' t1 e2' t2 /\
    m1' <M| m2' /\
    Value e2'.
Proof.
  intros * HMSt.
  generalize dependent m2.
  generalize dependent t2.
  generalize dependent e2.
  induction HMSt; intros * HV HPE HMem.
  - specialize (CatchUp m2 HPE HV) as [? [? ?]].
    eexists. eexists; repeat split; eauto using PrecisionPreservationMult.
  - specialize (Sim HPE H HMem) as [? [? [? [? ?]]]].
    specialize (IHHMSt _ _ _ HV H2 H1) as [? [? [? [? [? ?]]]]].
    exists x1. exists x2. repeat split; eauto using multiTrans.
Qed.


(*
** Simulation theorem for programmers: no mentions to precision,
** concept expressed only in terms of 'dyn'
*)
Corollary SimDyn : forall m1 e1 t1 m1' e1',
  m1 / e1 -->* m1' / e1'   ->
  MEmpty |= e1 : t1 ->
  mem_correct m1 ->
  Value e1' ->
  exists e2' m2',
    m1 / dyn e1 -->* m2' / e2' /\
    e2' = dyn e1' /\
    (* m1' <M| m2' /\ *)
    Value e2'.
Proof.
  intros * HSt Hty HM HV.
  assert(Precision PEmpty e1 t1 (dyn e1) IRTStar) by
    eauto using PrecisionIrrel, Env2DynEmpty, DynLessPrecise.
  assert (m1 <M| m1) by auto using PrecMemRefl.
  specialize (SimMult HSt HV H H0) as [? [? [? [? [? ?]]]]].
  eexists x. eexists. repeat split;
  eauto using PrecDynEqualVal.
Qed.

