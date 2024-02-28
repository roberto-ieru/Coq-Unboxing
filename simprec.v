(*
** Simulation: assuming a well-typed memory m1 and a
** well-typed term e1, if (m1 / e1) reduces to a value (m1' / e1'),
** then (m1 / dyn e1) reduces to (m2' / dyn e1') (for some
** memory m2' less precise than m1').
*)

Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.

Require Import LIR.maps.
Require Import LIR.lir.
Require Import LIR.precision.
Require Import LIR.dyn.

Set Implicit Arguments.

(*
** Precision relation for memories: implies that memory is correct,
** because the precision relation needs the types of the terms
** being compared.
*)
Inductive PrecMem : Mem -> Mem -> Prop :=
| PrecMemE : PrecMem EmptyMem EmptyMem
| PrecMemUD : forall addr idx v1 v2 m1 m2,
    Precision MEmpty (EV2Val v1) IRTStar MEmpty (EV2Val v2) IRTStar ->
    PrecMem m1 m2 ->
    PrecMem (UpdateT addr idx v1 m1) (UpdateT addr idx v2 m2)
| PrecMemUDF : forall addr var b1 b2 m1 m2,
    Precision (var |=> IRTStar; MEmpty) b1 IRTStar (var |=> IRTStar; MEmpty)b2 IRTStar ->
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
  induction 1; eauto using PrecMem, PrecisionRefl.
Qed.


(*
** Memory precision implies that memory 1 is correct.
*)
Lemma PrecCorrect1 : forall m1 m2, m1 <M| m2 -> mem_correct m1.
Proof.
  induction 1; eauto using mem_correct, PrecisionType1.
Qed.


(*
** Memory precision implies that memory 2 is correct.
*)
Lemma PrecCorrect2 : forall m1 m2, m1 <M| m2 -> mem_correct m2.
Proof.
  induction 1; eauto using mem_correct, PrecisionType2.
Qed.


(*
** Expressions equal "up to precision" generate the same indices
*)
Lemma PrecIndex : forall e1 e2,
    Precision MEmpty e1 IRTStar MEmpty e2 IRTStar ->
    ToIndex e1 = ToIndex e2.
Proof. induction 1; eauto. Qed.


(*
** Memories in a precision relation generate equal "fresh" addresses
*)
Lemma PrecFreshaux : forall m1 m2,
    m1 <M| m2 -> freshaux m1 = freshaux m2.
Proof. induction 1; simpl; eauto. Qed.


(*
** Creating a new table entry preserves memory precision and
** results in equal addresses.
*)
Lemma PrecFreshT : forall m1 m2 free m1',
    m1 <M| m2 ->
    (free, m1') = freshT m1 ->
    exists m2', (free, m2') = freshT m2 /\ m1' <M| m2'.
Proof.
  unfold freshT.
  injection 2; intros; subst.
  replace (freshaux m2) with (freshaux m1) by auto using PrecFreshaux.
  eexists; split;
  eauto using PrecMem, Precision, EnvCompRefl.
Qed.


(*
** Creating a new closure preserves memory precision and
** results in equal addresses.
*)
Lemma PrecFreshF : forall m1 m2 var d1 d2 free m1',
    m1 <M| m2 ->
    Precision
       (var |=> IRTStar; MEmpty) d1 IRTStar
       (var |=> IRTStar; MEmpty) d2 IRTStar ->
    (free, m1') = freshF m1 var d1 ->
    exists m2', m1' <M| m2' /\ (free, m2') = freshF m2 var d2.
Proof.
  unfold freshF.
  injection 3; intros; subst.
  replace (freshaux m2) with (freshaux m1) by auto using PrecFreshaux.
  eauto using PrecMemUDF.
Qed.


(*
** Querying table entries in memories related by precision
** results in terms related by precision.
*)
Lemma PrecQueryT : forall m1 m2 a i1 i2,
    m1 <M| m2 ->
    Precision MEmpty i1 IRTStar MEmpty i2 IRTStar ->
    Precision MEmpty (queryT a i1 m1) IRTStar MEmpty (queryT a i2 m2) IRTStar.
Proof.
  intros * HOM HP.
  induction HOM; simpl; eauto using Precision, EnvCompRefl.
  replace (ToIndex i2) with (ToIndex i1) by eauto using PrecIndex.
  breakIndexDec; subst. trivial.
Qed.


(*
** Querying functions in memories related by precision
** results in terms related by precision.
*)
Lemma PrecQueryF : forall m1 m2 a var var' body body',
    m1 <M| m2 ->
    (var, body) = queryF a m1 ->
    (var', body') = queryF a m2 ->
    var = var' /\
      Precision
         (var |=> IRTStar; MEmpty) body IRTStar
         (var |=> IRTStar; MEmpty) body' IRTStar.
Proof.
  intros * HM HEq1 HEq2.
  induction HM; simpl in *;
    breakIndexDec; eauto;
    injection HEq1; injection HEq2; intros; subst;
    split; eauto 6 using Precision, EnvCompRefl.
Qed.


(*
** Updating memories with values related by precision
** preserves precision.
*)
Lemma PrecUpdate : forall m1 m2 a i1 i2 v1 v2,
    m1 <M| m2 ->
    forall (vv1 : Value v1) (vv2 : Value v2),
    Precision MEmpty i1 IRTStar MEmpty i2 IRTStar ->
    Precision MEmpty v1 IRTStar MEmpty v2 IRTStar ->
    UpdateT a (ToIndex i1) (EV v1 vv1) m1 <M|
    UpdateT a (ToIndex i2) (EV v2 vv2) m2.
Proof.
  intros.
  replace (ToIndex i2) with (ToIndex i1) by eauto using PrecIndex.
  auto using PrecMem.
Qed.


(*
** Substitution preserves precision. (The 'map_eq' gives the
** flexibility to handle the 'let-in' case, where othersiwe we
** would need to prove that environments are equal up to permutes.)
*)
Lemma PrecSubs : forall body Γ Γ' Δ Δ' var  body' v1 v2 t1 t2 t1' t2',
    Precision MEmpty v1 t1 MEmpty v2 t2 ->
    map_eq (var |=> t1; Γ) Γ' ->
    map_eq (var |=> t2; Δ) Δ' ->
    Γ <E| Δ ->
    Precision Γ' body t1' Δ' body' t2' ->
    Precision Γ ([var := v1] body) t1' Δ ([var := v2] body') t2'.
Proof.
  intros * HPV HE1 HE2 HPE HPB.
  generalize dependent Δ.
  generalize dependent Γ.
  induction HPB; intros; eauto using Precision, EnvCompRefl;
     simpl.

  - (* variable *)
    breakStrDec.
    + replace t1 with t0 in * by eauto using map_eq_In.
      replace t2 with t3 in * by eauto using map_eq_In.
      auto using PrecisionInclusionE.
    + eapply PVar; trivial.
      * eapply InNotEq with (var := var0) in HE1; congruence.
      * eapply InNotEq with (var := var0) in HE2; congruence.

  - (* let *)
    breakStrDec;
      eauto 12 using Precision, PrecisionInclusion, map_eq_incl,
      map_eq_sym, eqeq_shadow, EnvCompExt, extend2Types, eqeq_permute.

  - (* fun *)
    breakStrDec;
      eauto 12 using Precision, PrecisionInclusion, map_eq_incl,
      map_eq_sym, eqeq_shadow, EnvCompExt, extend2Types, eqeq_permute.
Qed.


(*
** Substitution applied to function bodies
*)
Lemma PrecSubs' : forall var body body' v1 v2,
    Precision MEmpty (IREFun var body) IRTFun
              MEmpty (IREFun var body') IRTFun ->
    Precision MEmpty v1 IRTStar MEmpty v2 IRTStar ->
    Precision MEmpty ([var := v1] body) IRTStar MEmpty ([var := v2] body') IRTStar.
Proof.
  inversion 1; subst.
  eauto using PrecSubs, map_eq_refl.
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
  intros. GroundFlat. congruence.
Qed.


Lemma GroundType: forall g t g',
    t <| Tag2Type g -> Type2Tag t = Some g' -> g = g'.
Proof.
  intros.
  destruct t eqn:Heq';
  ContraTags;
  GroundFlat;
  simpl in *; congruence.
Qed.


(*
** About "catch-up": when e1 ⊑ e2 and e1 is a value, e2 may not be
** a value (e.g., (unbox (box 10))). But we can guarantee that e2
** reduces to a value (nor errors or infinite loops) in a somewhat
** restricted way (only 'StUnbox' steps). This property is called "catch-up",
** and several of the following lemmas help its proof.
*)

(*
** Catch-up steps do not change the memory
*)
Lemma stepValueMem : forall e1 e2 e2' t1 t2 m m',
    Precision MEmpty e1 t1 MEmpty e2 t2 ->
    Value e1 ->
    m / e2 --> m' / e2' ->
    m = m'.
Proof.
  intros * HP HV HStep.
  remember MEmpty as Γ.
  generalize dependent e2'.
  induction HP; intros * HStep; inversion HV;
  inversion HStep; subst; eauto using Precision.
Qed.


Ltac ForceΓEmpty Γ :=
    replace Γ with (@MEmpty IRType) in *
      by (symmetry; eauto using PPE, EnvCompEmpty).


(*
** Catch-up steps preserve precision
*)
Lemma PrecisionPreservation : forall e1 e2 e2' t1 t2 m m',
    Precision MEmpty e1 t1 MEmpty e2 t2 ->
    Value e1 ->
    m / e2 --> m' / e2' ->
    Precision MEmpty e1 t1 MEmpty e2' t2.
Proof.
  intros * HP HV HStep.
  remember MEmpty as Γ.
  generalize dependent e2'.
  induction HP; subst; intros * HStep; inversion HV; subst;
  ForceΓEmpty Γ;
  inversion HStep; subst; eauto using Precision;
  try (inversion HP; subst; trivial; fail).

  exfalso.
  apply PrecisionType1 in HP. inversion HP; subst.
  ContraTags.
Qed.


(*
** Catch-up multi-steps preserve precision
*)
Lemma PrecisionPreservationMult : forall e1 e2 e2' t1 t2 m m',
    Precision MEmpty e1 t1 MEmpty e2 t2 ->
    Value e1 ->
    m / e2 -->* m' / e2' ->
    Precision MEmpty e1 t1 MEmpty e2' t2.
Proof.
  induction 3; eauto using PrecisionPreservation.
Qed.


(*
** Catch-up applied to boxes: if the term "catching-up" is a box,
** it remains a box.
*)
Lemma BoxPreservePrecision : forall e m m' b tg v t,
  m / IREBox tg e -->* m' / b ->
  Precision MEmpty v t MEmpty (IREBox tg e) IRTStar ->
  Value v ->
  exists o, b = IREBox tg o /\ Precision MEmpty v t MEmpty b IRTStar.
Proof.
  intros * Hst.
  remember (IREBox tg e) as E.
  generalize dependent e.
  induction Hst; intros * HEq HP HV; eauto.
  - subst.
    replace m' with m in * by (eauto using stepValueMem).
    inversion H; subst.
    eauto using PrecisionPreservation.
Qed.


Ltac typePrecLT :=
  match goal with
    [HP: Precision _ _ ?t _ _ (Tag2Type ?g),
     HT: ?t <| Tag2Type ?tg |- _] =>
       replace g with tg in * by (eauto using GroundTop, PPT)
  end.

(*
** If the term "catching-up" has type '*', it converges to a box.
*)
Lemma ValueStarP : forall tg t v e m e',
    Precision MEmpty v t MEmpty e IRTStar ->
    t <| Tag2Type tg ->
    Value v ->
    m / e -->* m / e' ->
    Value e' ->
      exists o,
        e' = IREBox tg o /\ Precision MEmpty v t MEmpty e' IRTStar.
Proof.
  intros * HP HSty HVP HStep HV.
  inversion HP; subst; try (inversion HVP; fail);
  ContraTags.
  typePrecLT.
  eauto using BoxPreservePrecision.
Qed.


(*
** Obs: reduction uses only unbox(box x); it does not change memory
*)
Theorem CatchUp : forall e1 t1 e2 t2 m,
  Precision MEmpty e1 t1 MEmpty e2 t2 ->
  Value e1 ->
  exists e2', m / e2 -->* m / e2' /\ Value e2'.
Proof.
  intros * HP HV.
  remember MEmpty as Γ eqn:Heq.
  induction HP; subst; inversion HV; subst;
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
  ForceΓEmpty Γ;

  destruct (ValueStarP HP H HV H0 H1) as [? [? _]]; eauto; subst;
  try (eapply GroundType in H; only 2: (simpl; trivial);
    apply valBoxVal in H1;
    exists x0; split;
    eauto using multiTrans, CongUnbox, StUnbox, multistep).
Qed.


Corollary CatchUpP : forall e1 t1 e2 t2 m,
  Precision MEmpty e1 t1 MEmpty e2 t2 ->
  Value e1 ->
  exists e2', m / e2 -->* m / e2' /\ Value e2' /\
              Precision MEmpty e1 t1 MEmpty e2' t2.
Proof.
  intros * HP HV.
  specialize (CatchUp m HP HV) as [e2' [HSt HV']].
  exists e2'.
  repeat split; eauto using PrecisionPreservationMult.
Qed.


Ltac BreakIH :=
  match goal with
    [IH: context [_ / ?E --> _ / _ -> (PrecMem _ _) -> _] ,
     HSt: ?M / ?E --> _ / _ ,
     HM: ?M <M| ?M' |- _ ] =>
       specialize (IH eq_refl _ _ _ _ HSt HM) as [? [? [? [? ?]]]]
  end.


(*
** Unbox terms are not values. (Avoid repeated inversions.)
*)
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
  [ HP: Precision _ ?E _ _ ?E' _ |- context [?M / _ -->* _ / _] ] =>
      match goal with
      | [ H: _ / E' -->* _ / _  |- _ ] => fail 1  (* already done *)
      | [ |- _ ] =>  (* otherwise *)
        assert (HXX: Value E) by eauto using Value;
        specialize (CatchUp M HP HXX) as [? [? ?]];
        clear HXX
      end
  end.


Ltac applyRules := repeat split;
  eauto 9 using EnvCompRefl, CongBox, CongUnbox,
    CongPlus1, CongPlus2, CongGet1, CongGet2,
    CongApp1, CongApp2, CongSet1, CongSet2, CongSet3, CongLet,
    PrecQueryT, PrecUpdate, PrecSubs, map_eq_refl,
    Precision, PrecisionPreservationMult, multiTrans, multistep1, step
.

Ltac solveSim2 := eexists; eexists; applyRules.

Ltac solveSim1 m := eexists; exists m; applyRules.

Ltac solveSim e m := exists e; exists m; applyRules.

(*
** Main simulation lemma
*)
Theorem Sim : forall m1 e1 t1 e2 m2 t2 m1' e1',
  Precision MEmpty e1 t1 MEmpty e2 t2 ->
  m1 / e1 --> m1' / e1'   ->
  m1 <M| m2 ->
  exists e2' m2',
    m2 / e2 -->* m2' / e2' /\ m1' <M| m2' /\ Precision MEmpty e1' t1 MEmpty e2' t2.
Proof.
  intros * HP.
  generalize dependent m2.
  generalize dependent e1'.
  generalize dependent m1'.
  generalize dependent m1.
  remember MEmpty as Γ.
  induction HP; intros * Hstep HM;

  (* Handle BoxR and UnboxR, which should not invert step *)
  try (subst; BreakIH; solveSim2; fail);

  inversion Hstep; subst; repeat BreakIH;
  try ForceΓEmpty Γ;

  repeat doCatchUp;

  (* Handle all "congruence" cases *)
  try (solveSim1 x0; fail).


  - (* StPlus *)
    assert (N1: IRENum n1 = x) by
      eauto using PrecValue, Value, PrecisionPreservationMult.

    assert (N2: IRENum n2 = x0) by
      eauto using PrecValue, Value, PrecisionPreservationMult.

    subst.
    solveSim (IRENum (n1 + n2)) m2.

  - (* StCstr *)
    destruct (PrecFreshT HM H0) as [? [? ?]]; eauto.
    solveSim2.

  - (* StGet *)
    clear IHHP1 IHHP2.

    assert (N1: IRETAddr a = x) by
      eauto using PrecValue, Value, PrecisionPreservationMult.

    subst.
    solveSim (queryT a x0 m2) m2.

  - (* StSet *)
    clear IHHP1 IHHP2 IHHP3.

    assert (N1: IRETAddr a = x) by
      eauto using PrecValue, Value, PrecisionPreservationMult.

    subst.
    exists IRENil. eexists (UpdateT _ _ (EV x1 H4) _).
    applyRules.

  - (* StLet *)
    clear IHHP1 IHHP2.
    solveSim ([var := x] b2) m2.

  - (* StFun *)
    clear IHHP.
    destruct (PrecFreshF HM HP H5) as [? [? ?]]; eauto.
    solveSim2.

  - (* StApp *)
    clear IHHP1 IHHP2.

    assert (N1: IREFAddr a = x0) by
      eauto using PrecValue, Value, PrecisionPreservationMult.

    subst.
    destruct (queryF a m2) as [var' body'] eqn:HEq2. symmetry in HEq2.
    destruct (PrecQueryF a HM H5 HEq2) as [? ?]; eauto; subst.
    solveSim (IRELet var' IRTStar x body') m2.

  - (* StUnbox *)
    clear IHHP.
    inversion HP; subst; ContraTags.
    * exfalso. apply PPT in H1. ContraTags.
    * exists x. exists m2. split. auto. split. auto.
      assert ((Tag2Type g) <| (Tag2Type g)) as R. apply TPrecisionRefl.
      destruct (ValueStarP H3 R H5 H) as [? [? ?]]; eauto using TPrecision.
Qed.


(*
** Simulation theorem
*)
Theorem SimMult : forall m1 e1 t1 e2 m2 t2 m1' e1',
  m1 / e1 -->* m1' / e1'   ->
  Value e1' ->
  Precision MEmpty e1 t1 MEmpty e2 t2 ->
  m1 <M| m2 ->
  exists e2' m2',
    m2 / e2 -->* m2' / e2' /\
    Precision MEmpty e1' t1 MEmpty e2' t2 /\
    m1' <M| m2' /\
    Value e2'.
Proof.
  intros * HMSt.
  generalize dependent m2.
  generalize dependent t2.
  generalize dependent e2.
  induction HMSt; intros * HV HPE HMem.
  - destruct (CatchUp m2 HPE HV) as [? [? ?]]; eauto.
    eexists. eexists; repeat split; eauto using PrecisionPreservationMult.
  - destruct (Sim HPE H HMem) as [? [? [? [? ?]]]]; eauto.
    destruct (IHHMSt x t2 x0 HV H2 H1) as [? [? [? [? [? ?]]]]]; eauto.
    exists x1. exists x2. repeat split; eauto using multiTrans.
Qed.


(*
** Simulation theorem for programmers: no mentions to precision,
** concept expressed only in terms of 'dyn'
*)
Corollary SimDyn : forall m1 e1 t1 m1' v1,
  m1 / e1 -->* m1' / v1   ->
  MEmpty |= e1 : t1 ->
  mem_correct m1 ->
  Value v1 ->
  exists v2 m2',
    m1 / dyn e1 -->* m2' / v2 /\
    v2 = dyn v1 /\
    (* m1' <M| m2' /\ *)
    Value v2.
Proof.
  intros * HSt Hty HM HV.
  assert(Precision MEmpty e1 t1 MEmpty (dyn e1) IRTStar)
    by (eapply DynLessPrecise; trivial).
  assert (m1 <M| m1) by auto using PrecMemRefl.
  destruct (SimMult HSt HV H H0) as [? [? [? [? [? ?]]]]]; eauto.
  eexists x. eexists. repeat split;
  eauto using PrecDynEqualVal.
Qed.


