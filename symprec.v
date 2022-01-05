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

Set Implicit Arguments.


Inductive PrecMem : Mem -> Mem -> Prop :=
| PrecMemE : PrecMem EmptyMem EmptyMem
| PrecMemUD : forall addr idx v1 v2 m1 m2,
    Value v1 ->
    Value v2 ->
    Precision PEmpty v1 IRTStar v2 IRTStar ->
    PrecMem m1 m2 ->
    PrecMem (Update addr idx v1 m1) (Update addr idx v2 m2)
.


Infix "<M|" := PrecMem (at level 80).


Lemma PrecCorrect1 : forall m1 m2, m1 <M| m2 -> mem_correct m1.
Proof.
  unfold mem_correct.
  intros * H.
  induction H; intros *; simpl.
  - eauto using Value, IRTyping.
  - breakIndexDec; subst; eauto using PrecisionType1Empty.
Qed.


Lemma PrecCorrect2 : forall m1 m2, m1 <M| m2 -> mem_correct m2.
Proof.
  unfold mem_correct.
  intros * H.
  induction H; intros *; simpl.
  - eauto using Value, IRTyping.
  - breakIndexDec; subst; eauto using PrecisionType2Empty.
Qed.


Lemma PrecFreshaux : forall m1 m2,
    m1 <M| m2 -> freshaux m1 = freshaux m2.
Proof.
  intros * HOM.
  induction HOM; simpl; eauto.
Qed.


Lemma PrecFresh : forall m1 m2 free m1',
    m1 <M| m2 ->
    (free, m1') = fresh m1 ->
    exists m2', m1' <M| m2' /\ (free, m2') = fresh m2.
Proof.
  unfold fresh.
  intros * HOM HF.
  injection HF; intros; subst; clear HF.
  replace (freshaux m2) with (freshaux m1) by auto using PrecFreshaux.
  eexists. split; only 2: trivial;
  eauto 6 using PrecMem, Value, Precision.
Qed.


Axiom PrecIndex : forall e1 e2,
    Precision PEmpty e1 IRTStar e2 IRTStar ->
    ToIndex e1 = ToIndex e2.


Lemma PrecQuery : forall m1 m2 a i1 i2,
    m1 <M| m2 ->
    Precision PEmpty i1 IRTStar i2 IRTStar ->
    Precision PEmpty (query a i1 m1) IRTStar (query a i2 m2) IRTStar.
Proof.
  intros * HOM HP.
  induction HOM; simpl.
  - eauto using Precision.
  - rewrite <- (PrecIndex HP).
    breakIndexDec; trivial.
Qed.


Lemma PrecUpdate : forall m1 m2 a i1 i2 v1 v2,
    m1 <M| m2 ->
    Value v1 ->
    Value v2 ->
    Precision PEmpty i1 IRTStar i2 IRTStar ->
    Precision PEmpty v1 IRTStar v2 IRTStar ->
    Update a (ToIndex i1) v1 m1 <M| Update a (ToIndex i2) v2 m2.
Proof.
  intros * HOM HV1 HV2 HP1 HP2.
  rewrite <- (PrecIndex HP1).
  auto using PrecMem.
Qed.


(*
Lemma subst_typing : forall e2 Γ var tv te e1,
  var |=> tv; Γ |= e2 : te -> MEmpty |= e1 : tv ->
       Γ |= ([var := e1] e2) : te.
Proof.
  induction e2; intros Γ var tv te e1 HT2 HT1;
  simpl; inversion HT2; subst;
  breakStrDec;
  eauto 6 using inclusion_typing, inclusion_shadow, inclusion_permute,
    IRTyping, typing_empty, InNotEq.
  - assert (te = tv). { rewrite InEq in H1. congruence. }
      subst. eauto using typing_empty.
Qed.
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
  induction HPB; intros ? HPE; eauto using Precision.

  - simpl.
    destruct HPE.
    breakStrDec.
    + specialize (H1 var0).
      specialize (H2 var0).
      rewrite Expand1 in H1.
      rewrite Expand2 in H2.
      rewrite InEq in H1.
      rewrite InEq in H2.
      replace t0 with t1 by congruence.
      replace t3 with t2 by congruence.
      eauto using PrecisionInclusion, PinclusionEmpty.

    + apply PVar.
      * specialize (H1 var0).
        rewrite Expand1 in H1.
        rewrite InNotEq' in H1;
        congruence.
      * specialize (H2 var0).
        rewrite Expand2 in H2.
        rewrite InNotEq' in H2;
        congruence.

  - simpl.
    breakStrDec.
    + apply PFun with (H12 := H0).
      eauto using PrecisionIrrel, PEquivTrans, PEquivShadow, ExpandEquiv,
                  PEquivSym.
      Unshelve. trivial.
    + apply PFun with (H12 := H0).
      apply IHHPB.
      eauto using PrecisionIrrel, PEquivTrans, PEquivPermute, ExpandEquiv,
                  PEquivSym.
      Unshelve. trivial.
Qed.


Lemma PrecSubs' : forall var t1 t2 t1' t2' body body' v1 v2,
    Precision PEmpty (IREFun var t1 body) (IRTFun t1 t1')
                     (IREFun var t2 body') (IRTFun t2 t2') ->
    Precision PEmpty v1 t1 v2 t2 ->
    Precision PEmpty ([var := v1] body) t1' ([var := v2] body') t2'.
Proof.
  intros * HPF HPV.
  inversion HPF; subst.
  eapply PrecSubs; eauto.
  unfold Pinclusion; split.
  * unfold inclusion.
    rewrite Expand1.
    rewrite Expand1.
    trivial.
  * unfold inclusion.
    rewrite Expand2.
    rewrite Expand2.
    trivial.

  Unshelve. trivial.
Qed.


Lemma GroundFlat' : forall t g g',
    t <| Tag2Type g' -> t = Tag2Type g -> g = g'.
Proof.
  intros * H HEq. subst. auto using GroundFlat.
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


Lemma GroundType: forall g t g',
    t <| Tag2Type g -> Type2Tag t = Some g' -> g = g'.
Proof.
  intros * HT Heq.
  destruct t eqn:Heq';
  ContraTags;
  try (injection Heq; intros;
    rewrite <- Heq' in HT;
    replace t with (Tag2Type g') in HT by (subst; trivial);
    symmetry;
    eauto using GroundFlat).
  injection Heq; intros; subst.
  assert (IRTFun i1 i2 <| Tag2Type TgFun) by (simpl; auto using TPrecision).
  eauto using GroundTop.
Qed.


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


Lemma PrecisionPreservationM : forall e1 e2 e2' t1 t2 m m',
    Precision PEmpty e1 t1 e2 t2 ->
    Value e1 ->
    m / e2 -->* m' / e2' ->
    Precision PEmpty e1 t1 e2' t2.
Proof.
  intros * HP HV HStep.
  induction HStep; eauto using PrecisionPreservation.
Qed.


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
  replace g with tg in *. 2:{
    apply PPT in H.
    eauto using GroundTop.
  }
  eauto using BoxPreservePrecision.
Qed.


Lemma ValueLR : forall e1 t1 e2 t2 m,
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

  specialize (ValueStarP _ HP H HV H0 H1) as [? [? _]];
      subst;

  try (eapply GroundType in H; only 2: (simpl; trivial);
    apply valBoxVal in H1;
    exists x0; split;
    eauto using multiTrans, CongUnbox, step, multistep).
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


Theorem Sym : forall m1 e1 t1 e2 m2 t2 m1' e1',
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
  induction HP; intros * Hstep HM; try (inversion Hstep; fail).

  - (* Plus *)
    inversion Hstep; subst.

    + (* StPlus1 *)
      BreakIH.
      eexists; eexists; split; try split; eauto using Precision, CongPlus1.

    + (* StPlus2 *)
      BreakIH.
      specialize (ValueLR m2 HP1 H2) as [? [? ?]].
      eexists; exists x0; split; try split;
        eauto using multiTrans, CongPlus1, CongPlus2,
                    Precision, PrecisionPreservationM.

    + (* StPlus *)
      clear IHHP1 IHHP2.
      specialize (ValueLR m2 HP1 (Vnum n1)) as [? [? ?]].
      specialize (ValueLR m2 HP2 (Vnum n2)) as [? [? ?]].

      assert (N1: x = IRENum n1). {
        specialize (PrecisionPreservationM HP1 (Vnum n1) H) as NH1.
        inversion NH1; subst; trivial; NoValueUnbox.
      }

      assert (N2: x0 = IRENum n2). {
        specialize (PrecisionPreservationM HP2 (Vnum n2) H1) as NH2.
        inversion NH2; subst; trivial; NoValueUnbox.
      }

      subst.
      exists (IRENum (n1 + n2)). exists m2. split; try split;
        eauto 7 using multiTrans, CongPlus1, CongPlus2, multistep1, step,
           Precision.


  - (* StCstr *)
    inversion Hstep; subst.
    specialize (PrecFresh HM H) as [? [? ?]].
    eexists; eexists; split; try split;
    eauto using multistep1, step, Precision.


  - (* Get *)
    inversion Hstep; subst.

    + (* StGet1 *)
      BreakIH.
      eexists; eexists; split; try split; eauto using Precision, CongGet1.

    + (* StGet2 *)
      BreakIH.
      specialize (ValueLR m2 HP1 H2) as [? [? ?]].
      eexists; exists x0; split; try split;
        eauto using multiTrans, CongGet1, CongGet2,
                    Precision, PrecisionPreservationM.

    + (* StGet *)
      clear IHHP1 IHHP2.

      specialize (ValueLR m2 HP1 (Vtbl a)) as [? [? ?]].
      specialize (ValueLR m2 HP2 H4) as [? [? ?]].

      assert (N1: x = IREAddr a). {
        specialize (PrecisionPreservationM HP1 (Vtbl a) H) as NH1.
        inversion NH1; subst; trivial; NoValueUnbox.
      } subst.

      exists (query a x0 m2). exists m2. split; try split;
        eauto 7 using multiTrans, CongGet1, CongGet2, multistep1, step,
           Precision, PrecQuery, PrecisionPreservationM.

  - (* Set *)
    inversion Hstep; subst.

    + (* StSet1 *)
      BreakIH.
      eexists; eexists; split; try split; eauto using Precision, CongSet1.

    + (* StSet2 *)
      BreakIH.
      specialize (ValueLR m2 HP1 H5) as [? [? ?]].
      eexists; exists x0; split; try split;
        eauto using multiTrans, CongSet1, CongSet2,
                    Precision, PrecisionPreservationM.

    + (* StSet3 *)
      BreakIH.
      specialize (ValueLR m2 HP1 H3) as [? [? ?]].
      specialize (ValueLR m2 HP2 H6) as [? [? ?]].
      eexists; exists x0; split; try split;
        eauto 6 using multiTrans, CongSet1, CongSet2, CongSet3,
                    Precision, PrecisionPreservationM.

    + (* StSet *)
      clear IHHP1 IHHP2 IHHP3.

      specialize (ValueLR m2 HP1 (Vtbl a)) as [? [? ?]].
      specialize (ValueLR m2 HP2 H5) as [? [? ?]].
      specialize (ValueLR m2 HP3 H6) as [? [? ?]].

      assert (N1: x = IREAddr a). {
        specialize (PrecisionPreservationM HP1 (Vtbl a) H) as NH1.
        inversion NH1; subst; trivial; NoValueUnbox.
      } subst.

      exists x1. exists (Update a x0 x1 m2). split; try split;
        eauto 10 using multiTrans, CongSet1, CongSet2, CongSet3,
          multistep1, step, Precision, PrecQuery, PrecisionPreservationM,
          PrecUpdate.


  - (* StFunApp *)
    inversion Hstep; subst.

    + (* StFunApp1 *)
      BreakIH.
      eexists; eexists; split; try split; eauto using Precision, CongFunApp1.

    + (* StFunApp2 *)
      BreakIH.
      specialize (ValueLR m2 HP2 H2) as [? [? ?]].
      eexists; exists x0; split; try split;
        eauto using multiTrans, CongFunApp1, CongFunApp2,
                    Precision, PrecisionPreservationM.

    + (* StFunApp *)
      clear IHHP1 IHHP2.

      replace t with t1 in * by
        (apply PrecisionType1 in HP2; inversion HP2; subst; trivial).

      specialize (ValueLR m2 HP1 H4) as [? [? ?]].
      specialize (ValueLR m2 HP2 (Vfun var t1 body)) as [? [? ?]].

      assert (N1: exists body', x0 = IREFun var t2 body'). {
        specialize (PrecisionPreservationM HP2 (Vfun var t1 body) H1) as NH1.
        inversion NH1; subst; eauto; NoValueUnbox.
      }
      destruct N1 as [body' ?].
      subst.
      exists ([var := x] body'). exists m2. split; try split;
        eauto 7 using multiTrans, CongFunApp1, CongFunApp2, multistep1, step,
           Precision.

      eauto using PrecSubs', PrecisionPreservationM, Value.

  - (* BoxR *)
      subst.
      BreakIH.
      eexists; eexists; split; try split; eauto using Precision, CongBox.

  - (* BoxL *)
      inversion Hstep; subst.
      BreakIH.
      eexists; eexists; split; try split; eauto using Precision, CongBox.

  - (* UnboxL *)
      inversion Hstep; subst.

      + BreakIH.
       eexists; eexists; split; try split; eauto using Precision, CongUnbox.

      + clear IHHP.
        specialize (ValueLR m2 HP (Vbox g e1' H5)) as [? [? ?]].

        inversion HP; subst; ContraTags.
        * exfalso. apply PPT in H1. ContraTags.
        * specialize (@ValueStarP _ _ _ _ _ _ H3 (TPrecisionRefl (Tag2Type g))
            H5 H H0) as [? [? ?]].
          subst.
          eexists; eexists; split; try split; eauto.

  - (* UnboxR *)
      subst.
      BreakIH.
      eexists; eexists; split; try split; eauto using Precision, CongUnbox.
Qed.


