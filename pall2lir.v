Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.

Require Import LIR.lir.
Require Import LIR.pallene.


(*
** Convert a Pallene type to its corresponding Lir type
*)
Definition PT2IRT (t : PType) : IRType :=
  match t with
  | PTStar => IRTStar
  | PTNil => Tag2Type TgNil
  | PTInt => Tag2Type TgInt
  | PTArr _ => Tag2Type TgTbl
  | PTFun _ _ =>  Tag2Type TgFun
  end.


Lemma PT2IRTFun : forall T1 T2,
    PT2IRT (PTFun T1 T2) = IRTFun.
Proof. intros T1 T2. unfold PT2IRT. trivial. Qed.


(*
** Convert a Pallene environment to a Lir environment
*)
Fixpoint TP2TGamma (Γ : Map PType) : IREnvironment :=
  match Γ with
  | MEmpty => MEmpty
  | MCons var T Γ' => MCons var (PT2IRT T) (TP2TGamma Γ')
  end.


Lemma TP2TGammaIn : forall Γ var T,
    In Γ var = Some T -> In (TP2TGamma Γ) var = Some (PT2IRT T).
Proof.
  induction Γ; intros var T H; simpl in *; breakStrDec;
  auto;
  congruence.
Qed.


(*
** Casts an expression of type 't1' to one of type 't2'.
*)
Definition Cast (t1 t2 : IRType) (e : IRE) : IRE :=
  match t1, t2 with
  | IRTStar, IRTStar => e
  | IRTStar, Tag2Type t => IREBox t e
  | Tag2Type t, IRTStar => IREUnbox t e
  | Tag2Type t1', Tag2Type t2' => if dec_Tag t1' t2' then e
                                  else IREUnbox t1' (IREBox t2' e)
  end.


Notation "'<' t1 '<=' t2 '>' e" := (Cast t1 t2 e)
    (at level 50, t1 at next level, t2 at next level).


Lemma CastStep : forall t1 t2 e m e' m',
  step m e m' e' ->
  step m (<t1 <= t2> e) m' (<t1 <= t2> e').
Proof.
  intros * HSt.
  unfold Cast.
  destruct t1; destruct t2; eauto using step.
  destruct (dec_Tag t t0); eauto using step.
Qed.


Lemma CongCast : forall t1 t2 e m e' m',
  multistep m e m' e' ->
  multistep m (<t1 <= t2> e) m' (<t1 <= t2> e').
Proof.
  intros * HSt.
  induction HSt; eauto using multistep, CastStep.
Qed.



(*
** Get the ground type of an expression; if correctly typed;
** otherwise assume nil. (The expression will always be correctly
** typed.)
*)
Definition tagOf Γ e : IRType :=
  match typeOf Γ e with
  | Some T => PT2IRT T
  | None => IRTNil
  end.


Lemma tagOfT : forall Γ e T, typeOf Γ e = Some T -> tagOf Γ e = PT2IRT T.
Proof. intros. unfold tagOf. rewrite H. trivial. Qed.


Lemma tagOfT' : forall Γ e T, Γ |= e : T -> tagOf Γ e = PT2IRT T.
Proof. eauto using tagOfT, typeOfCorrect'. Qed.


Lemma tagStar2type : forall Γ e,
    tagOf Γ e = IRTStar -> typeOf Γ e = Some PTStar.
Proof.
  unfold tagOf.
  intros Γ e H.
  destruct (typeOf Γ e) eqn:?; try easy.
  destruct p; easy.
Qed.


(*
** Translation (compilation) of Pallene programs to Lir
*)
Fixpoint Pall2Lir (Γ : PEnvironment) (e : PE) : IRE :=
  match e with
  | PENil => IRENil
  | PENum a => IRENum a
  | PEPlus e1 e2 => IREPlus (Pall2Lir Γ e1) (Pall2Lir Γ e2)
  | PENew _ => IRENew
  | PETAddr a _ => IRETAddr a
  | PEFAddr a _ _ => IREFAddr a
  | PEGet e1 e2 =>
         <tagOf Γ e <= IRTStar>
           (IREGet (Pall2Lir Γ e1) (<IRTStar <= (Tag2Type TgInt)> (Pall2Lir Γ e2)))
  | PESet e1 e2 e3 =>
         (IRESet (Pall2Lir Γ e1)
                 (<IRTStar <= Tag2Type TgInt> (Pall2Lir Γ e2))
                 (<IRTStar <= tagOf Γ e3> Pall2Lir Γ e3))
  | PEVar var => IREVar var
  | PEFun var T body _  => let Γ' := (var |=> T; Γ) in
        IREFun var
          (IRELet var (PT2IRT T) (<PT2IRT T <= IRTStar> (IREVar var))
                     (<IRTStar <= tagOf Γ' body> (Pall2Lir Γ' body)))
  | PEApp e1 e2 => <tagOf Γ e <= IRTStar>
         (IREApp (Pall2Lir Γ e1)
                  (<IRTStar <= (tagOf Γ e2)> Pall2Lir Γ e2))
  | PECast e1 t => <PT2IRT t <= tagOf Γ e1> (Pall2Lir Γ e1)
  end.


Lemma invertCall : forall Γ e1 e2 T1 T2,
  typeOf Γ e1 = Some (PTFun T1 T2) -> typeOf Γ e2 = Some T1 ->
    typeOf Γ (PEApp e1 e2) = Some T2.
Proof.
  intros Γ e1 r2 T1 T2 H1 H2.
  simpl. rewrite H1. rewrite H2.
  destruct (dec_TP T1 T1); congruence.
Qed.


Lemma invertFun : forall Γ e1 e2 T1 T2,
    typeOf Γ e1 = Some (PTFun T1 T2) ->
    tagOf Γ (PEApp e1 e2) = IRTStar ->
    T2 = PTStar.
Proof.
  intros Γ e1 e2 T1 T2 H1 H2.
  unfold tagOf in H2.
  destruct (typeOf Γ (PEApp e1 e2)) eqn:?; try easy.
  apply typeOfCorrect'' in H1.
  apply typeOfCorrect'' in Heqo.
  destruct p; try easy.
  inversion Heqo; subst.
  apply (PTypeUnique _ _ _ _ H1) in H4.
  congruence.
Qed.


Ltac breakTagOf :=
  match goal with
  [H: typeOf _ ?E = Some ?T |- context C [tagOf _ ?E] ] =>
    apply tagOfT in H; rewrite H; destruct (PT2IRT T) eqn:?;
    eauto using IRTyping
  end.


Lemma PT2IRTag : forall tg T,
  PT2IRT T = Tag2Type tg -> T <> PTStar.
Proof.
  intros * Heq HCnt.
  destruct T; discriminate.
Qed.


Lemma PTStarB : forall (T : PType),
    PT2IRT T = IRTStar -> T = PTStar.
Proof.
  intros T H.
  destruct T; inversion H; easy.
Qed.


Lemma typeStar : forall Γ e T,
    typeOf Γ e = Some T -> tagOf Γ e = IRTStar -> T = PTStar.
Proof.
  intros Γ e T HT Htg.
  unfold tagOf in Htg.
  rewrite HT in Htg.
  auto using PTStarB.
Qed.


Lemma typeTag : forall Γ e T tg,
    typeOf Γ e = Some T -> tagOf Γ e = Tag2Type tg -> PT2IRT T = Tag2Type tg.
Proof.
  intros Γ e T tg HT Htg.
  unfold tagOf in Htg.
  rewrite HT in Htg.
  auto.
Qed.


(*
** Compilation of well-typed programs results in well-typed code
*)
Theorem Pall2LirWellTyped : forall Γ Γ' (e : PE) T T',
    Γ |= e : T ->
    TP2TGamma Γ = Γ' ->
    PT2IRT T = T' ->
    IRTyping Γ' (Pall2Lir Γ e) T'.
Proof with eauto using IRTyping.
  intros * H Eq1 Eq2. subst.
  induction H; simpl in *;
  eauto using IRTyping,TP2TGammaIn;
  repeat match goal with
  | [H: PTyping ?G ?E ?T |- _] =>
      apply typeOfCorrect in H
  end.

  - (* Get *)
    unfold tagOf. simpl. rewrite H. rewrite H0.
    destruct (PT2IRT T) eqn:?; simpl; eauto using IRTyping.

  - (* Set *)
    unfold tagOf. rewrite H1.
    destruct (PT2IRT T) eqn:?; simpl; eauto using IRTyping.

  - (* Fun *)
    apply IRTyFun. eapply IRTyLet.
    + destruct (tagOf (var |=> Tvar; Γ)) eqn:?; subst.
      * apply IRTyBox.
        eapply inclusion_typing.
        ** eapply inclusion_shadow'.
        ** unfold tagOf in Heqi. rewrite H in Heqi.
           rewrite <- Heqi. trivial.
      *  unfold tagOf in Heqi. rewrite H in Heqi.
        rewrite Heqi in IHPTyping.
        simpl in IHPTyping.
        eapply inclusion_typing; eauto.
        apply inclusion_shadow'.
    + unfold Cast.
      destruct (PT2IRT Tvar) eqn:?.
      * apply IRTyUnbox.
        ** trivial.
        ** apply IRTyVar. apply InEq.
      * subst. simpl.
        apply IRTyVar. apply InEq.

  - (* App *)
    destruct (tagOf Γ (PEApp e1 e2)) eqn:?.
    + specialize (invertCall _ _ _ _ _ H H0) as H2.
      unfold tagOf in Heqi. rewrite H2 in Heqi.
      simpl.
      apply IRTyUnbox; trivial.
      eapply IRTyApp; eauto.
      destruct (tagOf Γ e2) eqn:?.
      * apply IRTyBox.
        specialize (typeTag _ _ _ _ H0 Heqi0) as HTt.
        rewrite <- HTt. trivial.
      * specialize (typeStar _ _ _ H0 Heqi0) as HTS.
        subst. trivial.
    + unfold Cast.
      specialize (invertFun _ _ _ _ _ H Heqi); intros; subst; simpl.
      destruct (tagOf Γ e2) eqn:?.
      * eapply IRTyApp; eauto using IRTyping.
        eapply IRTyBox.
        specialize (typeTag _ _ _ _ H0 Heqi0) as HTt.
        rewrite <- HTt. trivial.
      * eapply IRTyApp; eauto using IRTyping.
        specialize (typeStar _ _ _ H0 Heqi0) as HTS.
        subst. trivial.

  - (* Cast *)
    unfold Cast.
    destruct (PT2IRT T2) eqn:?;
    unfold tagOf;
    rewrite H;
    destruct (PT2IRT T1) eqn:?.
    + destruct (dec_Tag t t0); subst; trivial.
      eapply IRTyUnbox; trivial.
      eapply IRTyBox.
      trivial.
    + apply IRTyUnbox; trivial.
  + apply IRTyBox. trivial.
  + unfold PT2IRT in *.
    trivial.
Qed.


Lemma typeOfEq : forall Γ1 e1 Γ2 e2 T,
  Γ1 |= e1 : T ->
  Γ2 |= e2 : T ->
  typeOf Γ1 e1 = typeOf Γ2 e2.
Proof.
  intros * HTy1 HTy2.
  erewrite typeOfCorrect'; eauto.
  erewrite typeOfCorrect'; eauto.
Qed.

Lemma tagOfEq : forall Γ1 e1 Γ2 e2 T,
  Γ1 |= e1 : T ->
  Γ2 |= e2 : T ->
  tagOf Γ1 e1 = tagOf Γ2 e2.
Proof.
  intros * HTy1 HTy2.
  unfold tagOf.
  erewrite typeOfEq; eauto.
Qed.


Ltac tagOf2T :=
  repeat   (* replace tagOfs with theirs types *)
      (erewrite tagOfT';
       eauto using PTyping, PinclusionType, inclusion_update,
                   Psubst_typing, inclusion_shadow, inclusion_permute,
                   PexpPreservation).


Lemma Pall2LirEEnv : forall Γ Γ' e T,
  Γ |= e : T ->
  inclusion Γ Γ' ->
  Pall2Lir Γ e = Pall2Lir Γ' e.
Proof.
  intros * HTy HIn.
  generalize dependent Γ'.
  induction HTy; intros; subst; trivial;
  simpl;   (* expose tagOfs *)
  tagOf2T;
  repeat match goal with   (* do the rewrites from the hypotheses *)
  | [ H: _ -> _ -> _ = _ |- _] =>
     erewrite H; eauto using inclusion_update; clear H
  end.
Qed.



Lemma Psubst : forall Γ var Tvar e1 e2 te,
  (var |=> Tvar; Γ) |= e2 : te ->
  MEmpty |= e1 : Tvar ->
  Pall2Lir Γ ([var := e1] e2) =
    lir.substitution var (Pall2Lir MEmpty e1) (Pall2Lir (var |=> Tvar; Γ) e2).
Proof.
  intros * HTy2 HTy1.
  generalize dependent te.
  generalize dependent Γ.
  induction e2; intros * HTy2; trivial; inversion HTy2; subst;
  simpl;

  repeat match goal with   (* do the rewrites from the hypotheses *)
  | [ H: _ -> _ -> _ -> _ = _ |- _] =>
     erewrite H; eauto using inclusion_update, PTyping; clear H
  end.

  - tagOf2T.
    destruct (PT2IRT te); trivial.

  - simpl.
    tagOf2T.
    destruct (PT2IRT T); trivial.

  - simpl. destruct (string_dec var s); trivial.
    symmetry. eauto using Pall2LirEEnv, PinclusionType, inclusion_empty.

  - simpl.
    tagOf2T.
    destruct (PT2IRT te).
    + destruct t; simpl; destruct (PT2IRT T1); trivial.
    + simpl.
      destruct (PT2IRT T1); trivial.

   - simpl. destruct (string_dec var s); subst; simpl.
     + tagOf2T.
       replace (Pall2Lir (s |=> p; (s |=> Tvar; Γ)) e2)
         with (Pall2Lir (s |=> p; Γ) e2); trivial.
       eauto using Pall2LirEEnv,  inclusion_shadow,
         PinclusionType, inclusion_shadow'.
     + destruct (PT2IRT p); subst.
       * tagOf2T.
         destruct t;
         simpl;
            f_equal;
            f_equal;
           destruct (string_dec var s); try easy;
           destruct (PT2IRT p0); simpl;
               f_equal;
                    replace (Pall2Lir (s |=> p; (var |=> Tvar; Γ)) e2)
                      with  (Pall2Lir (var |=> Tvar; (s |=> p; Γ)) e2);
                    eauto using Pall2LirEEnv, inclusion_permute,
                                   PinclusionType.
      * simpl.
        f_equal.
        f_equal.
        ** destruct (string_dec var s); easy.
        ** tagOf2T.
           destruct (PT2IRT p0); simpl;
           f_equal;
           replace (Pall2Lir (s |=> p; (var |=> Tvar; Γ)) e2)
             with  (Pall2Lir (var |=> Tvar; (s |=> p; Γ)) e2);
           eauto using Pall2LirEEnv, inclusion_permute, PinclusionType.

  - simpl. tagOf2T.
    destruct (PT2IRT te); subst; destruct (PT2IRT T1); subst; simpl;
    try destruct (dec_Tag t t0); subst; eauto.
Qed.


Lemma PValueValue : forall e, PValue e -> Value (Pall2Lir MEmpty e).
Proof.
  intros * PV.
  induction PV; simpl; eauto using Value.
  destruct (tagOf MEmpty v); eauto using Value.
Defined.


Fixpoint MPall2Lir (m : PMem) : Mem :=
  match m with
  | PEmptyMem => EmptyMem
  | PUpdateT addr idx (PEV v ev) m =>
      UpdateT addr
              idx
              (EV (Pall2Lir MEmpty v) (PValueValue v ev))
              (MPall2Lir m)
  | PUpdateF addr var T body m =>
      UpdateF addr
              var
              (IRELet var (PT2IRT T) (<PT2IRT T <= IRTStar> (IREVar var))
                 (Pall2Lir (var |=> T; MEmpty) body))
              (MPall2Lir m)
  end.


Lemma MPall2LirCorrect : forall m,
  Pmem_correct m -> mem_correct (MPall2Lir m).
Proof.
  induction m; intros H; only 1: constructor;
  inversion H; subst.
  - destruct p. eauto using mem_correct, Pall2LirWellTyped.
  - constructor; auto.
    constructor.
    + eauto using inclusion_typing, inclusion_shadow', Pall2LirWellTyped.
    + destruct (PT2IRT p); eauto using IRTyping, InEq.
Qed.


Lemma sameFreeaux : forall m,
  Pfreshaux m = freshaux (MPall2Lir m).
Proof.
  induction m; trivial.
  - destruct p. simpl. congruence.
  - simpl. congruence.
Qed.


Lemma P2LfreshT : forall m m' free,
  (free, m') = PfreshT m ->
  (free, MPall2Lir m') = freshT (MPall2Lir m).
Proof.
  unfold PfreshT,  freshT.
  intros * HEq.
  induction m; injection HEq; intros; subst; trivial;
  try (destruct p); rewrite sameFreeaux; trivial.
Qed.


Lemma TagFromType : forall e T,
  MEmpty |= e : T ->
  tagOf MEmpty e = PT2IRT T.
Proof.
  unfold tagOf. intros * HTy.
  replace (typeOf MEmpty e) with (Some T); trivial.
  symmetry; eauto using typeOfCorrect'.
Qed.


Lemma PreserveTagOf' : forall m e T m' e',
  Pmem_correct m ->
  m / e --> m' / e' ->
  MEmpty |= e : T ->
  tagOf MEmpty e' = PT2IRT T.
Proof.
  intros * HM HSt HTy.
  eauto using TagFromType, PexpPreservation.
Qed.


Lemma PreserveTagOf : forall m e t m' e',
  Pmem_correct m ->
  MEmpty |= e : t ->
  m / e --> m' / e' ->
  tagOf MEmpty e = tagOf MEmpty e'.
Proof.
  unfold tagOf. intros * HM HTy Hst.
  replace (typeOf MEmpty e') with (typeOf MEmpty e)
        by eauto using pstep, PexpPreservTypeOf.
  trivial.
Qed.


Lemma PqueryT2 : forall m a idx v,
  Pmem_correct m ->
  PqueryT a idx m = v ->
  queryT a (IREBox TgInt (IRENum idx)) (MPall2Lir m) = Pall2Lir MEmpty v.
Proof.
  intros * HMC HQr.
  generalize dependent v.
  induction HMC; intros * HEq.
  - simpl in HEq. subst. trivial.
  - destruct v.
    breakIndexDec; subst; simpl;
    breakIndexDec; subst; simpl;
      auto;
      exfalso; auto.
  - simpl. inversion HMC; subst; auto.
Qed.


Lemma PqueryF2 : forall m a var T body body',
  Pmem_correct m ->
  (var, T, body) = PqueryF a m ->
  (var, body') = queryF a (MPall2Lir m) ->
  body'= IRELet var (PT2IRT T) (< PT2IRT T <= IRTStar > IREVar var)
               (Pall2Lir (var |=> T; MEmpty) body).
Proof.
  intros * HMC.
  induction m; intros * HQr1 HQr2; inversion HMC; subst.
  - injection HQr1; injection HQr2; intros; subst; trivial.
  - destruct p. eauto.
  - simpl in *. destruct (Nat.eq_dec a a0); eauto.
    injection HQr1; injection HQr2; intros; subst; trivial.
Qed.


Lemma PqueryF2V : forall m a var var' T body body',
  Pmem_correct m ->
  (var, T, body) = PqueryF a m ->
  (var', body') = queryF a (MPall2Lir m) ->
  var = var'.
Proof.
  intros * HMC.
  induction m; intros * HQr1 HQr2; inversion HMC; subst.
  - injection HQr1; injection HQr2; intros; subst; trivial.
  - destruct p. eauto.
  - simpl in *. destruct (Nat.eq_dec a a0); eauto.
    injection HQr1; injection HQr2; intros; subst; trivial.
Qed.


Lemma PCast2Lir : forall e T1 T2 v,
  MEmpty |= e : T1 ->
  PValue e ->
  PCast e T2 = Some v ->
  Pall2Lir MEmpty v = < PT2IRT T2 <= PT2IRT T1> (Pall2Lir MEmpty e).
Proof.
Abort.


Lemma PCastBox : forall v T v' t,
  MEmpty |= v : PTStar ->
  PValue v ->
  PCast v T = Some v' ->
  PT2IRT T = Tag2Type t ->
  Pall2Lir MEmpty v = IREBox t (Pall2Lir MEmpty v').
Proof.
  intros * HTy HV HCst Heq.
  assert (T <> PTStar) by (intros contra; subst; discriminate).
  specialize (ValStar _ HV HTy) as [v'' [Heq' HV']]; subst.
  simpl in *.
  assert (HCst': PCast v'' T = Some v') by (destruct T; easy).
  inversion HTy; subst.
  clear HCst HV HTy.
  generalize dependent T.
  generalize dependent t.
  generalize dependent T1.
  induction HV'; intros * HTy * HEq HNEq HCst.

  - destruct T; simpl in *; try discriminate.
    injection HEq; injection HCst; intros; subst. trivial.

  - destruct T; simpl in *; try discriminate.
    injection HEq; injection HCst; intros; subst. trivial.

  - destruct T0; simpl in *; try discriminate.
    injection HEq; injection HCst; intros; subst. trivial.

  - destruct T; simpl in *; try discriminate.
    injection HEq; injection HCst; intros; subst. trivial.

  - unfold tagOf.
    replace (typeOf MEmpty (PECast v PTStar)) with (Some T1)
      by (symmetry; eauto using typeOfCorrect').
    inversion HTy; subst.
    simpl.
    eapply IHHV'; clear IHHV'; eauto.
    subst. simpl in *.
    destruct T; trivial; discriminate.
Qed.


Lemma subsCast : forall var e T,
  lir.substitution var e (< T <= IRTStar > IREVar var) =
  < T <= IRTStar > e.
Proof.
  intros.
  destruct T; simpl;
  destruct (string_dec var var); easy.
Qed.


Lemma PCast2Star : forall {v v' T tg},
  PValue v ->
  MEmpty |= v : T ->
  PT2IRT T = Tag2Type tg ->
  PCast v PTStar = Some v' ->
  Pall2Lir MEmpty v' = IREBox tg (Pall2Lir MEmpty v).
Proof.
  intros * HV HTy HEq HCast.
  specialize (PT2IRTag _ _ HEq) as ?.
  assert (v' = PECast v PTStar).
  { induction HV; simpl in *;
  injection HCast; try congruence.
  exfalso.
  inversion HTy; subst; eauto. }
  subst; simpl.
  tagOf2T.
  destruct T; only 1: easy;
  inversion HEq; subst; trivial.
Qed.


Lemma PCast2NStar : forall {v v' tg1 T1 tg2 T2},
  PValue v ->
  PT2IRT T1 = Tag2Type tg1 ->
  PT2IRT T2 = Tag2Type tg2 ->
  MEmpty |= v : T1 ->
  PCast v T2 = Some v' ->
  tg1 = tg2.
Proof.
  intros * HV HEq1 HEq2 HTy HCst.
  destruct T1; only 1: (exfalso; eapply PT2IRTag in HEq1; easy);
  destruct T2; only 1: (exfalso; eapply PT2IRTag in HEq2; easy);
  inversion HEq1; inversion HEq2; subst; trivial;
  inversion HTy; subst; discriminate.
Qed.


Lemma castTags : forall v v' T1 T2 t,
  PValue v ->
  MEmpty |= v : T1 ->
  PCast v T2 = Some v' ->
  PT2IRT T1 = Tag2Type t ->
  PT2IRT T2 = Tag2Type t ->
  Pall2Lir MEmpty v = Pall2Lir MEmpty v'.
Proof.
  intros * HV HTy HCst HEq1 HEq2.
  induction HV; inversion HTy; subst; inversion HEq1; subst;
  destruct T2; try discriminate;
  simpl in HCst; try congruence;
  injection HCst; intros; subst; trivial.
Qed.


Lemma castStar : forall v v' T t,
  PValue v ->
  MEmpty |= v : T ->
  PCast v PTStar = Some v' ->
  PT2IRT T = Tag2Type t ->
  IREBox t (Pall2Lir MEmpty v) = Pall2Lir MEmpty v'.
Proof.
  intros * HV HTy HCst HEq.
  induction HV; inversion HTy; subst; inversion HEq; subst;
  simpl in HCst;
  injection HCst; intros; subst; trivial.
Qed.


Lemma castFStar : forall v v' T t,
  PValue v ->
  MEmpty |= v : PTStar ->
  PCast v T = Some v' ->
  PT2IRT T = Tag2Type t ->
  (Pall2Lir MEmpty v) = IREBox t (Pall2Lir MEmpty v').
Proof.
  intros * HV HTy HCst HEq.
  induction HV; inversion HTy; subst.
  simpl.
  tagOf2T.
  assert (PCast v T = Some v') by (destruct T; easy).
  destruct (PT2IRT T1) eqn:?.
  - replace t with t0 by eauto using PCast2NStar.
    f_equal.
    destruct HV; simpl;
    destruct T; try easy;
      try (simpl in H; injection H; intros; subst; trivial);
      inversion H1; subst; discriminate.
  - replace T1 with PTStar in * by (symmetry; auto using PTStarB).
    auto.
Qed.



Lemma SimPallLir : forall m e T m' e',
  Pmem_correct m ->
  MEmpty |= e : T ->
  m / e --> m' / e' ->
  multistep (MPall2Lir m) (Pall2Lir MEmpty e)
            (MPall2Lir m') (Pall2Lir MEmpty e').
Proof.
  intros * HM HTy HSt.
  generalize dependent T.
  induction HSt; intros * HTy;
  inversion HTy; subst;

  (* instantiate induction hipothesis *)
  try match goal with
    | [H: Pmem_correct ?m -> forall _, PTyping MEmpty ?E _ -> _,
       HM: Pmem_correct ?m,
       HTy: PTyping MEmpty ?E _ |- _] =>
      specialize (H HM _ HTy)
  end;
  try (simpl; eauto using step, multistep1, PValueValue, P2LfreshT,
              CongPlus1, CongPlus2; fail).

  - simpl. tagOf2T.
    destruct (PT2IRT T);
    eauto using CongGet1, CongUnbox.

  - simpl. tagOf2T.
    destruct (PT2IRT T);
    eauto using CongUnbox, CongGet2, CongBox, PValueValue.

  - simpl. tagOf2T.
    destruct (PT2IRT T0) eqn:?.
    + simpl.
      inversion H3; subst.
      eapply MStMStep.
      eapply StUnbox1; eauto using step, Value.
      unshelve erewrite (PqueryT2 _ _ _ _ _ eq_refl); trivial.
      eapply multistep1.
      erewrite (PCastBox);
      eauto using step, PValueValue, CastValue, PMCValue, PMCTy.
    + simpl.
      inversion H3; subst.
      replace T0 with PTStar in * by (destruct T0; easy).
      clear T0 Heqi.
      eapply MStMStep; eauto using step, Value.
      unshelve erewrite (PqueryT2 _ _ _ _ _ eq_refl); trivial.
      erewrite CastToItsType in H; eauto using PMCValue, PMCTy.
      injection H; intros; subst.
      constructor.

  - destruct (tagOf MEmpty e3); eauto using CongSet1.

  - destruct (tagOf MEmpty e3); eauto using CongSet2, CongBox, PValueValue.

  - simpl. tagOf2T.
    destruct (PT2IRT T0);
      eapply CongSet3; eauto using CongBox, PValueValue, Value.

 - eapply multistep1.
   eapply StSet.
   eauto using Value.

  - eapply multistep1.
    eapply StFun.
    fold Pall2Lir.
    unfold PfreshF in H.
    injection H; intros; subst.
    unfold freshF.
    rewrite sameFreeaux. trivial.

  - simpl. tagOf2T.
    destruct (PT2IRT T);
    eauto using CongUnbox, CongApp1.

  - simpl.
    tagOf2T.
    destruct (PT2IRT T);
      destruct (PT2IRT T1);
      eauto using CongUnbox, CongApp2, PValueValue, CongBox.

  - inversion H5; subst.
    destruct (queryF a (MPall2Lir m)) eqn:?.
    replace s with var in * by eauto using PqueryF2V.
    specialize (PqueryF2 m a var type body i HM H0 (eq_sym Heqp)).
    assert (MEmpty |= v' : type) by eauto using CastEqType.
    specialize (PMCTyF _ _ _ _ _ MEmpty H0 HM) as HTy'.
    intros; subst.
    simpl.
    erewrite tagOfT'; eauto.
    erewrite tagOfT'; eauto.
    erewrite tagOfT'; eauto using Psubst_typing.
    simpl.
    eapply CongCast.
    destruct (PT2IRT T0) eqn:?.

    + eapply MStMStep.
      * eapply StApp.
        ** eauto using Value, PValueValue.
        ** symmetry. eauto.
      * simpl. destruct (string_dec var var); try easy.
        clear e.
        rewrite subsCast.
        destruct (PT2IRT type) eqn:?.

        ** simpl.
           replace t0 with t in * by eauto using PCast2NStar.
           eapply MStMStep.
           *** eauto using step, PValueValue.
           *** erewrite Psubst.
               eapply multistep1.
               **** replace (Pall2Lir MEmpty v')
                       with (Pall2Lir MEmpty v) by eauto using castTags.
               eauto using step, PValueValue.
               **** eapply HTy'.
               **** eauto using CastEqType.

        ** simpl.
           replace type with PTStar in * by (symmetry; auto using PTStarB).
           erewrite castStar; eauto.
           erewrite Psubst.
           eapply multistep1.
           *** eauto using step, PValueValue,  CastValue, Value.
           *** eapply HTy'.
           *** trivial.

    + replace T0 with PTStar in * by (symmetry; auto using PTStarB).
      clear Heqi.
      eapply MStMStep.
      * eapply StApp.
        ** eauto using Value, PValueValue.
        ** symmetry. eauto.
      * simpl. destruct (string_dec var var); try easy.
        clear e.
        rewrite subsCast.
        destruct (PT2IRT type) eqn:?.

        ** simpl.
           erewrite Psubst.
           2: { eauto. }
           2: { eauto. }
           replace (Pall2Lir MEmpty v) with
                   (IREBox t (Pall2Lir MEmpty v')) by
                      (symmetry; eauto using castFStar).
           eapply MStMStep;
           eauto using step, MStMStep, multistep1, CastValue, PValueValue.

        ** simpl.
           replace type with PTStar in * by (symmetry; auto using PTStarB).
           replace v' with v.
           2:{ specialize (CastToItsType PTStar v H H7).
               congruence. }
           erewrite Psubst; eauto using multistep1, step, PValueValue.

  - simpl. tagOf2T. eauto using CongCast.

  - simpl. tagOf2T.
    destruct (PT2IRT T0) eqn:?; destruct (PT2IRT T1) eqn:?; simpl.
    + replace t0 with t in * by (symmetry; eauto using PCast2NStar).
      destruct (dec_Tag t t); try easy.
      erewrite castTags; eauto using multistep.
    + replace T1 with PTStar in * by (symmetry; eauto using PTStarB).
      erewrite PCastBox; eauto using multistep1, step, PValueValue,
                                     CastValue.
    + replace T0 with PTStar in * by (symmetry; eauto using PTStarB).
      erewrite <- PCast2Star; eauto using multistep.
    + replace T0 with PTStar in * by (symmetry; eauto using PTStarB).
      replace T1 with PTStar in * by (symmetry; eauto using PTStarB).
      specialize (CastToItsType _ _ H H6) as ?.
      replace v' with v by congruence.
      constructor.
Qed.



