(*
** Translation of λ-Pallene to LIR.
*)

Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.

Require Import LIR.maps.

Require Import LIR.lir.
Require Import LIR.pallene.


(*
** Convert a λ-Pallene type to its corresponding LIR type
*)
Definition PT2IRT (t : PType) : IRType :=
  match t with
  | PTStar => IRTStar
  | PTNil => Tag2Type TgNil
  | PTInt => Tag2Type TgInt
  | PTArr _ => Tag2Type TgTbl
  | PTFun _ _ =>  Tag2Type TgFun
  end.


(*
** Convert a λ-Pallene environment to a LIR environment
*)
Fixpoint TP2TGamma (Γ : Map PType) : IREnvironment :=
  match Γ with
  | MEmpty => MEmpty
  | MCons var T Γ' => MCons var (PT2IRT T) (TP2TGamma Γ')
  end.


(*
** The conversion of an environment is the conversion of its types.
*)
Lemma TP2TGammaIn : forall Γ var T,
    In Γ var = Some T -> In (TP2TGamma Γ) var = Some (PT2IRT T).
Proof.
  induction Γ; intros var T H; breakStrDec;
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


(*
** Cast and substitution commute.
*)
Lemma SubstCast : forall var e1 e2 T T',
  [var := e1] (<T <= T'> e2) = (<T <= T'> [var := e1] e2).
Proof.
  intros.
  destruct T; destruct T'; simpl; trivial.
  destruct (dec_Tag t t0); subst; trivial.
Qed.


(*
** Context rules for casts
*)
Lemma CastStep : forall t1 t2 e m e' m',
  m / e --> m' / e' ->
  m / (<t1 <= t2> e) --> m' / (<t1 <= t2> e').
Proof.
  intros * HSt.
  unfold Cast.
  destruct t1; destruct t2; eauto using step.
  destruct (dec_Tag t t0); eauto using step.
Qed.

Lemma CastStepF : forall t1 t2 e m,
  m / e --> fail ->
  m / (<t1 <= t2> e) --> fail.
Proof.
  intros * HSt.
  unfold Cast.
  destruct t1; destruct t2; eauto using stepF.
  destruct (dec_Tag t t0); eauto using stepF.
Qed.

Lemma CongCast : forall t1 t2 e m e' m',
  m / e -->* m' / e' ->
  m / (<t1 <= t2> e) -->* m' / (<t1 <= t2> e').
Proof.
  intros * HSt.
  induction HSt; eauto using multistep, CastStep.
Qed.



(*
** Get the LIR type of a λ-Pallene expression, if correctly typed;
** otherwise assume nil. (The expression will always be correctly
** typed.)
*)
Definition typeof Γ e : IRType :=
  match PtypeOf Γ e with
  | Some T => PT2IRT T
  | None => IRTNil
  end.


(*
** typeof is correct.
*)
Lemma GtypeOfT : forall Γ e T, PtypeOf Γ e = Some T -> typeof Γ e = PT2IRT T.
Proof. intros. unfold typeof. rewrite H. trivial. Qed.

Lemma GtypeOfT' : forall Γ e T, Γ |p= e : T -> typeof Γ e = PT2IRT T.
Proof. eauto using GtypeOfT, typeOfCorrect'. Qed.

Lemma tagStar2type : forall Γ e,
    typeof Γ e = IRTStar -> PtypeOf Γ e = Some PTStar.
Proof.
  unfold typeof.
  intros Γ e H.
  destruct (PtypeOf Γ e) eqn:?; try easy.
  destruct p; easy.
Qed.


(*
** Translation (compilation) of Pallene programs to LIR
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
         <typeof Γ e <= IRTStar>
           (IREGet (Pall2Lir Γ e1) (<IRTStar <= (Tag2Type TgInt)> (Pall2Lir Γ e2)))
  | PESet e1 e2 e3 =>
         (IRESet (Pall2Lir Γ e1)
                 (<IRTStar <= Tag2Type TgInt> (Pall2Lir Γ e2))
                 (<IRTStar <= typeof Γ e3> Pall2Lir Γ e3))
  | PEVar var => IREVar var
  | PEFun var T body _  => let Γ' := (var |=> T; Γ) in
        IREFun var
          (IRELet var (PT2IRT T) (<PT2IRT T <= IRTStar> (IREVar var))
                     (<IRTStar <= typeof Γ' body> (Pall2Lir Γ' body)))
  | PELet var T init body =>
      IRELet var (PT2IRT T) (Pall2Lir Γ init) (Pall2Lir (var |=> T; Γ) body)
  | PEApp e1 e2 => <typeof Γ e <= IRTStar>
         (IREApp (Pall2Lir Γ e1)
                  (<IRTStar <= (typeof Γ e2)> Pall2Lir Γ e2))
  | PECast e1 t => <PT2IRT t <= typeof Γ e1> (Pall2Lir Γ e1)
  end.


Lemma invertCall : forall {Γ e1 e2 T1 T2},
  PtypeOf Γ e1 = Some (PTFun T1 T2) ->
  PtypeOf Γ e2 = Some T1 ->
  PtypeOf Γ (PEApp e1 e2) = Some T2.
Proof.
  intros Γ e1 r2 T1 T2 H1 H2.
  simpl. rewrite H1. rewrite H2.
  destruct (dec_TP T1 T1); congruence.
Qed.


Lemma invertFun : forall {Γ e1 e2 T1 T2},
    PtypeOf Γ e1 = Some (PTFun T1 T2) ->
    typeof Γ (PEApp e1 e2) = IRTStar ->
    T2 = PTStar.
Proof.
  intros Γ e1 e2 T1 T2 H1 H2.
  unfold typeof in H2.
  destruct (PtypeOf Γ (PEApp e1 e2)) eqn:?; try easy.
  apply typeOfCorrect'' in H1.
  apply typeOfCorrect'' in Heqo.
  destruct p; try easy.
  inversion Heqo; subst.
  apply (PTypeUnique _ _ _ _ H1) in H4.
  congruence.
Qed.


Ltac breakTagOf :=
  match goal with
  [H: PtypeOf _ ?E = Some ?T |- context C [typeof _ ?E] ] =>
    apply GtypeOfT in H; rewrite H; destruct (PT2IRT T) eqn:?;
    eauto using IRTyping
  end.


Lemma PT2IRTag : forall {tg T},
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

Ltac T2Star :=
  repeat match goal with
  |[H: PT2IRT _ = IRTStar |- _] => rewrite (PTStarB _ H) in *
  end.


Lemma typeStar : forall {Γ e T},
    PtypeOf Γ e = Some T -> typeof Γ e = IRTStar -> T = PTStar.
Proof.
  intros Γ e T HT Htg.
  unfold typeof in Htg.
  rewrite HT in Htg.
  auto using PTStarB.
Qed.


Lemma typeTag : forall {Γ e T tg},
    PtypeOf Γ e = Some T ->
    typeof Γ e = Tag2Type tg ->
    PT2IRT T = Tag2Type tg.
Proof.
  intros Γ e T tg HT Htg.
  unfold typeof in Htg.
  rewrite HT in Htg.
  auto.
Qed.


(*
** Compiling well-typed λ-Pallene results in well-typed LIR.
*)
Theorem Pall2LirWellTyped : forall Γ Γ' (e : PE) T T',
    Γ |p= e : T ->
    TP2TGamma Γ = Γ' ->
    PT2IRT T = T' ->
    Γ' |= (Pall2Lir Γ e) : T'.
Proof with eauto using IRTyping.
  intros * H Eq1 Eq2. subst.
  induction H; simpl in *;
  eauto using IRTyping, TP2TGammaIn;
  repeat match goal with
  | [H: PTyping ?G ?E ?T |- _] =>
      apply typeOfCorrect in H
  end.

  - (* Get *)
    unfold typeof. simpl. rewrite H. rewrite H0.
    destruct (PT2IRT T) eqn:?; simpl; eauto using IRTyping.

  - (* Set *)
    unfold typeof. rewrite H1.
    destruct (PT2IRT T) eqn:?; simpl; eauto using IRTyping.

  - (* Fun *)
    apply IRTyFun. eapply IRTyLet.
    + destruct (typeof (var |=> Tvar; Γ)) eqn:?; subst.
      * apply IRTyBox.
        eapply inclusion_typing.
        ** unfold typeof in Heqi. rewrite H in Heqi.
           rewrite <- Heqi. eauto.
        ** eapply inclusion_shadow'.
      *  unfold typeof in Heqi. rewrite H in Heqi.
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
    destruct (typeof Γ (PEApp e1 e2)) eqn:?.
    + specialize (invertCall H H0) as H2.
      unfold typeof in Heqi. rewrite H2 in Heqi.
      simpl.
      apply IRTyUnbox; trivial.
      eapply IRTyApp; eauto.
      destruct (typeof Γ e2) eqn:?.
      * apply IRTyBox.
        specialize (typeTag H0 Heqi0) as HTt.
        rewrite <- HTt. trivial.
      * replace T1 with PTStar in * by (symmetry; eauto using typeStar).
        trivial.
    + unfold Cast.
      specialize (invertFun H Heqi); intros; subst; simpl.
      destruct (typeof Γ e2) eqn:?.
      * eapply IRTyApp; eauto using IRTyping.
        eapply IRTyBox.
        replace (Tag2Type t) with (PT2IRT T1); trivial.
        eauto using typeTag.
      * eapply IRTyApp; eauto using IRTyping.
        replace T1 with PTStar in * by (symmetry; eauto using typeStar).
        trivial.

  - (* Cast *)
    unfold Cast.
    destruct (PT2IRT T2) eqn:?;
    unfold typeof;
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
  Γ1 |p= e1 : T ->
  Γ2 |p= e2 : T ->
  PtypeOf Γ1 e1 = PtypeOf Γ2 e2.
Proof.
  intros * HTy1 HTy2.
  erewrite typeOfCorrect'; eauto.
  erewrite typeOfCorrect'; eauto.
Qed.

Lemma GtypeOfEq : forall Γ1 e1 Γ2 e2 T,
  Γ1 |p= e1 : T ->
  Γ2 |p= e2 : T ->
  typeof Γ1 e1 = typeof Γ2 e2.
Proof.
  intros * HTy1 HTy2.
  unfold typeof.
  erewrite typeOfEq; eauto.
Qed.


Ltac GtypeOf2T :=
  repeat   (* replace GtypeOfs with theirs types *)
      (erewrite GtypeOfT';
       eauto 4 using PTyping, PinclusionType, inclusion_update,
                   Psubst_typing, inclusion_shadow, inclusion_permute,
                   PexpPreservation).


Lemma Pall2LirEEnv : forall Γ Γ' e T,
  Γ |p= e : T ->
  inclusion Γ Γ' ->
  Pall2Lir Γ e = Pall2Lir Γ' e.
Proof.
  intros * HTy HIn.
  generalize dependent Γ'.
  induction HTy; intros; subst; trivial;
  simpl;   (* expose GtypeOfs *)
  GtypeOf2T;
  repeat match goal with   (* do the rewrites from the hypotheses *)
  | [ H: _ -> _ -> _ = _ |- _] =>
     erewrite H; eauto using inclusion_update; clear H
  end.
Qed.


(*
** Compilation to LIR and substitution commute
*)
Lemma Psubst : forall Γ var Tvar e1 e2 te,
  (var |=> Tvar; Γ) |p= e2 : te ->
  MEmpty |p= e1 : Tvar ->
  Pall2Lir Γ ([var := e1]p e2) =
    [var := (Pall2Lir MEmpty e1)] (Pall2Lir (var |=> Tvar; Γ) e2).
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

  - GtypeOf2T.
    destruct (PT2IRT te); trivial.

  - simpl.
    GtypeOf2T.
    destruct (PT2IRT T); trivial.

  - breakStrDec.
    symmetry. eauto using Pall2LirEEnv, PinclusionType, inclusion_empty.

  - simpl.
    GtypeOf2T.
    destruct (PT2IRT te).
    + destruct t; simpl; destruct (PT2IRT T1); trivial.
    + simpl.
      destruct (PT2IRT T1); trivial.

   - breakStrDec; simpl.
     + GtypeOf2T.
       replace (Pall2Lir (s |=> p; (s |=> Tvar; Γ)) e2)
         with (Pall2Lir (s |=> p; Γ) e2); trivial.
       eauto using Pall2LirEEnv,  inclusion_shadow,
         PinclusionType, inclusion_shadow'.
     + destruct (PT2IRT p); subst.
       * GtypeOf2T.
         destruct t;
         simpl;
            f_equal;
            f_equal;
            breakStrDec;
           destruct (PT2IRT p0); simpl;
               f_equal;
                    replace (Pall2Lir (s |=> p; (var |=> Tvar; Γ)) e2)
                      with  (Pall2Lir (var |=> Tvar; (s |=> p; Γ)) e2);
                    eauto using Pall2LirEEnv, inclusion_permute,
                                   PinclusionType.
      * simpl.
        f_equal.
        f_equal.
        ** breakStrDec.
        ** GtypeOf2T.
           destruct (PT2IRT p0); simpl;
           f_equal;
           replace (Pall2Lir (s |=> p; (var |=> Tvar; Γ)) e2)
             with  (Pall2Lir (var |=> Tvar; (s |=> p; Γ)) e2);
           eauto using Pall2LirEEnv, inclusion_permute, PinclusionType.

  - destruct (string_dec var s) eqn:HVeq; subst.
    + simpl. f_equal;
       eauto using Pall2LirEEnv,  inclusion_shadow,
         PinclusionType, inclusion_shadow'.
    + simpl. f_equal; eauto.
      replace (Pall2Lir (s |=> p; (var |=> Tvar; Γ)) e2_2)
      with (Pall2Lir (var |=> Tvar; (s |=> p; Γ)) e2_2) by
           eauto using Pall2LirEEnv, inclusion_permute, PinclusionType.
      eauto using Pall2LirEEnv, inclusion_permute, PinclusionType.

  - simpl. GtypeOf2T.
    destruct (PT2IRT te); subst; destruct (PT2IRT T1); subst; simpl;
    try destruct (dec_Tag t t0); subst; eauto.
Qed.


(*
** The translation of a value gives a value
*)
Theorem PValueValue : forall e, PValue e -> Value (Pall2Lir MEmpty e).
Proof.
  intros * PV.
  induction PV; simpl; eauto using Value.
  destruct (typeof MEmpty v); eauto using Value.
Defined.


(*
** Lifting compilation to memories
*)
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


(*
** Lifting preserves correctness
*)
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
  MEmpty |p= e : T ->
  typeof MEmpty e = PT2IRT T.
Proof.
  unfold typeof. intros * HTy.
  replace (PtypeOf MEmpty e) with (Some T); trivial.
  symmetry; eauto using typeOfCorrect'.
Qed.


Lemma PreserveTagOf' : forall m e T m' e',
  Pmem_correct m ->
  m / e -p-> m' / e' ->
  MEmpty |p= e : T ->
  typeof MEmpty e' = PT2IRT T.
Proof.
  intros * HM HSt HTy.
  eauto using TagFromType, PexpPreservation.
Qed.


Lemma PreserveTagOf : forall m e t m' e',
  Pmem_correct m ->
  MEmpty |p= e : t ->
  m / e -p-> m' / e' ->
  typeof MEmpty e = typeof MEmpty e'.
Proof.
  unfold typeof. intros * HM HTy Hst.
  replace (PtypeOf MEmpty e') with (PtypeOf MEmpty e)
        by eauto using pstep, PexpPreservTypeOf.
  trivial.
Qed.


Opaque Index_dec.

Lemma PqueryT2 : forall {m a idx v},
  Pmem_correct m ->
  PqueryT a idx m = v ->
  queryT a (IREBox TgInt (IRENum idx)) (MPall2Lir m) = Pall2Lir MEmpty v.
Proof.
  intros * HMC HQr.
  generalize dependent v.
  induction HMC; intros * HEq.
  - simpl in HEq. subst. trivial.
  - destruct v.
    subst. simpl.
    breakIndexDec; subst; auto.
  - simpl. inversion HMC; subst; auto.
Qed.


Lemma PqueryF2 : forall {m a var T body body'},
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


Lemma PqueryF2V : forall {m a var var' T body body'},
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


Lemma PQueryQuery : forall {s type body a m},
  Pmem_correct m ->
  (s, type, body) = PqueryF a m ->
  (s, IRELet s (PT2IRT type) (< PT2IRT type <= IRTStar > IREVar s)
         (Pall2Lir (s |=> type; MEmpty) body)) = queryF a (MPall2Lir m).
Proof.
  intros * HM HEq.
  destruct (queryF a (MPall2Lir m)) eqn:HEq1.
  symmetry in HEq1.
  specialize (PqueryF2V HM HEq HEq1) as ?; subst.
  specialize (PqueryF2 HM HEq HEq1) as ?; subst.
  trivial.
Qed.


Lemma PCastBox : forall v T v' t,
  MEmpty |p= v : PTStar ->
  PValue v ->
  vcast v T = Some v' ->
  PT2IRT T = Tag2Type t ->
  Pall2Lir MEmpty v = IREBox t (Pall2Lir MEmpty v').
Proof.
  intros * HTy HV HCst Heq.
  assert (T <> PTStar) by (intros contra; subst; discriminate).
  specialize (ValStar v) as [v'' [Heq' HV']]; trivial; subst.
  simpl in *.
  assert (HCst': vcast v'' T = Some v') by (destruct T; easy).
  inversion HTy; subst.
  clear HCst HV HTy.
  generalize dependent T.
  generalize dependent t.
  generalize dependent T1.
  induction HV'; intros * HTy * HEq HNEq HCst;
  try (
    match goal with
    [ T : PType |- _] =>
      destruct T; simpl in *; try discriminate;
      injection HEq; injection HCst; intros; subst; trivial; fail
    end).

  unfold typeof.
  replace (PtypeOf MEmpty (PECast v PTStar)) with (Some T1)
    by (symmetry; eauto using typeOfCorrect').
  inversion HTy; subst.
  simpl.
  eapply IHHV'; clear IHHV'; eauto.
  subst. simpl in *.
  destruct T; trivial; discriminate.
Qed.


Lemma subsCast : forall var e T,
  [var := e] (< T <= IRTStar > IREVar var) =
  < T <= IRTStar > e.
Proof.
  intros.
  destruct T; breakStrDec.
Qed.


Lemma PCast2Star : forall {v v' T tg},
  PValue v ->
  MEmpty |p= v : T ->
  PT2IRT T = Tag2Type tg ->
  vcast v PTStar = Some v' ->
  Pall2Lir MEmpty v' = IREBox tg (Pall2Lir MEmpty v).
Proof.
  intros * HV HTy HEq HCast.
  specialize (PT2IRTag HEq) as ?.
  assert (v' = PECast v PTStar).
  { induction HV; simpl in *;
  injection HCast; try congruence.
  exfalso.
  inversion HTy; subst; eauto. }
  subst; simpl.
  GtypeOf2T.
  destruct T; only 1: easy;
  inversion HEq; subst; trivial.
Qed.


Lemma PCast2NStar : forall {v v' tg1 T1 tg2 T2},
  PValue v ->
  PT2IRT T1 = Tag2Type tg1 ->
  PT2IRT T2 = Tag2Type tg2 ->
  MEmpty |p= v : T1 ->
  vcast v T2 = Some v' ->
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
  MEmpty |p= v : T1 ->
  vcast v T2 = Some v' ->
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
  MEmpty |p= v : T ->
  vcast v PTStar = Some v' ->
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
  MEmpty |p= v : PTStar ->
  vcast v T = Some v' ->
  PT2IRT T = Tag2Type t ->
  (Pall2Lir MEmpty v) = IREBox t (Pall2Lir MEmpty v').
Proof.
  intros * HV HTy HCst HEq.
  induction HV; inversion HTy; subst.
  simpl.
  GtypeOf2T.
  assert (vcast v T = Some v') by (destruct T; easy).
  destruct (PT2IRT T1) eqn:?.
  - replace t with t0 by eauto using PCast2NStar.
    f_equal.
    destruct HV; simpl;
    destruct T; try easy;
      try (simpl in H; injection H; intros; subst; trivial);
      inversion H1; subst; discriminate.
  - T2Star.
    auto.
Qed.


(*
** Simulation λ-Pallene - LIR: Success cases.
**
** If a well-typed λ-Pallene term e reduces in one step to e',
** its translation to LIR reduces in zero or more steps to
** the translation of e'.
*)
Theorem SimPallLir : forall m e T m' e',
  Pmem_correct m ->
  MEmpty |p= e : T ->
  m / e -p-> m' / e' ->
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
  simpl;

  try (GtypeOf2T;
       simpl; eauto using step, multistep1, PValueValue, P2LfreshT,
              CongPlus1, CongPlus2, CongCast, CongGet1, CongUnbox,
              CongGet1, CongGet2, CongBox, CongLet; fail).

  - inversion H2; subst.
    erewrite <- PqueryT2; eauto.
    GtypeOf2T.
    2:{ eauto using PMCTy. }
    eauto using CongCast, multistep1, step, Value.

  - destruct (typeof MEmpty e3); eauto using CongSet1.

  - destruct (typeof MEmpty e3); eauto using CongSet2, CongBox, PValueValue.

  - GtypeOf2T.
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

  - (* Let *)
    eapply multistep1.
    erewrite Psubst; eauto using step, PValueValue.

  - GtypeOf2T.
    destruct (PT2IRT T);
    eauto using CongUnbox, CongApp1.

  - GtypeOf2T.
    destruct (PT2IRT T);
      destruct (PT2IRT T1);
      eauto using CongUnbox, CongApp2, PValueValue, CongBox.

  - GtypeOf2T. 
    2:{ eapply PTyLet.
        - eauto using PTyCast.
        - eapply PMCTyF; eauto. }
    inversion H4; subst.
    simpl.
    eapply CongCast.
    destruct (PT2IRT T0) eqn:?.
    + eapply MStMStep.
      * eapply StApp.
        ** eauto using PValueValue, Value.
        ** eapply PQueryQuery; eauto.
      * eapply MStMStep.
        ** eapply StLet; eauto using PValueValue, Value.
        ** simpl. destruct (string_dec var var); try easy.
           rewrite SubstCast. simpl.
           destruct (string_dec var var); try easy.
           simpl.
           destruct (PT2IRT type) eqn:?; simpl.
           *** destruct (dec_Tag t0 t) eqn:?; subst; simpl.
               ++ eapply multistep1. eauto using step, PValueValue.
               ++ eapply MStRefl.
           *** eapply MStRefl.

    + eapply MStMStep.
      * eapply StApp.
        ** eauto using PValueValue, Value.
        ** eapply PQueryQuery; eauto.
      * eapply MStMStep.
        ** eapply StLet; eauto using PValueValue, Value.
        ** simpl. destruct (string_dec var var); try easy.
           rewrite SubstCast. simpl.
           destruct (string_dec var var); try easy.
           simpl.
           eapply MStRefl.

  - GtypeOf2T.
    destruct (PT2IRT T0) eqn:?; destruct (PT2IRT T1) eqn:?; simpl;
    T2Star.
    + replace t0 with t in * by (symmetry; eauto using PCast2NStar).
      destruct (dec_Tag t t); try easy.
      erewrite castTags; eauto using multistep.
    + erewrite PCastBox; eauto using multistep1, step, PValueValue,
                                     CastValue.
    + erewrite <- PCast2Star; eauto using multistep.
    + rewrite CastToItsType in H1; trivial.
      replace v' with v by congruence.
      constructor.
Qed.



(*
** Simulation for Fails
*)

(*
** A cast to a type IR-equivalent to its onw type never fails.
*)
Lemma CastToItsIRType : forall v T T',
  vcast v T' = None ->
  MEmpty |p= v : T ->
  PValue v ->
  PT2IRT T = PT2IRT T'->
  False.
Proof.
  intros * HEq HTy HV.
  inversion HV; subst; inversion HTy; subst;
  destruct T' eqn:?; easy.
Qed.


Lemma CastToStar': forall v, vcast v PTStar = None -> False.
Proof.
  intros.
  specialize (CastToStar v) as [? ?].
  congruence.
Qed.


Ltac CastToStarNone :=
  try match goal with
  |[H: vcast _ PTStar = None |- _] =>
 exfalso; apply (CastToStar' _ H)
end.


(*
** Main lemma for fail simulation: A failed cast in Pallene will
** fail when translated to LIR.
*)
Lemma CastFail : forall {v} m {T T'},
  PValue v ->
  MEmpty |p= v : T ->
  vcast v T' = None ->
  (MPall2Lir m) / (< PT2IRT T' <= PT2IRT T > Pall2Lir MEmpty v) --> fail.
Proof.
  intros * HV HTy HC.
  induction HV; inversion HTy; subst;
  destruct T'; simpl in HC;
   (* easy cases *)
      (* impossible cases (vcast could not fail) *)
      try discriminate;
      (* cases that actually fail *)
      try (eapply StUnboxF; try easy; eauto using Value; fail);
   (* not so easy cases *)
   destruct T1; simpl; GtypeOf2T; simpl;
      (* specialize induction hypothesis *)
      try (specialize IHHV; simpl in IHHV; eauto);
      (* cases that actually fail *)
      try (eapply StUnboxF; auto using stepF, PValueValue; easy);
      (* impossible cases (vcast could not fail) *)
      try (exfalso; eauto using CastToItsIRType; fail).
 Qed.


(*
** 'CastFail' when original type is *
*)
Lemma CastFailStar : forall v m t T,
  PValue v ->
  MEmpty |p= v : PTStar ->
  vcast v T = None ->
  PT2IRT T = Tag2Type t ->
  (MPall2Lir m) /  (IREUnbox t (Pall2Lir MEmpty v)) --> fail.
Proof.
  intros * HV HTy HCst Heq.
  specialize (CastFail m HV HTy HCst) as ?.
  simpl in H. unfold Cast in H. rewrite Heq in H.
  trivial.
Qed.


(*
** Similar to 'CastFail', but pass through * when going from T to T'
*)
Lemma DoubleCastFail : forall v m T T',
  vcast v T' = None ->
  PValue v ->
  MEmpty |p= v : T  ->
  (MPall2Lir m) /
    (<PT2IRT T' <= IRTStar> (<IRTStar <= PT2IRT T> Pall2Lir MEmpty v)) --> fail.
Proof.
  intros * HCst HV HTy.
  destruct (PT2IRT T') eqn:?; T2Star.
  * destruct (PT2IRT T) eqn:?; simpl; T2Star.
    ** eapply StUnboxF; eauto using PValueValue.
       intros ?. subst.
       eapply CastToItsIRType; eauto. congruence.
    ** specialize (CastFail m HV HTy HCst) as ?.
       destruct (PT2IRT T'); inversion Heqi; subst; trivial.
  * CastToStarNone.
Qed.




Lemma WCast : forall t v,
      (match t with | Tag2Type t => IREBox t v | IRTStar => v end) =
      Cast IRTStar t v.
Proof. trivial. Qed.


Lemma CanonQuery : forall m a idx,
  Pmem_correct m ->
    exists (o : IRE) (t : Tag),
         Pall2Lir MEmpty (PqueryT a idx m) = IREBox t o /\ Value o.
Proof.
  intros * HM.
  specialize (PMCTy m a idx MEmpty HM) as ?.
  specialize (PMCValue m a idx) as ?.
  remember (PqueryT a idx m) as v.
  assert (MEmpty |= (Pall2Lir MEmpty v) : IRTStar)
    by eauto using Pall2LirWellTyped.
  assert (Value (Pall2Lir MEmpty v)) by eauto using PValueValue.
  specialize (valbox MEmpty (Pall2Lir MEmpty v) H1 H2)
     as [? [? [? [? ?]]]].
  eexists; eexists; eauto.
Qed.


(*
** Fail simulation: If the evaluation of a well-typed
** λ-Pallene term e fails in one step, the evaluation of its
** translation to LIR fail in zero or more steps.
*)
Theorem SimPallLirF : forall m e T,
  Pmem_correct m ->
  MEmpty |p= e : T ->
  m / e -p-> fail ->
  multistepF (MPall2Lir m) (Pall2Lir MEmpty e).
Proof.
  intros * HM HTy HSt.
  generalize dependent T.
  induction HSt; intros * HTy;
  inversion HTy; subst;

  (* instantiate induction hipothesis *)
  try match goal with
    | [H: Pmem_correct ?m -> forall _, PTyping MEmpty ?E _ -> _,
       HM: Pmem_correct ?m,
       HTy: PTyping MEmpty ?E _ |- _] => specialize (H HM _ HTy)
    end;
    try (inversion IHHSt; subst;
         eauto 12 using multistepF, stepF, PValueValue, Value,
           CongCast, CastStepF,
           CongPlus1, CongPlus2, CongGet1, CongGet2, CongBox,
           CongSet1, CongSet2, CongSet3, CongApp1, CongApp2, CongLet;
         fail);
     simpl; GtypeOf2T;
       eauto using multistep, multistepF, CastFail.

Qed.


