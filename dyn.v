Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.

Require Import LIR.lir.
Require Import LIR.biglir.


Fixpoint dyn (e : IRE) : IRE :=
  match e with
  | IRENil => IREBox TgNil IRENil
  | IRENum n => IREBox TgInt (IRENum n)
  | IREPlus e1 e2 => IREBox TgInt (IREPlus (IREUnbox TgInt (dyn e1))
                                           (IREUnbox TgInt (dyn e2)))
  | IRECnst => IREBox TgTbl IRECnst
  | IREAddr a => IREBox TgTbl (IREAddr a)
  | IREGet e1 e2 => IREGet (IREUnbox TgTbl (dyn e1)) (dyn e2)
  | IRESet e1 e2 e3 => IRESet (IREUnbox TgTbl (dyn e1)) (dyn e2) (dyn e3)
  | IREVar var => IREVar var
  | IRELet var t exp body => IRELet var IRTStar (dyn exp) (dyn body)
  | IREFun var e => IREBox TgFun (IREFun var (dyn e))
  | IREFunApp e1 e2 => IREFunApp (IREUnbox TgFun (dyn e1)) (dyn e2)
  | IREBox _ e => dyn e
  | IREUnbox _ e => dyn e
  end.


Theorem dynIdempotent : forall e, dyn e = dyn (dyn e).
Proof. induction e; simpl; congruence. Qed.


Fixpoint dynGamma (Γ : IREnvironment) : IREnvironment :=
  match Γ with
  | MEmpty => MEmpty
  | MCons var T Γ' => MCons var IRTStar (dynGamma Γ')
  end.


Lemma TP2TGammaIn : forall Γ var T,
    In Γ var = Some T -> In (dynGamma Γ) var = Some IRTStar.
Proof.
  induction Γ; intros var T H; simpl in *; breakStrDec.
  - easy.
  - eauto.
Qed.


Theorem dynTyping : forall Γ e T,
    Γ |= e : T -> dynGamma Γ |= (dyn e) : IRTStar.
Proof.
  intros Γ e T Hty.
  induction Hty; eauto using IRTyping,TP2TGammaIn.
Qed.


Lemma dynValue : forall e, Value e -> Value (dyn e).
Proof.
  intros e HV. induction HV; simpl; auto using Value.
Qed.


Lemma dynSubst : forall var e1 e2,
    ([var := dyn e1](dyn e2)) = dyn ([var := e1]e2).
Proof.
  intros var e1 e2.
  induction e2;
  simpl; breakStrDec;
  simpl; congruence.
Qed.


Fixpoint dynMem (m : Mem) : Mem :=
  match m with
  | EmptyMem => EmptyMem
  | Update a n e m => Update a n (dyn e) (dynMem m)
  end.

Lemma dynMemEmpty : MEmpty = dynGamma MEmpty.
Proof. trivial. Qed.



Lemma dynMemCorrect : forall m, mem_correct m -> mem_correct (dynMem m).
Proof.
  unfold mem_correct.
  intros m H a n. specialize (H a n) as [? ?].
  induction m; split;
  auto using Value;
  simpl in *; breakIndexDec;
    try (apply IHm; easy).
  - auto using dynValue.
  - rewrite dynMemEmpty; eauto using dynTyping.
Qed.



Axiom DynIndex : forall e, ToIndex e = ToIndex (dyn e).

Lemma dynQuery : forall m a idx,
    dyn (query a idx m) = query a (dyn idx) (dynMem m).
Proof.
  intros. induction m; simpl; trivial.
  rewrite <- DynIndex.
  breakIndexDec; trivial.
Qed.


Lemma dynFreshAux : forall m, freshaux m = freshaux (dynMem m).
Proof.
  induction m; trivial; simpl; congruence.
Qed.


Lemma dynFresh : forall m free m',
   (free, m') = fresh m -> (free, dynMem m') = fresh (dynMem m).
Proof.
  induction m; intros free m' H; inversion H; subst; trivial.
  - rewrite dynFreshAux. trivial.
Qed.


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
