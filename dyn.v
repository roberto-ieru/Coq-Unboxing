Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.

Require Import LIR.lir.


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
  | IREFun var t exp => IREBox TgFun (IREFun var IRTStar (dyn exp))
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
Proof with apply IRTyUnbox; trivial.
  intros Γ e T Hty.
  induction Hty; simpl; eauto using IRTyping, TP2TGammaIn.
  - apply IRTyBox. apply IRTyPlus...
  - apply IRTyGet; trivial...
  - apply IRTySet; trivial...
  - eapply IRTyFunApp; eauto...
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


