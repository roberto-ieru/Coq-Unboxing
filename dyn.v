(*
** Dynamization of LIR terms: Type erasure for Lir expressions
*)

Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.

Require Import LIR.maps.

Require Import LIR.lir.


(*
** 'dyn' transformation
*)
Fixpoint dyn (e : IRE) : IRE :=
  match e with
  | IRENil => IREBox TgNil IRENil
  | IRENum n => IREBox TgInt (IRENum n)
  | IREPlus e1 e2 => IREBox TgInt (IREPlus (IREUnbox TgInt (dyn e1))
                                           (IREUnbox TgInt (dyn e2)))
  | IRENew => IREBox TgTbl IRENew
  | IRETAddr a => IREBox TgTbl (IRETAddr a)
  | IREFAddr a => IREBox TgFun (IREFAddr a)
  | IREGet e1 e2 => IREGet (IREUnbox TgTbl (dyn e1)) (dyn e2)
  | IRESet e1 e2 e3 => IREBox TgNil (IRESet (IREUnbox TgTbl (dyn e1))
                                            (dyn e2)
                                            (dyn e3))
  | IREVar var => IREVar var
  | IRELet var t e body => IRELet var IRTStar (dyn e) (dyn body)
  | IREFun var exp => IREBox TgFun (IREFun var (dyn exp))
  | IREApp e1 e2 => IREApp (IREUnbox TgFun (dyn e1)) (dyn e2)
  | IREBox _ e => dyn e
  | IREUnbox _ e => dyn e
  end.


(* 'dyn' is idempotent *)
Theorem dynIdempotent : forall e, dyn e = dyn (dyn e).
Proof. induction e; simpl; congruence. Qed.


(*
** 'dyn' for environments: all variables have type '*'
*)
Fixpoint dynGamma (Γ : IREnvironment) : IREnvironment :=
  match Γ with
  | MEmpty => MEmpty
  | MCons var t Γ' => MCons var IRTStar (dynGamma Γ')
  end.


(* Correctness of dynGamma *)

Lemma TP2TGammaIn : forall Γ var T,
    In Γ var = Some T -> In (dynGamma Γ) var = Some IRTStar.
Proof.
  induction Γ; intros; breakStrDec; try easy; eauto.
Qed.


Lemma NTP2TGammaIn : forall Γ var,
    In Γ var = None -> In (dynGamma Γ) var = None.
Proof.
  intros. induction Γ; breakStrDec; subst; auto.
Qed.


(*
** 'dyn' preserves well-typeness
*)
Theorem dynTyping : forall Γ e T,
    Γ |= e : T -> dynGamma Γ |= (dyn e) : IRTStar.
Proof with apply IRTyUnbox; trivial.
  induction 1; eauto using IRTyping, TP2TGammaIn.
Qed.


(*
** 'dyn' preserves well-typeness in the empty environment
*)
Corollary dynTypingE : forall e,
    MEmpty |= e : IRTStar -> MEmpty |= dyn e : IRTStar.
Proof.
  replace MEmpty with (dynGamma MEmpty) by trivial.
  eauto using dynTyping.
Qed.


(*
** 'dyn' preserves "valueness".
*)
Theorem dynValue : forall e, Value e -> Value (dyn e).
Proof.
  induction 1; simpl; auto using Value.
Qed.


(*
** 'dyn' commutes with substitution
*)
Lemma dynSubst : forall var e1 e2,
    ([var := dyn e1](dyn e2)) = dyn ([var := e1]e2).
Proof.
  induction e2;
  simpl; breakStrDec;
  simpl; congruence.
Qed.


(*
** Lift 'dyn' to memories
*)
Fixpoint dynMem (m : Mem) : Mem :=
  match m with
  | EmptyMem => EmptyMem
  | UpdateT a n (EV e ve) m =>
      UpdateT a n (EV (dyn e) (dynValue e ve)) (dynMem m)
  | UpdateF a v b m => UpdateF a v (dyn b) (dynMem m)
  end.


(*
** 'dynMem' preserves memory correctness
*)
Lemma dynMemCorrect : forall m, mem_correct m -> mem_correct (dynMem m).
Proof.
  induction 1;
  try match goal with
  [V: ExpValue |- _] => destruct V
  end; eauto using mem_correct, dynTypingE.
  constructor; eauto.
  replace (var |=> IRTStar; MEmpty) with
           (dynGamma (var |=> IRTStar; MEmpty)) by trivial.
  eauto using dynTyping.
Qed.


(* 'dyn' preserves indices *)
Lemma DynIndex : forall e, ToIndex e = ToIndex (dyn e).
Proof.
  induction e; eauto.
Qed.


(*
** Two values have equal indices iff they are equal up to type erasure.
*)
Lemma DynIndexEq : forall e1 e2,
    Value e1 ->
    Value e2 ->
    (ToIndex e1 = ToIndex e2 <-> dyn e1 = dyn e2).
Proof.
  intros * HV1 HV2. split.
  - induction e1; intros; induction e2; try easy; eauto using valBoxVal;
    simpl in *; congruence.
  - rewrite DynIndex. rewrite (DynIndex e2). congruence.
Qed.


(*
** For values with ground types, 'dyn' means boxing them.
*)
Lemma ValueTag : forall e tg,
    Value e -> MEmpty |= e : Tag2Type tg -> dyn e = IREBox tg e.
Proof.
  destruct tg; inversion 1; inversion 1; trivial.
Qed.


(*
** For values with type '*', 'dyn' does nothing.
*)
Lemma ValueStar : forall e,
    Value e -> MEmpty |= e : IRTStar -> e = dyn e.
Proof.
  induction 1; inversion 1; subst.
  simpl. erewrite ValueTag; trivial.
Qed.


