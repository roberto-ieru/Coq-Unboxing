Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.

Require Import LIR.lir.


Inductive PType : Set :=
| PTStar : PType | PTNil : PType | PTInt : PType
| TParr : PType -> PType | TPfun : PType -> PType -> PType
.


Fixpoint TPeq (t1 t2 : PType) : bool :=
  match t1, t2 with
  | PTStar, PTStar => true
  | PTNil, PTNil => true
  | PTInt, PTInt => true
  | TParr t1', TParr t2' => TPeq t1' t2'
  | TPfun t1' t1'', TPfun t2' t2'' => TPeq t1' t2' && TPeq t1'' t2''
  | _, _ => false
  end.


Lemma dec_TP : forall (t1 t2 : PType), TPeq t1 t2 = true <-> t1 = t2.
Proof.
  split.
  - generalize dependent t2.
    induction t1; intros t2 H; destruct t2 eqn:?; try easy.
    + f_equal. auto.
    + simpl in H.  apply andb_prop in H.
      destruct H. f_equal; auto.
  - intros H; subst. induction t2; trivial.
    simpl. auto using andb_true_intro.
Qed.


Lemma TPeqRefl : forall t, TPeq t t = true.
Proof. intros t. apply dec_TP. trivial. Qed.


Definition Environment := Map PType.

Inductive PE : Set :=
| PENil : PE
| PENum : nat -> PE
| PEPlus : PE -> PE -> PE
| PENew : PType -> PE
| PEGet : PE -> PE -> PE
| PESet : PE -> PE -> PE -> PE
| PEVar : string -> PE
| PEApp :  PE -> PE -> PE
| PEFun : string -> PType -> PE -> PE
| PECast : PE -> PType -> PE
.


Reserved Notation "Γ '|=' e ':' t"  (at level 40, no associativity,
                                     e at next level).

Inductive PTyping : Environment -> PE -> PType -> Prop :=
| PTyNil : forall Γ, Γ |= PENil : PTNil
| PTyInt : forall Γ n, Γ |= PENum n : PTInt
| PTyVal : forall Γ var T,
    In Γ var = Some T ->
    Γ |= PEVar var : T
| PTyPlus : forall Γ e1 e2,
    Γ |= e1 : PTInt ->
    Γ |= e2 : PTInt ->
    Γ |= PEPlus e1 e2 : PTInt
| PTyNew : forall Γ T, Γ |= PENew T : TParr T
| PTyGet : forall Γ e1 T e2,
    Γ |= e1 : TParr T ->
    Γ |= e2 : PTInt ->
    Γ |= PEGet e1 e2 : T
| PTySet : forall Γ e1 T e2 e3,
    Γ |= e1 : TParr T ->
    Γ |= e2 : PTInt ->
    Γ |= e3 : T ->
    Γ |= PESet e1 e2 e3 : PTNil
| PTyFun : forall Γ var Tvar body Tbody,
    var |=> Tvar; Γ |= body : Tbody ->
    Γ |= PEFun var Tvar body : TPfun Tvar Tbody
| PTyApp : forall Γ e1 e2 T1 T2,
    Γ |= e1 : TPfun T1 T2 ->
    Γ |= e2 : T1 ->
    Γ |= PEApp e1 e2 : T2
| PTyCast : forall Γ e T1 T2,
    Γ |= e : T1 ->
    Γ |= PECast e T2 : T2

where "Γ '|=' e ':' t" := (PTyping Γ e t)
.


Fixpoint typeOf Γ e : option PType :=
  match e with
  | PENil => Some PTNil
  | PENum _ => Some PTInt
  | PEPlus e1 e2 =>
    match (typeOf Γ e1), (typeOf Γ e2) with
    | Some PTInt, Some PTInt => Some PTInt
    | _, _ => None
    end
  | PENew T => Some (TParr T)
  | PEGet e1 e2 =>
    match (typeOf Γ e1), (typeOf Γ e2) with
    | Some (TParr T), Some PTInt => Some T
    | _, _ => None
    end
  | PESet e1 e2 e3 =>
    match (typeOf Γ e1), (typeOf Γ e2), (typeOf Γ e3) with
    | Some (TParr T), Some PTInt, Some T' =>
        if TPeq T T' then Some PTNil else None
    | _, _, _ => None
    end
  | PEVar var => In Γ var
  | PEApp e1 e2 =>
    match typeOf Γ e1, typeOf Γ e2 with
    | Some (TPfun T1 T2), Some T1' =>
        if TPeq T1 T1' then Some T2 else None
    | _, _ => None
    end
  | PEFun var Tv e =>
    match typeOf (var |=> Tv; Γ) e with
    | Some Tb => Some (TPfun Tv Tb)
    | None => None
    end
  | PECast e T =>
    match typeOf Γ e with
    | Some _ => Some T
    | None => None
    end
  end.



Lemma typeOfCorrect' : forall Γ e T, Γ |= e : T -> typeOf Γ e = Some T.
Proof.
  intros Γ e T Hty.
  induction Hty; try easy;
  simpl;
  repeat match goal with
  | [H: typeOf _ _ = Some _ |- _] => rewrite H; clear H end;
  try easy; rewrite TPeqRefl; trivial.
Qed.


Ltac destTOf Γ e :=
    destruct (typeOf Γ e) as [[ | | | ? | ? ?] | ?] eqn:?; try easy.

Lemma typeOfCorrect'' : forall Γ e T, typeOf Γ e = Some T -> Γ |= e : T.
Proof.
  intros Γ e T Heq.
  generalize dependent Γ.
  generalize dependent T.
  induction e; intros T Γ Heq; subst;
  simpl in Heq; inversion Heq; subst; eauto using PTyping;
  try (destTOf Γ e1; destTOf Γ e2;
    inversion Heq; subst; eauto using PTyping; fail).
  - destTOf Γ e1.
    destTOf Γ e2.
    destruct (typeOf Γ e3) eqn:?; try easy.
    destruct (TPeq p p0) eqn:?; try easy.
    assert(p = p0) by (apply dec_TP; trivial).
    inversion Heq; subst. eauto using PTyping.
  - destTOf Γ e1.
    destruct (typeOf Γ e2) eqn:?; try easy.
    destruct (TPeq p p1) eqn:?; try easy.
    assert (p = p1) by (apply dec_TP; trivial).
    inversion Heq; subst. eauto using PTyping.
  - destruct (typeOf (s |=> p; Γ) e) eqn:?; try easy.
    inversion Heq; subst. eauto using PTyping.
  - destruct (typeOf Γ e) eqn:?; try easy.
    inversion Heq; subst. eauto using PTyping.
Qed.

Theorem typeOfCorrect : forall Γ e T, typeOf Γ e = Some T <-> Γ |= e : T.
Proof. split; auto using typeOfCorrect', typeOfCorrect''. Qed.



Fixpoint TP2FCT (t : PType) : IRType :=
  match t with
  | PTStar => IRTStar
  | PTNil => TgNil
  | PTInt => TgInt
  | TParr _ => TgTbl
  | TPfun _ _ =>  TgFun
  end.


Fixpoint TP2TGamma (Γ : Map PType) : Map IRType :=
  match Γ with
  | MEmpty => MEmpty
  | MCons var T Γ' => MCons var (TP2FCT T) (TP2TGamma Γ')
  end.


Lemma TP2TGammaIn : forall Γ var T,
    In Γ var = Some T -> In (TP2TGamma Γ) var = Some (TP2FCT T).
Proof.
  induction Γ; intros var T H; simpl in *.
  - easy.
  - destruct (string_dec var s); auto; congruence.
Qed.


Definition Cast (t1 t2 : IRType) (e : IRE) : IRE :=
  match t1, t2 with
  | IRTStar, IRTStar => e
  | IRTStar, IRTTag t => IREBox t e
  | IRTTag t, IRTStar => IREUnbox t e
  | IRTTag t1', IRTTag t2' => if dec_Tag t1' t2' then e
                            else IREUnbox t1' (IREBox t2' e)
  end.


Notation "'<' t1 '<=' t2 '>' e" := (Cast t1 t2 e)
    (at level 50, t1 at next level, t2 at next level).



Definition tagOf Γ e : IRType :=
  match typeOf Γ e with
  | Some T => TP2FCT T
  | None => TgNil
  end.

Lemma tagOfT : forall Γ e T, typeOf Γ e = Some T -> tagOf Γ e = TP2FCT T.
Proof. intros. unfold tagOf. rewrite H. trivial. Qed.


Fixpoint Pall2Lir (Γ : Environment) (e : PE) : IRE :=
  match e with
  | PENil => IRENil
  | PENum a => IRENum a
  | PEPlus e1 e2 => IREPlus (Pall2Lir Γ e1) (Pall2Lir Γ e2)
  | PENew _ => IRECnst
  | PEGet e1 e2 =>
         <tagOf Γ e <= IRTStar> (IREGet (Pall2Lir Γ e1) (Pall2Lir Γ e2))
  | PESet e1 e2 e3 =>
         (IRESet (Pall2Lir Γ e1)
                 (Pall2Lir Γ e2)
                 (<IRTStar <= tagOf Γ e3> Pall2Lir Γ e3))
  | PEVar var => IREVar var
  | PEFun var T e => let Γ' := (var |=> T; Γ) in
        IREFun (IRELamb var IRTStar
                      (IRELambApp (IRELamb var (TP2FCT T)
                                  (<IRTStar <= tagOf Γ' e> (Pall2Lir Γ' e)))
                                  (<TP2FCT T <= IRTStar> (IREVar var))))
  | PEApp e1 e2 => <tagOf Γ e <= IRTStar>
         (IREFunApp (Pall2Lir Γ e1)
                  (<IRTStar <= (tagOf Γ e2)> Pall2Lir Γ e2))
  | PECast e1 t => <TP2FCT t <= tagOf Γ e1> (Pall2Lir Γ e1)
  end.


Lemma invertCall : forall Γ e1 e2 T1 T2 t,
  typeOf Γ e1 = Some (TPfun T1 T2) -> typeOf Γ e2 = Some T1 ->
    tagOf Γ (PEApp e1 e2) = t -> TP2FCT T2 = t.
Proof.
  intros Γ e1 r2 T1 T2 t H1 H2.
  unfold tagOf. simpl. rewrite H1. rewrite H2.
  rewrite TPeqRefl. congruence.
Qed.


Ltac breakTagOf :=
  match goal with
  [H: typeOf _ ?E = Some ?T |- context C [tagOf _ ?E] ] =>
    apply tagOfT in H; rewrite H; destruct (TP2FCT T) eqn:?;
    eauto using IRTyping
  end.


Theorem Pall2LirWellTyped : forall Γ (e : PE) T,
    Γ |= e : T -> IRTyping (TP2TGamma Γ) (Pall2Lir Γ e) (TP2FCT T).
Proof with eauto using IRTyping.
  intros Γ e T H.
  induction H; simpl in *;
  eauto using IRTyping,TP2TGammaIn;
  repeat match goal with
  | [H: PTyping ?G ?E ?T |- _] =>
      apply typeOfCorrect in H
  end.
  - unfold tagOf. simpl. rewrite H. rewrite H0.
    destruct (TP2FCT T) eqn:?; simpl...
  - unfold tagOf. rewrite H1.
    destruct (TP2FCT T) eqn:?; simpl...
  - apply IRTyFun. apply IRTyLamb. apply IRTyLambApp with (TP2FCT Tvar).
    apply IRTyLamb.
    + apply envExt with (var |=> TP2FCT Tvar; TP2TGamma Γ).
      apply inclusion_shadow'.
      breakTagOf.
    + apply tagOfT in H;
      destruct (TP2FCT Tvar) eqn:?;
      eauto using IRTyping,InEq.
  - destruct (tagOf Γ (PEApp e1 e2)) eqn:?;
      rewrite (invertCall _ _ _ _ _ _ H H0 Heqi);
      breakTagOf.
  - unfold Cast.
    breakTagOf;
    destruct (TP2FCT T2) eqn:?...
    destruct (dec_Tag t0 t); subst; try easy...
Qed.

