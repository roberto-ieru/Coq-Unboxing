Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.

Require Import LIR.lir.


Inductive TPall : Set :=
| TPstar : TPall | TPnil : TPall | TPint : TPall
| TParr : TPall -> TPall | TPfun : TPall -> TPall -> TPall
.


Fixpoint TPeq (t1 t2 : TPall) : bool :=
  match t1, t2 with
  | TPstar, TPstar => true
  | TPnil, TPnil => true
  | TPint, TPint => true
  | TParr t1', TParr t2' => TPeq t1' t2'
  | TPfun t1' t1'', TPfun t2' t2'' => TPeq t1' t2' && TPeq t1'' t2''
  | _, _ => false
  end.


Lemma dec_TP : forall (t1 t2 : TPall), TPeq t1 t2 = true <-> t1 = t2.
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


Definition Environment := Map TPall.

Inductive EPall : Set :=
| EPnil : EPall
| EPnum : nat -> EPall
| EPplus : EPall -> EPall -> EPall
| EPnew : TPall -> EPall
| EPget : EPall -> EPall -> EPall
| EPset : EPall -> EPall -> EPall -> EPall
| EPvar : string -> EPall
| EPapp :  EPall -> EPall -> EPall
| EPfunc : string -> TPall -> EPall -> EPall
| EPcast : EPall -> TPall -> EPall
.


Reserved Notation "Γ '|=' e ':' t"  (at level 40, no associativity,
                                     e at next level).

Inductive PTyping : Environment -> EPall -> TPall -> Prop :=
| PTyPnil : forall Γ, Γ |= EPnil : TPnil
| PTyInt : forall Γ n, Γ |= EPnum n : TPint
| PTyVal : forall Γ var T,
    In Γ var = Some T ->
    Γ |= EPvar var : T
| PTyAdd : forall Γ e1 e2,
    Γ |= e1 : TPint ->
    Γ |= e2 : TPint ->
    Γ |= EPplus e1 e2 : TPint
| PTyNew : forall Γ T, Γ |= EPnew T : TParr T
| PTyGet : forall Γ e1 T e2,
    Γ |= e1 : TParr T ->
    Γ |= e2 : TPint ->
    Γ |= EPget e1 e2 : T
| PTySet : forall Γ e1 T e2 e3,
    Γ |= e1 : TParr T ->
    Γ |= e2 : TPint ->
    Γ |= e3 : T ->
    Γ |= EPset e1 e2 e3 : TPnil
| PTyFun : forall Γ var Tvar body Tbody,
    var |=> Tvar; Γ |= body : Tbody ->
    Γ |= EPfunc var Tvar body : TPfun Tvar Tbody
| PTyApp : forall Γ e1 e2 T1 T2,
    Γ |= e1 : TPfun T1 T2 ->
    Γ |= e2 : T1 ->
    Γ |= EPapp e1 e2 : T2
| PTyCast : forall Γ e T1 T2,
    Γ |= e : T1 ->
    Γ |= EPcast e T2 : T2

where "Γ '|=' e ':' t" := (PTyping Γ e t)
.


Fixpoint typeOf Γ e : option TPall :=
  match e with
  | EPnil => Some TPnil
  | EPnum _ => Some TPint
  | EPplus e1 e2 =>
    match (typeOf Γ e1), (typeOf Γ e2) with
    | Some TPint, Some TPint => Some TPint
    | _, _ => None
    end
  | EPnew T => Some (TParr T)
  | EPget e1 e2 =>
    match (typeOf Γ e1), (typeOf Γ e2) with
    | Some (TParr T), Some TPint => Some T
    | _, _ => None
    end
  | EPset e1 e2 e3 =>
    match (typeOf Γ e1), (typeOf Γ e2), (typeOf Γ e3) with
    | Some (TParr T), Some TPint, Some T' =>
        if TPeq T T' then Some TPnil else None
    | _, _, _ => None
    end
  | EPvar var => In Γ var
  | EPapp e1 e2 =>
    match typeOf Γ e1, typeOf Γ e2 with
    | Some (TPfun T1 T2), Some T1' =>
        if TPeq T1 T1' then Some T2 else None
    | _, _ => None
    end
  | EPfunc var Tv e =>
    match typeOf (var |=> Tv; Γ) e with
    | Some Tb => Some (TPfun Tv Tb)
    | None => None
    end
  | EPcast e T =>
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
    destruct (TPeq t t0) eqn:?; try easy.
    inversion Heq; subst.
    assert(t = t0). { apply dec_TP. trivial. }
    subst. eauto using PTyping.
  - destTOf Γ e1.
    destruct (typeOf Γ e2) eqn:?; try easy.
    destruct (TPeq t t1) eqn:?; try easy.
    inversion Heq; subst. econstructor.
    eapply IHe1. eauto.
    assert (t = t1). { apply dec_TP. trivial. }
    subst. auto.
  - destruct (typeOf (s |=> t; Γ) e) eqn:?; try easy.
    inversion Heq; subst. eauto using PTyping.
  - destruct (typeOf Γ e) eqn:?; try easy.
    inversion Heq; subst. eauto using PTyping.
Qed.

Theorem typeOfCorrect : forall Γ e T, typeOf Γ e = Some T <-> Γ |= e : T.
Proof. split; auto using typeOfCorrect', typeOfCorrect''. Qed.



Fixpoint TP2FCT (t : TPall) : FCType :=
  match t with
  | TPstar => Tstar
  | TPnil => Tgnil
  | TPint => Tgint
  | TParr _ => Tgtbl
  | TPfun _ _ =>  Tgfun
  end.


Fixpoint TP2TGamma (Γ : Map TPall) : Map FCType :=
  match Γ with
  | MEmpty => MEmpty
  | MCons var T Γ' => MCons var (TP2FCT T) (TP2TGamma Γ')
  end.


Lemma TP2TGammaIn : forall Γ var T,
    In Γ var = Some T -> In (TP2TGamma Γ) var = Some (TP2FCT T).
Proof.
  induction Γ; intros var T H.
  - simpl in *. easy.
  - simpl in *. destruct (string_dec var s); subst; auto.
    congruence.
Qed.


Definition Cast (t1 t2 : FCType) (e : LirExp) : LirExp :=
  match t1, t2 with
  | Tstar, Tstar => e
  | Tstar, Ttag t => Ebox t e
  | Ttag t, Tstar => Eunbox t e
  | Ttag t1', Ttag t2' => if dec_Tag t1' t2' then e
                            else Eunbox t1' (Ebox t2' e)
  end.


Notation "'<' t1 '<=' t2 '>' e" := (Cast t1 t2 e)
    (at level 50, t1 at next level, t2 at next level).



Definition tagOf Γ e : FCType :=
  match typeOf Γ e with
  | Some T => TP2FCT T
  | None => Tgnil
  end.

Lemma tagOfT : forall Γ e T, typeOf Γ e = Some T -> tagOf Γ e = TP2FCT T.
Proof. intros. unfold tagOf. rewrite H. trivial. Qed.


Fixpoint Pall2Lir (Γ : Environment) (e : EPall) : LirExp :=
  match e with
  | EPnil => Enil
  | EPnum a => Enum a
  | EPplus e1 e2 => Eplus (Pall2Lir Γ e1) (Pall2Lir Γ e2)
  | EPnew _ => Ecstr
  | EPget e1 e2 =>
         <tagOf Γ e <= Tstar> (Eindx (Pall2Lir Γ e1) (Pall2Lir Γ e2))
  | EPset e1 e2 e3 =>
         (Eassg (Pall2Lir Γ e1)
               (Pall2Lir Γ e2)
                (<Tstar <= tagOf Γ e3> Pall2Lir Γ e3))
  | EPvar var => Evar var
  | EPfunc var T e => let Γ' := (var |=> T; Γ) in
        Efun (Elambda var Tstar
                      (Elambapp (Elambda var (TP2FCT T)
                                    (<Tstar <= tagOf Γ' e> (Pall2Lir Γ' e)))
                                (<TP2FCT T <= Tstar> (Evar var))))
  | EPapp e1 e2 => <tagOf Γ e <= Tstar>
         (Efunapp (Pall2Lir Γ e1)
                  (<Tstar <= (tagOf Γ e2)> Pall2Lir Γ e2))
  | EPcast e1 t => <TP2FCT t <= tagOf Γ e1> (Pall2Lir Γ e1)
  end.


Theorem Pall2LirWellTyped : forall Γ (e : EPall) T,
    Γ |= e : T -> Typing (TP2TGamma Γ) (Pall2Lir Γ e) (TP2FCT T).
Proof.
  intros Γ e T H.
  induction H; simpl in *;
  repeat match goal with
  | [H: PTyping ?G ?E ?T |- _] =>
      apply typeOfCorrect in H
  end;
  eauto using Typing,TP2TGammaIn.
  - unfold tagOf. simpl. rewrite H. rewrite H0.
    destruct (TP2FCT T) eqn:HTT; simpl; eauto using Typing.
  - unfold tagOf. rewrite H1.
    destruct (TP2FCT T) eqn:?; simpl; eauto using Typing.
  - apply TyFun. apply TyLam. apply TyLamApp with (TP2FCT Tvar).
    apply TyLam.
    + apply envExt with (var |=> TP2FCT Tvar; TP2TGamma Γ).
      apply inclusion_shadow'.
      apply tagOfT in H. rewrite H.
      destruct (TP2FCT Tbody) eqn:?; eauto using Typing.
    + apply tagOfT in H;
      destruct (TP2FCT Tvar) eqn:?;
      eauto using Typing,InEq.
  - destruct (tagOf Γ (EPapp e1 e2)) eqn:?.
    + assert (Ttag t = TP2FCT T2).
      { unfold tagOf in Heqf. simpl in Heqf.
        rewrite H in Heqf.
        rewrite H0 in Heqf.
        rewrite TPeqRefl in Heqf. easy. }
      rewrite <- H1. apply TyUnbox.
      apply TyFunApp. easy.
      apply tagOfT in H0. rewrite H0.
      destruct (TP2FCT T1) eqn:?; eauto using Typing.
    + assert (TP2FCT T2 = Tstar).
      { unfold tagOf in Heqf.
        destruct (typeOf Γ (EPapp e1 e2)) eqn:?; try easy.
        simpl in Heqo. rewrite H in Heqo. rewrite H0 in Heqo.
        rewrite TPeqRefl in Heqo. congruence. }
      rewrite H1. simpl. apply TyFunApp.
      trivial. apply tagOfT in H0. rewrite H0.
      destruct (TP2FCT T1) eqn:?; eauto using Typing.
  - unfold Cast.
    apply tagOfT in H. rewrite H.
    destruct (TP2FCT T1) eqn:?;
    destruct (TP2FCT T2) eqn:?; eauto using Typing.
    destruct (dec_Tag t0 t); subst; try easy.
    eauto using Typing.
Qed.


