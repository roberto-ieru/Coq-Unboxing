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
Theorem Pall2LirWellTyped : forall Γ (e : PE) T,
    Γ |= e : T -> IRTyping (TP2TGamma Γ) (Pall2Lir Γ e) (PT2IRT T).
Proof with eauto using IRTyping.
  intros Γ e T H.
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

  - (* FunApp *)
    destruct (tagOf Γ (PEApp e1 e2)) eqn:?.
    + specialize (invertCall _ _ _ _ _ H H0) as H2.
      unfold tagOf in Heqi. rewrite H2 in Heqi.
      simpl.
      apply IRTyUnbox; trivial.
      eapply IRTyFunApp; eauto.
      destruct (tagOf Γ e2) eqn:?.
      * apply IRTyBox.
        specialize (typeTag _ _ _ _ H0 Heqi0) as HTt.
        rewrite <- HTt. trivial.
      * specialize (typeStar _ _ _ H0 Heqi0) as HTS.
        subst. trivial.
    + unfold Cast.
      specialize (invertFun _ _ _ _ _ H Heqi); intros; subst; simpl.
      destruct (tagOf Γ e2) eqn:?.
      * eapply IRTyFunApp; eauto using IRTyping.
        eapply IRTyBox.
        specialize (typeTag _ _ _ _ H0 Heqi0) as HTt.
        rewrite <- HTt. trivial.
      * eapply IRTyFunApp; eauto using IRTyping.
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


