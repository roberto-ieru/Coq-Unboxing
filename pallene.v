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
| PTArr : PType -> PType | PTFun : PType -> PType -> PType
.


Lemma dec_TP : forall (t1 t2 : PType), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Qed.


Definition PEnvironment := Map PType.

(*
** Syntax of λ-Pallene
*)
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


(*
** Typing rules for λ-Pallene
*)
Reserved Notation "Γ '|=' e ':' t"  (at level 40, no associativity,
                                     e at next level).

Inductive PTyping : PEnvironment -> PE -> PType -> Prop :=
| PTyNil : forall Γ, Γ |= PENil : PTNil
| PTyInt : forall Γ n, Γ |= PENum n : PTInt
| PTyVal : forall Γ var T,
    In Γ var = Some T ->
    Γ |= PEVar var : T
| PTyPlus : forall Γ e1 e2,
    Γ |= e1 : PTInt ->
    Γ |= e2 : PTInt ->
    Γ |= PEPlus e1 e2 : PTInt
| PTyNew : forall Γ T, Γ |= PENew T : PTArr T
| PTyGet : forall Γ e1 T e2,
    Γ |= e1 : PTArr T ->
    Γ |= e2 : PTInt ->
    Γ |= PEGet e1 e2 : T
| PTySet : forall Γ e1 T e2 e3,
    Γ |= e1 : PTArr T ->
    Γ |= e2 : PTInt ->
    Γ |= e3 : T ->
    Γ |= PESet e1 e2 e3 : PTStar
| PTyFun : forall Γ var Tvar body Tbody,
    var |=> Tvar; Γ |= body : Tbody ->
    Γ |= PEFun var Tvar body : PTFun Tvar Tbody
| PTyApp : forall Γ e1 e2 T1 T2,
    Γ |= e1 : PTFun T1 T2 ->
    Γ |= e2 : T1 ->
    Γ |= PEApp e1 e2 : T2
| PTyCast : forall Γ e T1 T2,
    Γ |= e : T1 ->
    Γ |= PECast e T2 : T2

where "Γ '|=' e ':' t" := (PTyping Γ e t)
.


(*
** Typing algorithm for λ-Pallene
*)
Fixpoint typeOf Γ e : option PType :=
  match e with
  | PENil => Some PTNil
  | PENum _ => Some PTInt
  | PEPlus e1 e2 =>
    match (typeOf Γ e1), (typeOf Γ e2) with
    | Some PTInt, Some PTInt => Some PTInt
    | _, _ => None
    end
  | PENew T => Some (PTArr T)
  | PEGet e1 e2 =>
    match (typeOf Γ e1), (typeOf Γ e2) with
    | Some (PTArr T), Some PTInt => Some T
    | _, _ => None
    end
  | PESet e1 e2 e3 =>
    match (typeOf Γ e1), (typeOf Γ e2), (typeOf Γ e3) with
    | Some (PTArr T), Some PTInt, Some T' =>
        if dec_TP T T' then Some PTStar else None
    | _, _, _ => None
    end
  | PEVar var => In Γ var
  | PEApp e1 e2 =>
    match typeOf Γ e1, typeOf Γ e2 with
    | Some (PTFun T1 T2), Some T1' =>
        if dec_TP T1 T1' then Some T2 else None
    | _, _ => None
    end
  | PEFun var Tv e =>
    match typeOf (var |=> Tv; Γ) e with
    | Some Tb => Some (PTFun Tv Tb)
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
  | [H: typeOf _ _ = Some _ |- _] => rewrite H; clear H
  | [ |- context [dec_TP ?V1 ?V2] ] => destruct (dec_TP V1 V2)
  end; easy.
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
    destruct (dec_TP p p0) eqn:?; try easy.
    inversion Heq; subst. eauto using PTyping.
  - destTOf Γ e1.
    destruct (typeOf Γ e2) eqn:?; try easy.
    destruct (dec_TP p p1) eqn:?; try easy.
    inversion Heq; subst. eauto using PTyping.
  - destruct (typeOf (s |=> p; Γ) e) eqn:?; try easy.
    inversion Heq; subst. eauto using PTyping.
  - destruct (typeOf Γ e) eqn:?; try easy.
    inversion Heq; subst. eauto using PTyping.
Qed.


(*
** Rules and algorithm agree
*)
Lemma typeOfCorrect : forall Γ e T, typeOf Γ e = Some T <-> Γ |= e : T.
Proof. split; auto using typeOfCorrect', typeOfCorrect''. Qed.


(*
** Pallene types are unique
*)
Lemma PTypeUnique : forall Γ e t1 t2,
    Γ |= e : t1 -> Γ |= e : t2 -> t1 = t2.
Proof.
  intros Γ e t1 t2 H1 H2.
  apply typeOfCorrect in H1.
  apply typeOfCorrect in H2.
  congruence.
Qed.


Definition PT2Base (t : PType) : BaseType :=
  match t with
  | PTStar => BStar
  | PTNil => BGround TgNil
  | PTInt => BGround TgInt
  | PTArr _ => BGround TgTbl
  | PTFun _ _ =>  BGround TgFun
  end.


Definition PT2IRT (t : PType) : IRType := Base2Type (PT2Base t).


Lemma PT2IRTFun : forall T1 T2,
    PT2IRT (PTFun T1 T2) = IRTFun.
Proof. intros T1 T2. unfold PT2IRT. trivial. Qed.


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


Definition Cast (t1 t2 : BaseType) (e : IRE) : IRE :=
  match t1, t2 with
  | BStar, BStar => e
  | BStar, BGround t => IREBox t e
  | BGround t, BStar => IREUnbox t e
  | BGround t1', BGround t2' => if dec_Tag t1' t2' then e
                            else IREUnbox t1' (IREBox t2' e)
  end.


Notation "'<' t1 '<=' t2 '>' e" := (Cast t1 t2 e)
    (at level 50, t1 at next level, t2 at next level).



Definition tagOf Γ e : BaseType :=
  match typeOf Γ e with
  | Some T => PT2Base T
  | None => BGround TgNil
  end.


Lemma tagOfT : forall Γ e T, typeOf Γ e = Some T -> tagOf Γ e = PT2Base T.
Proof. intros. unfold tagOf. rewrite H. trivial. Qed.


Lemma tagStar2type : forall Γ e,
    tagOf Γ e = BStar -> typeOf Γ e = Some PTStar.
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
  | PENew _ => IRECnst
  | PEGet e1 e2 =>
         <tagOf Γ e <= BStar>
           (IREGet (Pall2Lir Γ e1) (<BStar <= (BGround TgInt)> (Pall2Lir Γ e2)))
  | PESet e1 e2 e3 =>
         (IRESet (Pall2Lir Γ e1)
                 (<BStar <= BGround TgInt> (Pall2Lir Γ e2))
                 (<BStar <= tagOf Γ e3> Pall2Lir Γ e3))
  | PEVar var => IREVar var
  | PEFun var T body => let Γ' := (var |=> T; Γ) in
        IREFun var
          (IRELet var (PT2IRT T) (<PT2Base T <= BStar> (IREVar var))
                     (<BStar <= tagOf Γ' body> (Pall2Lir Γ' body)))
  | PEApp e1 e2 => <tagOf Γ e <= BStar>
         (IREApp (Pall2Lir Γ e1)
                  (<BStar <= (tagOf Γ e2)> Pall2Lir Γ e2))
  | PECast e1 t => <PT2Base t <= tagOf Γ e1> (Pall2Lir Γ e1)
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
    tagOf Γ (PEApp e1 e2) = BStar ->
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


Lemma PTTagB : forall (T : PType) (tg : Tag),
    PT2Base T = BGround tg -> PT2IRT T = Tag2Type tg.
Proof.
  intros T tg H.
  destruct T; inversion H; easy.
Qed.


Lemma PTStarB : forall (T : PType),
    PT2Base T = BStar -> T = PTStar.
Proof.
  intros T H.
  destruct T; inversion H; easy.
Qed.


Lemma typeStar : forall Γ e T,
    typeOf Γ e = Some T -> tagOf Γ e = BStar -> T = PTStar.
Proof.
  intros Γ e T HT Htg.
  unfold tagOf in Htg.
  rewrite HT in Htg.
  auto using PTStarB.
Qed.


Lemma typeTag : forall Γ e T tg,
    typeOf Γ e = Some T -> tagOf Γ e = BGround tg -> PT2IRT T = Tag2Type tg.
Proof.
  intros Γ e T tg HT Htg.
  unfold tagOf in Htg.
  rewrite HT in Htg.
  auto using PTTagB.
Qed.


(*
** Compilation of well-typed programs result in well-typed code
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
    destruct (PT2Base T) eqn:?; simpl; eauto using IRTyping, PTTagB.
    apply PTStarB in Heqb; subst.
    eauto using IRTyping.

  - (* Set *)
    unfold tagOf. rewrite H1.
    destruct (PT2Base T) eqn:?; simpl.
    + apply PTTagB in Heqb. rewrite Heqb in IHPTyping3.
      eauto using IRTyping.
    + apply PTStarB in Heqb; subst.
      eauto using IRTyping.

  - (* Fun *)
    apply IRTyFun. eapply IRTyLet.
    + destruct (tagOf (var |=> Tvar; Γ)) eqn:?; subst.
      * apply IRTyBox.
        eapply inclusion_typing.
        ** eapply inclusion_shadow'.
        ** unfold tagOf in Heqb. rewrite H in Heqb.
           apply PTTagB in Heqb. rewrite <- Heqb. trivial.
      *  unfold tagOf in Heqb. rewrite H in Heqb.
        apply PTStarB in Heqb. rewrite Heqb in IHPTyping.
        simpl in IHPTyping.
        eapply inclusion_typing; eauto.
        apply inclusion_shadow'.
    + unfold Cast.
      destruct (PT2Base Tvar) eqn:?.
      * apply IRTyUnbox.
        ** apply PTTagB in Heqb. trivial.
        ** apply IRTyVar. apply InEq.
      * apply PTStarB in Heqb. subst. simpl.
        apply IRTyVar. apply InEq.

  - (* FunApp *)
    rewrite PT2IRTFun in IHPTyping1.
    destruct (tagOf Γ (PEApp e1 e2)) eqn:?.
    + specialize (invertCall _ _ _ _ _ H H0) as H2.
      unfold tagOf in Heqb. rewrite H2 in Heqb.
      simpl.
      apply PTTagB in Heqb.
      apply IRTyUnbox; trivial.
      eapply IRTyFunApp; eauto.
      destruct (tagOf Γ e2) eqn:?.
      * apply IRTyBox.
        specialize (typeTag _ _ _ _ H0 Heqb0) as HTt.
        rewrite <- HTt. trivial.
      * specialize (typeStar _ _ _ H0 Heqb0) as HTS.
        subst. trivial.
    + unfold Cast.
      specialize (invertFun _ _ _ _ _ H Heqb); intros; subst; simpl.
      destruct (tagOf Γ e2) eqn:?.
      * eapply IRTyFunApp; eauto using IRTyping.
        eapply IRTyBox.
        specialize (typeTag _ _ _ _ H0 Heqb0) as HTt.
        rewrite <- HTt. trivial.
      * eapply IRTyFunApp; eauto using IRTyping.
        specialize (typeStar _ _ _ H0 Heqb0) as HTS.
        subst. trivial.

  - (* Cast *)
    unfold Cast.
    destruct (PT2Base T2) eqn:?;
    unfold tagOf;
    rewrite H;
    destruct (PT2Base T1) eqn:?.
    + destruct (dec_Tag t t0); subst.
      * unfold PT2IRT in *.
        rewrite Heqb.
        rewrite <- Heqb0.
        trivial.
      * eapply IRTyUnbox.
        auto using PTTagB.
        eapply IRTyBox.
        apply PTTagB in Heqb0.
        rewrite <- Heqb0. trivial.
    + apply IRTyUnbox.
      * auto using PTTagB.
      * apply PTStarB in Heqb0.
        subst. eauto.
  + apply PTStarB in Heqb. subst.
    apply IRTyBox.
    apply PTTagB in Heqb0. rewrite <- Heqb0. trivial.
  + unfold PT2IRT in *.
    rewrite Heqb.
    rewrite Heqb0 in IHPTyping.
    trivial.
Qed.


