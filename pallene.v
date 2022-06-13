Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.

Require Import LIR.lir.


(* Pallene types *)
Inductive PType : Set :=
| PTStar : PType
| PTNil : PType
| PTInt : PType
| PTArr : PType -> PType
| PTFun : PType -> PType -> PType
.


Lemma dec_TP : forall (t1 t2 : PType), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Qed.


(* Type environment for Pallene *)
Definition PEnvironment := Map PType.

(*
** Syntax of λ-Pallene
*)
Inductive PE : Set :=
| PENil : PE
| PENum : nat -> PE
| PEPlus : PE -> PE -> PE
| PENew : PType -> PE
| PETAddr : address -> PType -> PE
| PEFAddr : address -> PType -> PType -> PE
| PEGet : PE -> PE -> PE
| PESet : PE -> PE -> PE -> PE
| PEVar : string -> PE
| PEApp :  PE -> PE -> PE
| PEFun : string -> PType -> PE -> PType -> PE
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
| PTyTAddr : forall Γ a T, Γ |= PETAddr a T : PTArr T
| PTyFAddr : forall Γ a T1 T2, Γ |= PEFAddr a T1 T2 : PTFun T1 T2
| PTyGet : forall Γ e1 T e2,
    Γ |= e1 : PTArr T ->
    Γ |= e2 : PTInt ->
    Γ |= PEGet e1 e2 : T
| PTySet : forall Γ e1 T e2 e3,
    Γ |= e1 : PTArr T ->
    Γ |= e2 : PTInt ->
    Γ |= e3 : T ->
    Γ |= PESet e1 e2 e3 : PTNil
| PTyFun : forall Γ var Tvar body Tbody,
    var |=> Tvar; Γ |= body : Tbody ->
    Γ |= PEFun var Tvar body Tbody : PTFun Tvar Tbody
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
  | PETAddr _ T => Some (PTArr T)
  | PEFAddr _ T1 T2 => Some (PTFun T1 T2)
  | PEGet e1 e2 =>
    match (typeOf Γ e1), (typeOf Γ e2) with
    | Some (PTArr T), Some PTInt => Some T
    | _, _ => None
    end
  | PESet e1 e2 e3 =>
    match (typeOf Γ e1), (typeOf Γ e2), (typeOf Γ e3) with
    | Some (PTArr T), Some PTInt, Some T' =>
        if dec_TP T T' then Some PTNil else None
    | _, _, _ => None
    end
  | PEVar var => In Γ var
  | PEApp e1 e2 =>
    match typeOf Γ e1, typeOf Γ e2 with
    | Some (PTFun T1 T2), Some T1' =>
        if dec_TP T1 T1' then Some T2 else None
    | _, _ => None
    end
  | PEFun var Tv e Tb =>
    match typeOf (var |=> Tv; Γ) e with
    | Some Tb' => if dec_TP Tb Tb' then Some (PTFun Tv Tb) else None
    | None => None
    end
  | PECast e T =>
    match typeOf Γ e with
    | Some _ => Some T
    | None => None
    end
  end.


(*
** 'typeOf' is correct (part 1)
*)
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

(*
** 'typeOf' is correct (part 2)
*)
Lemma typeOfCorrect'' : forall Γ e T, typeOf Γ e = Some T -> Γ |= e : T.
Proof.
  intros Γ e T Heq.
  generalize dependent Γ.
  generalize dependent T.
  induction e; intros T Γ Heq; subst;
  simpl in Heq; inversion Heq; subst; eauto using PTyping;
  try (destTOf Γ e1; destTOf Γ e2;
    inversion Heq; subst; eauto using PTyping; fail).
  - (* Set *)
    destTOf Γ e1.
    destTOf Γ e2.
    destruct (typeOf Γ e3) eqn:?; try easy.
    destruct (dec_TP p p0) eqn:?; try easy.
    inversion Heq; subst. eauto using PTyping.
  - (* App *)
    destTOf Γ e1.
    destruct (typeOf Γ e2) eqn:?; try easy.
    destruct (dec_TP p p1) eqn:?; try easy.
    inversion Heq; subst. eauto using PTyping.
  - (* Fun *)
    clear H0.
    destruct (typeOf (s |=> p; Γ) e) eqn:HT; try easy.
    destruct (dec_TP p0 p1); subst; try discriminate.
    inversion Heq; subst. eauto using PTyping.
  - (* Cast *)
    destruct (typeOf Γ e) eqn:?; try easy.
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



(*
** Direct Semantics for Pallene
*)


(*
** Pallene values
*)
Inductive PValue : PE -> Prop :=
| PVnil : PValue PENil
| PVnum : forall n, PValue (PENum n)
| PVtbl : forall a T, PValue (PETAddr a T)
| PVfun : forall a T1 T2, PValue (PEFAddr a T1 T2)
| PVbox : forall v, PValue v -> PValue (PECast v PTStar)
.


(* Canonical forms *)

Lemma ValStar : forall v,
  PValue v ->
  MEmpty |= v : PTStar ->
  exists v', v = PECast v' PTStar /\ PValue v'.
Proof.
  intros * HV HT. inversion HT; subst; inversion HV; subst; eauto.
Qed.

Lemma ValNil : forall v,
  PValue v ->
  MEmpty |= v : PTNil ->
  v = PENil.
Proof.
  intros * HV HT. inversion HT; subst; inversion HV; subst; eauto.
Qed.

Lemma ValInt : forall v,
  PValue v ->
  MEmpty |= v : PTInt ->
  exists n, v = PENum n.
Proof.
  intros * HV HT. inversion HT; subst; inversion HV; subst; eauto.
Qed.

Lemma ValArr : forall v T,
  PValue v ->
  MEmpty |= v : PTArr T ->
  exists a, v = PETAddr a T.
Proof.
  intros * HV HT. inversion HT; subst; inversion HV; subst; eauto.
Qed.

Lemma ValFun : forall v T1 T2,
  PValue v ->
  MEmpty |= v : PTFun T1 T2 ->
  exists a, v = PEFAddr a T1 T2.
Proof.
  intros * HV HT. inversion HT; subst; inversion HV; subst; eauto.
Qed.


(*
** Cast a Pallene expression to a given type; gives None iff cast
** fails.
*)
Fixpoint PCast (e : PE) (T : PType) : option PE :=
  match e, T with
  | PECast e' PTStar, PTStar => Some e		(* '*' to '*' *)
  | PECast e' PTStar, T => PCast e' T		(* downcast from '*' *)
  | e', PTStar => Some (PECast e' PTStar)	(* upcast to '*' *)
  | PENil, PTNil => Some e
  | PENum n, PTInt => Some e
  | PETAddr a T, PTArr T' => Some (PETAddr a T')
  | PEFAddr a T1 T2, PTFun T1' T2' => Some (PEFAddr a T1' T2')
  | _, _ => None
  end.

(*
** The cast of a value gives a value
*)
Lemma CastValue : forall e v T,
  PValue e ->
  PCast e T = Some v ->
  PValue v.
Proof.
  intros * PV PC.
  induction PV; destruct T; simpl in *;
   try discriminate;
   try (injection PC; intros; subst); auto using PValue.
Qed.


(*
** A successful cast of a value to a type has that type
*)
Lemma CastEqType : forall e T1 T2 v,
  PValue e ->
  MEmpty |= e : T1 ->
  PCast e T2 = Some v ->
  MEmpty |= v : T2.
Proof.
  intros * HV HT HC.
  remember MEmpty as Gamma eqn:HEq.
  induction HT; inversion HV; subst;
  destruct T2; simpl in *; try discriminate;
  try (injection HC; intros; subst); eauto using PTyping.
Qed.


(*
** A cast of a value to its own type gives the value itself
*)
Lemma CastToItsType : forall T v,
  PValue v ->
  MEmpty |= v : T ->
  PCast v T = Some v.
Proof.
  intros * HV HT.
  remember MEmpty as Gamma eqn:HEq.
  induction HT; trivial; inversion HV; subst; trivial.
Qed.


(*
** A cast to '*' never fails
*)
Lemma CastToStar : forall e, exists e', PCast e PTStar = Some e'.
Proof.
  induction e; try (eexists; simpl; eauto; fail).
  destruct IHe.
  destruct p;
  simpl; eauto.
Qed.


Fixpoint PToIndex (n : nat) : Index := I n TgInt.


Inductive PExpValue : Set :=
| PEV : forall e, PValue e -> PExpValue.


Definition PEV2Val (me : PExpValue) : PE :=
  match me with
  | PEV v _ => v
  end.



Inductive PMem : Set :=
| PEmptyMem : PMem
| PUpdateT : address -> Index -> PExpValue -> PMem -> PMem
| PUpdateF : address -> string -> PType -> PE -> PMem -> PMem.


Fixpoint PqueryT (a : address) (idx : nat) (m : PMem) : PE :=
  match m with
  | PEmptyMem => PENil
  | PUpdateT a' idx' e m' => if Nat.eq_dec a a' then
                           if Index_dec (PToIndex idx) idx' then (PEV2Val e)
                           else PqueryT  a idx m'
                         else PqueryT  a idx m'
  | PUpdateF _ _ _ _ m' => PqueryT a idx m'
  end.


Fixpoint PqueryF (a : address) (m : PMem) : (string * PType * PE) :=
  match m with
  | PEmptyMem => (""%string, PTStar,  PENil)
  | PUpdateT a' _ _ m' => PqueryF a m'
  | PUpdateF a' var type body m' => if Nat.eq_dec a a' then (var, type,  body)
                                    else PqueryF a m'
  end.


Fixpoint Pfreshaux (m : PMem) : address :=
  match m with
  | PEmptyMem => 1
  | PUpdateT _ _ _ m' => S (Pfreshaux m')
  | PUpdateF _ _ _ _ m' => S (Pfreshaux m')
  end.


Definition PfreshT (m : PMem) : (address * PMem) :=
  let f := Pfreshaux m in
    (f, PUpdateT f (I 0 TgNil) (PEV PENil PVnil) m).


Definition PfreshF (m : PMem) (v : string) (t : PType) (b : PE) :
             (address * PMem) :=
  let f := Pfreshaux m in
    (f, PUpdateF f v t b m).


Reserved Notation "'[' x ':=' s ']' t" (at level 20, x constr).


Fixpoint substitution (var : string) (y : PE)  (e : PE) : PE :=
 match e with
 | PENil => e
 | PENum n => e
 | PEPlus e1 e2 => PEPlus ([var := y] e1) ([var := y] e2)
 | PENew _ => e
 | PETAddr a _ => e
 | PEFAddr a _ _ => e
 | PEGet e1 e2 => PEGet ([var := y] e1) ([var := y] e2)
 | PESet e1 e2 e3 => PESet ([var := y] e1) ([var := y] e2) ([var := y] e3)
 | PEVar var' => if string_dec var var' then y else e
 | PEFun var' T1 body T2 => if string_dec var var' then e
                          else PEFun var' T1 ([var := y] body) T2
 | PEApp e1 e2 => PEApp ([var := y] e1) ([var := y] e2)
 | PECast e T => PECast ([var := y] e) T
end
where "'[' x ':=' s ']' t" := (substitution x s t)
.


(*
** Extending an environment preserves typing
*)
Lemma Pinclusion_typing : forall Γ Γ' e te,
  inclusion Γ Γ' -> Γ |= e : te -> Γ' |= e : te.
Proof.
  intros Γ Γ' e te Hin Hty.
  generalize dependent Γ'.
  induction Hty; eauto using PTyping, inclusion_update.
Qed.


(*
** Particular case when extending the empty environment
*)
Lemma Ptyping_empty : forall Γ e te, MEmpty |= e : te -> Γ |= e : te.
Proof.
  eauto using Pinclusion_typing, inclusion_empty.
Qed.


(*
** Substitution preserves typing
*)
Lemma Psubst_typing : forall e2 Γ var tv te e1,
  (var |=> tv; Γ) |= e2 : te ->
  MEmpty |= e1 : tv ->
       Γ |= ([var := e1] e2) : te.
Proof.
  induction e2; intros Γ var tv te e1 HT2 HT1;
  simpl; inversion HT2; subst;
  breakStrDec;
  eauto 6 using Pinclusion_typing, inclusion_shadow, inclusion_permute,
    PTyping, Ptyping_empty, InNotEq.
  - assert (te = tv). { rewrite InEq in H1. congruence. }
      subst. eauto using Ptyping_empty.
Qed.


(*
** Evaluation steps for Lir expressions
*)
Reserved Notation "m '/' e --> m1 '/' e1"
(at level 40, e at level 39, m1 at level 39, e1 at level 39).
Reserved Notation "m '/' e --> 'fail'"
(at level 40, e at level 39).


Inductive pstep : PMem -> PE -> PMem -> PE -> Prop :=
| PStPlus1 : forall m e1 e2 m' e1',
    m / e1 --> m' / e1' ->
    m / PEPlus e1 e2 --> m' / PEPlus e1' e2
| PStPlus2 : forall m e1 e2 m' e2',
    PValue e1 ->
    m / e2 --> m' / e2' ->
    m /  PEPlus e1 e2 --> m' /  PEPlus e1 e2'
| PStPlus : forall m n1 n2,
    m /  PEPlus (PENum n1) (PENum n2) --> m /  PENum (n1 + n2)
| PStNew : forall m m' free T,
    (free, m') = PfreshT m ->
    m / PENew T --> m' / PETAddr free T
| PStGet1 : forall m e1 e2 m' e1',
    m /e1 --> m' /e1' ->
    m / PEGet e1 e2 --> m' / PEGet e1' e2
| PStGet2 : forall m e1 e2 m' e2',
    PValue e1 ->
    m /e2 --> m' /e2' ->
    m / PEGet e1 e2 --> m' / PEGet e1 e2'
| PStGet : forall m a idx v T,
    PCast (PqueryT a idx m) T = Some v ->
    m / PEGet (PETAddr a T) (PENum idx) --> m / v
| PStSet1 : forall m e1 e2 e3 m' e1',
    m / e1 --> m' / e1' ->
    m / PESet e1 e2 e3 --> m' / PESet e1' e2 e3
| PStSet2 : forall m e1 e2 e3 m' e2',
    PValue e1 ->
    m / e2 --> m' / e2' ->
    m / PESet e1 e2 e3 --> m' / PESet e1 e2' e3
| PStSet3 : forall m e1 e2 e3 m' e3',
    PValue e1 -> PValue e2 ->
    m / e3 --> m' / e3' ->
    m / PESet e1 e2 e3 --> m' / PESet e1 e2 e3'
| PStSet : forall m a idx v T (Vv : PValue v),
    PValue v ->  (* shouldn't be necessary, but otherwise it is shelved *)
    m / PESet (PETAddr a T) (PENum idx) v -->
            PUpdateT a (PToIndex idx) (PEV v Vv) m / PENil
| PStFun : forall m m' v b free T1 T2,
    (free, m') = PfreshF m v T1 b ->
    m / PEFun v T1 b T2 --> m' / PEFAddr free T1 T2
| PStFunapp1 : forall m e1 e2 m' e1',
    m / e1 --> m' / e1' ->
    m / PEApp e1 e2 --> m' / PEApp e1' e2
| PStFunapp2 : forall m e1 e2 m' e2',
    PValue e1 ->
    m / e2 --> m' / e2' ->
    m / PEApp e1 e2 --> m' / PEApp e1 e2'
| PStFunapp : forall m a var type body v v' T1 T2,
    PValue v ->
    (var, type, body) = PqueryF a m ->
    PCast v type = Some v' ->
    m / PEApp (PEFAddr a T1 T2) v --> m / PECast ([var := v'] body) T2
| PStCast1 : forall m e m' e' T,
    m / e --> m' / e' ->
    m / PECast e T --> m' / PECast e' T
| PStCast : forall m T v v',
    PValue v ->
    T <> PTStar ->
    PCast v T = Some v' ->
    m / PECast v T --> m / v'

where "m / e --> m1 / e1" := (pstep m e m1 e1).


(*
** Fail evaluation for Pallene expressions
*)
Inductive pstepF : PMem -> PE -> Prop :=
| PStPlus1F : forall m e1 e2,
    m / e1 --> fail ->
    m / PEPlus e1 e2 --> fail
| PStPlus2F : forall m e1 e2,
    PValue e1 ->
    m / e2 --> fail ->
    m /  PEPlus e1 e2 --> fail
| PStGet1F : forall m e1 e2,
    m /e1 --> fail ->
    m / PEGet e1 e2 --> fail
| PStGet2F : forall m e1 e2,
    PValue e1 ->
    m /e2 --> fail ->
    m / PEGet e1 e2 --> fail
| PStGetF : forall m a idx T,
    PCast (PqueryT a idx m) T = None ->
    m / PEGet (PETAddr a T) (PENum idx) --> fail
| PStSet1F : forall m e1 e2 e3,
    m / e1 --> fail ->
    m / PESet e1 e2 e3 --> fail
| PStSet2F : forall m e1 e2 e3,
    PValue e1 ->
    m / e2 --> fail ->
    m / PESet e1 e2 e3 --> fail
| PStSet3F : forall m e1 e2 e3,
    PValue e1 -> PValue e2 ->
    m / e3 --> fail ->
    m / PESet e1 e2 e3 --> fail
| PStFunapp1F : forall m e1 e2,
    m / e1 --> fail ->
    m / PEApp e1 e2 --> fail
| PStFunapp2F : forall m e1 e2,
    PValue e1 ->
    m / e2 --> fail ->
    m / PEApp e1 e2 --> fail
| PStFunappF : forall m a var type body v T1 T2,
    PValue v ->
    (var, type, body) = PqueryF a m ->
    PCast v type = None ->
    m / PEApp (PEFAddr a T1 T2) v --> fail
| PStCast1F : forall m t e,
    m / e --> fail ->
    m / PECast e t --> fail
| PStCastF : forall m T v,
    PValue v ->
    PCast v T = None ->
    m / PECast v T --> fail

 where "m / e --> 'fail'" := (pstepF m e)
.


Lemma ValueNormal : forall v m,
  PValue v ->
  ~exists e' m', m / v --> m' / e'.
Proof.
  intros * HV [e' [m' H]].
  induction H; inversion HV; subst; eauto.
Qed.

Lemma ValueNormalF : forall v m,
  PValue v ->
  ~m / v --> fail.
Proof.
  intros * HV HF.
  induction HF; inversion HV; subst; eauto.
  specialize (CastToStar v) as [? ?].
  congruence.
Qed.



(*
** Ensures that all elements of tables and all "functions" in a
** memory are well typed.
*)
Inductive Pmem_correct : PMem -> Prop :=
| PMCE : Pmem_correct PEmptyMem
| PMCT : forall a idx v m T,
     MEmpty |= PEV2Val v : T ->
     Pmem_correct m ->
     Pmem_correct (PUpdateT a idx v m)
| PMCF : forall a var type body m T,
     var |=> type; MEmpty |= body : T ->
     Pmem_correct m ->
     Pmem_correct (PUpdateF a var type body m)
.


(*
** All expressions stored in memory tables are values
*)
Lemma PMCValue : forall m a n, PValue (PqueryT a n m).
Proof.
  intros.
  induction m; eauto using PValue.
  destruct p. simpl.
  breakIndexDec; trivial.
Qed.


(*
** All expressions stored in a table of a correct memory are
** well typed
*)
Lemma PMCTy : forall m a n Γ,
    Pmem_correct m ->
    exists T, Γ |= (PqueryT a n m) : T.
Proof.
  intros * H.
  induction H; trivial.
  - eauto using typing_empty, PTyping.
  - simpl. breakIndexDec; subst; eauto using Ptyping_empty.
Qed.


(*
** All functions stored in a correct memory have correct types.
*)
Lemma PMCTyF : forall m a var type body Γ,
    (var, type,  body) = PqueryF a m ->
    Pmem_correct m ->
    exists T, var |=> type; Γ |= body : T.
Proof.
  intros * HEq HMC.
  induction HMC; eauto.
  - simpl in HEq. injection HEq; intros; subst.
    eauto using PTyping.
  - simpl in HEq. breakIndexDec; eauto.
    injection HEq; intros; subst.
    eauto using Pinclusion_typing, inclusion_update, inclusion_empty.
Qed.


(*
** Table allocation preserves memory correctness
*)
Lemma Pmem_correct_freshT : forall m m' free,
  Pmem_correct m -> (free,m') = PfreshT m -> Pmem_correct m'.
Proof.
  unfold freshT. intros m m' free Hmc Heq. inversion Heq.
  eauto using Pmem_correct, PTyping.
Qed.


(*
** Function allocation preserves memory correctness
*)
Lemma Pmem_correct_freshF : forall m m' var T1 T2 body free,
  var |=> T1; MEmpty |= body : T2 ->
  Pmem_correct m ->
  (free,m') = PfreshF m var T1 body ->
  Pmem_correct m'.
Proof.
  unfold PfreshF. intros * HTy Hmc Heq.
  inversion Heq; subst.
  eauto using Pmem_correct.
Qed.


(*
** Executing an evaluation step preserves memory
** correctness
*)
Lemma PmemPreservation : forall (m m' : PMem) e e' t,
  Pmem_correct m ->
  MEmpty |= e : t ->
  m / e --> m' / e' ->
  Pmem_correct m'.
Proof.
  intros m m' e e' t HMC HTy Hst.
  generalize dependent m'.
  generalize dependent e'.
  remember MEmpty as Γ.
  induction HTy; intros e' m' Hst; inversion Hst; subst;
  eauto using Pmem_correct_freshT, Pmem_correct_freshF, Pmem_correct.
Qed.


(*
** Preservation of types for Pallene expressions
*)
Lemma PexpPreservation : forall m e t m' e',
  Pmem_correct m ->
  MEmpty |= e : t ->
  m / e --> m' / e' ->
  MEmpty |= e' : t.
Proof.
  intros m e t m' e' Hmc HT.
  generalize dependent m'.
  generalize dependent e'.
  remember MEmpty as Γ.
  induction HT; intros e' m' Hst; inversion Hst; subst;
  eauto using PTyping, PMCTy, PMCTyF, Psubst_typing, CastEqType.
  - inversion HT1; subst.
    assert (PValue (PqueryT a idx m')) by eauto using PMCValue.
    specialize (PMCTy m' a idx MEmpty Hmc) as [T' ?].
    eauto using CastEqType.
  - inversion HT1; subst.
    specialize (PMCTyF m' a var type body MEmpty H3 Hmc) as [T' ?].
    eauto using CastEqType, CastValue, PTyCast, Psubst_typing.
Qed.


Ltac openCanonicValue rule :=
  repeat match goal with
    | [ Ht : MEmpty |= ?e : _,
        Hv : PValue ?e |- _] =>
          eapply rule in Ht; trivial; decompose [ex or and] Ht; clear Ht
    end.

Ltac dostep :=
  right; only 1: (right; eauto using pstep); left;  eauto using pstepF.


(*
** Progress for Pallene terms
*)
Theorem Progress : forall m e t,
    MEmpty |= e : t  ->
    PValue e \/
    (m / e --> fail \/ exists m' e', m / e --> m' / e').
Proof.
  intros m e t Hty.
  remember MEmpty as Γ eqn:Heq.
  generalize dependent m.
  induction Hty; intros m; subst;

  (* handle values *)
    try (left; auto using PValue; fail);

  (* handle variables (no variables in an empty environment) *)
  try match goal with
  | [ H: In MEmpty _ = Some _ |- _] => inversion H
  end;

  (* instantiate and break induction hypotheses *)
  repeat match goal with
    | [H: ?E = ?E -> _ |- _] =>
      specialize (H eq_refl m) as [? | [? | [? [? ?]]]]
  end;

  (* instantiate canonic forms *)
  openCanonicValue ValInt;
  openCanonicValue ValArr;
  openCanonicValue ValFun;
  subst;

  (* handle fails *)
  try (eauto using pstepF; fail);

  (* handle easy step cases *)
  try (unshelve (right; right; subst; eauto using pstep); trivial; fail).

  (* Each of the next cases needs some very specific destructs *)

  - (* New *)
    pose (PfreshT m) as P. destruct P eqn:?;
    dostep.

  - (* Get *)
    destruct (PCast (PqueryT x0 x m) T) eqn:?; subst;
    dostep.

  - (* Fun *)
    pose (PfreshF m var Tvar body) as P; destruct P eqn:?;
    dostep.

  - (* App *)
    pose (PqueryF x m) as P. destruct P as [[? ?] ?] eqn:?; subst.
    destruct (PCast e2 p) eqn:?;
    dostep.

  - (* Cast *)
    destruct (dec_TP T2 PTStar) eqn:?; subst.
    + (* upcast *) left. eauto using PValue.
    + (* downcast *) destruct (PCast e T2) eqn:?;
      dostep.

Qed.

