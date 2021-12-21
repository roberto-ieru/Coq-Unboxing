Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.
Require Import LIR.lir.
Require Import LIR.dyn.



(*
τ ⊑ ★

int ⊑ int

σ₁ ⊑ σ₂    τ₁ ⊑ τ₂
-----------------------
fun[σ₁→τ₁] ⊑ fun[σ₂→τ₂]

Lemma. ⊑ is reflexive and transitive.

Precision on terms of LIR.

Environments Γ⊑ ::= ∅ | Γ⊑, x : σ ⊑ τ

| ∅ |ₗ              =  ∅
| Γ⊑, x : σ ⊑ τ |ₗ  =  | Γ⊑ |ₗ, x : σ

| ∅ |ᵣ              =  ∅
| Γ⊑, x : σ ⊑ τ |ᵣ  =  | Γ⊑ |ᵣ, x : τ

| ∅ ∣ₗᵣ             =  ∅
| Γ, x : τ |ₗᵣ      =  | Γ |ₗᵣ, x : τ ⊑ τ 

The general relation is of the form Γ⊑ ⊢ d ⊑ e : σ ⊑ τ.

Lemma. If Γ⊑ ⊢ d ⊑ e : σ ⊑ τ then σ ⊑ τ and | Γ⊑ |ₗ ⊢ d : σ and | Γ⊑ |ᵣ ⊢ e : τ.

Γ⊑ ⊢ d ⊑ e : ★ ⊑ ★
----------------------------------    ???
Γ⊑ ⊢ box[g](d) ⊑ box[g](e) : g ⊑ g

Γ⊑ ⊢ d ⊑ e : ★ ⊑ ★
----------------------------
Γ⊑ ⊢ unbox[g](d) ⊑ e : g ⊑ ★

Γ⊑ ⊢ d ⊑ e : g ⊑ ★
----------------------------
Γ⊑ ⊢ d ⊑ unbox[g](e) : g ⊑ g

Γ⊑ ⊢ d ⊑ e : g ⊑ ★
--------------------------
Γ⊑ ⊢ box[g](d) ⊑ e : ★ ⊑ ★

*)


Reserved Infix "<|" (at level 80).


Inductive TPrecision : IRType -> IRType -> Prop :=
| PRNil : IRTNil <| IRTNil
| PRInt : IRTInt <| IRTInt
| PRTbl : IRTTbl <| IRTTbl
| PRFun : forall t1 t2 t1' t2',
    t1 <| t2 -> t1' <| t2' -> IRTFun t1 t1' <| IRTFun t2 t2'
| TPStar : forall t, t <| IRTStar

  where "x '<|' y" := (TPrecision x y).


Lemma TPrecisionRefl: forall t, t <| t.
Proof. intros t. induction t; auto using TPrecision. Qed.


Lemma TPrecisionTrans: forall t1 t2 t3,
  t1 <| t2 -> t2 <| t3 -> t1 <| t3.
Proof.
  intros t1 t2 t3 H12.
  generalize dependent t3.
  induction H12; intros ? H23; auto using TPrecision;
  inversion H23; subst; auto using TPrecision.
Qed.
  

Inductive PEnvEntry : Type :=
| pent : forall t1 t2, t1 <| t2 -> PEnvEntry
.

Definition PEnvironment := Map PEnvEntry.


Fixpoint PEnv1 (Γ : PEnvironment) : IREnvironment :=
  match Γ with
  | MEmpty => MEmpty
  | MCons k (pent t _ _) Γ' => MCons k t (PEnv1 Γ')
  end.


Lemma InP1 : forall Γ var t1 t2 p,
    In Γ var = Some (pent t1 t2 p) -> In (PEnv1 Γ) var = Some t1.
Proof.
  intros Γ var t1 t2 HIn.
  induction Γ.
  - discriminate.
  - destruct a. simpl in *.
    breakStrDec; try congruence; auto.
Qed.


Fixpoint PEnv2 (Γ : PEnvironment) : IREnvironment :=
  match Γ with
  | MEmpty => MEmpty
  | MCons k (pent _ t _) Γ' => MCons k t (PEnv2 Γ')
  end.


Lemma InP2 : forall Γ var t1 t2 p,
    In Γ var = Some (pent t1 t2 p) -> In (PEnv2 Γ) var = Some t2.
Proof.
  intros Γ var t1 t2 HIn.
  induction Γ.
  - discriminate.
  - destruct a. simpl in *.
    breakStrDec; try congruence; auto.
Qed.


Fixpoint Env2P (Γ : IREnvironment) : PEnvironment :=
  match Γ with
  | MEmpty => MEmpty
  | MCons k t Γ' => MCons k (pent t t (TPrecisionRefl t)) (Env2P Γ')
  end.


Lemma Env2Env : forall Γ, PEnv1 (Env2P Γ) = Γ.
Proof.
  intros Γ. induction Γ; trivial.
  simpl. congruence.
Qed.


Lemma InP12 : forall Γ var t,
    In Γ var = Some t ->
    In (Env2P Γ) var = Some (pent t t (TPrecisionRefl t)).
Proof.
  intros Γ var t HIn.
  induction Γ.
  - discriminate.
  - simpl in *.
    breakStrDec; auto.
    injection HIn; intros; subst; trivial.
Qed.


Lemma InE2PType : forall Γ var t1 t2 p,
  In (Env2P Γ) var = Some (pent t1 t2 p) -> t1 = t2.
Proof.
  intros Γ var t1 t2 p HIn.
  induction Γ.
  - discriminate.
  - simpl in *; breakStrDec; auto;
    injection HIn; intros; subst; trivial.
Qed.


Lemma InE2PVar : forall Γ var t1 t2 p,
  In (Env2P Γ) var = Some (pent t1 t2 p) -> In Γ var = Some t2.
Proof.
  intros Γ var t1 t2 p HIn.
  induction Γ.
  - discriminate.
  - simpl in *; breakStrDec; auto;
    injection HIn; intros; subst; trivial.
Qed.


Inductive Precision : PEnvironment -> IRE -> IRType ->
                                       IRE -> IRType -> Prop :=

| PNil : forall Γ, Precision Γ IRENil IRTNil IRENil IRTNil

(* Γ⊑ ∋ (x : σ ⊑ τ)
------------------
Γ⊑ ⊢ x ⊑ x : σ ⊑ τ	*)
| PVar : forall Γ var t1 t2 p,
    In Γ var = Some (pent t1 t2 p) ->
    Precision Γ (IREVar var) t1 (IREVar var) t2

(* ----------------------
   Γ⊑ ⊢ n ⊑ n : int ⊑ int	*)
| PInt : forall Γ n, Precision Γ (IRENum n) IRTInt (IRENum n) IRTInt

(* Γ⊑ ⊢ d₁ ⊑ e₁ : int ⊑ int   Γ⊑ ⊢ d₂ ⊑ e₂ : int ⊑ int
   ----------------------------------------------------
   Γ⊑ ⊢ d₁ + d₂ ⊑ e₁ + e₂ : int ⊑ int	*)
| PPlus : forall Γ d1 e1 d2 e2,
    Precision Γ d1 IRTInt e1 IRTInt ->
    Precision Γ d2 IRTInt e2 IRTInt ->
    Precision Γ (IREPlus d1 d2) IRTInt (IREPlus e1 e2) IRTInt

(* ----------------------
   Γ⊑ ⊢ {} ⊑ {} : tbl ⊑ tbl	*)
| PCnst : forall Γ, Precision Γ IRECnst IRTTbl IRECnst IRTTbl

(* ----------------------
   Γ⊑ ⊢ n ⊑ n : int ⊑ int	*)
| PAddr : forall Γ addr, Precision Γ (IREAddr addr) IRTTbl
                                     (IREAddr addr) IRTTbl

(* Γ⊑ ⊢ d₁ ⊑ e₁ : tbl ⊑ tbl   Γ⊑ ⊢ d₂ ⊑ e₂ : * ⊑ *
   ----------------------------------------------------
   Γ⊑ ⊢ d₁[d₂] ⊑ e₁[e₂] : * ⊑ *	*)
| PGet : forall Γ d1 d2 i1 i2,
    Precision Γ d1 IRTTbl d2 IRTTbl ->
    Precision Γ i1 IRTStar i2 IRTStar ->
    Precision Γ (IREGet d1 i1) IRTStar (IREGet d2 i2) IRTStar

| PSet : forall Γ d1 d2 i1 i2 v1 v2,
    Precision Γ d1 IRTTbl d2 IRTTbl ->
    Precision Γ i1 IRTStar i2 IRTStar ->
    Precision Γ v1 IRTStar v2 IRTStar ->
    Precision Γ (IRESet d1 i1 v1) IRTStar (IRESet d2 i2 v2) IRTStar

(* Γ⊑, x : σ ⊑ τ ⊢ d ⊑ e : σ′ ⊑ τ′
   ------------------------------------------------
   Γ⊑ ⊢ (λx:σ.d) ⊑ (λx:τ.e) : fun[σ→σ′] ⊑ fun[τ→τ′]	*)
| PFun : forall Γ var t1 t2 lt12 d1 t1' d2 t2',
    Precision (var |=> pent t1 t2 lt12; Γ) d1 t1' d2 t2' ->
    Precision Γ (IREFun var t1 d1) (IRTFun t1 t1')
                (IREFun var t2 d2) (IRTFun t2 t2')

(* Γ⊑ ⊢ d₁ ⊑ e₁ : fun[σ→σ′] ⊑ fun[τ→τ′]    Γ⊑ ⊢ d₂ ⊑ e₂ : σ ⊑ τ
  -------------------------------------------------------------
  Γ⊑ ⊢ d₁(d₂) ⊑ e₁(e₂) : σ′ ⊑ τ′	*)
| PFunApp : forall Γ f1 t1 t1' v1 f2 t2 t2' v2,
    Precision Γ f1 (IRTFun t1 t1') f2 (IRTFun t2 t2') ->
    Precision Γ v1 t1 v2 t2 ->
    Precision Γ (IREFunApp f1 v1) t1' (IREFunApp f2 v2) t2'

(* Γ⊑ ⊢ d ⊑ e : g ⊑ g
   ----------------------------------
   Γ⊑ ⊢ box[g](d) ⊑ box[g](e) : ★ ⊑ ★	*)
| PBox : forall Γ d e g,
    Precision Γ d (Tag2Type g) e (Tag2Type g) ->
    Precision Γ (IREBox g d) IRTStar (IREBox g e) IRTStar

(* Γ⊑ ⊢ d ⊑ e : g ⊑ g
   ----------------------------------
   Γ⊑ ⊢ d ⊑ box[g](e) : g ⊑ ★	*)
| PBoxR : forall Γ d e g,
    Precision Γ d (Tag2Type g) e (Tag2Type g) ->
    Precision Γ d (Tag2Type g) (IREBox g e) IRTStar

(* Γ⊑ ⊢ d ⊑ e : ★ ⊑ ★
   ----------------------------------
   Γ⊑ ⊢ unbox[g](d) ⊑ unbox[g](e) : g ⊑ g	*)
| PUnbox : forall Γ d e g,
    Precision Γ d IRTStar e IRTStar ->
    Precision Γ (IREUnbox g d) (Tag2Type g) (IREUnbox g e) (Tag2Type g)

(* Γ⊑ ⊢ d ⊑ e : ★ ⊑ ★
   ----------------------------------
   Γ⊑ ⊢ unbox[g](d) ⊑ e : g ⊑ *	*)
| PUnboxL : forall Γ d e g,
    Precision Γ d IRTStar e IRTStar ->
    Precision Γ (IREUnbox g d) (Tag2Type g) e IRTStar

(* Γ⊑ ⊢ d ⊑ e : g ⊑ ★
   ----------------------------------
   Γ⊑ ⊢ d ⊑ unbox[g](d) : g ⊑ g	*)
| PUnboxR : forall Γ d e g,
    Precision Γ d (Tag2Type g) e IRTStar ->
    Precision Γ d (Tag2Type g) (IREUnbox g e) (Tag2Type g)

.


Lemma PPT : forall Γ e1 t1 e2 t2, Precision Γ e1 t1 e2 t2 -> t1 <| t2.
Proof.
  intros Γ e1 t1 e2 t2 HP.
  induction HP; auto using TPrecision, TPrecisionRefl.
  - inversion IHHP1; subst; trivial.
Qed.


Lemma PrecisionType1: forall Γ e1 t1 e2 t2,
  Precision Γ e1 t1 e2 t2 -> (PEnv1 Γ) |= e1 : t1.
Proof.
  intros Γ e1 t1 e2 t2 HP.
  induction HP; eauto using IRTyping, InP1.
Qed.


Lemma PrecisionType2: forall Γ e1 t1 e2 t2,
  Precision Γ e1 t1 e2 t2 -> (PEnv2 Γ) |= e2 : t2.
Proof.
  intros Γ e1 t1 e2 t2 HP.
  induction HP; eauto using IRTyping, InP2.
Qed.


Lemma PrecisionType: forall Γ e t,
    Γ |= e : t  <->  Precision (Env2P Γ) e t e t.
Proof.
  intros Γ e t.
  split; intros H.
  - induction H; eauto using Precision, InP12.
  - apply PrecisionType1 in H.
    rewrite Env2Env in H. trivial.
Qed.


Lemma NoTag2Star : forall g, Tag2Type g <> IRTStar.
Proof. destruct g; easy. Qed.


Ltac NoTag2Star :=
  try match goal with
    [H: IRTStar = Tag2Type _ |- _ ] => symmetry in H
  end;
  match goal with
    [H: Tag2Type _ = IRTStar |- _ ] =>
      apply NoTag2Star in H; exfalso; trivial
  end.


Lemma Tag2TypeInjective : forall g1 g2,
    Tag2Type g1 = Tag2Type g2 -> g1 = g2.
Proof.
  intros g1 g2. destruct g1; destruct g2; easy.
Qed.


Lemma TagInt : forall g,
   Tag2Type g = IRTInt -> g = TgInt.
Proof. intros g. destruct g; try easy. Qed.


Lemma TagFun : forall g t t',
   Tag2Type g = IRTFun t t' -> g = TgFun /\ t = IRTStar /\ t' = IRTStar.
Proof.
  intros g t t'.
  destruct g; try easy.
  intros H. simpl in H. injection H; intros; subst; intuition.
Qed.


Ltac EnvUnique :=
  match goal with 
  [ H1: In ?Γ ?var = _,
    H2: In ?Γ ?var = _ |- _ ] =>
    rewrite H1 in H2; injection H2; intros; subst
  end.

(*
Lemma PrecisionTrans : forall Γ e1 t1 e2 t2 e3 t3,
  Precision Γ e1 t1 e2 t2 ->
  Precision Γ e2 t2 e3 t3 ->
  Precision Γ e1 t1 e3 t3.
Proof with eauto using Precision.
  intros Γ e1 t1 e2 t2 e3 t3 H12 H23.
  generalize dependent e3.
  generalize dependent t3.
  induction H12; intros ? ? H23; try easy.
  - (* var *) inversion H23; subst.
    + EnvUnique...
    + inversion H0; subst. 
      EnvUnique...
      NoTag2Star.
  - (* plus *) inversion H23; subst...
    apply TagInt in H; subst g.
    inversion H2; subst...
  - (* get *) inversion H23; subst...
    NoTag2Star.
  - (* set *) inversion H23; subst...
    NoTag2Star.
  - (* fun *) inversion H23; subst; shelve. 
  - (* funapp *) inversion H23; subst.
    + eapply PFunApp.
      apply IHPrecision1.

  inversion H23; subst;
  try match goal with 
  [ H1: In ?Γ ?var = _,
    H2: In ?Γ ?var = _ |- _ ] => idtac H1 H2;
    rewrite H1 in H2; injection H2; intros; subst
  end;
  try NoTag2Star;
  eauto using Precision.
  7: { apply Tag2TypeInjective in H; subst.
       eapply PUnboxL. eapply IHPrecision.
       inversion H2; subst.
       + NoTag2Star.
       + 
  - apply PrecisionType1 in H23. inversion H23; subst.
    erewrite (InP1 _ var t1 (Tag2Type g)) in H3; trivial;
    inversion H3; subst; eauto using Precision.
  - assert (g = TgInt) by (destruct g; easy); subst.
    eapply PBoxR.
    inversion H2; subst; eauto using Precision.
  - admit.
  - apply TagFun in H. destruct H as [? [? ?]]; subst.
    eapply PBoxR.

  - apply Tag2TypeInjective in H; subst.
    eapply PBoxR.    
    inversion H2; subst; eauto using Precision;
    NoTag2Star.
  - eapply PUnboxL.
Qed.
*)


Fixpoint Env2Dyn (Γ : IREnvironment) : PEnvironment :=
  match Γ with
  | MEmpty => MEmpty
  | MCons k t Γ' => MCons k (pent t IRTStar (TPStar t)) (Env2Dyn Γ')
  end.


Lemma InEnv2Dyn : forall Γ var t,
  In Γ var = Some t ->
  In (Env2Dyn Γ) var = Some (pent t IRTStar (TPStar t)).
Proof.
  intros Γ var t H.
  induction Γ.
  - discriminate.
  - simpl in *.
    breakStrDec; auto.
    injection H; intros; subst; trivial.
Qed.


Lemma PrecisionDyn : forall Γ e t,
  Γ |= e : t -> Precision (Env2Dyn Γ) e t (dyn e) IRTStar.
Proof.
  intros Γ e t H.
  induction H; simpl.
  - replace IRTNil with (Tag2Type TgNil) by trivial.
    eauto using Precision.
  - eauto using Precision, InEnv2Dyn.
  - replace IRTInt with (Tag2Type TgInt) by trivial.
    eauto using Precision.
  - replace IRTInt with (Tag2Type TgInt) by trivial.
    apply PBoxR.
    apply PPlus;
    replace IRTInt with (Tag2Type TgInt) by trivial.
    + apply PUnboxR. trivial.
    + apply PUnboxR. trivial.
  - replace IRTTbl with (Tag2Type TgTbl) by trivial.
    eauto using Precision.
  - replace IRTTbl with (Tag2Type TgTbl) by trivial.
    eauto using Precision.
  - apply PGet; trivial.
    replace IRTTbl with (Tag2Type TgTbl) by trivial.
    apply PUnboxR. trivial.
  - apply PSet; trivial.
    replace IRTTbl with (Tag2Type TgTbl) by trivial.
    apply PUnboxR. trivial.
  - assert (Precision (Env2Dyn Γ) (IREFun var t body) (IRTFun t t')
                                  (IREFun var IRTStar (dyn body))
                                     (IRTFun IRTStar IRTStar)).
    { eauto using Precision. }
      
    
    


