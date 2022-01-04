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


Lemma TPrecisionAsym : forall t1 t2,
  t1 <| t2 -> t2 <| t1 -> t1 = t2.
Proof.
  intros t1 t2 H12.
  induction H12; intros H21; trivial; inversion H21; subst;
  f_equal; auto.
Qed.


Lemma TPFun : forall t1 t2, IRTFun t1 t2 <| Tag2Type TgFun.
Proof.
  intros t1 t2.
  simpl. auto using TPrecision.
Qed.


Lemma GroundTop : forall t g1 g2,
  t <| Tag2Type g1 -> t <| Tag2Type g2 -> g1 = g2.
Proof.
  intros * H1 H2.
  destruct t; destruct g1; destruct g2; trivial;
  inversion H1; inversion H2.
Qed.


Lemma GroundFlat: forall g g', (Tag2Type g) <| (Tag2Type g') -> g = g'.
Proof.
  intros * H.
  eauto using GroundTop, TPrecisionRefl.
Qed.


Lemma NoneBiggerThanStar : forall t, IRTStar <| t -> IRTStar = t.
Proof.
  intros t H.
  destruct t; inversion H; trivial.
Qed.


Inductive TPrecOption : option IRType -> option IRType -> Prop :=
| TPrecN : TPrecOption None None
| TPrecS : forall t1 t2, t1 <| t2 -> TPrecOption (Some t1) (Some t2)
.


Definition EnvComp (Γ1 Γ2 : IREnvironment) : Prop :=
    forall var, TPrecOption (In Γ1 var) (In Γ2 var).


Infix "<E|" := EnvComp (at level 70).


Lemma EnvCompRefl : forall Γ, Γ <E| Γ.
Proof.
  unfold EnvComp.
  intros.
  destruct (In Γ var); auto using TPrecOption, TPrecisionRefl.
Qed.


Lemma EnvCompExt : forall Γ1 Γ2 var t,
    Γ1 <E| Γ2 -> var |=> t; Γ1 <E| var |=> t; Γ2.
Proof.
  unfold EnvComp.
  intros.
  simpl.
  destruct (string_dec var0 var); subst;
  auto using TPrecOption, TPrecisionRefl.
Qed.


Lemma EnvCompTrans : forall {Γ1} {Γ2} {Γ3},
    Γ1 <E| Γ2 -> Γ2 <E| Γ3 -> Γ1 <E| Γ3.
Proof.
  unfold EnvComp.
  intros Γ1 Γ2 Γ3 H12 H23 var.
  specialize (H12 var).
  specialize (H23 var).
  destruct (In Γ1 var);
  inversion H12; subst;
    match goal with
      [H: _ = In _ _ |- _] => rewrite <- H in *
    end;
  inversion H23; subst;
  constructor;
  eauto using TPrecisionTrans.
Qed.
  

Inductive PEnvironment :=
| PEnv : forall Γ1 Γ2, Γ1 <E| Γ2 -> PEnvironment.


Definition PEmpty : PEnvironment.
refine (PEnv MEmpty MEmpty _).
  unfold EnvComp.
  intros. simpl. constructor.
Defined.


Definition PEnv1 (Γ : PEnvironment) : IREnvironment :=
  match Γ with
  | PEnv Γ1 _ _ => Γ1
  end.


Definition PEnv2 (Γ : PEnvironment) : IREnvironment :=
  match Γ with
  | PEnv _ Γ2 _ => Γ2
  end.


Lemma PEnvIn : forall Γ var t1 t2,
    In (PEnv1 Γ) var = Some t1 ->
    In (PEnv2 Γ) var = Some t2 ->
    t1 <| t2.
Proof.
  intros Γ var t1 t2 H1 H2.
  destruct Γ.
  unfold EnvComp in e.
  simpl in *.
  specialize (e var).
  rewrite H1 in e.
  rewrite H2 in e.
  inversion e. trivial.
Qed.


Definition Env2P : IREnvironment -> PEnvironment.
refine (fun Γ => (PEnv Γ Γ _)).
  unfold EnvComp. intros var.
  destruct (In Γ var); auto using TPrecOption, TPrecisionRefl.
Defined.


Definition ExpandPEnv : PEnvironment -> string ->
    forall t1 t2, t1 <| t2 -> PEnvironment.
refine (fun Γ var t1 t2 H12 =>
    match Γ with
    | PEnv Γ1 Γ2 H12' => PEnv (var |=> t1; Γ1) (var |=> t2; Γ2) _
    end).
  unfold EnvComp; intros var'.
  simpl.
  destruct (string_dec var' var); auto using TPrecOption.
Defined.


Lemma Expand1 : forall Γ var t1 t2 H12,
    PEnv1 (ExpandPEnv Γ var t1 t2 H12) = (var |=> t1; PEnv1 Γ).
Proof. intros Γ. destruct Γ. trivial. Qed.


Lemma Expand2 : forall Γ var t1 t2 H12,
    PEnv2 (ExpandPEnv Γ var t1 t2 H12) = (var |=> t2; PEnv2 Γ).
Proof. intros Γ. destruct Γ. trivial. Qed.


Lemma Env2Env : forall Γ, PEnv1 (Env2P Γ) = Γ.
Proof. intros Γ. trivial. Qed.


Inductive PEEquiv : PEnvironment -> PEnvironment -> Prop :=
| PEE : forall Γ1 Γ2 P1 P2, PEEquiv (PEnv Γ1 Γ2 P1) (PEnv Γ1 Γ2 P2)
.


Lemma PEEquiv' : forall Γ1 Γ2,
  PEnv1 Γ1 = PEnv1 Γ2 -> PEnv2 Γ1 = PEnv2 Γ2 -> PEEquiv Γ1 Γ2.
Proof.
  intros Γ1 Γ2 H1 H2.
  destruct Γ1.
  destruct Γ2.
  simpl in *; subst.
  constructor.
Qed.


Lemma PEEquivRefl : forall Γ1 Γ2, PEEquiv Γ1 Γ2 -> PEEquiv Γ2 Γ1.
Proof.
  intros Γ1 Γ2 H.
  inversion H; constructor.
Qed.


Lemma PEEquivTrans : forall Γ1 Γ2 Γ3,
    PEEquiv Γ1 Γ2 -> PEEquiv Γ2 Γ3 -> PEEquiv Γ1 Γ3.
Proof.
  intros Γ1 Γ2 Γ3 H12 H23.
  inversion H12; subst.
  inversion H23; subst.
  constructor.
Qed.


Lemma ExpandEquiv : forall Γ1 Γ2 var t1 t2 P1 P2,
    PEEquiv Γ1 Γ2 ->
    PEEquiv (ExpandPEnv Γ1 var t1 t2 P1) (ExpandPEnv Γ2 var t1 t2 P2).
Proof.
  intros Γ1 Γ2 var t1 t2 P1 P2 HEE.
  destruct HEE. constructor.
Qed.


Lemma Expand2P : forall Γ var t,
    PEEquiv (Env2P (var |=> t; Γ))
            (ExpandPEnv (Env2P Γ) var t t (TPrecisionRefl t)).
Proof. intros Γ var t. constructor. Qed.


Lemma Expand12 : forall Γ1 Γ2 P12 var t1 t2 H12,
  exists P12', 
    ExpandPEnv (PEnv Γ1 Γ2 P12) var t1 t2 H12 =
    PEnv (var |=> t1; Γ1) (var |=> t2; Γ2) P12'.
Proof. intros. eexists. constructor. Qed.


Lemma PEEquivShadow : forall Γ Γ' var t0 t1 t2 t3 H0 H12,
    PEEquiv (ExpandPEnv Γ var t1 t2 H12) Γ' ->
    PEEquiv (ExpandPEnv Γ var t0 t3 H0)
            (ExpandPEnv Γ' var t0 t3 H0).
Proof.
  intros * HPE.
  destruct Γ. destruct Γ'.
  inversion HPE; subst.


Inductive Precision : PEnvironment -> IRE -> IRType ->
                                      IRE -> IRType -> Prop :=

| PNil : forall Γ, Precision Γ IRENil IRTNil IRENil IRTNil

(* Γ⊑ ∋ (x : σ ⊑ τ)
------------------
Γ⊑ ⊢ x ⊑ x : σ ⊑ τ	*)
| PVar : forall Γ var t1 t2,
    In (PEnv1 Γ) var = Some t1 ->
    In (PEnv2 Γ) var = Some t2 ->
    Precision Γ (IREVar var) t1 (IREVar var) t2

(* ----------------------
   Γ⊑ ⊢ n ⊑ n : int ⊑ int	*)
| PNum : forall Γ n, Precision Γ (IRENum n) IRTInt (IRENum n) IRTInt

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
| PFun : forall Γ var t1 t2 d1 t1' d2 t2' (H12 : t1 <| t2),
    Precision (ExpandPEnv Γ var t1 t2 H12) d1 t1' d2 t2' ->
    Precision Γ (IREFun var t1 d1) (IRTFun t1 t1')
                (IREFun var t2 d2) (IRTFun t2 t2')

(* Γ⊑ ⊢ d₁ ⊑ e₁ : fun[σ→σ′] ⊑ fun[τ→τ′]    Γ⊑ ⊢ d₂ ⊑ e₂ : σ ⊑ τ
  -------------------------------------------------------------
  Γ⊑ ⊢ d₁(d₂) ⊑ e₁(e₂) : σ′ ⊑ τ′	*)
| PFunApp : forall Γ f1 t1 t1' v1 f2 t2 t2' v2,
    Precision Γ v1 t1 v2 t2 ->
    Precision Γ f1 (IRTFun t1 t1') f2 (IRTFun t2 t2') ->
    Precision Γ (IREFunApp f1 v1) t1' (IREFunApp f2 v2) t2'

(* Γ⊑ ⊢ d ⊑ e : t ⊑ g
   ----------------------------------
   Γ⊑ ⊢ d ⊑ box[g](e) : g ⊑ ★	*)
| PBoxR : forall Γ d e t g,
    Precision Γ d t e (Tag2Type g) ->
    Precision Γ d t (IREBox g e) IRTStar

(* Γ⊑ ⊢ d ⊑ e : g ⊑ ★
   ----------------------------------
   Γ⊑ ⊢ box[g]d ⊑ e : ★ ⊑ ★	*)
| PBoxL : forall Γ d e g,
    Precision Γ d (Tag2Type g) e IRTStar ->
    Precision Γ (IREBox g d) IRTStar e IRTStar

(* Γ⊑ ⊢ d ⊑ e : ★ ⊑ ★
   ----------------------------------
   Γ⊑ ⊢ unbox[g](d) ⊑ e : g ⊑ *		*)
| PUnboxL : forall Γ d e g tg,
    tg = Tag2Type g ->
    Precision Γ d IRTStar e IRTStar ->
    Precision Γ (IREUnbox g d) tg e IRTStar

(* Γ⊑ ⊢ d ⊑ e : t ⊑ ★ , t ⊑ g
   ----------------------------------
   Γ⊑ ⊢ d ⊑ unbox[g](d) : t ⊑ g	*)
| PUnboxR : forall Γ d e t g tg,
    t <| (Tag2Type g) ->
    tg = Tag2Type g ->
    Precision Γ d t e IRTStar ->
    Precision Γ d t (IREUnbox g e) tg

.


(* Γ⊑ ⊢ d ⊑ e : g ⊑ g
   ----------------------------------
   Γ⊑ ⊢ box[g](d) ⊑ box[g](e) : ★ ⊑ ★	*)
Lemma BoxCongruent : forall Γ d e g,
    Precision Γ d (Tag2Type g) e (Tag2Type g) ->
    Precision Γ (IREBox g d) IRTStar (IREBox g e) IRTStar.
Proof. eauto using Precision. Qed.


(* Γ⊑ ⊢ d ⊑ e : ★ ⊑ ★
   ----------------------------------
   Γ⊑ ⊢ unbox[g](d) ⊑ unbox[g](e) : g ⊑ g	*)
Lemma UnboxCongruent: forall Γ d e g,
    Precision Γ d IRTStar e IRTStar ->
    Precision Γ (IREUnbox g d) (Tag2Type g) (IREUnbox g e) (Tag2Type g).
Proof. eauto using Precision, TPrecisionRefl. Qed.


Section Examples.

Definition B10 := (IREBox TgInt (IRENum 10)).

Definition UB10 := IREUnbox TgInt B10.

Example e1 : Precision PEmpty (IRENum 10) IRTInt UB10 IRTInt.
  eauto using Precision, TPrecisionRefl.
Qed.

Example e2 : ~ Precision PEmpty UB10 IRTInt (IRENum 10) IRTInt.
  intros HF.
  inversion HF.
Qed.

Example e3 : Precision PEmpty UB10 IRTInt B10 IRTStar.
  eauto using Precision.
Qed.

Example e4 : exists e1 t1 e2 t2,
    Precision PEmpty e1 t1 e2 t2 /\ Value e1 /\ ~Value e2.
  eexists; eexists; eexists; eexists.
  split; try split.
  - apply e1.
  - eauto using Value.
  - intros Hcontra. inversion Hcontra.
Qed.

Example e5 : exists e1 t1 e2 t2,
    Precision PEmpty e1 t1 e2 t2 /\ Value e2 /\ ~Value e1.
  eexists; eexists; eexists; eexists.
  split; try split.
  - apply e3.
  - eauto using Value.
  - intros Hcontra. inversion Hcontra.
Qed.


End Examples.


Definition Pinclusion (Γ Γ' : PEnvironment) : Prop :=
  inclusion (PEnv1 Γ) (PEnv1 Γ') /\ inclusion (PEnv2 Γ) (PEnv2 Γ').


Lemma PinclusionEmpty : forall Γ, Pinclusion PEmpty Γ.
Proof.
  intros. 
  unfold Pinclusion. simpl.
  auto using inclusion_empty.
Qed.


Lemma PinclusionEquiv : forall Γ Γ',
    PEEquiv Γ Γ' -> Pinclusion Γ Γ'.
Proof.
  intros * H.
  destruct H.  
  unfold EnvComp in P1.
  unfold Pinclusion.
  auto using inclusion_refl.
Qed.


Lemma PinclusionExpand : forall Γ Γ' var t1 t2 H12,
    Pinclusion Γ Γ' ->
    Pinclusion (ExpandPEnv Γ var t1 t2 H12)
               (ExpandPEnv Γ' var t1 t2 H12).
Proof.
  unfold Pinclusion.
  intros * HIn.
  destruct Γ. destruct Γ'.
  simpl in *. destruct HIn.
  auto using inclusion_update.
Qed.


Lemma ExpandShadow : forall Γ var t0 t1 t2 t3 H12 H12',
    Pinclusion
      (ExpandPEnv (ExpandPEnv Γ var t1 t2 H12) var t0 t3 H12')
      (ExpandPEnv Γ var t0 t3 H12').
Proof.
  intros.
  unfold Pinclusion.
  destruct Γ.
  simpl.
  auto using inclusion_shadow.
Qed.


Lemma PrecisionInclusion : forall Γ Γ' e1 t1 e2 t2,
    Pinclusion Γ Γ' ->
    Precision Γ e1 t1 e2 t2 ->
    Precision Γ' e1 t1 e2 t2.
Proof.
  intros * HI HP.
  generalize dependent Γ'.
  induction HP; intros; subst; eauto using Precision, PinclusionExpand.
  destruct HI.
  eauto using Precision.
Qed.


Lemma PrecisionIrrel : forall Γ1 Γ2 e1 t1 e2 t2,
   PEEquiv Γ1 Γ2 ->
   Precision Γ1 e1 t1 e2 t2 ->
   Precision Γ2 e1 t1 e2 t2.
Proof.
  eauto using PrecisionInclusion, PinclusionEquiv.
Qed.


Lemma PrecisionRefl: forall Γ e t,
    Γ |= e : t ->  Precision (Env2P Γ) e t e t.
Proof.
  intros Γ e t Hty.
  induction Hty; subst; eauto using Precision, UnboxCongruent, Expand2P,
      PrecisionIrrel.
Qed.


Lemma PPT : forall Γ e1 t1 e2 t2,
    Precision Γ e1 t1 e2 t2 -> t1 <| t2.
Proof.
  intros Γ e1 t1 e2 t2 HP.
  induction HP; subst; eauto using TPrecision, TPrecisionRefl,
    PEnvIn.
  - inversion IHHP2; subst; trivial.
Qed.


Lemma PrecisionType1: forall Γ e1 t1 e2 t2,
  Precision Γ e1 t1 e2 t2 -> (PEnv1 Γ) |= e1 : t1.
Proof.
  intros Γ e1 t1 e2 t2 HP.
  induction HP; subst; eauto using IRTyping.
  rewrite Expand1 in IHHP. eauto using IRTyping.
Qed.


Lemma PrecisionType1Empty: forall e1 t1 e2 t2,
  Precision PEmpty e1 t1 e2 t2 -> MEmpty |= e1 : t1.
Proof.
  intros.
  replace MEmpty with (PEnv1 PEmpty) by trivial.
  eauto using PrecisionType1.
Qed.


Lemma PrecisionType2: forall Γ e1 t1 e2 t2,
  Precision Γ e1 t1 e2 t2 -> (PEnv2 Γ) |= e2 : t2.
Proof.
  intros Γ e1 t1 e2 t2 HP.
  induction HP; subst; eauto using IRTyping.
  rewrite Expand2 in IHHP. eauto using IRTyping.
Qed.


Lemma PrecisionType2Empty: forall e1 t1 e2 t2,
  Precision PEmpty e1 t1 e2 t2 -> MEmpty |= e2 : t2.
Proof.
  intros.
  replace MEmpty with (PEnv2 PEmpty) by trivial.
  eauto using PrecisionType2.
Qed.


Lemma PrecisionType: forall Γ e t,
    Γ |= e : t  <->  Precision (Env2P Γ) e t e t.
Proof.
  intros Γ e t.
  split; intros H.
  - induction H; eauto using Precision, TPrecisionRefl.
    + assert (Γ |= IREFun var t body : IRTFun t t') by eauto using IRTyping.
      auto using PrecisionRefl.
    + assert (Γ |= IREUnbox tg e : t) by eauto using IRTyping.
      auto using PrecisionRefl.
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


Fixpoint Env2Dyn (Γ : IREnvironment) : IREnvironment :=
  match Γ with
  | MEmpty => MEmpty
  | MCons var _ Γ' => MCons var IRTStar (Env2Dyn Γ')
  end.


Lemma InEnv2Dyn : forall Γ var t,
    In Γ var = Some t ->
    In (Env2Dyn Γ) var = Some IRTStar.
Proof.
  intros.
  induction Γ; try easy.
  simpl in H.
  destruct (string_dec var s); subst; simpl.
  - destruct (string_dec s s); easy.
  - destruct (string_dec var s); auto.
Qed.


Lemma NInEnv2Dyn : forall Γ var,
    In Γ var = None -> In (Env2Dyn Γ) var = None.
Proof.
  intros.
  induction Γ; try easy.
  simpl in H.
  destruct (string_dec var s); subst; simpl.
  - destruct (string_dec s s); easy.
  - destruct (string_dec var s); try easy; auto.
Qed.


Definition PEnvDyn (Γ : IREnvironment) : PEnvironment.
refine (PEnv Γ (Env2Dyn Γ) _).
  unfold EnvComp. intros.
  destruct (In Γ var) eqn:?.
  - rewrite InEnv2Dyn with (t := i); auto using TPrecOption, TPrecision.
  - rewrite NInEnv2Dyn; auto using TPrecOption.
Defined.


Lemma EquivDyn : forall Γ var t P,
  PEEquiv (PEnvDyn (var |=> t; Γ))
          (ExpandPEnv (PEnvDyn Γ) var t IRTStar P).
Proof. intros. constructor. Qed.


Theorem PrecisionDyn : forall Γ e t,
  Γ |= e : t -> Precision (PEnvDyn Γ) e t (dyn e) IRTStar.
Proof.
  intros Γ e t H.
  induction H; simpl; eauto using Precision, TPrecision, InEnv2Dyn.
  - apply PVar; unfold PEnvDyn; simpl; eauto using InEnv2Dyn.
  - apply PBoxR. apply PFun with (TPStar t).
    eauto using PrecisionIrrel, EquivDyn.
Qed.




(*
Lemma HiEnv : forall Γ1 Γ2 Γ2' P12 P12' e1 t1 e2 t2 t2',
  Precision (PEnv Γ1 Γ2 P12) e1 t1 e2 t2 ->
  Γ2' |= e2 : t2' ->
  Γ2 <E| Γ2' ->
  Precision (PEnv Γ1 Γ2' P12') e1 t1 e2 t2'.
Proof.
  intros until t2'.
  intros HP.
  remember (PEnv Γ1 Γ2 P12) as Γ.
  generalize dependent P12.
  generalize dependent t2'.
  generalize dependent Γ2'.
  generalize dependent Γ2.
  generalize dependent Γ1.
  induction HP; intros Γ1 Γ2 Γ2' P12' ? P12 HEq HTy HLE;
  inversion HTy; subst;
  eauto using Precision, TPrecision.
  - apply PFun with (H12 := H12).
    specialize (Expand12 Γ1 Γ2' P12' var t1 t2 H12) as [xN HN].
    specialize (Expand12 Γ1 Γ2 P12 var t1 t2 H12) as [xN2 HN2].
    rewrite HN.
    eapply IHHP; eauto using EnvCompExt.
  - apply PFunApp with (t1 := t1) (t2 := t).
*)

(*
Lemma PrecisionTrans : forall Γ1 Γ2 Γ3 e1 t1 e2 t2 e3 t3 P12 P23,
  Precision (PEnv Γ1 Γ2 P12) e1 t1 e2 t2 ->
  Precision (PEnv Γ2 Γ3 P23) e2 t2 e3 t3 ->
  Precision (PEnv Γ1 Γ3 (EnvCompTrans P12 P23)) e1 t1 e3 t3.
Proof with eauto using Precision.
  intros Γ1 Γ2 Γ3 e1 t1 e2 t2 e3 t3 P12 P23 H12 H23.
  generalize dependent e3.
  generalize dependent t3.
  generalize dependent Γ3.
  remember (PEnv Γ1 Γ2 P12) as PΓ12.
  generalize dependent Γ2.
  generalize dependent Γ1.
  induction H12; intros.
  - 

  - (* var *) inversion H23; subst.
    + eauto using Precision.
    + inversion H23; subst.
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

