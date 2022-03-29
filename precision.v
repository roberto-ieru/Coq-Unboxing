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


(*
** Precision of types
*)
Inductive TPrecision : IRType -> IRType -> Prop :=
| PRNil : IRTNil <| IRTNil
| PRInt : IRTInt <| IRTInt
| PRTbl : IRTTbl <| IRTTbl
| PRFun : IRTFun <| IRTFun
| TPStar : forall t, t <| IRTStar

  where "x '<|' y" := (TPrecision x y).


(*
** Type precision is reflexive
*)
Lemma TPrecisionRefl: forall t, t <| t.
Proof. intros t. destruct t; auto using TPrecision. Qed.


(*
** Type precision is transitive
*)
Lemma TPrecisionTrans: forall t1 t2 t3,
  t1 <| t2 -> t2 <| t3 -> t1 <| t3.
Proof.
  intros * H12 H23.
  destruct H12; auto using TPrecision.
  inversion H23; subst; auto using TPrecision.
Qed.


(*
** Type precision is assymetric
*)
Lemma TPrecisionAsym : forall t1 t2,
  t1 <| t2 -> t2 <| t1 -> t1 = t2.
Proof.
  intros t1 t2 H12.
  destruct H12; intros H21; trivial; inversion H21; subst; auto.
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


(*
** '*' is the largest type
*)
Lemma NoneBiggerThanStar : forall t, IRTStar <| t -> IRTStar = t.
Proof.
  intros t H.
  destruct t; inversion H; trivial.
Qed.


Inductive TPrecOption : option IRType -> option IRType -> Prop :=
| TPrecN : TPrecOption None None
| TPrecS : forall t1 t2, t1 <| t2 -> TPrecOption (Some t1) (Some t2)
.


(*
** Environment precision
*)
Definition EnvComp (Γ1 Γ2 : IREnvironment) : Prop :=
    forall var, TPrecOption (In Γ1 var) (In Γ2 var).


Infix "<E|" := EnvComp (at level 70).


(*
** Environment precision is reflexive
*)
Lemma EnvCompRefl : forall Γ, Γ <E| Γ.
Proof.
  unfold EnvComp.
  intros.
  destruct (In Γ var); auto using TPrecOption, TPrecisionRefl.
Qed.


(*
** Extending environments preserve precisions
*)
Lemma EnvCompExt : forall Γ1 Γ2 var t,
    Γ1 <E| Γ2 -> (var |=> t; Γ1) <E| (var |=> t; Γ2).
Proof.
  unfold EnvComp.
  intros.
  simpl.
  destruct (string_dec var0 var); subst;
  auto using TPrecOption, TPrecisionRefl.
Qed.


(*
** Environment precision is transitive
*)
Lemma EnvCompTrans : forall Γ1 Γ2 Γ3,
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


(*
** Environments for precision
** (Pairs of environments)
*)
Inductive PEnvironment :=
| PEnv : forall Γ1 Γ2, Γ1 <E| Γ2 -> PEnvironment.


(*
** Empty environment for precision
*)
Definition PEmpty : PEnvironment.
refine (PEnv MEmpty MEmpty _).
  unfold EnvComp.
  intros. simpl. constructor.
Defined.


(*
** Projection 1
*)
Definition PEnv1 (Γ : PEnvironment) : IREnvironment :=
  match Γ with
  | PEnv Γ1 _ _ => Γ1
  end.


(*
** Projection 2
*)
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


(*
** Create a precision environment with two copies
** of a given environment
*)
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


(*
** How 'ExpandPEnv' affects the first environment
*)
Lemma Expand1 : forall Γ var t1 t2 H12,
    PEnv1 (ExpandPEnv Γ var t1 t2 H12) = (var |=> t1; PEnv1 Γ).
Proof. intros Γ. destruct Γ. trivial. Qed.


(*
** How 'ExpandPEnv' affects the second environment
*)
Lemma Expand2 : forall Γ var t1 t2 H12,
    PEnv2 (ExpandPEnv Γ var t1 t2 H12) = (var |=> t2; PEnv2 Γ).
Proof. intros Γ. destruct Γ. trivial. Qed.


Lemma Env2Env : forall Γ, PEnv1 (Env2P Γ) = Γ.
Proof. intros Γ. trivial. Qed.


(*
** Two PEnv are equivalent if their environments are equivalent
*)
Definition PEquiv (Γ Γ' : PEnvironment) : Prop :=
  (forall var, In (PEnv1 Γ) var = In (PEnv1 Γ') var) /\
  (forall var, In (PEnv2 Γ) var = In (PEnv2 Γ') var).


(*
** PEquiv is an equivalence relation
*)

Lemma PEquivRefl : forall Γ, PEquiv Γ Γ.
Proof.
  unfold PEquiv.
  intros Γ.
  intuition trivial.
Qed.

Lemma PEquivSym : forall Γ1 Γ2, PEquiv Γ1 Γ2 -> PEquiv Γ2 Γ1.
Proof.
  unfold PEquiv.
  intros Γ1 Γ2 H.
  intuition congruence.
Qed.

Lemma PEquivTrans : forall Γ1 Γ2 Γ3,
    PEquiv Γ1 Γ2 -> PEquiv Γ2 Γ3 -> PEquiv Γ1 Γ3.
Proof.
  unfold PEquiv.
  intros Γ1 Γ2 Γ3 H12 H23.
  intuition congruence.
Qed.


(*
** Shadowing a variable gives a result that is equivalent to
** one without the shadowed entry
*)
Lemma PEquivShadow : forall Γ var t0 t1 t2 t3 H12 H12' H03,
  PEquiv (ExpandPEnv Γ var t1 t2 H12)
         (ExpandPEnv (ExpandPEnv Γ var t0 t3 H03) var t1 t2 H12').
Proof.
  unfold PEquiv.
  intros *.
  destruct Γ. simpl.
  split; intros; breakStrDec.
Qed.

(*
** Changind the order of addition of two different variables gives
** equivalent results
*)
Lemma PEquivPermute : forall Γ var var' t1 t2 t1' t2' H12 H12' H12'' H12''',
  var <> var' ->
  PEquiv (ExpandPEnv (ExpandPEnv Γ var t1 t2 H12) var' t1' t2' H12')
         (ExpandPEnv (ExpandPEnv Γ var' t1' t2' H12'') var t1 t2 H12''').
Proof.
  unfold PEquiv.
  intros *.
  destruct Γ. simpl.
  split; intros; breakStrDec.
Qed.


(*
** Expanding environments with the same element preserves
** equivalence.
*)
Lemma ExpandEquiv : forall Γ1 Γ2 var t1 t2 P1 P2,
    PEquiv Γ1 Γ2 ->
    PEquiv (ExpandPEnv Γ1 var t1 t2 P1) (ExpandPEnv Γ2 var t1 t2 P2).
Proof.
  unfold PEquiv.
  intros * HPE.
  repeat rewrite Expand1 in *.
  repeat rewrite Expand2 in *.
  simpl.
  split; intros; breakStrDec.
Qed.


(*
** Expanding and duplicating commute (up to equivalence)
*)
Lemma Expand2P : forall Γ var t,
    PEquiv (Env2P (var |=> t; Γ))
            (ExpandPEnv (Env2P Γ) var t t (TPrecisionRefl t)).
Proof.
  intros Γ var t.
  unfold PEquiv.
  simpl.
  split; intros; breakStrDec.
Qed.


(*
** The Precision relation
*)
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

(* Γ⊑, x : σ ⊑ τ ⊢ d₂ ⊑ e₂ : σ′ ⊑ τ′    Γ⊑ ⊢ d₁ ⊑ e₁ : σ ⊑ τ
   -------------------------------------------------------
   Γ⊑ ⊢ let x:σ = d₁ in d₂ ⊑ let x:τ = e₁ in e₂ : σ′ ⊑ τ′	*)
| PLet : forall Γ var d1 t1 d2 t2 b1 t1' b2 t2' H12,
    Precision (ExpandPEnv Γ var t1 t2 H12) b1 t1' b2 t2' ->
    Precision Γ d1 t1 d2 t2 ->
    Precision Γ (IRELet var t1 d1 b1) t1' (IRELet var t2 d2 b2) t2'

(* Γ⊑, x : * ⊑ * ⊢ d ⊑ e : * ⊑ *
   --------------------------------
   Γ⊑ ⊢ (λx.d) ⊑ (λx.e) : fun ⊑ fun	*)
| PFun : forall Γ var d1 d2,
    Precision (ExpandPEnv Γ var IRTStar IRTStar (TPrecisionRefl IRTStar))
                 d1 IRTStar d2 IRTStar ->
    Precision Γ (IREFun var d1) IRTFun
                (IREFun var d2) IRTFun

(* Γ⊑ ⊢ d₁ ⊑ e₁ : fun ⊑ fun    Γ⊑ ⊢ d₂ ⊑ e₂ : * ⊑ *
  -------------------------------------------------
  Γ⊑ ⊢ d₁(d₂) ⊑ e₁(e₂) : * ⊑ *	*)
| PFunApp : forall Γ f1 v1 f2 v2,
    Precision Γ v1 IRTStar v2 IRTStar ->
    Precision Γ f1 IRTFun f2 IRTFun ->
    Precision Γ (IREApp f1 v1) IRTStar (IREApp f2 v2) IRTStar

(* Γ⊑ ⊢ d ⊑ e : t ⊑ g
   ----------------------------------
   Γ⊑ ⊢ d ⊑ box[g](e) : t ⊑ ★	*)
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
   Γ⊑ ⊢ d ⊑ unbox[g](e) : t ⊑ g	*)
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


Module Examples.

Definition B10 := (IREBox TgInt (IRENum 10)).

Definition UB10 := IREUnbox TgInt B10.

Example example1 : Precision PEmpty (IRENum 10) IRTInt UB10 IRTInt.
  eauto using Precision, TPrecisionRefl.
Qed.

Example example2 : ~ Precision PEmpty UB10 IRTInt (IRENum 10) IRTInt.
  intros HF.
  inversion HF.
Qed.

Example example3 : Precision PEmpty UB10 IRTInt B10 IRTStar.
  eauto using Precision.
Qed.

Example example4 : exists e1 t1 e2 t2,
    Precision PEmpty e1 t1 e2 t2 /\ Value e1 /\ ~Value e2.
  eexists; eexists; eexists; eexists.
  split; try split.
  - apply example1.
  - eauto using Value.
  - intros Hcontra. inversion Hcontra.
Qed.

Example example5 : exists e1 t1 e2 t2,
    Precision PEmpty e1 t1 e2 t2 /\ Value e2 /\ ~Value e1.
  eexists; eexists; eexists; eexists.
  split; try split.
  - apply example3.
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
    PEquiv Γ Γ' -> Pinclusion Γ Γ'.
Proof.
  intros * H.
  destruct H.
  unfold Pinclusion.
  intuition congruence.
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


(*
** Precision is preserved if we extend PEnv
** with extra variables
*)
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


(*
** Precision is preserved if we replace PEnv
** with an equivalent one.
*)
Lemma PrecisionIrrel : forall Γ1 Γ2 e1 t1 e2 t2,
   PEquiv Γ1 Γ2 ->
   Precision Γ1 e1 t1 e2 t2 ->
   Precision Γ2 e1 t1 e2 t2.
Proof.
  eauto using PrecisionInclusion, PinclusionEquiv.
Qed.


(*
** The types in a precision relation must be
** in a precision relation too.
*)
Lemma PPT : forall Γ e1 t1 e2 t2,
    Precision Γ e1 t1 e2 t2 -> t1 <| t2.
Proof.
  intros Γ e1 t1 e2 t2 HP.
  induction HP; subst; eauto using TPrecision, TPrecisionRefl,
    PEnvIn.
Qed.


(*
** Precision subsumes typing for its first expression
*)
Lemma PrecisionType1: forall Γ e1 t1 e2 t2,
  Precision Γ e1 t1 e2 t2 -> (PEnv1 Γ) |= e1 : t1.
Proof.
  intros Γ e1 t1 e2 t2 HP.
  induction HP; subst; eauto using IRTyping;
  try match goal with
    [H: context [PEnv1 (ExpandPEnv _ _ _ _ _)] |- _] =>
      rewrite Expand1 in H end;
  eauto using IRTyping.
Qed.


(*
** Special case for the empty environment
*)
Lemma PrecisionType1Empty: forall e1 t1 e2 t2,
  Precision PEmpty e1 t1 e2 t2 -> MEmpty |= e1 : t1.
Proof.
  intros.
  replace MEmpty with (PEnv1 PEmpty) by trivial.
  eauto using PrecisionType1.
Qed.


(*
** Precision subsumes typing for its second expression
*)
Lemma PrecisionType2: forall Γ e1 t1 e2 t2,
  Precision Γ e1 t1 e2 t2 -> (PEnv2 Γ) |= e2 : t2.
Proof.
  intros Γ e1 t1 e2 t2 HP.
  induction HP; subst;
  try match goal with
    [H: context [PEnv2 (ExpandPEnv _ _ _ _ _)] |- _] =>
      rewrite Expand2 in H end;
  eauto using IRTyping.
Qed.


(*
** Special case for the empty environment
*)
Lemma PrecisionType2Empty: forall e1 t1 e2 t2,
  Precision PEmpty e1 t1 e2 t2 -> MEmpty |= e2 : t2.
Proof.
  intros.
  replace MEmpty with (PEnv2 PEmpty) by trivial.
  eauto using PrecisionType2.
Qed.


(*
** Precision is relfexive for well-typed terms
*)
Lemma PrecisionRefl: forall Γ e t,
    Γ |= e : t ->  Precision (Env2P Γ) e t e t.
Proof.
  intros * Hty.
  induction Hty; subst; eauto using Precision, UnboxCongruent, Expand2P,
      PrecisionIrrel.
Qed.


(*
** Precision subsumes typing
*)
Lemma PrecisionType: forall Γ e t,
    Γ |= e : t  <->  Precision (Env2P Γ) e t e t.
Proof.
  intros Γ e t.
  split; intros H.
  - induction H; eapply PrecisionRefl; eauto using IRTyping.
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


Lemma TagFun : forall g,
   Tag2Type g = IRTFun -> g = TgFun.
Proof.
  intros g. destruct g; try easy. Qed.


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


Lemma Env2DynEmpty : PEquiv (PEnvDyn MEmpty) PEmpty.
Proof. unfold PEquiv. split; trivial. Qed.


Lemma EquivDyn : forall Γ var t P,
  PEquiv (PEnvDyn (var |=> t; Γ))
          (ExpandPEnv (PEnvDyn Γ) var t IRTStar P).
Proof.
  intros.
  unfold PEquiv.
  split; intros; auto.
Qed.


Theorem DynLessPrecise : forall Γ e t,
  Γ |= e : t -> Precision (PEnvDyn Γ) e t (dyn e) IRTStar.
Proof.
  intros Γ e t H.
  induction H; simpl; eauto using Precision, TPrecision, InEnv2Dyn.
  - apply PVar; unfold PEnvDyn; simpl; eauto using InEnv2Dyn.
  - apply PLet with (TPStar t);
    eauto using PrecisionIrrel, EquivDyn.
  - apply PBoxR. apply PFun.
    eauto using PrecisionIrrel, EquivDyn.
Qed.


Theorem PrecDynEqual : forall Γ e1 t1 e2 t2,
    Precision Γ e1 t1 e2 t2 -> dyn e2 = dyn e1.
Proof.
  intros * HP. induction HP; simpl; congruence.
Qed.


(*
** (dyn e1) is larger than any expression larger than e1:
** forall e2, e1 ⊑ e2  ->  e2 ⊑ dyn (e1)
*)
Theorem DynMoreDyn : forall Γ e1 t1 e2 t2,
  Precision Γ e1 t1 e2 t2 ->
  Precision (PEnvDyn (PEnv2 Γ)) e2 t2 (dyn e1) IRTStar.
Proof.
  intros.
  replace (dyn e1) with (dyn e2) by eauto using PrecDynEqual.
  eauto using DynLessPrecise, PrecisionType2.
Qed.

