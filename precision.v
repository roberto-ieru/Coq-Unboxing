(*
** The Precision Relation for LIR
*)

Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.

Require Import LIR.maps.
Require Import LIR.lir.
Require Import LIR.dyn.



Reserved Infix "<|" (at level 80).


(*
** Precision of types
*)
Inductive TPrecision : IRType -> IRType -> Prop :=
| PRTag : forall tg, Tag2Type tg <| Tag2Type tg
| TPStar : forall t, t <| IRTStar

  where "x '<|' y" := (TPrecision x y).


(*
** Type precision is reflexive
*)
Lemma TPrecisionRefl: forall t, t <| t.
Proof. destruct t; auto using TPrecision. Qed.


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
  intros * H12.
  destruct H12; intros H21; trivial; inversion H21; subst; auto.
Qed.


(*
** Ground types have nothing below them.
*)
Lemma GroundFlat : forall t g,
    t <| Tag2Type g -> t = Tag2Type g.
Proof.
  intros * H. inversion H; trivial.
Qed.

Ltac GroundFlat :=
  repeat match goal with [H: ?T1 <| Tag2Type ?T2 |- _] =>
    match goal with
    | [H: T1 = Tag2Type T2 |- _] => fail 1
    | [ |- _] => specialize (GroundFlat _ _ H) as ?
    end
  end.


Lemma GroundTop : forall t g1 g2,
  t <| Tag2Type g1 -> t <| Tag2Type g2 -> g1 = g2.
Proof.
  intros. GroundFlat. congruence.
Qed.


(*
** '*' is the largest type
*)
Lemma NoneBiggerThanStar : forall t, IRTStar <| t -> IRTStar = t.
Proof.
  destruct t; inversion 1; trivial.
Qed.


(*
** Lift type precision to optional types.
*)
Inductive TPrecOption : option IRType -> option IRType -> Prop :=
| TPrecN : TPrecOption None None
| TPrecS : forall t1 t2, t1 <| t2 -> TPrecOption (Some t1) (Some t2)
.


(*
** Lift precision to Environments
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


(* Nothing is smaller than the empty environment *)
Lemma EnvCompEmpty : forall Γ, Γ <E| MEmpty -> Γ = MEmpty.
Proof.
  intros [ | var ? ?] H; trivial.
  exfalso.
  specialize (H var).
  erewrite InEq in H.
  inversion H.
Qed.


(*
** Environment precision is transitive
*)
Lemma EnvCompTrans : forall Γ1 Γ2 Γ3,
    Γ1 <E| Γ2 -> Γ2 <E| Γ3 -> Γ1 <E| Γ3.
Proof.
  unfold EnvComp.
  intros * H12 H23 var.
  specialize (H12 var).
  specialize (H23 var).
  destruct (In Γ1 var);
  inversion H12; subst;
    match goal with
      [H: _ = In _ _ |- _] => rewrite <- H in *
    end;
  inversion H23; subst;
  eauto using TPrecOption, TPrecisionTrans.
Qed.


(*
** Extending environments preserve precision
*)
Lemma EnvCompExt : forall Γ1 Γ2 var t1 t2,
    Γ1 <E| Γ2 ->
    t1 <| t2 ->
    (var |=> t1; Γ1) <E| (var |=> t2; Γ2).
Proof.
  unfold EnvComp.
  intros.
  breakStrDec;
  auto using TPrecOption, TPrecisionRefl.
Qed.


(*
** Precision for environments imply precision
** for their elements
*)
Lemma PEnvIn : forall Γ1 Γ2 var t1 t2,
    Γ1 <E| Γ2 ->
    In Γ1 var = Some t1 ->
    In Γ2 var = Some t2 ->
    t1 <| t2.
Proof.
  intros * HP H1 H2.
  specialize (HP var).
  rewrite H1 in HP.
  rewrite H2 in HP.
  inversion HP. trivial.
Qed.


(*
** Precision for environments imply precision for terms typed by them
*)
Lemma LELT : forall Γ1 Γ2 e t1 t2,
    Γ1 |= e : t1 ->
    Γ2 |= e : t2 ->
    Γ1 <E| Γ2 ->
    t1 <| t2.
Proof.
  intros * HT1.
  generalize dependent Γ2.
  induction HT1; inversion 1; subst;
    eauto using TPrecisionRefl, PEnvIn, EnvCompExt.
Qed.


(*
** The Precision relation for terms
*)

(*
** (Precision Γ e1 τ1 Δ e2 τ2) means Γ ⊢ e1 : τ1 ⊑ Δ ⊢ e2 : τ2.
** In words: the term e1 with type τ1 in the environment Γ is
** more (or equally) precise than the term e2 with type τ2
** in the environment Δ.
*)
Inductive Precision : IREnvironment -> IRE -> IRType ->
                      IREnvironment -> IRE -> IRType -> Prop :=

| PNil : forall Γ Δ, Γ <E| Δ -> Precision Γ IRENil IRTNil Δ IRENil IRTNil

| PVar : forall Γ Δ var t1 t2,
    Γ <E| Δ ->
    In Γ var = Some t1 ->
    In Δ var = Some t2 ->
    Precision Γ (IREVar var) t1 Δ (IREVar var) t2

| PNum : forall Γ Δ n, Γ <E| Δ -> Precision Γ (IRENum n) IRTInt Δ (IRENum n) IRTInt

| PPlus : forall Γ Δ d1 e1 d2 e2,
    Precision Γ d1 IRTInt Δ e1 IRTInt ->
    Precision Γ d2 IRTInt Δ e2 IRTInt ->
    Precision Γ (IREPlus d1 d2) IRTInt Δ (IREPlus e1 e2) IRTInt

| PNew : forall Γ Δ, Γ <E| Δ -> Precision Γ IRENew IRTTbl Δ IRENew IRTTbl

| PTAddr : forall Γ Δ addr, Γ <E| Δ -> Precision Γ (IRETAddr addr) IRTTbl
                                                 Δ (IRETAddr addr) IRTTbl

| PFAddr : forall Γ Δ addr, Γ <E| Δ -> Precision Γ (IREFAddr addr) IRTFun
                                                 Δ (IREFAddr addr) IRTFun

| PGet : forall Γ Δ d1 d2 i1 i2,
    Precision Γ d1 IRTTbl Δ d2 IRTTbl ->
    Precision Γ i1 IRTStar Δ i2 IRTStar ->
    Precision Γ (IREGet d1 i1) IRTStar Δ (IREGet d2 i2) IRTStar

| PSet : forall Γ Δ d1 d2 i1 i2 v1 v2,
    Precision Γ d1 IRTTbl Δ d2 IRTTbl ->
    Precision Γ i1 IRTStar Δ i2 IRTStar ->
    Precision Γ v1 IRTStar Δ v2 IRTStar ->
    Precision Γ (IRESet d1 i1 v1) IRTNil Δ (IRESet d2 i2 v2) IRTNil

| PLet : forall Γ Δ var d1 t1 d2 t2 b1 t1' b2 t2',
    Precision (var |=> t1; Γ) b1 t1' (var |=> t2; Δ) b2 t2' ->
    Precision Γ d1 t1 Δ d2 t2 ->
    Precision Γ (IRELet var t1 d1 b1) t1' Δ (IRELet var t2 d2 b2) t2'

| PFun : forall Γ Δ var d1 d2,
    Precision (var |=> IRTStar; Γ) d1 IRTStar (var |=> IRTStar; Δ) d2 IRTStar ->
    Γ <E| Δ ->
    Precision Γ (IREFun var d1) IRTFun Δ (IREFun var d2) IRTFun

| PApp : forall Γ Δ f1 v1 f2 v2,
    Precision Γ v1 IRTStar Δ v2 IRTStar ->
    Precision Γ f1 IRTFun Δ f2 IRTFun ->
    Precision Γ (IREApp f1 v1) IRTStar Δ (IREApp f2 v2) IRTStar

(* Note: in our particular case, t must be equal to g, because
   g is a ground type and there is no type strictly more precise
   than a ground type. *)
| PBoxR : forall Γ Δ d e t g,
    Precision Γ d t Δ e (Tag2Type g) ->
    Precision Γ d t Δ (IREBox g e) IRTStar

| PBoxL : forall Γ Δ d e g,
    Precision Γ d (Tag2Type g) Δ e IRTStar ->
    Precision Γ (IREBox g d) IRTStar Δ e IRTStar

| PUnboxL : forall Γ Δ d e g tg,
    tg = Tag2Type g ->
    Precision Γ d IRTStar Δ e IRTStar ->
    Precision Γ (IREUnbox g d) tg Δ e IRTStar

| PUnboxR : forall Γ Δ d e t g tg,
    t <| (Tag2Type g) ->
    tg = Tag2Type g ->
    Precision Γ d t Δ e IRTStar ->
    Precision Γ d t Δ (IREUnbox g e) tg

.


(*
** Boxing preserves precision.
*)
Lemma BoxCongruent : forall Γ Δ d e g,
    Precision Γ d (Tag2Type g) Δ e (Tag2Type g) ->
    Precision Γ (IREBox g d) IRTStar Δ (IREBox g e) IRTStar.
Proof. eauto using Precision. Qed.


(*
** Unboxing preserves precision.
*)
Lemma UnboxCongruent: forall Γ Δ d e g,
    Precision Γ d IRTStar Δ e IRTStar ->
    Precision Γ (IREUnbox g d) (Tag2Type g) Δ (IREUnbox g e) (Tag2Type g).
Proof. eauto using Precision, TPrecisionRefl. Qed.


(*
** Strip a term of all its boxes and unboxes
*)
Fixpoint Tbones (e : IRE) : IRE :=
  match e with
  | IRENil => e
  | IRENum n => e
  | IREPlus e1 e2 => IREPlus (Tbones e1) (Tbones e2)
  | IRENew => e
  | IRETAddr a => e
  | IREFAddr b => e
  | IREGet t i => IREGet (Tbones t) (Tbones i)
  | IRESet t i v => IRESet (Tbones t) (Tbones i) (Tbones v)
  | IREVar v => e
  | IRELet v t e1 e2 => IRELet v IRTStar (Tbones e1) (Tbones e2)
  | IREFun v b => IREFun v (Tbones b)
  | IREApp e1 e2 => IREApp (Tbones e1) (Tbones e2)
  | IREBox t e => Tbones e
  | IREUnbox t e => Tbones e
  end.


(*
** Equal bones is the same as equal 'dyn'
*)
Lemma DynBones : forall e1 e2, dyn e1 = dyn e2 <-> Tbones e1 = Tbones e2.
Proof.
  split; generalize dependent e2; induction e1; intros * H;
  induction e2;
  try (discriminate H);  (* eliminate cases with different structures *)
  try (injection H; intros; subst);  (* extract equality of fields *)
  eauto;  (* solve cases that don't need 'f_equal' *)
  simpl;
  (* break equalities up to 'dyn' or 'Tbones' *)
  repeat match goal with
    |[ |- dyn _ = dyn _] => idtac  (* ignore *)
    |[ |- Tbones _ = Tbones _] => idtac  (* ignore *)
    |[ |- _ _ = _ _] => f_equal  (* apply f_equal to all other equalities *)
  end;
  eauto.  (* solve the subcases *)
Qed.


(*
** Terms related by Precision differ only in boxes and unboxes
*)
Lemma EqBones : forall Γ Δ e1 t1 e2 t2,
  Precision Γ e1 t1 Δ e2 t2 -> Tbones e1 = Tbones e2.
Proof.
  induction 1; trivial; simpl; congruence.
Qed.


Module Examples.

Definition B10 := (IREBox TgInt (IRENum 10)).

Definition UB10 := IREUnbox TgInt B10.

(* 10 ⊑ unbox[int](box[int](10)) *)
Example example1 : Precision MEmpty (IRENum 10) IRTInt MEmpty UB10 IRTInt.
  eauto using Precision, TPrecisionRefl, EnvCompRefl.
Qed.

(* FALSE!  unbox[int](box[int](10)) ⊑ 10 *)
Example example2 : ~ Precision MEmpty UB10 IRTInt MEmpty (IRENum 10) IRTInt.
  inversion 1.
Qed.

(* unbox[int](box[int](10)) ⊑ box[int](10) *)
Example example3 : Precision MEmpty UB10 IRTInt MEmpty B10 IRTStar.
  eauto using Precision, EnvCompRefl.
Qed.

(*
  let x : int = 10 in x + 1
  let x : * = box 10 in unbox x + 1
*)
Definition X := "x":string.

Goal Precision MEmpty
  (IRELet X IRTInt (IRENum 10)
     (IREPlus (IREVar X) (IRENum 1)))  IRTInt
    MEmpty
  (IRELet X IRTStar (IREBox TgInt(IRENum 10))
     (IREPlus (IREUnbox TgInt (IREVar X)) (IRENum 1))) IRTInt.
Proof.
  unfold IRTInt.
  eapply PLet.
  - eapply PPlus;
    eauto using Precision, TPrecision, EnvCompRefl, EnvCompExt.
  - eauto using Precision, EnvCompRefl.
Qed.



(* Nothing is smaller than 10 *)
Goal forall E T,
  Precision MEmpty E T MEmpty (IRENum 10) IRTInt ->
  E = IRENum 10.
Proof.
  induction E; inversion 1; subst; trivial.
Qed.


(* Precision does not preserve values in any direction *)

Goal exists e1 t1 e2 t2,
    Precision MEmpty e1 t1 MEmpty e2 t2 /\ Value e1 /\ ~Value e2.
  eexists; eexists; eexists; eexists.
  repeat split.
  - apply example1.
  - eauto using Value.
  - intros Hcontra. inversion Hcontra.
Qed.

Goal exists e1 t1 e2 t2,
    Precision MEmpty e1 t1 MEmpty e2 t2 /\ Value e2 /\ ~Value e1.
  eexists; eexists; eexists; eexists.
  repeat split.
  - apply example3.
  - eauto using Value.
  - inversion 1.
Qed.


(* Types inside precision-related terms can go astray... *)
Goal Precision MEmpty (IREBox TgTbl (IREUnbox TgTbl B10)) IRTStar MEmpty B10 IRTStar.
Proof.
  eauto 6 using Precision, EnvCompRefl.
Qed.

(*
** ... which breaks some nice properties: although B10 is a maximum
** for 10 (everything larger than 10 is smaller than B10), 10 is not
** a minimum for B10...
*)
Goal ~ Precision MEmpty (IRENum 10) IRTInt
                 MEmpty (IREBox TgTbl (IREUnbox TgTbl B10)) IRTStar.
Proof.
  intro.
  repeat match goal with
  |[H: Precision _ _ _ _ _ _ |- _] => inversion H; subst; clear H
  |[H: _ <| Tag2Type _ |- _] => inversion H; subst; clear H
  end.
Qed.


(* a[10] *)
Definition get10 (a : nat) := IREGet (IRETAddr a) B10.

(* unbox[int](a[10]) ⊑ a[10] *)
Goal forall a,
    Precision MEmpty (IREUnbox TgInt (get10 a)) (Tag2Type TgInt)
              MEmpty (get10 a) IRTStar.
Proof.
  eauto 7 using Precision, EnvCompRefl.
Qed.


(* box[int](unbox[int](a[10])) ⊑ a[10] *)
Goal forall a, Precision
                 MEmpty (IREBox TgInt (IREUnbox TgInt (get10 a))) IRTStar
                 MEmpty (get10 a) IRTStar.
Proof.
  eauto 8 using Precision, EnvCompRefl.
Qed.


(* ~ a[10] ⊑ box[int](unbox[int](a[10])) *)
Goal forall a, ~ Precision
                   MEmpty (get10 a) IRTStar
                   MEmpty (IREBox TgInt (IREUnbox TgInt (get10 a))) IRTStar.
Proof.
  intros * ?.
  repeat match goal with
  |[H: Precision _ _ _ _ _ _ |- _] => inversion H; subst; clear H
  |[H: _ <| Tag2Type _ |- _] => inversion H; subst; clear H
  end.
Qed.


(*
** Next two examples show that Precision is not a proper order,
** but a preorder.
*)
Definition BUB10 := IREBox TgInt UB10.

(* box[int](unbox[int](box[int](10))) ⊑ box[int](10) : * ⊑ * *)
Example e6 : Precision MEmpty BUB10 IRTStar MEmpty B10 IRTStar.
  eauto 6 using Precision, EnvCompRefl.
Qed.

(* box[int](10) ⊑ box[int](unbox[int](box[int](10))) : * ⊑ * *)
Example e7 : Precision MEmpty B10 IRTStar MEmpty BUB10 IRTStar.
  eauto 6 using Precision, TPrecisionRefl, EnvCompRefl.
Qed.

End Examples.



(*
** For precision environments, equivalence implies inclusion
*)
Lemma PinclusionEquiv : forall (Γ Γ' : IREnvironment),
    map_eq Γ Γ' -> inclusion Γ Γ'.
Proof.
  intuition congruence.
Qed.


(*
** The environments in a precision relation must be
** in a precision relation too.
*)
Lemma PPE : forall Γ Δ e1 t1 e2 t2,
    Precision Γ e1 t1 Δ e2 t2 -> Γ <E| Δ.
Proof.
  induction 1; eauto using TPrecision, TPrecisionRefl, PEnvIn.
Qed.


(*
** The types in a precision relation must be in a precision relation too.
*)
Lemma PPT : forall Γ Δ e1 t1 e2 t2,
    Precision Γ e1 t1 Δ e2 t2 -> t1 <| t2.
Proof.
  induction 1; subst; eauto using TPrecision, TPrecisionRefl, PEnvIn.
Qed.


(*
** Special case of PEnvIn
*)
Lemma extend2Types : forall Γ Δ var t1 t1' t2 t2' b1 b2,
    Precision (var |=> t1; Γ) b1 t1' (var |=> t2; Δ) b2 t2' ->
    t1 <| t2.
Proof.
  intros.
  eapply PEnvIn with (var:=var); eauto using InEq, PPE.
Qed.


(*
** Inclusion preserves precision
*)
Lemma PrecisionInclusion : forall Γ1 Γ2 Δ1 Δ2 e1 t1 e2 t2,
    Precision Γ1 e1 t1 Δ1 e2 t2 ->
    inclusion Γ1 Γ2 ->
    inclusion Δ1 Δ2 ->
    Γ2 <E| Δ2 ->
    Precision Γ2 e1 t1 Δ2 e2 t2.
Proof.
  intros * HP.
  generalize dependent Γ2.
  generalize dependent Δ2.
  induction HP;
    eauto 8 using Precision, inclusion_update, EnvCompExt, PPT.
Qed.


Lemma PrecisionInclusionE : forall Γ Δ e1 t1 e2 t2,
    Precision MEmpty e1 t1 MEmpty e2 t2 ->
    Γ <E| Δ ->
    Precision Γ e1 t1 Δ e2 t2.
Proof.
  intros; eauto using PrecisionInclusion, inclusion_empty.
Qed.


(*
** Precision subsumes typing for its first term
*)
Lemma PrecisionType1: forall Γ Δ e1 t1 e2 t2,
  Precision Γ e1 t1 Δ e2 t2 -> Γ |= e1 : t1.
Proof.
  induction 1; eauto using IRTyping.
Qed.


(*
** Precision subsumes typing for its second term
*)
Lemma PrecisionType2: forall Γ Δ e1 t1 e2 t2,
  Precision Γ e1 t1 Δ e2 t2 -> Δ |= e2 : t2.
Proof.
  induction 1; eauto using IRTyping.
Qed.


(*
** Precision is relfexive for well-typed terms
*)
Lemma PrecisionRefl: forall Γ e t,
    Γ |= e : t ->  Precision Γ e t Γ e t.
Proof.
  induction 1; subst; eauto using Precision, UnboxCongruent, EnvCompRefl.
Qed.


(*
** Dynamisation of environments makes them less precise
*)
Lemma PEnvDyn : forall Γ, Γ <E| dynGamma Γ.
Proof.
  intros Γ var.
  destruct (In Γ var) eqn:?.
  - rewrite TP2TGammaIn with (T := i); auto using TPrecOption, TPrecision.
  - rewrite NTP2TGammaIn; auto using TPrecOption.
Qed.


(*
** Type erasure produces terms that are less precise than
** the original
*)
Theorem DynLessPrecise : forall Γ e t,
  Γ |= e : t -> Precision Γ e t (dynGamma Γ) (dyn e) IRTStar.
Proof.
  induction 1; simpl; eauto using Precision, TPrecision, TP2TGammaIn, PEnvDyn.
Qed.


(*
** Any pair of terms in a precision relation are equal
** up to type erasure.
*)
Theorem PrecDynEqual : forall Γ Δ e1 t1 e2 t2,
    Precision Γ e1 t1 Δ e2 t2 -> dyn e2 = dyn e1.
Proof.
  induction 1; simpl; congruence.
Qed.


(*
** Any star value less precise than a term is equal to the
** term type erasure.
*)
Theorem PrecDynEqualVal : forall e1 t1 e2,
    Value e2 ->
    Precision MEmpty e1 t1 MEmpty e2 IRTStar ->
    e2 = dyn e1.
Proof.
  intros.
  replace e2 with (dyn e2);
  eauto using PrecDynEqual, PrecisionType2, ValueStar, eq_sym.
Qed.


(*
** (dyn e1) is larger than any expression larger than e1:
** forall e2, e1 ⊑ e2  ->  e2 ⊑ dyn e1
*)
Theorem DynMoreDyn : forall Γ Δ e1 t1 e2 t2,
  Precision Γ e1 t1 Δ e2 t2 ->
  Precision Δ e2 t2 (dynGamma Δ) (dyn e1) IRTStar.
Proof.
  intros.
  replace (dyn e1) with (dyn e2) by eauto using PrecDynEqual.
  eauto using DynLessPrecise, PrecisionType2.
Qed.


Ltac NoneBiggerThanStar :=
  try match goal with
    |[H: Precision _ _ IRTStar _ _ (Tag2Type _) |- _] => apply PPT in H
  end;
  try match goal with
    |[H: IRTStar <| Tag2Type _ |- _] => apply NoneBiggerThanStar in H; discriminate
   end.


Lemma PrecTagGround : forall Γ Δ e1 t1 e2 t2,
    Precision Γ e1 (Tag2Type t1) Δ e2 (Tag2Type t2) ->
    t1 = t2.
Proof.
  intros * H. apply PPT in H. inversion H; subst; trivial.
Qed.


Lemma PrecValueGround : forall Γ Δ v1 v2 t,
    Precision Γ v1 (Tag2Type t) Δ v2 (Tag2Type t) ->
    Value v1 ->
    Value v2 ->
    v1 = v2.
Proof.
  inversion 1; subst; intros * V1 V2; trivial;
  try (inversion V1; fail); inversion V2.
Qed.


Lemma PrecValueStar : forall Γ Δ v1 v2,
    Precision Γ v1 IRTStar Δ v2 IRTStar ->
    Value v1 ->
    Value v2 ->
    v1 = v2.
Proof.
  inversion 1; subst; intros V1 V2; trivial;
  try (inversion V1; fail);
  try (inversion V2; fail);
  NoneBiggerThanStar.
  specialize (valbox Δ v2) as [? [? [? [? ?]]]]; eauto using PrecisionType2; subst.
  inversion H0; subst.
  - replace x0 with g in * by eauto using PrecTagGround.
    f_equal. eauto using PrecValueGround, valBoxVal.
  - inversion V1. inversion H6.
Qed.


(*
** Any two values related by precision with the same type are equal.
*)
Lemma PrecValue : forall Γ Δ v1 v2 t,
    Precision Γ v1 t Δ v2 t ->
    Value v1 ->
    Value v2 ->
    v1 = v2.
Proof.
  destruct t; eauto using PrecValueGround, PrecValueStar.
Qed.


(*
** Auxiliar lemma for precision transitivity
*)
Lemma PrecEnvL1 : forall Γ1 Γ1' Γ2 e1 e2 t1 t1' t2,
    Precision Γ1 e1 t1 Γ2 e2 t2 ->
    Γ1' <E| Γ1 ->
    Γ1' |= e1 : t1' ->
    Precision Γ1' e1 t1' Γ2 e2 t2.
Proof.
  intros * HP1.
  generalize dependent t1'.
  generalize dependent Γ1'.
  induction HP1; intros * HPE HT; GroundFlat;
    inversion HT; subst;
    eauto using Precision, EnvCompTrans, EnvCompExt, TPrecisionRefl,
                LELT, PrecisionType1.
Qed.


(*
** Auxiliar lemma for precision transitivity
*)
Lemma PrecEnvL2 : forall Γ1 Γ2 Γ2' e1 e2 t1 t2 t2',
    Precision Γ1 e1 t1 Γ2 e2 t2 ->
    Γ2 <E| Γ2' ->
    Γ2' |= e2 : t2' ->
    Precision Γ1 e1 t1 Γ2' e2 t2'.
Proof.
  intros * HP1.
  generalize dependent t2'.
  generalize dependent Γ2'.
  induction HP1; intros * HPE HT;

  (* Get cases when t2' must be '*' *)
  try match goal with
  [H1: Precision _ _ _ ?E1 ?e IRTStar,
   H2: ?E2 |= ?e : ?T,
   H3: ?E1 <E| ?E2 |- _] =>
     assert (IRTStar = T) by
       (eauto using NoneBiggerThanStar, LELT, PrecisionType2);
     subst
  end;

  inversion HT; subst;
    eauto using Precision, EnvCompTrans, EnvCompExt, TPrecisionRefl.
Qed.


(*
** For 'PrecTrans': generalize the term in the second Precision hypothesis
** and does an induction in that Precision.
*)
Ltac ind2 Γ3 e3 t3 :=
  match goal with
    |[H: Precision _ ?E _ Γ3 e3 t3 |- _] =>
      remember E as E' eqn:Heq;
      induction H; intros; GroundFlat; inversion Heq; subst;
      eauto using Precision, EnvCompTrans, PPT
  end.


(*
** A few cases need only this change of type to succeed.
*)
Ltac changeT T :=
  match goal with
    |[H: Precision _ _ IRTStar _ _ T |- _] =>
       replace T with IRTStar in * by (eauto using NoneBiggerThanStar, PPT);
       eauto using Precision
  end.


(*
** Precision for terms is transitive.
*)
Lemma PrecTrans : forall e2 Γ1 Γ2 Γ3 e1 e3 t1 t2 t3,
    Precision Γ1 e1 t1 Γ2 e2 t2 ->
    Precision Γ2 e2 t2 Γ3 e3 t3 ->
    Precision Γ1 e1 t1 Γ3 e3 t3.
Proof.

  intros * HP1.
  generalize dependent t3.
  generalize dependent e3.
  generalize dependent Γ3.
  induction HP1; intros * HP2;
    GroundFlat; subst;

    try (changeT t3);

    (* most cases can be solved by inversion on HP2 *)
    try (inversion HP2; subst;
         eauto using Precision, EnvCompTrans, PrecEnvL1, IRTyping;
         NoneBiggerThanStar;
         fail);

    (* some cases need induction on HP2 *)
    ind2 Γ3 e3 t3.

Qed.


