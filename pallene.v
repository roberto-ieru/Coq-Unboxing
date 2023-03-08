Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.

Require Import LIR.maps.

Require LIR.lir.


(* Pallene types *)
Inductive PType : Set :=
| PTStar : PType
| PTNil : PType
| PTInt : PType
| PTArr : PType -> PType
| PTFun : PType -> PType -> PType
.


Lemma dec_TP : forall (t1 t2 : PType), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.


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
| PETAddr : lir.address -> PType -> PE
| PEFAddr : lir.address -> PType -> PType -> PE
| PEGet : PE -> PE -> PE
| PESet : PE -> PE -> PE -> PE
| PEVar : string -> PE
| PEApp :  PE -> PE -> PE
| PEFun : string -> PType -> PE -> PType -> PE
| PELet : string -> PType -> PE -> PE -> PE
| PECast : PE -> PType -> PE
.


(*
** Typing rules for λ-Pallene
*)
Reserved Notation "Γ '|p=' e ':' t"  (at level 40, no associativity,
                                     e at next level).

Inductive PTyping : PEnvironment -> PE -> PType -> Prop :=
| PTyNil : forall Γ, Γ |p= PENil : PTNil
| PTyInt : forall Γ n, Γ |p= PENum n : PTInt
| PTyVal : forall Γ var T,
    In Γ var = Some T ->
    Γ |p= PEVar var : T
| PTyPlus : forall Γ e1 e2,
    Γ |p= e1 : PTInt ->
    Γ |p= e2 : PTInt ->
    Γ |p= PEPlus e1 e2 : PTInt
| PTyNew : forall Γ T, Γ |p= PENew T : PTArr T
| PTyTAddr : forall Γ a T, Γ |p= PETAddr a T : PTArr T
| PTyFAddr : forall Γ a T1 T2, Γ |p= PEFAddr a T1 T2 : PTFun T1 T2
| PTyGet : forall Γ e1 T e2,
    Γ |p= e1 : PTArr T ->
    Γ |p= e2 : PTInt ->
    Γ |p= PEGet e1 e2 : T
| PTySet : forall Γ e1 T e2 e3,
    Γ |p= e1 : PTArr T ->
    Γ |p= e2 : PTInt ->
    Γ |p= e3 : T ->
    Γ |p= PESet e1 e2 e3 : PTNil
| PTyFun : forall Γ var Tvar body Tbody,
    (var |=> Tvar; Γ) |p= body : Tbody ->
    Γ |p= PEFun var Tvar body Tbody : PTFun Tvar Tbody
| PTyLet : forall Γ var Tvar init body Tbody,
    Γ |p= init : Tvar ->
    (var |=> Tvar; Γ) |p= body : Tbody ->
    Γ |p= PELet var Tvar init body : Tbody
| PTyApp : forall Γ e1 e2 T1 T2,
    Γ |p= e1 : PTFun T1 T2 ->
    Γ |p= e2 : T1 ->
    Γ |p= PEApp e1 e2 : T2
| PTyCast : forall Γ e T1 T2,
    Γ |p= e : T1 ->
    Γ |p= PECast e T2 : T2

where "Γ '|p=' e ':' t" := (PTyping Γ e t)
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
  | PELet var Tv init body =>
    match typeOf Γ init, typeOf (var |=> Tv; Γ) body with
    | Some Tv', Some Tb =>
        if dec_TP Tv Tv' then Some Tb else None
    | _, _ => None
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
Lemma typeOfCorrect' : forall Γ e T, Γ |p= e : T -> typeOf Γ e = Some T.
Proof.
  induction 1; try easy;
  simpl;
  repeat match goal with
  | [H: typeOf _ _ = Some _ |- _] => rewrite H; clear H
  | [ |- context [dec_TP ?V1 ?V2] ] => destruct (dec_TP V1 V2)
  end; easy.
Qed.


Ltac destTOf Γ e :=
    destruct (typeOf Γ e) as [[ | | | ? | ? ?] | ?] eqn:?; try easy.

Ltac destTOf' :=
  match goal with
  H: context [typeOf ?Γ ?e] |- _ => idtac e; destTOf Γ e
  end.


Ltac destTOf''' :=
  match goal with
  | H: context [match typeOf ?Γ ?e with Some _ => _ | None => _ end] |- _ =>
     idtac e; destruct (typeOf Γ e) eqn:?; try easy
  | H: context [match typeOf ?Γ ?e with Some _ => _ | _ => _ end] |- _ =>
     idtac e; destTOf Γ e
  end.

(*
** 'typeOf' is correct (part 2)
*)
Lemma typeOfCorrect'' : forall Γ e T, typeOf Γ e = Some T -> Γ |p= e : T.
Proof.
  intros * Heq.
  generalize dependent Γ.
  generalize dependent T.
  induction e; intros * Heq; subst;
  simpl in Heq; inversion Heq; subst; eauto using PTyping;
  try (destTOf Γ e1; destTOf Γ e2;
    inversion Heq; subst; eauto using PTyping; fail).
  - (* Set *)
    destTOf'.
    destTOf'.
    repeat destTOf'''.
    destruct (dec_TP p p0) eqn:?; try easy.
    inversion Heq; subst. eauto using PTyping.
  - (* App *)
    destTOf'.
    destTOf'''.
    destruct (dec_TP p p1) eqn:?; try easy.
    inversion Heq; subst. eauto using PTyping.
  - (* Fun *)
    destTOf'''.
    destruct (dec_TP p0 p1); subst; try discriminate.
    inversion Heq; subst. eauto using PTyping.
  - (* Let *)
    repeat destTOf'''.
    destruct (dec_TP p p0); subst; try easy.
    inversion Heq; subst. eauto using PTyping.
  - (* Cast *)
    destTOf'''.
    inversion Heq; subst. eauto using PTyping.
Qed.


(*
** Rules and algorithm agree
*)
Lemma typeOfCorrect : forall Γ e T, typeOf Γ e = Some T <-> Γ |p= e : T.
Proof. split; auto using typeOfCorrect', typeOfCorrect''. Qed.


(*
** Pallene types are unique
*)
Lemma PTypeUnique : forall Γ e t1 t2,
    Γ |p= e : t1 -> Γ |p= e : t2 -> t1 = t2.
Proof.
  intros * H1 H2.
  apply typeOfCorrect in H1.
  apply typeOfCorrect in H2.
  congruence.
Qed.


Lemma PinclusionType : forall Γ Γ' e T,
  Γ |p= e : T ->
  inclusion Γ Γ' ->
  Γ' |p= e : T.
Proof.
  intros * HTy HIn.
  generalize dependent Γ'.
  induction HTy; intros; eauto using PTyping, inclusion_update.
Qed.


Lemma PinclusionEmpty : forall Γ e T,
  MEmpty |p= e : T ->
  Γ |p= e : T.
Proof.
  eauto using PinclusionType, inclusion_empty.
Qed.


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
  MEmpty |p= v : PTStar ->
  exists v', v = PECast v' PTStar /\ PValue v'.
Proof.
  intros * HV HT. inversion HT; subst; inversion HV; subst; eauto.
Qed.

Lemma ValNil : forall v,
  PValue v ->
  MEmpty |p= v : PTNil ->
  v = PENil.
Proof.
  intros * HV HT. inversion HT; subst; inversion HV; subst; eauto.
Qed.

Lemma ValInt : forall v,
  PValue v ->
  MEmpty |p= v : PTInt ->
  exists n, v = PENum n.
Proof.
  intros * HV HT. inversion HT; subst; inversion HV; subst; eauto.
Qed.

Lemma ValArr : forall v T,
  PValue v ->
  MEmpty |p= v : PTArr T ->
  exists a, v = PETAddr a T.
Proof.
  intros * HV HT. inversion HT; subst; inversion HV; subst; eauto.
Qed.

Lemma ValFun : forall v T1 T2,
  PValue v ->
  MEmpty |p= v : PTFun T1 T2 ->
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
  MEmpty |p= e : T1 ->
  PCast e T2 = Some v ->
  MEmpty |p= v : T2.
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
  MEmpty |p= v : T ->
  PCast v T = Some v.
Proof.
  intros * HV HT.
  induction HV; inversion HT; trivial.
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


Definition PToIndex (n : nat) : lir.Index := lir.I n lir.TgInt.


Inductive PExpValue : Set :=
| PEV : forall e, PValue e -> PExpValue.


Ltac DExpValue := match goal with E: PExpValue |- _ => destruct E end.

Definition PEV2Val (me : PExpValue) : PE :=
  match me with
  | PEV v _ => v
  end.



Inductive PMem : Set :=
| PEmptyMem : PMem
| PUpdateT : lir.address -> lir.Index -> PExpValue -> PMem -> PMem
| PUpdateF : lir.address -> string -> PType -> PE -> PMem -> PMem.


(* [nil as *] *)
Definition NilStar : PE := PECast PENil PTStar.

(* Proof object that [nil as *] is a value *)
Definition NilStarVal : PValue NilStar := PVbox PENil PVnil.


Fixpoint PqueryT (a : lir.address) (idx : nat) (m : PMem) : PE :=
  match m with
  | PEmptyMem => NilStar
  | PUpdateT a' idx' e m' => if Nat.eq_dec a a' then
                           if lir.Index_dec (PToIndex idx) idx' then (PEV2Val e)
                           else PqueryT  a idx m'
                         else PqueryT  a idx m'
  | PUpdateF _ _ _ _ m' => PqueryT a idx m'
  end.


Fixpoint PqueryF (a : lir.address) (m : PMem) : (string * PType * PE) :=
  match m with
  | PEmptyMem => (""%string, PTStar,  NilStar)
  | PUpdateT a' _ _ m' => PqueryF a m'
  | PUpdateF a' var type body m' => if Nat.eq_dec a a' then (var, type,  body)
                                    else PqueryF a m'
  end.


Fixpoint Pfreshaux (m : PMem) : lir.address :=
  match m with
  | PEmptyMem => 1
  | PUpdateT _ _ _ m' => S (Pfreshaux m')
  | PUpdateF _ _ _ _ m' => S (Pfreshaux m')
  end.


Definition PfreshT (m : PMem) : (lir.address * PMem) :=
  let f := Pfreshaux m in
    (f, PUpdateT f (lir.I 0 lir.TgNil) (PEV NilStar NilStarVal) m).


Definition PfreshF (m : PMem) (v : string) (t : PType) (b : PE) :
             (lir.address * PMem) :=
  let f := Pfreshaux m in
    (f, PUpdateF f v t (PECast b PTStar) m).


Reserved Notation "'[' x ':=' s ']p' t" (at level 20, x constr).


Fixpoint substitution (var : string) (y : PE)  (e : PE) : PE :=
 match e with
 | PENil => e
 | PENum n => e
 | PEPlus e1 e2 => PEPlus ([var := y]p e1) ([var := y]p e2)
 | PENew _ => e
 | PETAddr a _ => e
 | PEFAddr a _ _ => e
 | PEGet e1 e2 => PEGet ([var := y]p e1) ([var := y]p e2)
 | PESet e1 e2 e3 => PESet ([var := y]p e1) ([var := y]p e2) ([var := y]p e3)
 | PEVar var' => if string_dec var var' then y else e
 | PEFun var' T1 body T2 => if string_dec var var' then e
                          else PEFun var' T1 ([var := y]p body) T2
 | PELet var' Tvar init body =>
     if string_dec var var'
       then PELet var' Tvar ([var := y]p init) body
       else PELet var' Tvar ([var := y]p init) ([var := y]p body)
 | PEApp e1 e2 => PEApp ([var := y]p e1) ([var := y]p e2)
 | PECast e T => PECast ([var := y]p e) T
end
where "'[' x ':=' s ']p' t" := (substitution x s t)
.


(*
** Extending an environment preserves typing
*)
Lemma Pinclusion_typing : forall Γ Γ' e te,
  inclusion Γ Γ' -> Γ |p= e : te -> Γ' |p= e : te.
Proof.
  intros * Hin Hty.
  generalize dependent Γ'.
  induction Hty; eauto using PTyping, inclusion_update.
Qed.


(*
** Particular case when extending the empty environment
*)
Lemma Ptyping_empty : forall Γ e te, MEmpty |p= e : te -> Γ |p= e : te.
Proof.
  eauto using Pinclusion_typing, inclusion_empty.
Qed.


(*
** Substitution preserves typing
*)
Lemma Psubst_typing : forall e2 Γ var tv te e1,
  (var |=> tv; Γ) |p= e2 : te ->
  MEmpty |p= e1 : tv ->
       Γ |p= ([var := e1]p e2) : te.
Proof.
  induction e2; intros * HT2 HT1;
  simpl; inversion HT2; subst;
  breakStrDec;
  try match goal with H: Some ?e = Some ?e' |- _ =>
    replace e' with e in * by congruence
  end;
  eauto 6 using Pinclusion_typing, inclusion_shadow, inclusion_permute,
    PTyping, Ptyping_empty, InNotEq.
Qed.


Definition setTable (m : PMem) (a : lir.address) (idx : nat) (v : PE)
                    (Vv : PValue v) : PMem :=
        PUpdateT a (PToIndex idx) (PEV (PECast v PTStar) (PVbox v Vv)) m.


(*
** Evaluation steps for Lir expressions
*)
Reserved Notation "m '/' e '-p->' m1 '/' e1"
(at level 40, e at level 39, m1 at level 39, e1 at level 39).
Reserved Notation "m '/' e '-p->' 'fail'"
(at level 40, e at level 39).


Inductive pstep : PMem -> PE -> PMem -> PE -> Prop :=
| PStPlus1 : forall m e1 e2 m' e1',
    m / e1 -p-> m' / e1' ->
    m / PEPlus e1 e2 -p-> m' / PEPlus e1' e2
| PStPlus2 : forall m e1 e2 m' e2',
    PValue e1 ->
    m / e2 -p-> m' / e2' ->
    m /  PEPlus e1 e2 -p-> m' /  PEPlus e1 e2'
| PStPlus : forall m n1 n2,
    m /  PEPlus (PENum n1) (PENum n2) -p-> m /  PENum (n1 + n2)
| PStNew : forall m m' free T,
    (free, m') = PfreshT m ->
    m / PENew T -p-> m' / PETAddr free T
| PStGet1 : forall m e1 e2 m' e1',
    m /e1 -p-> m' /e1' ->
    m / PEGet e1 e2 -p-> m' / PEGet e1' e2
| PStGet2 : forall m e1 e2 m' e2',
    PValue e1 ->
    m /e2 -p-> m' /e2' ->
    m / PEGet e1 e2 -p-> m' / PEGet e1 e2'
| PStGet : forall m a idx T,
    m / PEGet (PETAddr a T) (PENum idx) -p-> m / PECast (PqueryT a idx m) T
| PStSet1 : forall m e1 e2 e3 m' e1',
    m / e1 -p-> m' / e1' ->
    m / PESet e1 e2 e3 -p-> m' / PESet e1' e2 e3
| PStSet2 : forall m e1 e2 e3 m' e2',
    PValue e1 ->
    m / e2 -p-> m' / e2' ->
    m / PESet e1 e2 e3 -p-> m' / PESet e1 e2' e3
| PStSet3 : forall m e1 e2 e3 m' e3',
    PValue e1 -> PValue e2 ->
    m / e3 -p-> m' / e3' ->
    m / PESet e1 e2 e3 -p-> m' / PESet e1 e2 e3'
| PStSet : forall m a idx v T (Vv : PValue v),
    PValue v ->  (* shouldn't be necessary, but otherwise it is shelved *)
    m / PESet (PETAddr a T) (PENum idx) v -p-> setTable m a idx v Vv / PENil
| PStFun : forall m m' v b free T1 T2,
    (free, m') = PfreshF m v T1 b ->
    m / PEFun v T1 b T2 -p-> m' / PEFAddr free T1 T2
| PStLet1 : forall m m' init init' body var TV,
    m / init -p-> m' / init' ->
    m / PELet var TV init body -p-> m' / PELet var TV init' body
| PStLet : forall m init body var TV,
  PValue init ->
  m / PELet var TV init body -p-> m / ([var := init]p body)
| PStApp1 : forall m e1 e2 m' e1',
    m / e1 -p-> m' / e1' ->
    m / PEApp e1 e2 -p-> m' / PEApp e1' e2
| PStApp2 : forall m e1 e2 m' e2',
    PValue e1 ->
    m / e2 -p-> m' / e2' ->
    m / PEApp e1 e2 -p-> m' / PEApp e1 e2'
| PStApp : forall m a var type body v T1 T2,
    PValue v ->
    (var, type, body) = PqueryF a m ->
    m / PEApp (PEFAddr a T1 T2) v -p->
          m / PECast (PELet var type (PECast v type) body) T2
| PStCast1 : forall m e m' e' T,
    m / e -p-> m' / e' ->
    m / PECast e T -p-> m' / PECast e' T
| PStCast : forall m T v v',
    PValue v ->
    T <> PTStar ->
    PCast v T = Some v' ->
    m / PECast v T -p-> m / v'

where "m / e -p-> m1 / e1" := (pstep m e m1 e1).


(*
** Fail evaluation for Pallene expressions
*)
Inductive pstepF : PMem -> PE -> Prop :=
| PStPlus1F : forall m e1 e2,
    m / e1 -p-> fail ->
    m / PEPlus e1 e2 -p-> fail
| PStPlus2F : forall m e1 e2,
    PValue e1 ->
    m / e2 -p-> fail ->
    m /  PEPlus e1 e2 -p-> fail
| PStGet1F : forall m e1 e2,
    m /e1 -p-> fail ->
    m / PEGet e1 e2 -p-> fail
| PStGet2F : forall m e1 e2,
    PValue e1 ->
    m /e2 -p-> fail ->
    m / PEGet e1 e2 -p-> fail
| PStSet1F : forall m e1 e2 e3,
    m / e1 -p-> fail ->
    m / PESet e1 e2 e3 -p-> fail
| PStSet2F : forall m e1 e2 e3,
    PValue e1 ->
    m / e2 -p-> fail ->
    m / PESet e1 e2 e3 -p-> fail
| PStSet3F : forall m e1 e2 e3,
    PValue e1 -> PValue e2 ->
    m / e3 -p-> fail ->
    m / PESet e1 e2 e3 -p-> fail
| PStLet1F : forall m init body var TV,
    m / init -p-> fail ->
    m / PELet var TV init body -p-> fail
| PStApp1F : forall m e1 e2,
    m / e1 -p-> fail ->
    m / PEApp e1 e2 -p-> fail
| PStApp2F : forall m e1 e2,
    PValue e1 ->
    m / e2 -p-> fail ->
    m / PEApp e1 e2 -p-> fail
| PStCast1F : forall m t e,
    m / e -p-> fail ->
    m / PECast e t -p-> fail
| PStCastF : forall m T v,
    PValue v ->
    PCast v T = None ->
    m / PECast v T -p-> fail

 where "m / e -p-> 'fail'" := (pstepF m e)
.


Lemma ValueNormal : forall v m,
  PValue v ->
  ~exists e' m', m / v -p-> m' / e'.
Proof.
  intros * HV [e' [m' H]].
  induction H; inversion HV; subst; eauto.
Qed.

Lemma ValueNormalF : forall v m,
  PValue v ->
  ~m / v -p-> fail.
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
| PMCT : forall a idx v m,
     MEmpty |p= PEV2Val v : PTStar ->
     Pmem_correct m ->
     Pmem_correct (PUpdateT a idx v m)
| PMCF : forall a var type body m,
     (var |=> type; MEmpty) |p= body : PTStar ->
     Pmem_correct m ->
     Pmem_correct (PUpdateF a var type body m)
.


(*
** All expressions stored in memory tables are values
*)
Lemma PMCValue : forall m a n, PValue (PqueryT a n m).
Proof.
  unfold PqueryT.
  intros.
  induction m; try DExpValue; lir.breakIndexDec; eauto using PValue.
Qed.


(*
** All expressions stored in a table of a correct memory are
** well typed
*)
Lemma PMCTy : forall m a n Γ,
    Pmem_correct m ->
    Γ |p= (PqueryT a n m) : PTStar.
Proof.
  unfold PqueryT.
  induction 1; lir.breakIndexDec; eauto using PTyping, Ptyping_empty.
Qed.


(*
** All functions stored in a correct memory have correct types.
*)
Lemma PMCTyF : forall m a var type body Γ,
    (var, type,  body) = PqueryF a m ->
    Pmem_correct m ->
    (var |=> type; Γ) |p= body : PTStar.
Proof.
  intros * HEq HMC.
  induction HMC; simpl in HEq;
    lir.breakIndexDec; try (injection HEq; intros; subst);
    eauto using PTyping, Pinclusion_typing, inclusion_update, inclusion_empty.
Qed.


(*
** Table allocation preserves memory correctness
*)
Lemma Pmem_correct_freshT : forall m m' free,
  Pmem_correct m -> (free,m') = PfreshT m -> Pmem_correct m'.
Proof.
  inversion 2.
  eauto using Pmem_correct, PTyping.
Qed.


(*
** Function allocation preserves memory correctness
*)
Lemma Pmem_correct_freshF : forall m m' var T1 T2 body free,
  (var |=> T1; MEmpty) |p= body : T2 ->
  Pmem_correct m ->
  (free,m') = PfreshF m var T1 body ->
  Pmem_correct m'.
Proof.
  inversion 3; subst.
  eauto using Pmem_correct, PTyping.
Qed.


Lemma memCorrectSet : forall a idx v (Vv: PValue v) T m,
  MEmpty |p= v : T ->
  Pmem_correct m ->
  Pmem_correct (setTable m a idx v Vv).
Proof.
  eauto using Pmem_correct, PTyping.
Qed.


(*
** Executing an evaluation step preserves memory
** correctness
*)
Lemma PmemPreservation : forall (m m' : PMem) e e' t,
  Pmem_correct m ->
  MEmpty |p= e : t ->
  m / e -p-> m' / e' ->
  Pmem_correct m'.
Proof.
  intros * HMC HTy Hst.
  generalize dependent m'.
  generalize dependent e'.
  remember MEmpty as Γ.
  induction HTy; intros * Hst; inversion Hst; subst;
  eauto using Pmem_correct_freshT, Pmem_correct_freshF, Pmem_correct,
              memCorrectSet.
Qed.


(*
** Preservation of types for Pallene expressions
*)
Theorem PexpPreservation : forall m e t m' e',
  Pmem_correct m ->
  MEmpty |p= e : t ->
  m / e -p-> m' / e' ->
  MEmpty |p= e' : t.
Proof.
  intros m e t m' e' Hmc HT.
  generalize dependent m'.
  generalize dependent e'.
  remember MEmpty as Γ.
  induction HT; intros * Hst; inversion Hst; subst;
  eauto using PTyping, PMCTy, PMCTyF, Psubst_typing, CastEqType;
  inversion HT1; subst;
    eauto using PTyping, PMCTy, PMCTyF, PMCValue.
Qed.


(*
** Preservation of types for Pallene expressions,
** function version.
*)
Lemma PexpPreservTypeOf : forall m e t m' e',
  Pmem_correct m ->
  MEmpty |p= e : t ->
  m / e -p-> m' / e' ->
  typeOf MEmpty e = typeOf MEmpty e'.
Proof.
  intros * PM PTy PSt.
  erewrite typeOfCorrect'; eauto.
  erewrite typeOfCorrect'; eauto.
  eauto using PexpPreservation.
Qed.


Ltac openCanonicValue rule :=
  repeat match goal with
    | [ Ht : MEmpty |p= ?e : _,
        Hv : PValue ?e |- _] =>
          eapply rule in Ht; trivial; decompose [ex or and] Ht; clear Ht
    end.

Ltac dostep :=
  right; only 1: (right; eauto using pstep); left;  eauto using pstepF.


(*
** Progress for Pallene terms
*)
Theorem Progress : forall m e t,
    MEmpty |p= e : t  ->
    PValue e \/
    (m / e -p-> fail \/ exists m' e', m / e -p-> m' / e').
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

  - (* Fun *)
    pose (PfreshF m var Tvar body) as P; destruct P eqn:?;
    dostep.

  - (* App *)
    pose (PqueryF x m) as P. destruct P as [[? ?] ?] eqn:?; subst.
    dostep.

  - (* Cast *)
    destruct (dec_TP T2 PTStar) eqn:?; subst.
    + (* upcast *) left. eauto using PValue.
    + (* downcast *) destruct (PCast e T2) eqn:?;
      dostep.

Qed.

