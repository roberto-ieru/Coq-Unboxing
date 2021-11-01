
Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.



Inductive Tag : Set := | TgNil | TgInt | TgTbl | TgFun.


Lemma dec_Tag : forall (t1 t2 : Tag), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Qed.


Inductive IRType : Set :=
| IRTTag : Tag -> IRType
| IRTStar
.

Coercion IRTTag : Tag >-> IRType.

Inductive EType : Set :=
| ETn : IRType -> EType
| ETLamb : IRType -> EType -> EType
.

Coercion ETn : IRType >-> EType.

Definition address := nat.

Inductive IRE : Set :=
| IRENil : IRE
| IRENum : nat -> IRE
| IREPlus : IRE -> IRE -> IRE
| IRECnst : IRE
| IREAddr : address -> IRE
| IREGet : IRE -> IRE -> IRE
| IRESet : IRE -> IRE -> IRE -> IRE
| IREVar : string -> IRE
| IRELamb : string -> EType -> IRE -> IRE
| IREFun : IRE -> IRE
| IRELambApp : IRE -> IRE -> IRE
| IREFunApp : IRE -> IRE -> IRE
| IREBox : Tag -> IRE -> IRE
| IREUnbox : Tag -> IRE -> IRE
.

Definition IREnvironment := Map IRType.


Reserved Notation "Γ '|=' e ':' t"  (at level 40, no associativity,
                                     e at next level).

Inductive IRTyping : IREnvironment -> IRE -> EType -> Prop :=
| IRTyNil : forall Γ, Γ |= IRENil : TgNil
| IRTyVar : forall Γ var T,
    In Γ var = Some T ->
    Γ |= IREVar var : T
| IRTyInt : forall Γ n, Γ |= IRENum n : TgInt
| IRTyPlus : forall Γ e1 e2,
    Γ |= e1 : TgInt ->
    Γ |= e2 : TgInt ->
    Γ |= (IREPlus e1 e2) : TgInt
| IRTyCnst : forall Γ, Γ |= IRECnst : TgTbl
| IRTyAddr : forall Γ addr, Γ |= IREAddr addr : TgTbl
| IRTyGet : forall Γ e1 e2,
    Γ |= e1 : TgTbl ->
    Γ |= e2 : TgInt ->
    Γ |= (IREGet e1 e2) : IRTStar
| IRTySet : forall Γ e1 e2 e3,
    Γ |= e1 : TgTbl ->
    Γ |= e2 : TgInt ->
    Γ |= e3 : IRTStar ->
    Γ |= (IRESet e1 e2 e3) : IRTStar
| IRTyLamb : forall Γ var tvar e te,
    var |=> tvar; Γ |= e : te ->
    Γ |= (IRELamb var tvar e) : (ETLamb tvar te)
| IRTyLambApp : forall Γ e1 e2 t1 t2,
    Γ |= e1 : (ETLamb t1 t2) ->
    Γ |= e2 : t1 ->
    Γ |= (IRELambApp e1 e2) : t2
| IRTyFun : forall Γ e,
    Γ |= e : (ETLamb IRTStar IRTStar) ->
    Γ |= (IREFun e) : TgFun
| IRTyFunApp : forall Γ e1 e2,
    Γ |= e1 : TgFun ->
    Γ |= e2 : IRTStar ->
    Γ |= (IREFunApp e1 e2) : IRTStar
| IRTyBox : forall Γ e (t : Tag),
    Γ |= e : t ->
    Γ |= (IREBox t e) : IRTStar
| IRTyUnbox : forall Γ e (t : Tag),
    Γ |= e : IRTStar ->
    Γ |= (IREUnbox t e) : t
where "Γ '|=' e ':' t" := (IRTyping Γ e t)
.

Lemma lambUnique : forall t1 t1' t2 t2',
     ETLamb t1 t2 = ETLamb t1' t2' -> t2 = t2'.
Proof. intros. injection H. trivial. Qed.


Theorem typeUnique : forall Γ e t t',
   (Γ  |= e : t) -> (Γ |= e : t') -> t = t'.
Proof.
  intros Γ e t t' H1.
  generalize dependent t'.
  induction H1; intros t' H2; inversion H2; subst; f_equal;
  eauto using lambUnique; congruence.
Qed.


Theorem envExt : forall Γ Γ' e t,
    inclusion Γ Γ' -> Γ |= e : t  -> Γ' |= e : t.
Proof.
  intros Γ Γ' e t Hinc Hty.
  generalize dependent Γ'.
  induction Hty; intros Γ' Hinc; subst; eauto using IRTyping.
  - constructor. apply IHHty.
    auto using inclusion_update.
Qed.



Example TypeFunId : forall Γ var,
  Γ |= IREFun (IRELamb var IRTStar (IREVar var)) : TgFun.
Proof. eauto using IRTyping,  InEq. Qed.


Inductive Value : IRE -> Prop :=
| Vnil : Value IRENil
| Vnum : forall n, Value (IRENum n)
| Vtbl : forall a, Value (IREAddr a)
| Vfun : forall var e, Value (IREFun (IRELamb var IRTStar e))
| Vbox : forall gt v, Value v -> Value (IREBox gt v)
| Vlam : forall var t e, Value (IRELamb var t e)
.


Lemma valnil : forall Γ e,
  Γ |= e : TgNil -> Value e -> e = IRENil.
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; congruence.
Qed.


Lemma valint : forall Γ e,
    Γ |= e : TgInt -> Value e -> exists n, e = IRENum n.
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  eexists; eauto 1.
Qed.


Lemma valtbl : forall Γ e,
    Γ |= e : TgTbl -> Value e -> exists a, e = IREAddr a.
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  eexists; eauto 1.
Qed.


Lemma valfun : forall Γ e,
    Γ |= e : TgFun -> Value e -> exists var b, e = IREFun (IRELamb var IRTStar b).
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  eexists; eexists; split; eauto 1 using Value.
Qed.


Lemma vallam : forall {Γ e t1 t2},
    Γ |= e : ETLamb t1 t2 -> Value e -> exists var b, e = IRELamb var t1 b.
Proof.
  intros Γ e t1 t2 HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  eexists; eexists; eauto 1.
Qed.


Lemma valbox : forall Γ e, Γ |= e : IRTStar -> Value e ->
    exists o t, e = IREBox t o /\ (Γ |= o : t) /\ Value o.
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  match goal with
  | [H: IREBox _ _ = IREBox _ _ |- _ ] => inversion H; subst end.
  (eexists; eexists; eauto using Value).
Qed.


Inductive Mem : Set :=
| EmptyMem : Mem
| Update : address -> nat -> IRE -> Mem -> Mem.


Definition BoxedNil := IREBox TgNil IRENil.

Fixpoint query (a : address) (idx : nat) (m : Mem) :=
  match m with
  | EmptyMem => BoxedNil
  | Update a' idx' e m' => if Nat.eq_dec a a' then
                           if Nat.eq_dec idx idx' then e
                           else query  a idx m'
                         else query  a idx m'
  end.


Fixpoint freshaux (m : Mem) : address :=
  match m with
  | EmptyMem => 1
  | Update _ _ _ m' => S (freshaux m')
  end.


Definition fresh (m : Mem) : (address * Mem) :=
  let f := freshaux m in (f, Update f 1 BoxedNil m).


Reserved Notation "'[' x ':=' s ']' t" (at level 20, x constr).

Fixpoint substitution (var : string) (y : IRE)  (e : IRE) : IRE :=
 match e with
 | IRENil => e
 | IRENum n => e
 | IREPlus e1 e2 => IREPlus ([var := y] e1) ([var := y] e2)
 | IRECnst => e
 | IREAddr a => e
 | IREGet e1 e2 => IREGet ([var := y] e1) ([var := y] e2)
 | IRESet e1 e2 e3 => IRESet ([var := y] e1) ([var := y] e2) ([var := y] e3)
 | IREVar var' => if string_dec var var' then y else e
 | IRELamb var' type body => if string_dec var var' then e
                       else IRELamb var' type ([var := y] body)
 | IREFun e  => IREFun ([var := y] e)
 | IRELambApp e1 e2 => IRELambApp ([var := y] e1) ([var := y] e2)
 | IREFunApp e1 e2 => IREFunApp ([var := y] e1) ([var := y] e2)
 | IREBox tg e  => IREBox tg ([var := y] e)
 | IREUnbox tg e  => IREUnbox tg ([var := y] e)
end
where "'[' x ':=' s ']' t" := (substitution x s t)
.


Lemma inclusion_typing : forall Γ Γ' e te,
  inclusion Γ Γ' -> Γ |= e : te -> Γ' |= e : te.
Proof.
  intros Γ Γ' e te Hin Hty.
  generalize dependent Γ'.
  induction Hty; eauto using IRTyping, inclusion_update.
Qed.


Corollary typing_empty : forall Γ e te, MEmpty |= e : te -> Γ |= e : te.
Proof.
  eauto using inclusion_typing, inclusion_empty.
Qed.


Lemma subst_typing : forall e2 Γ var tv te e1,
  var |=> tv; Γ |= e2 : te -> MEmpty |= e1 : tv ->
       Γ |= ([var := e1] e2) : te.
Proof.
  induction e2; intros Γ var tv te e1 HT2 HT1;
  simpl; inversion HT2; subst; eauto using IRTyping.
  - destruct (string_dec var s); subst.
    + assert (T = tv). { rewrite InEq in H1. congruence. }
      subst. eauto using typing_empty.
    + constructor. apply InNotEq with var T; try congruence.
      simpl. destruct (string_dec s var); subst; try easy.
      eauto using InNotEq.
  - destruct (string_dec var s); subst.
    + eauto using inclusion_typing, inclusion_shadow, IRTyping.
    + eauto using inclusion_typing, inclusion_permute, IRTyping.
Qed.


Reserved Notation "m '/' e --> m1 '/' e1"
(at level 40, e at level 39, m1 at level 39, e1 at level 39).
Reserved Notation "m '/' e --> 'fail'"
(at level 40, e at level 39).


Inductive step : Mem -> IRE -> Mem -> option IRE -> Prop :=
| StPlus1 : forall m e1 e2 m' e1',
    m / e1 --> m' / e1' ->
    m / IREPlus e1 e2 --> m' / IREPlus e1' e2
| StPlus1F : forall m e1 e2,
    m / e1 --> fail ->
    m / IREPlus e1 e2 --> fail
| StPlus2 : forall m e1 e2 m' e2',
    Value e1 ->
    m / e2 --> m' / e2' ->
    m /  IREPlus e1 e2 --> m' /  IREPlus e1 e2'
| StPlus2F : forall m e1 e2,
    Value e1 ->
    m / e2 --> fail ->
    m /  IREPlus e1 e2 --> fail
| StPlus : forall m n1 n2,
    m /  IREPlus (IRENum n1) (IRENum n2) --> m /  IRENum (n1 + n2)
| StCstr : forall m m' free,
    (free, m') = fresh m ->
    m / IRECnst --> m' / IREAddr free
| StGet1 : forall m e1 e2 m' e1',
    m /e1 --> m' /e1' ->
    m / IREGet e1 e2 --> m' / IREGet e1' e2
| StGet1F : forall m e1 e2,
    m /e1 --> fail ->
    m / IREGet e1 e2 --> fail
| StGet2 : forall m e1 e2 m' e2',
    Value e1 ->
    m /e2 --> m' /e2' ->
    m / IREGet e1 e2 --> m' / IREGet e1 e2'
| StGet2F : forall m e1 e2,
    Value e1 ->
    m /e2 --> fail ->
    m / IREGet e1 e2 --> fail
| StGet : forall m a n,
    m / IREGet (IREAddr a) (IRENum n) --> m / query a n m
| StSet1 : forall m e1 e2 e3 m' e1',
    m / e1 --> m' / e1' ->
    m / IRESet e1 e2 e3 --> m' / IRESet e1' e2 e3
| StSet1F : forall m e1 e2 e3,
    m / e1 --> fail ->
    m / IRESet e1 e2 e3 --> fail
| StSet2 : forall m e1 e2 e3 m' e2',
    Value e1 ->
    m / e2 --> m' / e2' ->
    m / IRESet e1 e2 e3 --> m' / IRESet e1 e2' e3
| StSet2F : forall m e1 e2 e3,
    Value e1 ->
    m / e2 --> fail ->
    m / IRESet e1 e2 e3 --> fail
| StSet3 : forall m e1 e2 e3 m' e3',
    Value e1 -> Value e2 ->
    m / e3 --> m' / e3' ->
    m / IRESet e1 e2 e3 --> m' / IRESet e1 e2 e3'
| StSet3F : forall m e1 e2 e3,
    Value e1 -> Value e2 ->
    m / e3 --> fail ->
    m / IRESet e1 e2 e3 --> fail
| StSet : forall m a n v,
    Value v ->
    m / IRESet (IREAddr a) (IRENum n) v --> Update a n v m / v
| StFun1 : forall m e m' e',
    m / e --> m' / e' ->
    m / IREFun e --> m' / IREFun e'
| StFun1F : forall m e,
    m / e --> fail ->
    m / IREFun e --> fail
| StLambapp1 : forall m e1 e2 m' e1',
    m / e1 --> m' / e1' ->
    m / IRELambApp e1 e2 --> m' / IRELambApp e1' e2
| StLambapp1F : forall m e1 e2,
    m / e1 --> fail ->
    m / IRELambApp e1 e2 --> fail
| StLambapp2 : forall m e1 e2 m' e2',
    Value e1 ->
    m / e2 --> m' / e2' ->
    m / IRELambApp e1 e2 --> m' / IRELambApp e1 e2'
| StLambapp2F : forall m e1 e2,
    Value e1 ->
    m / e2 --> fail ->
    m / IRELambApp e1 e2 --> fail
| StLambapp : forall m var t e1 v2,
     Value v2 ->
     m / IRELambApp (IRELamb var t e1) v2 -->
     m / ([var := v2] e1)
| StFunapp1 : forall m e1 e2 m' e1',
    m / e1 --> m' / e1' ->
    m / IREFunApp e1 e2 --> m' / IREFunApp e1' e2
| StFunapp1F : forall m e1 e2,
    m / e1 --> fail ->
    m / IREFunApp e1 e2 --> fail
| StFunapp2 : forall m e1 e2 m' e2',
    Value e1 ->
    m / e2 --> m' / e2' ->
    m / IREFunApp e1 e2 --> m' / IREFunApp e1 e2'
| StFunapp2F : forall m e1 e2,
    Value e1 ->
    m / e2 --> fail ->
    m / IREFunApp e1 e2 --> fail
| StFunapp : forall m var b v2,
    Value v2 ->
    m / IREFunApp (IREFun (IRELamb var IRTStar b)) v2 -->
    m / IRELambApp (IRELamb var IRTStar b) v2
| StBox1 : forall m t e m' e',
    m / e --> m' / e' ->
    m / IREBox t e --> m' / IREBox t e'
| StBox1F : forall m t e,
    m / e --> fail ->
    m / IREBox t e --> fail
| StUnbox1 : forall m t e m' e',
    m / e --> m' / e' ->
    m / IREUnbox t e --> m' / IREUnbox t e'
| StUnbox1F : forall m t e,
    m / e --> fail ->
    m / IREUnbox t e --> fail
| StUnbox : forall m t v,
    Value v ->
    m / IREUnbox t (IREBox t v) --> m / v
| StUnboxF : forall m t t' v,
    t <> t' ->
    Value v ->
    m / IREUnbox t (IREBox t' v) --> fail

where "m / e --> m1 / e1" := (step m e m1 (Some e1))
  and "m / e --> 'fail'" := (step m e m None)
.



Definition mem_correct (m : Mem) :=
  forall a n, Value (query a n m) /\ MEmpty |= (query a n m) : IRTStar.


Lemma mem_correct_empty : mem_correct EmptyMem.
Proof. unfold mem_correct; eauto using Value,IRTyping. Qed.


Lemma mem_correct_query : forall Γ m a n,
  mem_correct m -> Γ |= (query a n m) : IRTStar.
Proof.
  intros Γ m a n Hmc.
  specialize (Hmc a n) as [? ?].
  eauto using envExt, inclusion_empty.
Qed.


Ltac breakNatDec :=
  repeat match goal with
  [ |- context C [Nat.eq_dec ?V1 ?V2] ] =>
    destruct (Nat.eq_dec V1 V2) end.


Lemma mem_correct_update : forall m a idx e,
  mem_correct m -> Value e -> MEmpty |= e : IRTStar ->
      mem_correct (Update a idx e m).
Proof.
  intros m a idx e Hmc.
  unfold mem_correct; intros.
  simpl.
  breakNatDec; eauto using IRTyping,Value.
Qed.


Lemma mem_correct_fresh : forall m m' free,
  mem_correct m -> (free,m') = fresh m -> mem_correct m'.
Proof.
  unfold fresh. intros m m' free Hmc Heq. inversion Heq.
  eauto using mem_correct_update,IRTyping,Value.
Qed.


Lemma memPreservation : forall (m m' : Mem) e e' t,
  mem_correct m ->
  MEmpty |= e : t ->
  m / e --> m' / e' ->
     mem_correct m'.
Proof.
  intros m m' e e' t HMC HTy Hst.
  generalize dependent m'.
  generalize dependent e'.
  remember MEmpty as Γ.
  induction HTy; intros e' m' Hst; inversion Hst; subst;
  eauto using mem_correct_fresh,mem_correct_update.
Qed.


Lemma expPreservation : forall m e t m' e',
  mem_correct m ->
  MEmpty |= e : t -> m / e --> m' / e' -> MEmpty |= e' : t.
Proof.
  intros m e t m' e' Hmc HT.
  generalize dependent m'.
  generalize dependent e'.
  remember MEmpty as Γ.
  induction HT; intros e' m' Hst; inversion Hst; subst;
  eauto using IRTyping, mem_correct_query;
  match goal with
  | [ H: _ |= _ : _ |- _ ] =>
        (inversion H; subst; eauto using IRTyping, subst_typing; fail)
  end.
Qed.


Theorem Preservation : forall m e t m' e',
  mem_correct m -> MEmpty |= e : t -> m / e --> m' / e' ->
    mem_correct m' /\ MEmpty |= e' : t.
Proof. intuition; eauto using memPreservation,expPreservation. Qed.


Lemma value_normal : forall m e,
    Value e -> ~exists m' v, step m e m' v.
Proof.
  intros m e HV.
  induction HV; intros HEx; destruct HEx as [m' [v' Hst]];
  inversion Hst; subst; eauto;
  match goal with
  | [H: step _ (IRELamb _ _ _) _ _ |- _] => inversion H end.
Qed.


Ltac open_value rule :=
  match goal with
    | [ Ht : MEmpty |= ?e : _,
        Hv : Value ?e |- _] =>
          eapply rule in Ht; trivial; decompose [ex or and] Ht
    end.


Theorem Progress : forall m e t,
    MEmpty |= e : t  ->
        Value e \/ (m / e --> fail \/ exists m' e', m / e --> m' / e').
Proof.
  intros m e t Hty.
  remember MEmpty as Γ.
  induction Hty; subst;
  (* variables *)
  try match goal with
  | [H : In MEmpty _ = _ |- _] => inversion H
   end;
  (* break induction hypotheses *)
  repeat match goal with
  | [H : _ -> _ \/ (_ \/ _) |- _] =>
      decompose [or ex and] (H eq_refl); clear H
  end; subst;
  (* trivial steps and failures *)
  try (right; eauto using step; fail);
  (* trivial values *)
  eauto using Value;
  (* break values *)
  repeat open_value valint;
  try open_value valtbl;
  try open_value valfun;
  try open_value valbox;
  try match goal with
    | [ Ht : MEmpty |= ?e : _,
        Hv : Value ?e |- _] => eapply vallam in Ht; trivial;
          decompose [ex or and] Ht
  end; subst;
  (* try cases that became easy after breaking values *)
  try (right; right; eauto using step,eq_refl; fail);
  (* 'fun' value needed to break its inner lambda *)
  auto using Value.
  - (* unboxing has to handle success vs. failure *)
    match goal with | [t1:Tag, t2:Tag |- _] => destruct (dec_Tag t1 t2) end;
    right; subst; eauto using step.
Qed.


Reserved Notation "m '/' e -->* m1 '/' e1"
(at level 40, e at level 39, m1 at level 39, e1 at level 39).
Reserved Notation "m '/' e -->* 'fail'"
(at level 40, e at level 39).

Inductive multistep : Mem -> IRE -> Mem -> option IRE -> Prop :=
| MStRefl : forall m e, m / e -->* m / e
| MStMStep : forall m e m' e' m'' e'',
    m / e --> m' / e' ->
    m' / e' -->* m'' / e'' ->
    m / e -->* m'' / e''
| MStStepF : forall m e,
    m / e --> fail ->
    m / e -->* fail
| MStMStepF : forall m e m' e',
    m / e --> m' / e' ->
    m' / e' -->* fail ->
    m / e -->* fail

where "m / e -->* m1 / e1" := (multistep m e m1 (Some e1))
  and "m / e -->* 'fail'" := (multistep m e m None)
.


Theorem MultiProgress : forall m e t m' e',
    mem_correct m ->
    MEmpty |= e : t  ->
    m / e -->* m' / e' ->
        Value e' \/
       (m' / e' --> fail \/ exists m'' e'', m' / e' --> m'' / e'').
Proof.
  intros m e t m' e' HTy HMem HMulti.
  remember (Some e') as E eqn:Heq.
  induction HMulti; inversion Heq; subst.
  - eauto using Progress.
  - eapply IHHMulti; trivial; eapply Preservation; eauto.
Qed.


Ltac finishmExp :=
  intros m e m' e' Hmt;
  remember (Some e') as E' eqn:Heq;
  generalize dependent e';
  induction Hmt; intros ? Heq; inversion Heq; subst;
  eauto using step,multistep.

Lemma mPlus1 : forall e2 m e m' e',
    m / e -->* m' / e' ->  m / IREPlus e e2 -->* m' / IREPlus e' e2.
Proof. intros e2; finishmExp. Qed.

Lemma mPlus2 : forall e1, Value e1 -> forall m e m' e',
    m / e -->* m' / e' ->  m / IREPlus e1 e -->* m' / IREPlus e1 e'.
Proof. intros e1 HV; finishmExp. Qed.


Lemma mBox1 : forall t m e m' e',
    m / e -->* m' / e' ->  m / IREBox t e -->* m' / IREBox t e'.
Proof.
  intros t; finishmExp. Qed.


Lemma mUnbox1 : forall t m e m' e',
    m / e -->* m' / e' ->  m / IREUnbox t e -->* m' / IREUnbox t e'.
Proof. intros t; finishmExp. Qed.





