
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
| IRELet : string -> IRType -> IRE -> IRE -> IRE
| IREFun : string -> IRE -> IRE
| IREFunApp : IRE -> IRE -> IRE
| IREBox : Tag -> IRE -> IRE
| IREUnbox : Tag -> IRE -> IRE
.

Definition IREnvironment := Map IRType.


Reserved Notation "Γ '|=' e ':' t"  (at level 40, no associativity,
                                     e at next level).

Inductive IRTyping : IREnvironment -> IRE -> IRType -> Prop :=
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
    Γ |= e2 : IRTStar ->
    Γ |= (IREGet e1 e2) : IRTStar
| IRTySet : forall Γ e1 e2 e3,
    Γ |= e1 : TgTbl ->
    Γ |= e2 : IRTStar ->
    Γ |= e3 : IRTStar ->
    Γ |= (IRESet e1 e2 e3) : IRTStar
| IRTyLet : forall Γ var tvar e body tb,
    Γ |= e : tvar ->
    var |=> tvar; Γ |= body : tb ->
    Γ |= (IRELet var tvar e body) : tb
| IRTyFun : forall Γ var body,
    var |=> IRTStar; Γ |= body : IRTStar ->
    Γ |= (IREFun var body) : TgFun
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


Theorem typeUnique : forall Γ e t t',
   (Γ  |= e : t) -> (Γ |= e : t') -> t = t'.
Proof.
  intros Γ e t t' H1.
  generalize dependent t'.
  induction H1; intros t' H2; inversion H2; subst; f_equal;
  auto ; congruence.
Qed.


Theorem envExt : forall Γ Γ' e t,
    inclusion Γ Γ' -> Γ |= e : t  -> Γ' |= e : t.
Proof.
  intros Γ Γ' e t Hinc Hty.
  generalize dependent Γ'.
  induction Hty; intros Γ' Hinc; subst;
  eauto using IRTyping, inclusion_update.
Qed.



Example TypeFunId : forall Γ var,
  Γ |= IREFun var (IREVar var) : TgFun.
Proof. eauto using IRTyping,  InEq. Qed.


Inductive Value : IRE -> Prop :=
| Vnil : Value IRENil
| Vnum : forall n, Value (IRENum n)
| Vtbl : forall a, Value (IREAddr a)
| Vfun : forall var e, Value (IREFun var e)
| Vbox : forall gt v, Value v -> Value (IREBox gt v)
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
  eexists; auto 1.
Qed.


Lemma valtbl : forall Γ e,
    Γ |= e : TgTbl -> Value e -> exists a, e = IREAddr a.
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  eexists; auto 1.
Qed.


Lemma valfun : forall Γ e,
    Γ |= e : TgFun -> Value e -> exists var b, e = IREFun var b.
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  eexists; eexists. auto 1 using Value.
Qed.


Lemma valbox : forall Γ e, Γ |= e : IRTStar -> Value e ->
    exists o t, e = IREBox t o /\ (Γ |= o : t) /\ Value o.
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  match goal with
  | [H: IREBox _ _ = IREBox _ _ |- _ ] => inversion H; subst end.
  (eexists; eexists; auto using Value).
Qed.


Axiom Index : Set.
Axiom ToIndex : IRE -> Index.

Coercion ToIndex : IRE >-> Index.

Axiom Index_dec : Index -> Index -> bool.


Inductive Mem : Set :=
| EmptyMem : Mem
| Update : address -> Index -> IRE -> Mem -> Mem.


Definition BoxedNil := IREBox TgNil IRENil.

Fixpoint query (a : address) (idx : IRE) (m : Mem) :=
  match m with
  | EmptyMem => BoxedNil
  | Update a' idx' e m' => if Nat.eq_dec a a' then
                           if Index_dec idx idx' then e
                           else query  a idx m'
                         else query  a idx m'
  end.


Fixpoint freshaux (m : Mem) : address :=
  match m with
  | EmptyMem => 1
  | Update _ _ _ m' => S (freshaux m')
  end.


Definition fresh (m : Mem) : (address * Mem) :=
  let f := freshaux m in (f, Update f BoxedNil BoxedNil m).


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
 | IRELet var' type exp body =>
        if string_dec var var' then IRELet var' type ([var := y] exp) body
        else IRELet var' type ([var := y] exp) ([var := y] body)
 | IREFun var' body  => if string_dec var var' then e
                    else IREFun var' ([var := y] body)
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
  simpl; inversion HT2; subst;
  breakStrDec;
  eauto 6 using inclusion_typing, inclusion_shadow, inclusion_permute,
    IRTyping, typing_empty, InNotEq.
  - assert (te = tv). { rewrite InEq in H1. congruence. }
      subst. eauto using typing_empty.
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
| StGet : forall m a idx,
    Value idx ->
    m / IREGet (IREAddr a) idx --> m / query a idx m
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
| StSet : forall m a idx v,
    Value idx ->
    Value v ->
    m / IRESet (IREAddr a) idx v --> Update a idx v m / v
| StLet1 : forall m var t exp body m' exp',
    m / exp --> m' / exp' ->
    m / IRELet var t exp body --> m' / IRELet var t exp' body
| StLet1F : forall m var t exp body,
    m / exp --> fail ->
    m / IRELet var t exp body --> fail
| StLet : forall m var t exp body,
    Value exp ->
    m / IRELet var t exp body --> m / [var := exp] body
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
| StFunapp : forall m var body v2,
    Value v2 ->
    m / IREFunApp (IREFun var body) v2 -->
    m / [var := v2] body
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


Lemma MCValue : forall m a n, mem_correct m -> Value (query a n m).
Proof. intros. apply H. Qed.


Lemma MCTy : forall m a n Γ,
    mem_correct m -> Γ |= (query a n m) : IRTStar.
Proof. intros. apply typing_empty. apply H. Qed.


Lemma mem_correct_empty : mem_correct EmptyMem.
Proof. unfold mem_correct; eauto using Value,IRTyping. Qed.


Ltac breakIndexDec :=
  repeat match goal with
  | [ |- context C [Nat.eq_dec ?V1 ?V2] ] =>
    destruct (Nat.eq_dec V1 V2)
  | [ |- context C [Index_dec ?V1 ?V2] ] =>
    destruct (Index_dec V1 V2)
  end.


Lemma mem_correct_update : forall m a idx e,
  mem_correct m -> Value e -> MEmpty |= e : IRTStar ->
      mem_correct (Update a idx e m).
Proof.
  intros m a idx e Hmc.
  unfold mem_correct; intros.
  simpl.
  breakIndexDec; eauto using IRTyping,Value.
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
  eauto using IRTyping, MCTy;
  match goal with
  | [ H: _ |= _ : _ |- _ ] =>
        (inversion H; subst; eauto using IRTyping, subst_typing; fail)
  end.
Qed.


Theorem Preservation : forall m e t m' e',
  mem_correct m -> MEmpty |= e : t -> m / e --> m' / e' ->
    mem_correct m' /\ MEmpty |= e' : t.
Proof. intuition; eauto using memPreservation,expPreservation. Qed.


Lemma PresMC : forall m e t m' e',
  mem_correct m -> MEmpty |= e : t -> m / e --> m' / e' -> mem_correct m'.
Proof. apply Preservation. Qed.

Lemma PresTy : forall m e t m' e',
  mem_correct m -> MEmpty |= e : t -> m / e --> m' / e' -> MEmpty |= e' : t.
Proof. apply Preservation. Qed.


Lemma value_normal : forall m e,
    Value e -> ~exists m' v, step m e m' v.
Proof.
  intros m e HV.
  induction HV; intros HEx; destruct HEx as [m' [v' Hst]];
  inversion Hst; subst; eauto.
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
  try (right; auto using step; fail);
  (* trivial values *)
  auto using Value;
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
  try (right; right; eauto using step, eq_refl; fail).
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

Theorem multiRefl : forall m0 e0 m1 e1 m2 e2,
    m0 / e0 -->* m1 / e1 ->
    m1 / e1 -->* m2 / e2 ->
    m0 / e0 -->* m2 / e2.
Proof.
  intros m0 e0 m1 e1 m2 e2 H0 H1.
  remember (Some e1) as E1.
  generalize dependent e1.
  generalize dependent m2.
  generalize dependent e2.
  induction H0; intros ? ? ? Heq H2; inversion Heq; subst; trivial.
  eauto using multistep.
Qed.


Lemma multistep1 : forall m0 e0 m1 e1,
    m0 / e0 --> m1 / e1 ->
    m0 / e0 -->* m1 / e1.
Proof. eauto using multistep. Qed.


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
  - eauto using PresTy, PresMC.
Qed.



