
Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.



Inductive Tag : Set := | Tgnil | Tgint | Tgtbl | Tgfun.


Lemma dec_Tag : forall (t1 t2 : Tag), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Qed.


(* variable type? *)
Inductive FCType : Set :=
| Ttag : Tag -> FCType
| Tstar
.

Coercion Ttag : Tag >-> FCType.

Inductive EType : Set :=
| ETn : FCType -> EType
| ETlam : FCType -> EType -> EType
.

Coercion ETn : FCType >-> EType.

Definition address := nat.

Inductive LirExp : Set :=
| Enil : LirExp
| Enum : nat -> LirExp
| Eplus : LirExp -> LirExp -> LirExp
| Ecstr : LirExp
| Etbl : address -> LirExp
| Eindx : LirExp -> LirExp -> LirExp
| Eassg : LirExp -> LirExp -> LirExp -> LirExp
| Evar : string -> LirExp
| Elambda : string -> EType -> LirExp -> LirExp
| Efun : LirExp -> LirExp
| Elambapp : LirExp -> LirExp -> LirExp
| Efunapp : LirExp -> LirExp -> LirExp
| Ebox : Tag -> LirExp -> LirExp
| Eunbox : Tag -> LirExp -> LirExp
.

Definition Environment := Map FCType.


Reserved Notation "Γ '|=' e ':' t"  (at level 40, no associativity,
                                     e at next level).

Inductive Typing : Environment -> LirExp -> EType -> Prop :=
| TyNil : forall Γ, Γ |= Enil : Tgnil
| TyVar : forall Γ var T,
    In Γ var = Some T ->
    Γ |= Evar var : T
| TyInt : forall Γ n, Γ |= Enum n : Tgint
| TyAdd : forall Γ e1 e2,
    Γ |= e1 : Tgint ->
    Γ |= e2 : Tgint ->
    Γ |= (Eplus e1 e2) : Tgint
| TyNew : forall Γ, Γ |= Ecstr : Tgtbl
| TyTbl : forall Γ addr, Γ |= Etbl addr : Tgtbl
| TyGet : forall Γ e1 e2,
    Γ |= e1 : Tgtbl ->
    Γ |= e2 : Tgint ->
    Γ |= (Eindx e1 e2) : Tstar
| TySet : forall Γ e1 e2 e3,
    Γ |= e1 : Tgtbl ->
    Γ |= e2 : Tgint ->
    Γ |= e3 : Tstar ->
    Γ |= (Eassg e1 e2 e3) : Tgnil
| TyLam : forall Γ var tvar e te,
    var |=> tvar; Γ |= e : te ->
    Γ |= (Elambda var tvar e) : (ETlam tvar te)
| TyLamApp : forall Γ e1 e2 t1 t2,
    Γ |= e1 : (ETlam t1 t2) ->
    Γ |= e2 : t1 ->
    Γ |= (Elambapp e1 e2) : t2
| TyFun : forall Γ e,
    Γ |= e : (ETlam Tstar Tstar) ->
    Γ |= (Efun e) : Tgfun
| TyFunApp : forall Γ e1 e2,
    Γ |= e1 : Tgfun ->
    Γ |= e2 : Tstar ->
    Γ |= (Efunapp e1 e2) : Tstar
| TyBox : forall Γ e (t : Tag),
    Γ |= e : t ->
    Γ |= (Ebox t e) : Tstar
| TyUnbox : forall Γ e (t : Tag),
    Γ |= e : Tstar ->
    Γ |= (Eunbox t e) : t
where "Γ '|=' e ':' t" := (Typing Γ e t)
.

Lemma lambUnique : forall t1 t1' t2 t2',
     ETlam t1 t2 = ETlam t1' t2' -> t2 = t2'.
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
  induction Hty; intros Γ' Hinc; subst; eauto using Typing.
  - constructor. apply IHHty.
    auto using inclusion_update.
Qed.



Example TypeFunId : forall Γ var,
  Γ |= Efun (Elambda var Tstar (Evar var)) : Tgfun.
Proof. eauto using Typing,  InEq. Qed.


Inductive Value : LirExp -> Prop :=
| Vnil : Value Enil
| Vnum : forall n, Value (Enum n)
| Vtbl : forall a, Value (Etbl a)
| Vfun : forall var e, Value (Efun (Elambda var Tstar e))
| Vbox : forall gt v, Value v -> Value (Ebox gt v)
| Vlam : forall var t e, Value (Elambda var t e)
.


Lemma valint : forall Γ e,
    Γ |= e : Tgint -> Value e -> exists n, e = Enum n.
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  eexists; eauto 1.
Qed.


Lemma valtbl : forall Γ e,
    Γ |= e : Tgtbl -> Value e -> exists a, e = Etbl a.
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  eexists; eauto 1.
Qed.


Lemma valfun : forall Γ e,
    Γ |= e : Tgfun -> Value e -> exists var b, e = Efun (Elambda var Tstar b).
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  eexists; eexists; split; eauto 1 using Value.
Qed.


Lemma vallam : forall {Γ e t1 t2},
    Γ |= e : ETlam t1 t2 -> Value e -> exists var b, e = Elambda var t1 b.
Proof.
  intros Γ e t1 t2 HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  eexists; eexists; eauto 1.
Qed.


Lemma valbox : forall Γ e, Γ |= e : Tstar -> Value e ->
    exists o t, e = Ebox t o /\ (Γ |= o : t) /\ Value o.
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  match goal with
  | [H: Ebox _ _ = Ebox _ _ |- _ ] => inversion H; subst end.
  (eexists; eexists; eauto using Value).
Qed.


Inductive Mem : Set :=
| EmptyMem : Mem
| Update : address -> nat -> LirExp -> Mem -> Mem.


Definition BoxedNil := Ebox Tgnil Enil.

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

Fixpoint substitution (var : string) (y : LirExp)  (e : LirExp) : LirExp :=
 match e with
 | Enil => e
 | Enum n => e
 | Eplus e1 e2 => Eplus ([var := y] e1) ([var := y] e2)
 | Ecstr => e
 | Etbl a => e
 | Eindx e1 e2 => Eindx ([var := y] e1) ([var := y] e2)
 | Eassg e1 e2 e3 => Eassg ([var := y] e1) ([var := y] e2) ([var := y] e3)
 | Evar var' => if string_dec var var' then y else e
 | Elambda var' type body => if string_dec var var' then e
                       else Elambda var' type ([var := y] body)
 | Efun e  => Efun ([var := y] e)
 | Elambapp e1 e2 => Elambapp ([var := y] e1) ([var := y] e2)
 | Efunapp e1 e2 => Efunapp ([var := y] e1) ([var := y] e2)
 | Ebox tg e  => Ebox tg ([var := y] e)
 | Eunbox tg e  => Eunbox tg ([var := y] e)
end
where "'[' x ':=' s ']' t" := (substitution x s t).


Lemma inclusion_typing : forall Γ Γ' e te,
  inclusion Γ Γ' -> Γ |= e : te -> Γ' |= e : te.
Proof.
  intros Γ Γ' e te Hin Hty.
  generalize dependent Γ'.
  induction Hty; eauto using Typing, inclusion_update.
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
  simpl; inversion HT2; subst; eauto using Typing.
  - destruct (string_dec var s); subst.
    + assert (T = tv). { rewrite InEq in H1. congruence. }
      subst. eauto using typing_empty.
    + constructor. apply InNotEq with var T; try congruence.
      simpl. destruct (string_dec s var); subst; try easy.
      eauto using InNotEq.
  - destruct (string_dec var s); subst.
    + eauto using inclusion_typing, inclusion_shadow, Typing.
    + eauto using inclusion_typing, inclusion_permute, Typing.
Qed.


Reserved Notation "m '/' e --> m1 '/' e1"
(at level 40, e at level 39, m1 at level 39, e1 at level 39).
Reserved Notation "m '/' e --> 'fail'"
(at level 40, e at level 39).


Inductive step : Mem -> LirExp -> Mem -> option LirExp -> Prop :=
| StPlus1 : forall m e1 e2 m' e1',
    m / e1 --> m' / e1' ->
    m / Eplus e1 e2 --> m' / Eplus e1' e2
| StPlus1F : forall m e1 e2,
    m / e1 --> fail ->
    m / Eplus e1 e2 --> fail
| StPlus2 : forall m e1 e2 m' e2',
    Value e1 ->
    m / e2 --> m' / e2' ->
    m /  Eplus e1 e2 --> m' /  Eplus e1 e2'
| StPlus2F : forall m e1 e2,
    Value e1 ->
    m / e2 --> fail ->
    m /  Eplus e1 e2 --> fail
| StPlus : forall m n1 n2,
    m /  Eplus (Enum n1) (Enum n2) --> m /  Enum (n1 + n2)
| StCstr : forall m m' free,
    (free, m') = fresh m ->
    m / Ecstr --> m' / Etbl free
| StIndx1 : forall m e1 e2 m' e1',
    m /e1 --> m' /e1' ->
    m / Eindx e1 e2 --> m' / Eindx e1' e2
| StIndx1F : forall m e1 e2,
    m /e1 --> fail ->
    m / Eindx e1 e2 --> fail
| StIndx2 : forall m e1 e2 m' e2',
    Value e1 ->
    m /e2 --> m' /e2' ->
    m / Eindx e1 e2 --> m' / Eindx e1 e2'
| StIndx2F : forall m e1 e2,
    Value e1 ->
    m /e2 --> fail ->
    m / Eindx e1 e2 --> fail
| StIndx : forall m a n,
    m / Eindx (Etbl a) (Enum n) --> m / query a n m
| StAssg1 : forall m e1 e2 e3 m' e1',
    m / e1 --> m' / e1' ->
    m / Eassg e1 e2 e3 --> m' / Eassg e1' e2 e3
| StAssg1F : forall m e1 e2 e3,
    m / e1 --> fail ->
    m / Eassg e1 e2 e3 --> fail
| StAssg2 : forall m e1 e2 e3 m' e2',
    Value e1 ->
    m / e2 --> m' / e2' ->
    m / Eassg e1 e2 e3 --> m' / Eassg e1 e2' e3
| StAssg2F : forall m e1 e2 e3,
    Value e1 ->
    m / e2 --> fail ->
    m / Eassg e1 e2 e3 --> fail
| StAssg3 : forall m e1 e2 e3 m' e3',
    Value e1 -> Value e2 ->
    m / e3 --> m' / e3' ->
    m / Eassg e1 e2 e3 --> m' / Eassg e1 e2 e3'
| StAssg3F : forall m e1 e2 e3,
    Value e1 -> Value e2 ->
    m / e3 --> fail ->
    m / Eassg e1 e2 e3 --> fail
| StAssg : forall m a n v,
    Value v ->
    m / Eassg (Etbl a) (Enum n) v --> Update a n v m / Enil
| StFun1 : forall m e m' e',
    m / e --> m' / e' ->
    m / Efun e --> m' / Efun e'
| StFun1F : forall m e,
    m / e --> fail ->
    m / Efun e --> fail
| StLambapp1 : forall m e1 e2 m' e1',
    m / e1 --> m' / e1' ->
    m / Elambapp e1 e2 --> m' / Elambapp e1' e2
| StLambapp1F : forall m e1 e2,
    m / e1 --> fail ->
    m / Elambapp e1 e2 --> fail
| StLambapp2 : forall m e1 e2 m' e2',
    Value e1 ->
    m / e2 --> m' / e2' ->
    m / Elambapp e1 e2 --> m' / Elambapp e1 e2'
| StLambapp2F : forall m e1 e2,
    Value e1 ->
    m / e2 --> fail ->
    m / Elambapp e1 e2 --> fail
| StLambapp : forall m var t e1 v2,
     Value v2 ->
     m / Elambapp (Elambda var t e1) v2 -->
     m / ([var := v2] e1)
| StFunapp1 : forall m e1 e2 m' e1',
    m / e1 --> m' / e1' ->
    m / Efunapp e1 e2 --> m' / Efunapp e1' e2
| StFunapp1F : forall m e1 e2,
    m / e1 --> fail ->
    m / Efunapp e1 e2 --> fail
| StFunapp2 : forall m e1 e2 m' e2',
    Value e1 ->
    m / e2 --> m' / e2' ->
    m / Efunapp e1 e2 --> m' / Efunapp e1 e2'
| StFunapp2F : forall m e1 e2,
    Value e1 ->
    m / e2 --> fail ->
    m / Efunapp e1 e2 --> fail
| StFunapp : forall m var b v2,
    Value v2 ->
    m / Efunapp (Efun (Elambda var Tstar b)) v2 -->
    m / Elambapp (Elambda var Tstar b) v2
| StBox1 : forall m t e m' e',
    m / e --> m' / e' ->
    m / Ebox t e --> m' / Ebox t e'
| StBox1F : forall m t e,
    m / e --> fail ->
    m / Ebox t e --> fail
| StUnbox1 : forall m t e m' e',
    m / e --> m' / e' ->
    m / Eunbox t e --> m' / Eunbox t e'
| StUnbox1F : forall m t e,
    m / e --> fail ->
    m / Eunbox t e --> fail
| StUnbox : forall m t v,
    Value v ->
    m / Eunbox t (Ebox t v) --> m / v
| StUnboxF : forall m t t' v,
    t <> t' ->
    Value v ->
    m / Eunbox t (Ebox t' v) --> fail

where "m / e --> m1 / e1" := (step m e m1 (Some e1))
  and "m / e --> 'fail'" := (step m e m None).



Definition mem_correct (m : Mem) :=
  forall a n, Value (query a n m) /\ MEmpty |= (query a n m) : Tstar.


Lemma mem_correct_empty : mem_correct EmptyMem.
Proof. unfold mem_correct; eauto using Value,Typing. Qed.


Lemma mem_correct_query : forall Γ m a n,
  mem_correct m -> Γ |= (query a n m) : Tstar.
Proof.
  intros Γ m a n Hmc.
  specialize (Hmc a n) as [? ?].
  eauto using envExt, inclusion_empty.
Qed.


Lemma mem_correct_update : forall m a idx e,
  mem_correct m -> Value e -> MEmpty |= e : Tstar ->
      mem_correct (Update a idx e m).
Proof.
  intros m a idx e Hmc.
  unfold mem_correct; intros.
  simpl.
  destruct (Nat.eq_dec a0 a); destruct (Nat.eq_dec n idx);
  simpl; subst; simpl; eauto using Typing,Value.
Qed.


Lemma mem_correct_fresh : forall m m' free,
  mem_correct m -> (free,m') = fresh m -> mem_correct m'.
Proof.
  unfold fresh. intros m m' free Hmc Heq. inversion Heq.
  eauto using mem_correct_update,Typing,Value.
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
  eauto using Typing, mem_correct_query;
  match goal with
  | [ H: _ |= _ : _ |- _ ] =>
        (inversion H; subst; eauto using Typing, subst_typing; fail)
  end.
Qed.


Theorem Preservation : forall m e t m' e',
  mem_correct m /\ MEmpty |= e : t ->
    m / e --> m' / e' ->
  mem_correct m' /\ MEmpty |= e' : t.
Proof. intuition; eauto using memPreservation,expPreservation. Qed.


Lemma value_normal : forall m e,
    Value e -> ~exists m' v, step m e m' v.
Proof.
  intros m e HV.
  induction HV; intros HEx; destruct HEx as [m' [v' Hst]];
  inversion Hst; subst; eauto;
  match goal with
  | [H: step _ (Elambda _ _ _) _ _ |- _] => inversion H end.
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

