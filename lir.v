
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
Proof. decide equality. Defined.


Inductive IRType : Set :=
| IRTNil
| IRTInt
| IRTTbl
| IRTFun
| IRTStar
.


Inductive BaseType : Set :=
| BGround : Tag  -> BaseType
| BStar : BaseType
.


Definition Tag2Type (tg : Tag) : IRType :=
  match tg with
  | TgNil => IRTNil
  | TgInt => IRTInt
  | TgTbl => IRTTbl
  | TgFun => IRTFun
  end.


Definition Type2Tag (t : IRType) : option Tag :=
  match t with
  | IRTNil => Some TgNil
  | IRTInt => Some TgInt
  | IRTTbl => Some TgTbl
  | IRTFun => Some TgFun
  | IRTStar => None
  end.


Definition Base2Type (bt : BaseType) : IRType :=
  match bt with
  | BGround tg => Tag2Type tg
  | BStar => IRTStar
  end.


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


(*
Coercion IRENum : nat >-> IRE.
Coercion IREVar : string >-> IRE.

Declare Custom Entry IRE.

Declare Scope IRE_scope.

Notation "'<{' e '}>'" := e
    (at level 0, e custom IRE at level 99) : IRE_scope.
Notation "( x )" := x (in custom IRE, x at level 99) : IRE_scope.
Notation "x" := x (in custom IRE at level 0, x constr at level 0) : IRE_scope.
Notation "f x" := (IREFunApp f x)
                  (in custom IRE at level 0,
                  f constr at level 0, x constr at level 9) : IRE_scope.
Notation "x + y" := (IREPlus x y)
   (in custom IRE at level 50, left associativity).
Notation "x '[' y ']'" := (IREGet x y)
    (in custom IRE at level 80).
Notation "x '[' y ']' '=' z" := (IRESet x y z)
    (in custom IRE at level 80, z at level 90).
Notation "{}" := (IRECnst) (in custom IRE at level 100).
Notation "'λ' x ':' t '.' e" := (IREFun x t e)
    (in custom IRE at level 100, e at level 110).
Notation "'box[' t '](' x ')'" := (IREBox t x)
    (in custom IRE at level 100).
Notation "'unbox[' t '](' x ')'" := (IREUnbox t x)
    (in custom IRE at level 100).

(* just for examples *)
Definition X := "X"%string.
Definition F := "F"%string.

Open Scope IRE_scope.

Unset Printing Notations.
Set Printing Coercions.
Check <{ X[0] = X[0] + 1 }>.
Unset Printing Coercions.
Set Printing Notations.
Check <{ X[0] = X[0] + 1 }>.

*)

Definition IREnvironment := Map IRType.


Reserved Notation "Γ '|=' e ':' t"  (at level 40, no associativity,
                                     e at next level).

Inductive IRTyping : IREnvironment -> IRE -> IRType -> Prop :=
| IRTyNil : forall Γ, Γ |= IRENil : IRTNil
| IRTyVar : forall Γ var T,
    In Γ var = Some T ->
    Γ |= IREVar var : T
| IRTyInt : forall Γ n, Γ |= IRENum n : IRTInt
| IRTyPlus : forall Γ e1 e2,
    Γ |= e1 : IRTInt ->
    Γ |= e2 : IRTInt ->
    Γ |= (IREPlus e1 e2) : IRTInt
| IRTyCnst : forall Γ, Γ |= IRECnst : IRTTbl
| IRTyAddr : forall Γ addr, Γ |= IREAddr addr : IRTTbl
| IRTyGet : forall Γ e1 e2,
    Γ |= e1 : IRTTbl ->
    Γ |= e2 : IRTStar ->
    Γ |= (IREGet e1 e2) : IRTStar
| IRTySet : forall Γ e1 e2 e3,
    Γ |= e1 : IRTTbl ->
    Γ |= e2 : IRTStar ->
    Γ |= e3 : IRTStar ->
    Γ |= (IRESet e1 e2 e3) : IRTStar
| IRTyLet : forall Γ var t t' v body,
    var |=> t; Γ |= body : t' ->
    Γ |= v : t ->
    Γ |= (IRELet var t v body) : t'
| IRTyFun : forall Γ var body,
    var |=> IRTStar; Γ |= body : IRTStar ->
    Γ |= (IREFun var body) : IRTFun
| IRTyFunApp : forall Γ e1 e2,
    Γ |= e1 : IRTFun ->
    Γ |= e2 : IRTStar ->
    Γ |= (IREFunApp e1 e2) : IRTStar
| IRTyBox : forall Γ e (tg : Tag),
    Γ |= e : (Tag2Type tg) ->
    Γ |= (IREBox tg e) : IRTStar
| IRTyUnbox : forall Γ e tg t,
    t = Tag2Type tg ->
    Γ |= e : IRTStar ->
    Γ |= (IREUnbox tg e) : t

where "Γ '|=' e ':' t" := (IRTyping Γ e t)
.


Lemma typeUnique : forall Γ e t t',
   (Γ  |= e : t) -> (Γ |= e : t') -> t = t'.
Proof.
  intros Γ e t t' H1.
  generalize dependent t'.
  induction H1; intros ? H2; inversion H2; subst; f_equal;
  auto ; try congruence.
Qed.


Lemma envExt : forall Γ Γ' e t,
    inclusion Γ Γ' -> Γ |= e : t  -> Γ' |= e : t.
Proof.
  intros Γ Γ' e t Hinc Hty.
  generalize dependent Γ'.
  induction Hty; intros Γ' Hinc; subst;
  eauto using IRTyping, inclusion_update.
Qed.



Inductive Value : IRE -> Prop :=
| Vnil : Value IRENil
| Vnum : forall n, Value (IRENum n)
| Vtbl : forall a, Value (IREAddr a)
| Vfun : forall var e, Value (IREFun var e)
| Vbox : forall gt v, Value v -> Value (IREBox gt v)
.


Fixpoint isValue (e : IRE) : bool :=
  match e with
  | IRENil => true
  | IRENum _ => true
  | IREAddr _ => true
  | IREFun _ _ => true
  | IREBox _ e => isValue e
  | _ => false
  end.


Lemma isValueCorrect : forall e, Value e <-> isValue e = true.
Proof.
  split; induction e; intros H; trivial;
  inversion H; subst; eauto using Value.
Qed.


Lemma valBoxVal : forall gt e, Value (IREBox gt e) -> Value e.
Proof.
  intros * HV.
  inversion HV; trivial.
Qed.


Lemma valnil : forall Γ e,
  Γ |= e : IRTNil -> Value e -> e = IRENil.
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; congruence.
Qed.


Lemma valint : forall Γ e,
    Γ |= e : IRTInt -> Value e -> exists n, e = IRENum n.
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  eexists; auto 1.
Qed.


Lemma valtbl : forall Γ e,
    Γ |= e : IRTTbl -> Value e -> exists a, e = IREAddr a.
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  eexists; auto 1.
Qed.


Lemma valfun : forall Γ e,
    Γ |= e : IRTFun -> Value e -> exists var b, e = IREFun var b.
Proof.
  intros * HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  inversion H2; subst.
  eexists; eexists; auto using Value.
Qed.


Lemma valbox : forall Γ e, Γ |= e : IRTStar -> Value e ->
    exists o t, e = IREBox t o /\ (Γ |= o : Tag2Type t) /\ Value o.
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


Inductive ExpValue : Set :=
| EV : forall e, Value e -> ExpValue.


Definition EV2Val (me : ExpValue) :=
  match me with
  | EV v _ => v
  end.


Inductive Mem : Set :=
| EmptyMem : Mem
| Update :
    address -> Index -> ExpValue -> Mem -> Mem.


Definition BoxedNil := IREBox TgNil IRENil.

Definition BoxedNilValue : Value BoxedNil := Vbox TgNil IRENil Vnil.


Fixpoint query (a : address) (idx : IRE) (m : Mem) :=
  match m with
  | EmptyMem => BoxedNil
  | Update a' idx' v m' => if Nat.eq_dec a a' then
                                    if Index_dec idx idx' then (EV2Val v)
                                    else query  a idx m'
                                  else query  a idx m'
  end.


Fixpoint freshaux (m : Mem) : address :=
  match m with
  | EmptyMem => 1
  | Update _ _ _ m' => S (freshaux m')
  end.


Definition fresh (m : Mem) : (address * Mem) :=
  let f := freshaux m in
    (f, Update f BoxedNil (EV BoxedNil BoxedNilValue) m).


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
 | IRELet var' t v body => if string_dec var var' then
                             IRELet var' t ([var := y] v) body
                           else
                             IRELet var' t ([var := y] v) ([var := y] body)
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


Lemma typing_empty : forall Γ e te, MEmpty |= e : te -> Γ |= e : te.
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


Inductive step : Mem -> IRE -> Mem -> IRE -> Prop :=
| StPlus1 : forall m e1 e2 m' e1',
    m / e1 --> m' / e1' ->
    m / IREPlus e1 e2 --> m' / IREPlus e1' e2
| StPlus2 : forall m e1 e2 m' e2',
    Value e1 ->
    m / e2 --> m' / e2' ->
    m /  IREPlus e1 e2 --> m' /  IREPlus e1 e2'
| StPlus : forall m n1 n2,
    m /  IREPlus (IRENum n1) (IRENum n2) --> m /  IRENum (n1 + n2)
| StCstr : forall m m' free,
    (free, m') = fresh m ->
    m / IRECnst --> m' / IREAddr free
| StGet1 : forall m e1 e2 m' e1',
    m /e1 --> m' /e1' ->
    m / IREGet e1 e2 --> m' / IREGet e1' e2
| StGet2 : forall m e1 e2 m' e2',
    Value e1 ->
    m /e2 --> m' /e2' ->
    m / IREGet e1 e2 --> m' / IREGet e1 e2'
| StGet : forall m a idx,
    Value idx ->
    m / IREGet (IREAddr a) idx --> m / query a idx m
| StSet1 : forall m e1 e2 e3 m' e1',
    m / e1 --> m' / e1' ->
    m / IRESet e1 e2 e3 --> m' / IRESet e1' e2 e3
| StSet2 : forall m e1 e2 e3 m' e2',
    Value e1 ->
    m / e2 --> m' / e2' ->
    m / IRESet e1 e2 e3 --> m' / IRESet e1 e2' e3
| StSet3 : forall m e1 e2 e3 m' e3',
    Value e1 -> Value e2 ->
    m / e3 --> m' / e3' ->
    m / IRESet e1 e2 e3 --> m' / IRESet e1 e2 e3'
| StSet : forall m a idx v,
    Value idx ->
    forall Vv : Value v,
    m / IRESet (IREAddr a) idx v --> Update a idx (EV v Vv) m / v
| StLet1 : forall var t body m e m' e',
    m / e --> m' / e' ->
    m / IRELet var t e body --> m' / IRELet var t e' body
| StLet : forall var t e body m,
    Value e ->
    m / IRELet var t e body --> m / [var := e] body
| StFunapp1 : forall m e1 e2 m' e1',
    m / e1 --> m' / e1' ->
    m / IREFunApp e1 e2 --> m' / IREFunApp e1' e2
| StFunapp2 : forall m e1 e2 m' e2',
    Value e1 ->
    m / e2 --> m' / e2' ->
    m / IREFunApp e1 e2 --> m' / IREFunApp e1 e2'
| StFunapp : forall m var body v2,
    Value v2 ->
    m / IREFunApp (IREFun var body) v2 --> m / [var := v2] body
| StBox1 : forall m t e m' e',
    m / e --> m' / e' ->
    m / IREBox t e --> m' / IREBox t e'
| StUnbox1 : forall m t e m' e',
    m / e --> m' / e' ->
    m / IREUnbox t e --> m' / IREUnbox t e'
| StUnbox : forall m t v,
    Value v ->
    m / IREUnbox t (IREBox t v) --> m / v

where "m / e --> m1 / e1" := (step m e m1 e1).


Inductive stepF : Mem -> IRE -> Prop :=
| StPlus1F : forall m e1 e2,
    m / e1 --> fail ->
    m / IREPlus e1 e2 --> fail
| StPlus2F : forall m e1 e2,
    Value e1 ->
    m / e2 --> fail ->
    m /  IREPlus e1 e2 --> fail
| StGet1F : forall m e1 e2,
    m /e1 --> fail ->
    m / IREGet e1 e2 --> fail
| StGet2F : forall m e1 e2,
    Value e1 ->
    m /e2 --> fail ->
    m / IREGet e1 e2 --> fail
| StSet1F : forall m e1 e2 e3,
    m / e1 --> fail ->
    m / IRESet e1 e2 e3 --> fail
| StSet2F : forall m e1 e2 e3,
    Value e1 ->
    m / e2 --> fail ->
    m / IRESet e1 e2 e3 --> fail
| StSet3F : forall m e1 e2 e3,
    Value e1 -> Value e2 ->
    m / e3 --> fail ->
    m / IRESet e1 e2 e3 --> fail
| StLet1F : forall var t e body m,
    m / e --> fail ->
    m / IRELet var t e body --> fail
| StFunapp1F : forall m e1 e2,
    m / e1 --> fail ->
    m / IREFunApp e1 e2 --> fail
| StFunapp2F : forall m e1 e2,
    Value e1 ->
    m / e2 --> fail ->
    m / IREFunApp e1 e2 --> fail
| StBox1F : forall m t e,
    m / e --> fail ->
    m / IREBox t e --> fail
| StUnbox1F : forall m t e,
    m / e --> fail ->
    m / IREUnbox t e --> fail
| StUnboxF : forall m t t' v,
    t <> t' ->
    Value v ->
    m / IREUnbox t (IREBox t' v) --> fail

 where "m / e --> 'fail'" := (stepF m e)
.


Ltac breakIndexDec :=
  repeat match goal with
  | [ |- context C [Nat.eq_dec ?V1 ?V2] ] =>
    destruct (Nat.eq_dec V1 V2)
  | [ |- context C [Index_dec ?V1 ?V2] ] =>
    destruct (Index_dec V1 V2) eqn:? ;
  try easy
  end.


Inductive mem_correct : Mem -> Prop :=
| MCE : mem_correct EmptyMem
| MCU : forall a idx v m,
     MEmpty |= EV2Val v : IRTStar ->
     mem_correct m ->
     mem_correct (Update a idx v m).


Lemma MCValue : forall m a n, Value (query a n m).
Proof.
  intros.
  induction m; eauto using Value.
  destruct e. simpl.
  breakIndexDec; trivial.
Qed.


Lemma MCTy : forall m a n Γ,
    mem_correct m -> Γ |= (query a n m) : IRTStar.
Proof.
  intros.
  induction H.
  - eauto using typing_empty, IRTyping.
  - simpl. breakIndexDec; auto using typing_empty.
Qed.


Lemma mem_correct_fresh : forall m m' free,
  mem_correct m -> (free,m') = fresh m -> mem_correct m'.
Proof.
  unfold fresh. intros m m' free Hmc Heq. inversion Heq.
  eauto using mem_correct, IRTyping.
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
  eauto using mem_correct_fresh, mem_correct.
Qed.


Lemma funcTyping :  forall var body e,
    MEmpty |= IREFun var body : IRTFun ->
    MEmpty |= e : IRTStar ->
    MEmpty |= [var := e] body : IRTStar.
Proof.
  intros * HT1 HT2.
  inversion HT1; subst; eauto using subst_typing.
Qed.


Lemma boxTyping : forall e t,
  MEmpty |= IREBox t e : IRTStar -> MEmpty |= e : Tag2Type t.
Proof. intros e t H. inversion H; trivial. Qed.


Lemma expPreservation : forall m e t m' e',
  mem_correct m ->
  MEmpty |= e : t -> m / e --> m' / e' -> MEmpty |= e' : t.
Proof.
  intros m e t m' e' Hmc HT.
  generalize dependent m'.
  generalize dependent e'.
  remember MEmpty as Γ.
  induction HT; intros e' m' Hst; inversion Hst; subst;
  eauto using IRTyping, MCTy, boxTyping, funcTyping, subst_typing.
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
  end;
  subst;
  (* trivial steps and failures *)
  try (right; auto using stepF; fail);
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
  try (unshelve (right; right; eauto using step, eq_refl); trivial; fail).
  - (* cannot find the correct sequence with StSet3 ? *)
    right. right. eexists. eexists.
    eapply StSet3; eauto.
  - (* unboxing has to handle success vs. failure *)
    match goal with | [t1:Tag, t2:Tag |- _] => destruct (dec_Tag t1 t2) end;
    right; subst; eauto using step, stepF.
Qed.


Reserved Notation "m '/' e -->* m1 '/' e1"
(at level 40, e at level 39, m1 at level 39, e1 at level 39).
Reserved Notation "m '/' e -->* 'fail'"
(at level 40, e at level 39).

Inductive multistep : Mem -> IRE -> Mem -> IRE -> Prop :=
| MStRefl : forall m e, m / e -->* m / e
| MStMStep : forall m e m' e' m'' e'',
    m / e --> m' / e' ->
    m' / e' -->* m'' / e'' ->
    m / e -->* m'' / e''

where "m / e -->* m1 / e1" := (multistep m e m1 e1)
.


Inductive multistepF : Mem -> IRE -> Prop :=
| MStStepF : forall m e,
    m / e --> fail ->
    m / e -->* fail
| MStMStepF : forall m e m' e',
    m / e --> m' / e' ->
    m' / e' -->* fail ->
    m / e -->* fail

where "m / e -->* 'fail'" := (multistepF m e)
.

Lemma multiTrans : forall m0 e0 m1 e1 m2 e2,
    m0 / e0 -->* m1 / e1 ->
    m1 / e1 -->* m2 / e2 ->
    m0 / e0 -->* m2 / e2.
Proof.
  intros m0 e0 m1 e1 m2 e2 H0 H1.
  generalize dependent m2.
  generalize dependent e2.
  induction H0; intros ? H2; trivial.
  eauto using multistep.
Qed.


Lemma multistep1 : forall m0 e0 m1 e1,
    m0 / e0 --> m1 / e1 ->
    m0 / e0 -->* m1 / e1.
Proof. eauto using multistep. Qed.


Theorem Soundness : forall m e t m' e',
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


Lemma multipreservation : forall m1 e1 m2 e2 t,
    MEmpty |= e1 : t ->
    mem_correct m1 ->
    m1 / e1 -->* m2 / e2 ->
    MEmpty |= e2 : t.
Proof.
  intros * Hty HM HSt.
  induction HSt; trivial.
  apply IHHSt;
  eapply Preservation; eauto.
Qed.


Ltac finishmExp :=
  intros * Hmt;
  induction Hmt; eauto using step,multistep.


Lemma CongPlus1 : forall e2 m e m' e',
    m / e -->* m' / e' ->  m / IREPlus e e2 -->* m' / IREPlus e' e2.
Proof. intros e2. finishmExp. Qed.

Lemma CongPlus2 : forall e1, Value e1 -> forall m e m' e',
    m / e -->* m' / e' ->  m / IREPlus e1 e -->* m' / IREPlus e1 e'.
Proof. intros e1 HV; finishmExp. Qed.

Lemma CongGet1 : forall e2 m e m' e',
    m / e -->* m' / e' ->  m / IREGet e e2 -->* m' / IREGet e' e2.
Proof. intros e2; finishmExp. Qed.

Lemma CongGet2 : forall e1, Value e1 -> forall m e m' e',
    m / e -->* m' / e' ->  m / IREGet e1 e -->* m' / IREGet e1 e'.
Proof. intros e1 HV; finishmExp. Qed.

Lemma CongSet1 : forall e2 e3 m e m' e',
    m / e -->* m' / e' ->  m / IRESet e e2 e3 -->* m' / IRESet e' e2 e3.
Proof. intros e2 e3; finishmExp. Qed.

Lemma CongSet2 : forall e1, Value e1 -> forall e3 m e m' e',
    m / e -->* m' / e' ->  m / IRESet e1 e e3 -->* m' / IRESet e1 e' e3.
Proof. intros e1 HV e3; finishmExp. Qed.

Lemma CongSet3 : forall e1 e2, Value e1 -> Value e2 -> forall m e m' e',
    m / e -->* m' / e' ->  m / IRESet e1 e2 e -->* m' / IRESet e1 e2 e'.
Proof. intros e1 e2 HV1 HV2; finishmExp. Qed.

Lemma CongLet : forall var t body m e m' e',
    m / e -->* m' / e' ->
    m / IRELet var t e body -->* m' / IRELet var t e' body.
Proof. finishmExp. Qed.

Lemma CongFunApp1 : forall e2 m e m' e',
    m / e -->* m' / e' ->  m / IREFunApp e e2 -->* m' / IREFunApp e' e2.
Proof. intros e2. finishmExp. Qed.

Lemma CongFunApp2 : forall e1, Value e1 -> forall m e m' e',
    m / e -->* m' / e' ->  m / IREFunApp e1 e -->* m' / IREFunApp e1 e'.
Proof. intros e1 HV; finishmExp. Qed.

Lemma CongBox : forall m e m' e' g,
    m / e -->* m' / e' -> m / IREBox g e -->* m' / IREBox g e'.
Proof. finishmExp. Qed.

Lemma CongUnbox : forall m e m' e' g,
    m / e -->* m' / e' -> m / IREUnbox g e -->* m' / IREUnbox g e'.
Proof. finishmExp. Qed.



