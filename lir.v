
Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.


(*
** Tags for Lir
*)
Inductive Tag : Set := | TgNil | TgInt | TgTbl | TgFun.


Lemma dec_Tag : forall (t1 t2 : Tag), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.


Inductive IRType : Set :=
| Tag2Type : Tag  -> IRType
| IRTStar : IRType
.


Lemma dec_IRType : forall (t1 t2 : IRType), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. auto using dec_Tag. Defined.


Definition Type2Tag (t : IRType) : option Tag :=
  match t with
  | Tag2Type tg => Some tg
  | IRTStar => None
  end.


Definition IRTNil := Tag2Type TgNil.
Definition IRTInt := Tag2Type TgInt.
Definition IRTTbl := Tag2Type TgTbl.
Definition IRTFun := Tag2Type TgFun.



(*
** Addresses represent tables and functions in memory
*)
Definition address := nat.


(*
** Syntax for Lir expressions
*)
Inductive IRE : Set :=
| IRENil : IRE
| IRENum : nat -> IRE
| IREPlus : IRE -> IRE -> IRE
| IRECnst : IRE
| IRETAddr : address -> IRE  (* only at runtime *)
| IREFAddr : address -> IRE  (* only at runtime *)
| IREGet : IRE -> IRE -> IRE
| IRESet : IRE -> IRE -> IRE -> IRE
| IREVar : string -> IRE
| IRELet : string -> IRType -> IRE -> IRE -> IRE
| IREFun : string -> IRE -> IRE
| IREApp : IRE -> IRE -> IRE
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
Notation "f x" := (IREApp f x)
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


(*
** Typing rules for Lir expressions
*)
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
| IRTyTAddr : forall Γ addr, Γ |= IRETAddr addr : IRTTbl
| IRTyFAddr : forall Γ addr, Γ |= IREFAddr addr : IRTFun
| IRTyGet : forall Γ e1 e2,
    Γ |= e1 : IRTTbl ->
    Γ |= e2 : IRTStar ->
    Γ |= (IREGet e1 e2) : IRTStar
| IRTySet : forall Γ e1 e2 e3,
    Γ |= e1 : IRTTbl ->
    Γ |= e2 : IRTStar ->
    Γ |= e3 : IRTStar ->
    Γ |= (IRESet e1 e2 e3) : IRTNil
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
    Γ |= (IREApp e1 e2) : IRTStar
| IRTyBox : forall Γ e (tg : Tag),
    Γ |= e : (Tag2Type tg) ->
    Γ |= (IREBox tg e) : IRTStar
| IRTyUnbox : forall Γ e tg t,
    t = Tag2Type tg ->
    Γ |= e : IRTStar ->
    Γ |= (IREUnbox tg e) : t

where "Γ '|=' e ':' t" := (IRTyping Γ e t)
.


(*
** Types for Lir expressions are unique
*)
Lemma typeUnique : forall Γ e t t',
   (Γ  |= e : t) -> (Γ |= e : t') -> t = t'.
Proof.
  intros Γ e t t' H1.
  generalize dependent t'.
  induction H1; intros ? H2; inversion H2; subst; f_equal;
  auto ; try congruence.
Qed.


(*
** Value predicate for Lir expressions
*)
Inductive Value : IRE -> Prop :=
| Vnil : Value IRENil
| Vnum : forall n, Value (IRENum n)
| Vtbl : forall a, Value (IRETAddr a)
| Vfun : forall a, Value (IREFAddr a)
| Vbox : forall gt v, Value v -> Value (IREBox gt v)
.


(*
** Equivalent to 'Value', but computable
*)
Fixpoint isValue (e : IRE) : bool :=
  match e with
  | IRENil => true
  | IRENum _ => true
  | IRETAddr _ => true
  | IREFAddr _ => true
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


(*
** Canonical forms
*)

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
    Γ |= e : IRTTbl -> Value e -> exists a, e = IRETAddr a.
Proof.
  intros Γ e HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  eauto.
Qed.


Lemma valfun : forall Γ e,
    Γ |= e : IRTFun -> Value e -> exists a, e = IREFAddr a.
Proof.
  intros * HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  eauto.
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


(*
  Table indices. Only values are used as table indices, but we will
  allow any expression for now.
*)
Inductive Index : Set :=
| I : nat -> Tag -> Index
| NI : Index   (* indices for non-values *)
.


(*
  Normalize values used as indices, so that boxed and unboxed values
  give the same index.
*)
Fixpoint ToIndex (e : IRE) : Index :=
  match e with
  | IRENil => I 0 TgNil
  | IRENum n => I n TgInt
  | IRETAddr a => I a TgTbl
  | IREFAddr a => I a TgFun
  | IREBox t e' => ToIndex e'
  | IREUnbox t e' => ToIndex e'
  | _ => NI
  end.



Lemma Index_dec : forall (i1 i2 : Index), {i1 = i2} + {i1 <> i2}.
Proof. 
  decide equality; auto using Nat.eq_dec, dec_Tag.
Defined.


(*
** Type representing expressions that are values
*)
Inductive ExpValue : Set :=
| EV : forall e, Value e -> ExpValue.


Definition EV2Val (me : ExpValue) : IRE :=
  match me with
  | EV v _ => v
  end.


Inductive Mem : Set :=
| EmptyMem : Mem
| UpdateT :
    address -> Index -> ExpValue -> Mem -> Mem
| UpdateF :
    address -> string -> IRE -> Mem -> Mem.


Definition BoxedNil : IRE := IREBox TgNil IRENil.

Definition BoxedNilValue : Value BoxedNil := Vbox TgNil IRENil Vnil.


Fixpoint queryT (a : address) (idx : IRE) (m : Mem) : IRE :=
  match m with
  | EmptyMem => BoxedNil
  | UpdateT a' idx' v m' => if Nat.eq_dec a a' then
                                    if Index_dec (ToIndex idx) idx'
                                      then (EV2Val v)
                                      else queryT  a idx m'
                                  else queryT a idx m'
  | UpdateF _ _ _ m' => queryT a idx m'
  end.


Fixpoint queryF (a : address) (m : Mem) : (string * IRE) :=
  match m with
  | EmptyMem => (""%string, IRELet "" IRTStar (IREVar "") BoxedNil)
  | UpdateT a' _ _ m' => queryF a m'
  | UpdateF a' var body m' => if Nat.eq_dec a a' then (var, body)
                              else queryF a m'
  end.


(*
** Create a fresh address for a memory
*)
Fixpoint freshaux (m : Mem) : address :=
  match m with
  | EmptyMem => 1
  | UpdateT _ _ _ m' => S (freshaux m')
  | UpdateF _ _ _ m' => S (freshaux m')
  end.


(*
** Create a fresh address for a table and initializes
** it with {Nil = Nil}.
*)
Definition freshT (m : Mem) : (address * Mem) :=
  let f := freshaux m in
    (f, UpdateT f (I 0 TgNil) (EV BoxedNil BoxedNilValue) m).


(*
** Create a fresh address for a function and initializes
** it with the given values.
*)
Definition freshF (m : Mem) (v : string) (b : IRE) : (address * Mem) :=
  let f := freshaux m in
    (f, UpdateF f v b m).


(*
** Substitution by closed Lir expressions
*)
Reserved Notation "'[' x ':=' s ']' t" (at level 20, x constr).

Fixpoint substitution (var : string) (y : IRE)  (e : IRE) : IRE :=
 match e with
 | IRENil => e
 | IRENum n => e
 | IREPlus e1 e2 => IREPlus ([var := y] e1) ([var := y] e2)
 | IRECnst => e
 | IRETAddr a => e
 | IREFAddr a => e
 | IREGet e1 e2 => IREGet ([var := y] e1) ([var := y] e2)
 | IRESet e1 e2 e3 => IRESet ([var := y] e1) ([var := y] e2) ([var := y] e3)
 | IREVar var' => if string_dec var var' then y else e
 | IRELet var' t v body => if string_dec var var' then
                             IRELet var' t ([var := y] v) body
                           else
                             IRELet var' t ([var := y] v) ([var := y] body)
 | IREFun var' body  => if string_dec var var' then e
                    else IREFun var' ([var := y] body)
 | IREApp e1 e2 => IREApp ([var := y] e1) ([var := y] e2)
 | IREBox tg e  => IREBox tg ([var := y] e)
 | IREUnbox tg e  => IREUnbox tg ([var := y] e)
end
where "'[' x ':=' s ']' t" := (substitution x s t)
.


(*
** Extending an environment preserves typing
*)
Lemma inclusion_typing : forall Γ Γ' e te,
  inclusion Γ Γ' -> Γ |= e : te -> Γ' |= e : te.
Proof.
  intros Γ Γ' e te Hin Hty.
  generalize dependent Γ'.
  induction Hty; eauto using IRTyping, inclusion_update.
Qed.


(*
** Particular case when extending the empty environment
*)
Lemma typing_empty : forall Γ e te, MEmpty |= e : te -> Γ |= e : te.
Proof.
  eauto using inclusion_typing, inclusion_empty.
Qed.


(*
** Substitution preserves typing
*)
Lemma subst_typing : forall e2 Γ var tv te e1,
  (var |=> tv; Γ) |= e2 : te ->
  MEmpty |= e1 : tv ->
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


(*
** Evaluation steps for Lir expressions
*)
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
    (free, m') = freshT m ->
    m / IRECnst --> m' / IRETAddr free
| StGet1 : forall m e1 e2 m' e1',
    m /e1 --> m' /e1' ->
    m / IREGet e1 e2 --> m' / IREGet e1' e2
| StGet2 : forall m e1 e2 m' e2',
    Value e1 ->
    m /e2 --> m' /e2' ->
    m / IREGet e1 e2 --> m' / IREGet e1 e2'
| StGet : forall m a idx,
    Value idx ->
    m / IREGet (IRETAddr a) idx --> m / queryT a idx m
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
    m / IRESet (IRETAddr a) idx v -->
            UpdateT a (ToIndex idx) (EV v Vv) m / IRENil
| StLet1 : forall var t body m e m' e',
    m / e --> m' / e' ->
    m / IRELet var t e body --> m' / IRELet var t e' body
| StLet : forall var t e body m,
    Value e ->
    m / IRELet var t e body --> m / [var := e] body
| StFun : forall m m' v b free,
    (free, m') = freshF m v b ->
    m / IREFun v b --> m' / IREFAddr free
| StFunapp1 : forall m e1 e2 m' e1',
    m / e1 --> m' / e1' ->
    m / IREApp e1 e2 --> m' / IREApp e1' e2
| StFunapp2 : forall m e1 e2 m' e2',
    Value e1 ->
    m / e2 --> m' / e2' ->
    m / IREApp e1 e2 --> m' / IREApp e1 e2'
| StFunapp : forall m a var body v,
    Value v ->
    (var, body) = queryF a m ->
    m / IREApp (IREFAddr a) v --> m / [var := v] body
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



(*
** Fail evaluation for Lir expressions
*)
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
    m / IREApp e1 e2 --> fail
| StFunapp2F : forall m e1 e2,
    Value e1 ->
    m / e2 --> fail ->
    m / IREApp e1 e2 --> fail
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
  | [ H : context C [Nat.eq_dec ?V1 ?V2] |- _] =>
    destruct (Nat.eq_dec V1 V2); subst
  end.


(*
** Ensures that all elements of tables in a memory have type '*'
*)
Inductive mem_correct : Mem -> Prop :=
| MCE : mem_correct EmptyMem
| MCT : forall a idx v m,
     MEmpty |= EV2Val v : IRTStar ->
     mem_correct m ->
     mem_correct (UpdateT a idx v m)
| MCF : forall a var body m,
     var |=> IRTStar; MEmpty |= body : IRTStar ->
     mem_correct m ->
     mem_correct (UpdateF a var body m)
.


(*
** All expressions stored in memory tables are values
*)
Lemma MCValue : forall m a n, Value (queryT a n m).
Proof.
  intros.
  induction m; eauto using Value.
  destruct e. simpl.
  breakIndexDec; trivial.
Qed.


(*
** All expressions stored in a table of a correct memory have
** type '*'
*)
Lemma MCTy : forall m a n Γ,
    mem_correct m -> Γ |= (queryT a n m) : IRTStar.
Proof.
  intros.
  induction H; trivial.
  - eauto using typing_empty, IRTyping.
  - simpl. breakIndexDec; auto using typing_empty.
Qed.


(*
** All functions stored in a correct memory have correct types.
*)
Lemma MCTyF : forall m a var body Γ,
    (var, body) = queryF a m ->
    mem_correct m ->
    var |=> IRTStar; Γ |= body : IRTStar.
Proof.
  intros * HEq HMC.
  induction HMC.
  - simpl in HEq. injection HEq; intros; subst.
    unfold BoxedNil. auto using IRTyping.
  -  eauto.
  - simpl in HEq. breakIndexDec; eauto.
    injection HEq; intros; subst.
    eauto using inclusion_typing, inclusion_update, inclusion_empty.
Qed.



(*
** Table allocation preserves memory correctness
*)
Lemma mem_correct_freshT : forall m m' free,
  mem_correct m -> (free,m') = freshT m -> mem_correct m'.
Proof.
  unfold freshT. intros m m' free Hmc Heq. inversion Heq.
  eauto using mem_correct, IRTyping.
Qed.


(*
** Function allocation preserves memory correctness
*)
Lemma mem_correct_freshF : forall m m' var body free,
  var |=> IRTStar; MEmpty |= body : IRTStar ->
  mem_correct m ->
  (free,m') = freshF m var body ->
  mem_correct m'.
Proof.
  unfold freshF. intros * HTy Hmc Heq.
  inversion Heq; subst.
  eauto using mem_correct.
Qed.


(*
** Executing an evaluation step preserves memory
** correctness
*)
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
  eauto using mem_correct_freshT, mem_correct_freshF, mem_correct.
Qed.


Lemma boxTyping : forall e t,
  MEmpty |= IREBox t e : IRTStar -> MEmpty |= e : Tag2Type t.
Proof. intros e t H. inversion H; trivial. Qed.


(*
** Preservation of types for Lir expressions
*)
Lemma expPreservation : forall m e t m' e',
  mem_correct m ->
  MEmpty |= e : t -> m / e --> m' / e' -> MEmpty |= e' : t.
Proof.
  intros m e t m' e' Hmc HT.
  generalize dependent m'.
  generalize dependent e'.
  remember MEmpty as Γ.
  induction HT; intros e' m' Hst; inversion Hst; subst;
  eauto using IRTyping, MCTy, boxTyping, MCTyF, subst_typing.
Qed.


(*
** Main preservation theorem for Lir
** (type preservation of memory and expression)
*)
Theorem Preservation : forall m e t m' e',
  mem_correct m -> MEmpty |= e : t -> m / e --> m' / e' ->
    mem_correct m' /\ MEmpty |= e' : t.
Proof. intuition; eauto using memPreservation,expPreservation. Qed.


(*
** Values cannot be reduced
*)
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


(*
** Progress for Lir terms
*)
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
  - right. right.
    destruct (queryF x m) eqn:?.
    eauto using step, Value.
  - (* unboxing has to handle success vs. failure *)
    match goal with | [t1:Tag, t2:Tag |- _] => destruct (dec_Tag t1 t2) end;
    right; subst; eauto using step, stepF.
Qed.


(*
** Multistep
*)
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


(*
** Multistep is transitive
*)
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


(*
** Multistep subsumes step
*)
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
  - eauto using expPreservation, memPreservation.
Qed.


(*
** Preservation for multistep
*)
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
    m / e -->* m' / e' ->  m / IREApp e e2 -->* m' / IREApp e' e2.
Proof. intros e2. finishmExp. Qed.

Lemma CongFunApp2 : forall e1, Value e1 -> forall m e m' e',
    m / e -->* m' / e' ->  m / IREApp e1 e -->* m' / IREApp e1 e'.
Proof. intros e1 HV; finishmExp. Qed.

Lemma CongBox : forall m e m' e' g,
    m / e -->* m' / e' -> m / IREBox g e -->* m' / IREBox g e'.
Proof. finishmExp. Qed.

Lemma CongUnbox : forall m e m' e' g,
    m / e -->* m' / e' -> m / IREUnbox g e -->* m' / IREUnbox g e'.
Proof. finishmExp. Qed.



