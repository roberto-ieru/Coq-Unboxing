(*
** LIR: Lua Intermediate Language. Syntax and semantics.
*)

Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Coq.Program.Equality.

Require Import LIR.maps.


(*
** Tags for LIR: represent unboxed types and
** tags for boxed values.
*)
Inductive Tag : Set := | TgNil | TgInt | TgTbl | TgFun.


(* Tag equality is decidable and computable *)
Lemma dec_Tag : forall (t1 t2 : Tag), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.


(*
** Types for LIR: a 'Tag2Type' represents unboxed values,
** IRTStar is the type for boxed values.
*)
Inductive IRType : Set :=
| Tag2Type : Tag  -> IRType  (* Ground Types *)
| IRTStar : IRType
.


(* Type equality is decidable and computable *)
Lemma dec_IRType : forall (t1 t2 : IRType), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. auto using dec_Tag. Defined.


(*
** Get the tag from a type, if possible.
*)
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
** Addresses represent tables and functions in memory.
*)
Definition address := nat.


(*
** Syntax for LIR terms (expressions).
*)
Inductive IRE : Set :=
| IRENil : IRE		(* nil *)
| IRENum : nat -> IRE	(* n - integer literal *)
| IREPlus : IRE -> IRE -> IRE	(* e + e *)
| IRENew : IRE		(* {} - table constructor *)
| IRETAddr : address -> IRE  (* table address - only at runtime *)
| IREFAddr : address -> IRE  (* function address - only at runtime *)
| IREGet : IRE -> IRE -> IRE	(* e[e] - table access *)
| IRESet : IRE -> IRE -> IRE -> IRE	(* e[e] := e - table assignment *)
| IREVar : string -> IRE	(* id - variables *)
| IRELet : string -> IRType -> IRE -> IRE -> IRE  (* let e:τ = e in e *)
| IREFun : string -> IRE -> IRE		(* λx. e *)
| IREApp : IRE -> IRE -> IRE	(* e e *)
| IREBox : Tag -> IRE -> IRE	(* box[τ] e *)
| IREUnbox : Tag -> IRE -> IRE	(* unbox[τ] e *)
.


(* Type environments for LIR *)
Definition IREnvironment := Map IRType.


(*
** Typing rules for LIR terms.
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
| IRTyNew : forall Γ, Γ |= IRENew : IRTTbl
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
| IRTyApp : forall Γ e1 e2,
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
** Types for LIR terms are unique.
*)
Theorem typeUnique : forall Γ e t t',
   (Γ  |= e : t) -> (Γ |= e : t') -> t = t'.
Proof.
  induction 1; inversion 1; subst; auto; congruence.
Qed.

Unset Elimination Schemes.

(*
** Value predicate for LIR terms: The only values are nil,
** numbers, and addresses, plus boxes of one of those previous values.
** (The type system forbids boxes of boxes.)
*)
Inductive Value : IRE -> Prop :=
| Vnil : Value IRENil
| Vnum : forall n, Value (IRENum n)
| Vtbl : forall a, Value (IRETAddr a)
| Vfun : forall a, Value (IREFAddr a)
| Vbox : forall gt v, Value v -> Value (IREBox gt v)
.

Set Elimination Schemes.

Scheme Value_ind := Induction for Value Sort Prop.

(*
** Value proofs are unique.
*)
Lemma Value_unique: forall v (Vv1 Vv2 : Value v), Vv1 = Vv2.
Proof.
  intros.
  dependent induction Vv1;
  dependent destruction Vv2; trivial.
  f_equal; auto.
Qed.


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


(*
** 'Value' and 'isValue' agree.
*)
Lemma isValueCorrect : forall e, Value e <-> isValue e = true.
Proof.
  split; induction e; trivial;
  inversion 1; subst; auto using Value.
Qed.


(*
** A term inside a box value is a value.
*)
Lemma valBoxVal : forall gt e, Value (IREBox gt e) -> Value e.
Proof.
  inversion 1; trivial.
Qed.


(*
** Canonical forms for Values.
*)

Lemma valnil : forall Γ e,
  Γ |= e : IRTNil -> Value e -> e = IRENil.
Proof.
  inversion 1; inversion 1; subst; congruence.
Qed.


Lemma valint : forall Γ e,
    Γ |= e : IRTInt -> Value e -> exists n, e = IRENum n.
Proof.
  inversion 1; inversion 1; try discriminate.
  eexists; auto 1.
Qed.


Lemma valtbl : forall Γ e,
    Γ |= e : IRTTbl -> Value e -> exists a, e = IRETAddr a.
Proof.
  inversion 1; inversion 1; try discriminate; eauto.
Qed.


Lemma valfun : forall Γ e,
    Γ |= e : IRTFun -> Value e -> exists a, e = IREFAddr a.
Proof.
  inversion 1; inversion 1; try discriminate; eauto.
Qed.


Lemma valbox : forall Γ e, Γ |= e : IRTStar -> Value e ->
    exists o t, e = IREBox t o /\ (Γ |= o : Tag2Type t) /\ Value o.
Proof.
  intros * HT HV.
  inversion HV;
  inversion HT; subst; try discriminate.
  match goal with
  | [H: IREBox _ _ = IREBox _ _ |- _ ] => injection H; intros; subst end.
  eexists; eexists; auto using Value.
Qed.


(*
** Table indices.
** To simplify some proofs, we encode any value used as index as an
** 'Index'. We can think of indices as isomorphic to bxoed values, so
** that in the end only boxed values are used as indices. From another
** angle, indices iron out the differences between boxed and unboxed
** values. Later we will prove that for two values, their indices are
** equal iff they are equal up to boxes and unboxes.
*)
Inductive Index : Set :=
| I : nat -> Tag -> Index
| NI : Index   (* indices for non-values *)
.


(*
** Normalize values used as indices, so that boxed and unboxed values
** give the same index.
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


(*
** This is an inverse of 'ToIndex'. It shows that Indices fully encode
** boxed values.
*)
Definition FromIndex (idx : Index) : IRE :=
  match idx with
  | I _ TgNil => IREBox TgNil IRENil
  | I n TgInt => IREBox TgInt (IRENum n)
  | I a TgTbl => IREBox TgTbl (IRETAddr a)
  | I a TgFun => IREBox TgFun (IREFAddr a)
  | NI => IREPlus (IRENum 0) (IRENum 0)   (* any non-value would do *)
  end.


(*
** For any ground value, FromIndex recovers the original value from its
** index (up to boxes).
*)
Lemma IndexValueGround : forall v tg,
  Value v ->
  MEmpty |= v : Tag2Type tg ->
  FromIndex (ToIndex v) = IREBox tg v.
Proof.
  induction 1; inversion 1; subst; simpl; trivial.
Qed.


(*
** 'FromIndex' is correct: For any boxed value, FromIndex recovers the
** original value from its index.
*)
Lemma FromIndexCorrect : forall v,
  Value v ->
  MEmpty |= v : IRTStar ->
 FromIndex (ToIndex v) = v.
Proof.
  induction 1; inversion 1; subst.
  simpl. auto using IndexValueGround.
Qed.


(* Index equality is decidable. *)
Lemma Index_dec : forall (i1 i2 : Index), {i1 = i2} + {i1 <> i2}.
Proof.
  decide equality; auto using Nat.eq_dec, dec_Tag.
Defined.


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
** Type representing terms that are values.
*)
Inductive ExpValue : Set :=
| EV : forall e, Value e -> ExpValue.


(* Extract the term from an ExpValue *)
Definition EV2Val (me : ExpValue) : IRE :=
  match me with
  | EV v _ => v
  end.


(*
** Memory for LIR.
*)
Inductive Mem : Set :=
| EmptyMem : Mem  (* the empty memory *)
| UpdateT :  (* table entries: address[index] := value *)
    address -> Index -> ExpValue -> Mem -> Mem
| UpdateF :  (* closures: address := λstring.expression *)
    address -> string -> IRE -> Mem -> Mem.


Definition BoxedNil : IRE := IREBox TgNil IRENil.

Definition BoxedNilValue : Value BoxedNil := Vbox TgNil IRENil Vnil.


(*
** Get the memory content of a table entry, or 'box nil' for undefined
** entries.
*)
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


(*
** Equal indices return equal contents.
*)
Lemma queryTIndexEq : forall m a idx idx',
  ToIndex idx = ToIndex idx' ->
  queryT a idx m = queryT a idx' m.
Proof.
  intros * HEq.
  induction m; trivial.
  simpl.
  breakIndexDec; subst; trivial;
  exfalso; auto.
Qed.


(*
** Get the memory content for closures
*)
Fixpoint queryF (a : address) (m : Mem) : (string * IRE) :=
  match m with
  | EmptyMem => (""%string, IRELet "" IRTStar (IREVar "") BoxedNil)
  | UpdateT a' _ _ m' => queryF a m'
  | UpdateF a' var body m' => if Nat.eq_dec a a' then (var, body)
                              else queryF a m'
  end.


(*
** Create a fresh address for a memory.
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
    (f, UpdateT f (ToIndex IRENil) (EV BoxedNil BoxedNilValue) m).


(*
** Create a fresh address for a function and initializes
** it with the given values.
*)
Definition freshF (m : Mem) (v : string) (b : IRE) : (address * Mem) :=
  let f := freshaux m in
    (f, UpdateF f v b m).


(*
** Substitution of closed LIR terms for variables.
*)
Reserved Notation "'[' x ':=' s ']' t" (at level 20, x constr).

Fixpoint substitution (var : string) (y : IRE)  (e : IRE) : IRE :=
 match e with
 | IRENil => e
 | IRENum n => e
 | IREPlus e1 e2 => IREPlus ([var := y] e1) ([var := y] e2)
 | IRENew => e
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
  Γ |= e : te ->
  inclusion Γ Γ' ->
  Γ' |= e : te.
Proof.
  intros * Hty Hin.
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
  induction e2; intros * HT2 HT1;
  simpl; inversion HT2; subst;
  breakStrDec;
  eauto 6 using inclusion_typing, inclusion_shadow, inclusion_permute,
    IRTyping, typing_empty, InNotEq.
  - replace te with tv by congruence.
    eauto using typing_empty.
Qed.


(*
** Reduction steps for LIR terms
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
| StNew : forall m m' free,
    (free, m') = freshT m ->
    m / IRENew --> m' / IRETAddr free
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
| StApp1 : forall m e1 e2 m' e1',
    m / e1 --> m' / e1' ->
    m / IREApp e1 e2 --> m' / IREApp e1' e2
| StApp2 : forall m e1 e2 m' e2',
    Value e1 ->
    m / e2 --> m' / e2' ->
    m / IREApp e1 e2 --> m' / IREApp e1 e2'
| StApp : forall m a var body v,
    Value v ->
    (var, body) = queryF a m ->
    m / IREApp (IREFAddr a) v --> m / IRELet var IRTStar v body
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
** Fail reduction for LIR terms
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
| StApp1F : forall m e1 e2,
    m / e1 --> fail ->
    m / IREApp e1 e2 --> fail
| StApp2F : forall m e1 e2,
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


(*
** Well-Typed Memory (heap)
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
** All terms stored in memory tables are values
*)
Lemma MCValue : forall m a n, Value (queryT a n m).
Proof.
  intros.
  induction m; eauto using Value.
  destruct e. simpl.
  breakIndexDec; trivial.
Qed.


(*
** All terms stored in a table of a correct memory have type '*'
*)
Lemma MCTy : forall m a n Γ,
    mem_correct m -> Γ |= (queryT a n m) : IRTStar.
Proof.
  induction 1; simpl; breakIndexDec;
    eauto using typing_empty, IRTyping.
Qed.


(*
** All functions stored in a correct memory have type '* -> *'.
*)
Lemma MCTyF : forall m a var body Γ,
    (var, body) = queryF a m ->
    mem_correct m ->
    var |=> IRTStar; Γ |= body : IRTStar.
Proof.
  intros * HEq HMC.
  induction HMC; simpl in HEq; breakIndexDec; eauto;
   injection HEq; intros; subst;
    unfold BoxedNil;
    eauto using IRTyping, inclusion_typing, inclusion_update, inclusion_empty.
Qed.



(*
** Table allocation preserves memory correctness
*)
Lemma mem_correct_freshT : forall m m' free,
  mem_correct m -> (free,m') = freshT m -> mem_correct m'.
Proof.
  unfold freshT. inversion 2.
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
  unfold freshF.
  inversion 3; subst.
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
  intros * ? HTy ?.
  generalize dependent e'.
  remember MEmpty as Γ.
  induction HTy; inversion 1; subst;
  eauto using mem_correct_freshT, mem_correct_freshF, mem_correct.
Qed.


(*
** A well-typed box has the correct type of element inside it.
*)
Lemma boxTyping : forall e t,
  MEmpty |= IREBox t e : IRTStar -> MEmpty |= e : Tag2Type t.
Proof. inversion 1; trivial. Qed.


(*
** Preservation of types for LIR terms
*)
Lemma expPreservation : forall m e t m' e',
  mem_correct m ->
  MEmpty |= e : t ->
  m / e --> m' / e' ->
  MEmpty |= e' : t.
Proof.
  intros * Hmc HT.
  generalize dependent e'.
  remember MEmpty as Γ.
  induction HT; inversion 1; subst;
  eauto using IRTyping, MCTy, boxTyping, MCTyF, subst_typing.
Qed.


(*
** Main Preservation theorem for LIR
** (type preservation of memory and term)
*)
Theorem Preservation : forall m e t m' e',
  mem_correct m ->
  MEmpty |= e : t ->
  m / e --> m' / e' ->
  mem_correct m' /\ MEmpty |= e' : t.
Proof. intuition; eauto using memPreservation,expPreservation. Qed.


(*
** Values cannot be reduced
*)
Theorem value_normal : forall m e m' v,
    m / e --> m' / v ->
    Value e ->
    False.
Proof.
  intros * Hst HV.
  generalize dependent m'.
  generalize dependent v.
  induction HV; inversion 1; subst; eauto.
Qed.


(*
** The same, for fail steps
*)
Theorem value_normalF : forall m e,
    m / e --> fail ->
    Value e ->
    False.
Proof.
  induction 1; inversion 1; subst; auto.
Qed.


Ltac open_value rule :=
  match goal with
    | [ Ht : MEmpty |= ?e : _,
        Hv : Value ?e |- _] =>
          eapply rule in Ht; trivial; decompose [ex or and] Ht
    end.


(*
** Regular steps and fail steps are excludent.
*)
Theorem failNfail : forall e m e' m' T,
    MEmpty |= e : T ->
    m / e --> m' / e' ->
    m / e --> fail ->
    False.
Proof.
  intros * HTy St HStF.
  generalize dependent T.
  induction St; intros; inversion HTy; inversion HStF; subst;
  eauto using value_normal, value_normalF, Value.
Qed.


(*
** Steps are deterministic, for memories.
*)
Lemma DeterministicStepM : forall m e m1 e1 m2 e2,
    m / e --> m1 / e1 ->
    m / e --> m2 / e2 ->
    m1 = m2.
Proof.
  intros * HSt1.
  generalize dependent e2.
  induction HSt1; inversion 1; subst; eauto;
   try (exfalso; eauto using value_normal, Value; fail);
   try congruence.
   f_equal. f_equal. eauto using Value_unique.
Qed.


(*
** Steps are deterministic, for terms.
*)
Theorem DeterministicStep : forall m e m1 e1 m2 e2,
    m / e --> m1 / e1 ->
    m / e --> m2 / e2 ->
    e1 = e2.
Proof.
  intros * HSt1.
  generalize dependent e2.
  induction HSt1; inversion 1; subst; eauto;
   try (exfalso; eauto using value_normal, Value; fail);
   f_equal; eauto; congruence.
Qed.


(*
** Progress for LIR terms
*)
Theorem Progress : forall m e t,
    MEmpty |= e : t  ->
    Value e \/
    (m / e --> fail \/ exists m' e', m / e --> m' / e').
Proof.
  intros * Hty.
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

  - (* App *)
    right. right.
    match goal with [a: address |- _] => destruct (queryF a m) eqn:? end.
    eauto using step, Value.

  - (* unboxing has to handle success vs. failure *)
    match goal with | [t1:Tag, t2:Tag |- _] => destruct (dec_Tag t1 t2) end;
    right; subst; eauto using step, stepF.
Qed.


(*
** Multisteps
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
| MStStepF : forall m e m' e',
    m / e -->* m' / e' ->
    m' / e' --> fail ->
    m / e -->* fail

where "m / e -->* 'fail'" := (multistepF m e)
.


(*
** An evaluation that fails in one step fails in multiple steps.
*)
Lemma multistepF1 : forall m e, m / e --> fail -> m / e -->* fail.
Proof.
  eauto using multistep, multistepF.
Qed.


(*
** Multistep is transitive
*)
Lemma multiTrans : forall m0 e0 m1 e1 m2 e2,
    m0 / e0 -->* m1 / e1 ->
    m1 / e1 -->* m2 / e2 ->
    m0 / e0 -->* m2 / e2.
Proof.
  induction 1; eauto using multistep.
Qed.


(*
** Multistep subsumes step
*)
Lemma multistep1 : forall m0 e0 m1 e1,
    m0 / e0 --> m1 / e1 ->
    m0 / e0 -->* m1 / e1.
Proof. eauto using multistep. Qed.


(*
** Soundness for LIR. (Progress for multiple steps.)
*)
Theorem Soundness : forall m e t m' e',
    mem_correct m ->
    MEmpty |= e : t  ->
    m / e -->* m' / e' ->
    Value e' \/
   (m' / e' --> fail \/ exists m'' e'', m' / e' --> m'' / e'').
Proof.
  induction 3; eauto using Progress, expPreservation, memPreservation.
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
  eapply Preservation; eauto using Preservation.
Qed.


Ltac finishmExp :=
  intros * Hmt;
  induction Hmt; eauto using step,multistep.


(*
** Congruence rules: e -->* e' implies that F[e] -->* F[e']
*)

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

Lemma CongApp1 : forall e2 m e m' e',
    m / e -->* m' / e' ->  m / IREApp e e2 -->* m' / IREApp e' e2.
Proof. intros e2. finishmExp. Qed.

Lemma CongApp2 : forall e1, Value e1 -> forall m e m' e',
    m / e -->* m' / e' ->  m / IREApp e1 e -->* m' / IREApp e1 e'.
Proof. intros e1 HV; finishmExp. Qed.

Lemma CongBox : forall m e m' e' g,
    m / e -->* m' / e' -> m / IREBox g e -->* m' / IREBox g e'.
Proof. finishmExp. Qed.

Lemma CongUnbox : forall m e m' e' g,
    m / e -->* m' / e' -> m / IREUnbox g e -->* m' / IREUnbox g e'.
Proof. finishmExp. Qed.

