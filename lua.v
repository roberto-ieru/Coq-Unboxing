Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.


Require Import LIR.pallene.
Require Import LIR.lir.
Require Import LIR.dyn.


Inductive LE : Set :=
| LENil : LE
| LENum : nat -> LE
| LEPlus : LE -> LE -> LE
| LECnst : LE
| LEAddr : address -> LE
| LEGet  : LE -> LE -> LE
| LESet : LE -> LE -> LE -> LE
| LEVar : string -> LE
| LEApp : LE -> LE -> LE
| LEFun : string -> LE -> LE
.


Inductive LEWT : IREnvironment -> LE -> Prop :=
| WTNil : forall Γ, LEWT Γ LENil
| WTNum : forall Γ n, LEWT Γ (LENum n)
| WTPlus : forall Γ e1 e2, LEWT Γ e1 -> LEWT Γ e2 -> LEWT Γ (LEPlus e1 e2)
| WTCnst : forall Γ, LEWT Γ LECnst
| WTAddr : forall Γ a, LEWT Γ (LEAddr a)
| WTGet : forall Γ e1 e2, LEWT Γ e1 -> LEWT Γ e2 -> LEWT Γ (LEGet e1 e2)
| WTSet : forall Γ e1 e2 e3, LEWT Γ e1 -> LEWT Γ e2 -> LEWT Γ e3 ->
               LEWT Γ (LESet e1 e2 e3)
| WTVar : forall Γ var, In Γ var = Some IRTStar -> LEWT Γ (LEVar var)
| WTApp : forall Γ e1 e2, LEWT Γ e1 -> LEWT Γ e2 -> LEWT Γ (LEApp e1 e2)
| WTFun : forall Γ var body, LEWT (var |=> IRTStar; Γ) body ->
            LEWT Γ (LEFun var body)
.


Fixpoint Lua2Lir (e : LE) : IRE :=
  match e with
  | LENil => IREBox TgNil IRENil
  | LENum n => IREBox TgInt (IRENum n)
  | LEPlus e1 e2 => IREBox TgInt (IREPlus (IREUnbox TgInt (Lua2Lir e1))
                                          (IREUnbox TgInt (Lua2Lir e2)))
  | LECnst => IREBox TgTbl IRECnst
  | LEGet e1 e2 => IREGet (IREUnbox TgTbl (Lua2Lir e1)) (Lua2Lir e2)
  | LESet e1 e2 e3 => IRESet (IREUnbox TgTbl (Lua2Lir e1))
                             (Lua2Lir e2)
                             (Lua2Lir e3)
  | LEAddr a => IREBox TgTbl (IREAddr a)
  | LEVar var => IREVar var
  | LEFun var body =>
      IREBox TgFun (IREFun (IRELamb var IRTStar (Lua2Lir body)))
  | LEApp e1 e2 => IREFunApp (IREUnbox TgFun (Lua2Lir e1)) (Lua2Lir e2)
  end.


Inductive LMem : Set :=
| LEmptyMem : LMem
| LUpdate : address -> Index -> LE -> LMem -> LMem.


Axiom LToIndex : LE -> Index.

Axiom LuaIndex : forall e, LToIndex e = ToIndex (Lua2Lir e).

Coercion LToIndex : LE >-> Index.


Fixpoint Lquery (a : address) (idx : LE) (m : LMem) :=
  match m with
  | LEmptyMem => LENil
  | LUpdate a' idx' e m' => if Nat.eq_dec a a' then
                           if Index_dec idx idx' then e
                           else Lquery  a idx m'
                         else Lquery  a idx m'
  end.


Fixpoint Lfreshaux (m : LMem) : address :=
  match m with
  | LEmptyMem => 1
  | LUpdate _ _ _ m' => S (Lfreshaux m')
  end.


Definition Lfresh (m : LMem) : (address * LMem) :=
  let f := Lfreshaux m in (f, LUpdate f LENil LENil m).


Reserved Notation "'[' x ':=' s ']' t" (at level 20, x constr).


Fixpoint substitution (var : string) (y : LE)  (e : LE) : LE :=
 match e with
 | LENil => e
 | LENum n => e
 | LEPlus e1 e2 => LEPlus ([var := y] e1) ([var := y] e2)
 | LECnst => e
 | LEAddr a => e
 | LEGet e1 e2 => LEGet ([var := y] e1) ([var := y] e2)
 | LESet e1 e2 e3 => LESet ([var := y] e1) ([var := y] e2) ([var := y] e3)
 | LEVar var' => if string_dec var var' then y else e
 | LEFun var' body => if string_dec var var' then e
                       else LEFun var' ([var := y] body)
 | LEApp e1 e2 => LEApp ([var := y] e1) ([var := y] e2)
end
where "'[' x ':=' s ']' t" := (substitution x s t)
.


Inductive LValue : LE -> Prop :=
| LVnil : LValue LENil
| LVnum : forall n, LValue (LENum n)
| LVtbl : forall a, LValue (LEAddr a)
| LVfun : forall var e, LValue (LEFun var e)
.


(* Issues: 1. globals; 2. type of assignments *)
Lemma Lua2LirTypeAux : forall Γ e, LEWT Γ e -> Γ |= Lua2Lir e : IRTStar.
Proof.
  intros Γ e.
  generalize dependent Γ.
  induction e; intros Γ HLE; inversion HLE; subst; simpl;
  eauto 8 using IRTyping.
Qed.


Lemma LuaIsDyn : forall e, Lua2Lir e = dyn (Lua2Lir e).
Proof.
  intros e.
  induction e; simpl; try congruence.
Qed.


Corollary Lua2LirType : forall e,
    LEWT MEmpty e -> MEmpty |= Lua2Lir e : IRTStar.
Proof. intros e. eapply Lua2LirTypeAux. Qed.


Fixpoint Pall2Lua (e : PE) : LE :=
  match e with
  | PENil => LENil
  | PENum n => LENum n
  | PEPlus e1 e2 => LEPlus (Pall2Lua e1) (Pall2Lua e2)
  | PENew _ => LECnst
  | PEGet e1 e2 => LEGet (Pall2Lua e1) (Pall2Lua e2)
  | PESet e1 e2 e3 => LESet (Pall2Lua e1) (Pall2Lua e2) (Pall2Lua e3)
  | PEVar var => LEVar var
  | PEApp e1 e2 => LEApp (Pall2Lua e1) (Pall2Lua e2)
  | PEFun var _ e => LEFun var (Pall2Lua e)
  | PECast e _ => Pall2Lua e
  end.

