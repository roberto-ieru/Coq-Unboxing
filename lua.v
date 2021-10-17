Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.maps.

Require Import LIR.lir.


Inductive LE : Set :=
| LENil : LE
| LENum : nat -> LE
| LEPlus : LE -> LE -> LE
| LECnst : LE
| LEGet  : LE -> LE -> LE
| LESet : LE -> LE -> LE -> LE
| LEVar : string -> LE
| LEApp : LE -> LE -> LE
| LEFun : string -> LE -> LE
.


Inductive LTyping : IREnvironment -> LE -> Prop :=
| LTyNil : forall Γ, LTyping Γ LENil
| LTyNum : forall Γ n, LTyping Γ (LENum n)
| LTyPlus : forall Γ e1 e2,
      LTyping Γ e1 ->
      LTyping Γ e2 ->
      LTyping Γ (LEPlus e1 e2)
| LTyCnst : forall Γ, LTyping Γ LECnst
| LTyGet :  forall Γ e1 e2,
      LTyping Γ e1 ->
      LTyping Γ e2 ->
      LTyping Γ (LEGet e1 e2)
| LTySet :  forall Γ e1 e2 e3,
      LTyping Γ e1 ->
      LTyping Γ e2 ->
      LTyping Γ e3 ->
      LTyping Γ (LESet e1 e2 e3)
| LTyVar : forall Γ var T,
    In Γ var = Some T ->
    LTyping Γ (LEVar var)
| LTyApp :  forall Γ e1 e2,
      LTyping Γ e1 ->
      LTyping Γ e2 ->
      LTyping Γ (LEApp e1 e2)
| LTyFun :  forall Γ var body,
      LTyping (var |=> IRTStar; Γ) body ->
      LTyping Γ (LEFun var body)
.


Fixpoint Lua2Lir (e : LE) : IRE :=
  match e with
  | LENil => IREBox TgNil IRENil
  | LENum n => IREBox TgInt (IRENum n)
  | LEPlus e1 e2 => IREBox TgInt (IREPlus (IREUnbox TgInt (Lua2Lir e1))
                                          (IREUnbox TgInt (Lua2Lir e2)))
  | LECnst => IREBox TgTbl IRECnst
  | LEGet e1 e2 => IREGet (IREUnbox TgTbl (Lua2Lir e1))
                          (IREUnbox TgInt (Lua2Lir e2))
  | LESet e1 e2 e3 => IRESet (IREUnbox TgTbl (Lua2Lir e1))
                             (IREUnbox TgInt (Lua2Lir e2))
                             (Lua2Lir e3)
  | LEVar var => IREVar var
  | LEFun var body => IREBox TgFun (IRELamb var IRTStar (Lua2Lir body))
  | LEApp e1 e2 => IREFunApp (IREUnbox TgFun (Lua2Lir e1)) (Lua2Lir e2)
  end.


Definition LuaEnv (Γ : IREnvironment) := forall var T,
    In Γ var = Some T -> T = IRTStar.


(* Theorem Lua2LirType : forall Γ e T, *)

