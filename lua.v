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

(*
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
*)

Fixpoint Lua2Lir (Γ : IREnvironment) (e : LE) : IRE :=
  match e with
  | LENil => IREBox TgNil IRENil
  | LENum n => IREBox TgInt (IRENum n)
  | LEPlus e1 e2 => IREBox TgInt (IREPlus (IREUnbox TgInt (Lua2Lir Γ e1))
                                          (IREUnbox TgInt (Lua2Lir Γ e2)))
  | LECnst => IREBox TgTbl IRECnst
  | LEGet e1 e2 => IREGet (IREUnbox TgTbl (Lua2Lir Γ e1))
                          (IREUnbox TgInt (Lua2Lir Γ e2))
  | LESet e1 e2 e3 => IRESet (IREUnbox TgTbl (Lua2Lir Γ e1))
                             (IREUnbox TgInt (Lua2Lir Γ e2))
                             (Lua2Lir Γ e3)
  | LEVar var =>
      match In Γ var with
      | Some _ => IREVar var
      | None => IREBox TgNil IRENil  (* global variables are always nil *)
      end
  | LEFun var body =>
      IREBox TgFun (IREFun
         (IRELamb var IRTStar (Lua2Lir (var |=> IRTStar; Γ) body)))
  | LEApp e1 e2 => IREFunApp (IREUnbox TgFun (Lua2Lir Γ e1)) (Lua2Lir Γ e2)
  end.


Definition LuaEnv (Γ : IREnvironment) := forall var T,
    In Γ var = Some T -> In Γ var = Some IRTStar.


Lemma LuaEnvUpdate : forall Γ var, LuaEnv Γ -> LuaEnv (var |=> IRTStar; Γ).
Proof.
  unfold LuaEnv.
  unfold In.
  intros Γ var HLE var' T HIn.
  destruct (string_dec var' var); eauto.
Qed.


(* Issues: 1. globals; 2. type of assignments *)
Lemma Lua2LirTypeAux : forall Γ e, LuaEnv Γ -> Γ |= Lua2Lir Γ e : IRTStar.
Proof.
  intros Γ e.
  generalize dependent Γ.
  induction e; intros Γ HLE; simpl;
  try match goal with  |- context [In Γ ?var] =>
    destruct (In Γ var) eqn:? end;  (* handle variables *)
  eauto 8 using IRTyping,LuaEnvUpdate.
Qed.


Corollary Lua2LirType : forall e, MEmpty |= Lua2Lir MEmpty e : IRTStar.
Proof. intros e. eapply Lua2LirTypeAux. discriminate. Qed.

