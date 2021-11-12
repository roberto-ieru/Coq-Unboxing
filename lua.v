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
| LEGet  : LE -> LE -> LE
| LESet : LE -> LE -> LE -> LE
| LEVar : string -> LE
| LEApp : LE -> LE -> LE
| LEFun : string -> LE -> LE
.


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


Lemma LuaIsDyn : forall Γ e, Lua2Lir Γ e = dyn (Lua2Lir Γ e).
Proof.
  intros Γ e.
  generalize dependent Γ.
  induction e; intros Γ; simpl; try congruence.
  destruct (In Γ s); trivial.
Qed.


Corollary Lua2LirType : forall e, MEmpty |= Lua2Lir MEmpty e : IRTStar.
Proof. intros e. eapply Lua2LirTypeAux. discriminate. Qed.


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


(*
Ltac destructTag :=
  simpl;
  match goal with
  [ |- context F [tagOf ?C ?E] ] =>
     idtac C E; destruct (tagOf C E); simpl end.


Lemma all : forall Γ e t,
    PTyping Γ e t ->
    dyn (Pall2Lir Γ e) = Lua2Lir (TP2TGamma Γ) (Pall2Lua e).
Proof.
  intros Γ e.
  generalize dependent Γ.
  induction e; intros Γ ? HTy; inversion HTy; subst;
  repeat match goal with
  |[ HT : PTyping ?C ?E ?T,
     IH : forall _, PTyping ?C ?E _ -> _ |- _] =>
      specialize (IH T HT) end;
  simpl; try (repeat destructTag; congruence).
  - repeat match goal with
   [ HT: PTyping ?G ?E ?T,
     IH: forall _ _, PTyping _ ?E _ -> _ |- _] =>
         specialize (IH G T HT)
     end. congruence.
  - repeat match goal with
   [ HT: PTyping ?G ?E ?T,
     IH: forall _ _, PTyping _ ?E _ -> _ |- _] =>
         specialize (IH G T HT)
     end.
     destructTag; congruence.

  - repeat f_equal. rewrite IHe1.
  - inversion H1.
  - destruct (tagOf (s |=> p; MEmpty) e); simpl.
  - admit.
Admitted.
*)


