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
      IREBox TgFun (IREFun var IRTStar
         (IRELet var IRTStar (IREVar var) (Lua2Lir body)))
  | LEApp e1 e2 => IREFunApp (IREUnbox TgFun (Lua2Lir e1)) (Lua2Lir e2)
  end.


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


Lemma dynCast : forall (t1 t2 : BaseType) (e : IRE),
    dyn (Cast t1 t2 e) = dyn e.
Proof.
  intros t1 t2 e.
  unfold Cast.
  destruct t1; destruct t2; simpl; trivial.
  destruct (dec_Tag t t0); simpl; trivial.
Qed.


Theorem PallLua : forall Γ e t,
    PTyping Γ e t -> Lua2Lir (Pall2Lua e) = dyn (Pall2Lir Γ e).
Proof.
  intros Γ e.
  generalize dependent Γ.
  induction e; intros Γ t Hty; inversion Hty; subst;
  trivial;
  (* instantiate induction hypotheses *)
  repeat match goal with
  [IH: _ -> _ -> PTyping _ ?E _ -> _,
   HTy: PTyping _ ?E _ |- _ ] =>
    specialize (IH _ _ HTy)
  end;
  (* eliminate casts *)
  simpl;
  repeat rewrite dynCast;
  (* break if's from casts *)
  repeat match goal with [ |- context [tagOf ?G ?E] ] =>
    destruct (tagOf G E) end;
  simpl;
  congruence.
Qed.


Theorem LuaIsDyn : forall e, Lua2Lir e = dyn (Lua2Lir e).
Proof.
  induction e; simpl; congruence.
Qed.


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
| LVfun : forall var body, LValue (LEFun var body)
.


Reserved Notation "m '/' e ==> m1 '/' e1"
(at level 40, e at level 39, m1 at level 39, e1 at level 39).

Inductive Lstep : LMem -> LE -> LMem -> LE -> Prop :=
| LStValue : forall m e, LValue e -> m / e ==> m / e
| LStPlus : forall m e1 e2 m' n1 m'' n2,
    m / e1 ==> m' / (LENum n1) ->
    m' / e2 ==> m'' / (LENum n2) ->
    m / LEPlus e1 e2 ==> m'' / LENum (n1 + n2)
| LStCstr : forall m m' free,
    (free, m') = Lfresh m ->
    m / LECnst ==> m' / LEAddr free
| LStGet : forall m e1 m' a e2 m'' idx,
    m / e1 ==> m' / LEAddr a ->
    m' / e2 ==> m'' / idx ->
    m / LEGet e1 e2 ==> m'' / Lquery a idx m''
| LStSet : forall m e1 m' a e2 m'' idx e3 v m''',
    m / e1 ==> m' / LEAddr a ->
    m' / e2 ==> m'' / idx ->
    m'' / e3 ==> m''' / v ->
    m / LESet e1 e2 e3 ==> LUpdate a idx v m''' / v
| LStApp : forall m e1 var body e2 m' m'' v m''' res,
     m / e1 ==> m' / LEFun var body ->
     m' / e2 ==> m'' / v ->
     m'' / ([var := v] body) ==> m''' / res ->
     m / LEApp e1 e2 ==> m''' / res

where "m / e ==> m1 / e1" := (Lstep m e m1 e1)
.

Example L1 : LEmptyMem / LEPlus (LENum 3) (LENum 5) ==>
             LEmptyMem / LENum 8.
Proof.
  replace 8 with (3 + 5) by lia.
  eauto using Lstep, LValue.
Qed.


Example L2 : LEmptyMem / LEApp (LEFun "x" (LEVar "x")) (LENum 10) ==>
             LEmptyMem / LENum 10.
Proof. eauto using Lstep, LValue. Qed.


Lemma L2LirValue : forall e, LValue e -> Value (Lua2Lir e).
Proof.
  intros e HV.
  inversion HV; simpl; subst; eauto using Value.
Qed.


Definition Lmem_correct (m : LMem) := forall a n,
    LValue (Lquery a n m) /\ LEWT MEmpty (Lquery a n m).


Lemma Lmem_correct_update : forall m a idx e,
  Lmem_correct m -> LEWT MEmpty e -> LValue e ->
     Lmem_correct (LUpdate a idx e m).
Proof.
  unfold Lmem_correct.
  intros.
  split;
  simpl;
    destruct (Nat.eq_dec a0 a); destruct (Index_dec n idx); subst; auto;
    apply H.
Qed.


Lemma mem_correct_fresh : forall m m' free,
  Lmem_correct m -> (free,m') = Lfresh m -> Lmem_correct m'.
Proof.
  unfold Lfresh. intros m m' free Hmc Heq. inversion Heq.
  eauto using Lmem_correct_update,LValue,LEWT.
Qed.


Lemma LMCquery : forall a v m, Lmem_correct m -> LValue (Lquery a v m).
Proof. intros a v m H. apply H. Qed.


Lemma LMCWT : forall a v m, Lmem_correct m -> LEWT MEmpty (Lquery a v m).
Proof. intros a v m H. apply H. Qed.


Lemma inclusion_WT : forall Γ Γ' e,
  inclusion Γ Γ' -> LEWT Γ e -> LEWT Γ' e.
Proof.
  intros Γ Γ' e Hin Hty.
  generalize dependent Γ'.
  induction Hty; eauto using LEWT, inclusion_update.
Qed.


Corollary WT_empty : forall Γ e, LEWT MEmpty e -> LEWT Γ e.
Proof.
  eauto using inclusion_WT, inclusion_empty.
Qed.


Lemma subst_WT : forall e2 Γ var e1,
  LEWT (var |=> IRTStar; Γ) e2 -> LEWT MEmpty e1 -> LEWT Γ ([var := e1] e2).
Proof.
  induction e2; intros Γ var e1 HWT2 HWT1; simpl;
  inversion HWT2; subst;
  breakStrDec;
  eauto using LEWT, WT_empty, InNotEq, inclusion_WT, inclusion_shadow,
  inclusion_permute.
Qed.


Lemma luaPreservation : forall e m v m',
  Lmem_correct m ->
  LEWT MEmpty e ->
  m / e ==> m' / v ->
  Lmem_correct m' /\ LValue v /\ LEWT MEmpty v.
Proof.
  intros e m v m' HM HWT HSt.
  induction HSt; inversion HWT; subst; repeat split;
  try apply HM; eauto using LValue;
  (* instantiate and split induction hyphoteses *)
  repeat match goal with
  | [ HM: Lmem_correct ?M,
    HWT: LEWT MEmpty ?E,
    IH: Lmem_correct ?M -> LEWT MEmpty ?E -> _ |- _ ] =>
     specialize (IH HM HWT) as [? [? ?]]
  end;
  eauto using LValue, LEWT;
  try match goal with
  | [ HM: Lmem_correct ?M,
      HFr: _ = Lfresh ?M |- _ ] =>
     specialize (mem_correct_fresh _ _ _ HM HFr); clear HFr; intros
  end;
  eauto using LValue, LEWT,Lmem_correct_update, LMCquery, LMCWT,
              Lmem_correct_update.
  - inversion H1; subst.
    apply LMCquery. apply IHHSt3;
    eauto using subst_WT.
  - inversion H1; subst.
    apply LMCWT. eapply IHHSt3; eauto using subst_WT.
  - inversion H1; subst.
    eapply IHHSt3; eauto using subst_WT.
  - inversion H1; subst.
    eapply IHHSt3; eauto using subst_WT.
Qed.


Fixpoint MLua2Lir (m : LMem) : Mem :=
  match m with
  | LEmptyMem => EmptyMem
  | LUpdate a n e m => Update a n (Lua2Lir e) (MLua2Lir m)
  end.


Lemma Lua2LirTypeAux : forall Γ e,
  LEWT Γ e -> Γ |= Lua2Lir e : IRTStar.
Proof.
  intros Γ e.
  generalize dependent Γ.
  induction e; intros Γ HLE; inversion HLE; subst; simpl;
  eauto 8 using IRTyping, InEq, envExt, inclusion_shadow'.
Qed.


Corollary Lua2LirType : forall e,
    LEWT MEmpty e ->  MEmpty |= Lua2Lir e : IRTStar.
Proof. eapply Lua2LirTypeAux. Qed.


Lemma L2LirQuery : forall mem a idx,
    Lua2Lir (Lquery a idx mem) =
    query a (Lua2Lir idx) (MLua2Lir mem).
Proof.
  intros mem a idx.
  induction mem.
  - simpl. trivial.
  - simpl. destruct (Nat.eq_dec a a0); subst; trivial.
    rewrite <- LuaIndex. destruct (Index_dec idx i); subst; trivial.
Qed.


Lemma L2LirFreshaux : forall m, Lfreshaux m = freshaux (MLua2Lir m).
Proof. induction m; simpl; congruence. Qed.


Lemma L2LirFresh : forall free m m',
  (free, m') = Lfresh m -> (free, MLua2Lir m') = fresh (MLua2Lir m).
Proof.
  intros free m m' H.
  unfold Lfresh in H. inversion H; subst.
  unfold fresh. f_equal.
  - apply L2LirFreshaux.
  - rewrite LuaIndex. rewrite L2LirFreshaux. trivial.
Qed.


Lemma L2LirSubst : forall e1 var e2,
  Lua2Lir (substitution var e1 e2) =
  lir.substitution var (Lua2Lir e1) (Lua2Lir e2).
Proof.
  intros e1 var e2.
  induction e2; simpl;
  breakStrDec;
  simpl; try congruence.
Qed.


(* Propagate 'Lmem_correct' to all memories *)
Ltac LmemC :=
  match goal with
    | [ M : LMem |- _] =>  (* for all memories *)
      match goal with
      | [ H : Lmem_correct M |- _] => fail 1  (* already done *)
      | [ HSt: Lstep _ ?E M _ |- _] =>  (* else *)
         assert(Lmem_correct M) by (eapply (luaPreservation E); eauto)
      end
    end.


Theorem SymLua : forall e m v m',
    Lmem_correct m ->
    LEWT MEmpty e ->
    m /e ==> m' / v  ->
    bigStep (MLua2Lir m) (Lua2Lir e)
            (MLua2Lir m') (Lua2Lir v).
Proof.
  intros e m v m' HMC HWT HSt.
  induction HSt; inversion HWT; subst;
  repeat LmemC;
  eauto using bigStep, L2LirValue, L2LirFresh, L2LirQuery.
  - simpl. apply BStBox.
    eapply BStPlus.
    + eapply BStUnbox.
      replace (IREBox TgInt (IRENum n1)) with (Lua2Lir (LENum n1))
        by trivial.
      eauto.
    + eapply BStUnbox.
      replace (IREBox TgInt (IRENum n2)) with (Lua2Lir (LENum n2))
        by trivial.
      eauto.
  - simpl. rewrite LuaIndex.
    eapply BStSet; eauto.
    eapply BStUnbox.
    replace (IREBox TgTbl (IREAddr a)) with (Lua2Lir (LEAddr a))
      by trivial. eauto.
  - simpl. eapply BStFunapp; eauto.
    + eapply BStUnbox.
      simpl in IHHSt1. eauto.
    + simpl. breakStrDec.
      eapply BStLet.
      * apply BStValue.
        apply L2LirValue.
        eapply (luaPreservation _ m'); eauto.
      * simpl. rewrite <- L2LirSubst.
        apply IHHSt3; eauto.
        assert (HX: LEWT MEmpty (LEFun var body)).
        { eapply (luaPreservation e1 m); eauto. }
        inversion HX; subst.
        apply subst_WT. auto.
        eapply (luaPreservation e2 m'); eauto.
Qed.


