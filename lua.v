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
Require Import LIR.biglir.


(*
** Sintax of λ-Lua
*)
Inductive LE : Set :=
| LENil : LE
| LENum : nat -> LE
| LEPlus : LE -> LE -> LE
| LENew : LE
| LETAddr : address -> LE
| LEFAddr : address -> LE
| LEGet  : LE -> LE -> LE
| LESet : LE -> LE -> LE -> LE
| LEVar : string -> LE
| LEApp : LE -> LE -> LE
| LEFun : string -> LE -> LE
.


(*
** A well-formed Lua expression cannot have free variables
*)
Inductive LEWT : IREnvironment -> LE -> Prop :=
| WTNil : forall Γ, LEWT Γ LENil
| WTNum : forall Γ n, LEWT Γ (LENum n)
| WTPlus : forall Γ e1 e2, LEWT Γ e1 -> LEWT Γ e2 -> LEWT Γ (LEPlus e1 e2)
| WTNew : forall Γ, LEWT Γ LENew
| WTTAddr : forall Γ a, LEWT Γ (LETAddr a)
| WTFAddr : forall Γ a, LEWT Γ (LEFAddr a)
| WTGet : forall Γ e1 e2, LEWT Γ e1 -> LEWT Γ e2 -> LEWT Γ (LEGet e1 e2)
| WTSet : forall Γ e1 e2 e3, LEWT Γ e1 -> LEWT Γ e2 -> LEWT Γ e3 ->
               LEWT Γ (LESet e1 e2 e3)
| WTVar : forall Γ var, In Γ var = Some IRTStar -> LEWT Γ (LEVar var)
| WTApp : forall Γ e1 e2, LEWT Γ e1 -> LEWT Γ e2 -> LEWT Γ (LEApp e1 e2)
| WTFun : forall Γ var body, LEWT (var |=> IRTStar; Γ) body ->
            LEWT Γ (LEFun var body)
.


(*
** Compilation of Lua programs to Lir
*)
Fixpoint Lua2Lir (e : LE) : IRE :=
  match e with
  | LENil => IREBox TgNil IRENil
  | LENum n => IREBox TgInt (IRENum n)
  | LEPlus e1 e2 => IREBox TgInt (IREPlus (IREUnbox TgInt (Lua2Lir e1))
                                          (IREUnbox TgInt (Lua2Lir e2)))
  | LENew => IREBox TgTbl IRENew
  | LETAddr a => IREBox TgTbl (IRETAddr a)
  | LEFAddr a => IREBox TgFun (IREFAddr a)
  | LEGet e1 e2 => IREGet (IREUnbox TgTbl (Lua2Lir e1)) (Lua2Lir e2)
  | LESet e1 e2 e3 => IREBox TgNil (IRESet (IREUnbox TgTbl (Lua2Lir e1))
                                           (Lua2Lir e2)
                                           (Lua2Lir e3))
  | LEVar var => IREVar var
  | LEFun var body =>
      IREBox TgFun (IREFun var
         (IRELet var IRTStar (IREVar var) (Lua2Lir body)))
  | LEApp e1 e2 => IREApp (IREUnbox TgFun (Lua2Lir e1)) (Lua2Lir e2)
  end.


(*
** Tanslation of Pallene programs to Lua (erasure)
*)
Fixpoint Pall2Lua (e : PE) : LE :=
  match e with
  | PENil => LENil
  | PENum n => LENum n
  | PEPlus e1 e2 => LEPlus (Pall2Lua e1) (Pall2Lua e2)
  | PENew _ => LENew
  | PETAddr a _ => LETAddr a
  | PEFAddr a _ _ => LEFAddr a
  | PEGet e1 e2 => LEGet (Pall2Lua e1) (Pall2Lua e2)
  | PESet e1 e2 e3 => LESet (Pall2Lua e1) (Pall2Lua e2) (Pall2Lua e3)
  | PEVar var => LEVar var
  | PEApp e1 e2 => LEApp (Pall2Lua e1) (Pall2Lua e2)
  | PEFun var _ e _ => LEFun var (Pall2Lua e)
  | PECast e _ => Pall2Lua e
  end.


(*
** Casts disapear under 'dyn'
*)
Lemma dynCast : forall (t1 t2 : IRType) (e : IRE),
    dyn (Cast t1 t2 e) = dyn e.
Proof.
  intros t1 t2 e.
  unfold Cast.
  destruct t1; destruct t2; simpl; trivial.
  destruct (dec_Tag t t0); simpl; trivial.
Qed.


(*
** Main syntactic theorem: compiling and erasuring commute
*)
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


(*
** Lua programs are as dynamic as possible
*)
Theorem LuaIsDyn : forall e, Lua2Lir e = dyn (Lua2Lir e).
Proof.
  induction e; simpl; congruence.
Qed.


(*
** Direct semantics of Lua programs, without
** translation to Lir
*)

Inductive LValue : LE -> Prop :=
| LVnil : LValue LENil
| LVnum : forall n, LValue (LENum n)
| LVtbl : forall a, LValue (LETAddr a)
| LVfun : forall a, LValue (LEFAddr a)
.

Inductive LExpValue : Set :=
| LEV : forall e, LValue e -> LExpValue.


Definition LEV2Val (me : LExpValue) :=
  match me with
  | LEV v _ => v
  end.


Inductive LMem : Set :=
| LEmptyMem : LMem
| LUpdateT : address -> Index -> LExpValue -> LMem -> LMem
| LUpdateF : address -> string -> LE -> LMem -> LMem.



Definition LToIndex (e : LE) : Index :=
  match e with
  | LENil => I 0 TgNil
  | LENum n => I n TgInt
  | LETAddr a => I a TgTbl
  | LEFAddr a => I a TgFun
  | _ => NI
  end.


Lemma LuaIndex : forall e, LToIndex e = ToIndex (Lua2Lir e).
Proof.
  destruct e; trivial.
Qed.



Fixpoint LqueryT (a : address) (idx : LE) (m : LMem) :=
  match m with
  | LEmptyMem => LENil
  | LUpdateT a' idx' e m' => if Nat.eq_dec a a' then
                           if Index_dec (LToIndex idx) idx' then (LEV2Val e)
                           else LqueryT  a idx m'
                         else LqueryT  a idx m'
  | LUpdateF _ _ _ m' => LqueryT a idx m'
  end.


Fixpoint LqueryF (a : address) (m : LMem) : (string * LE) :=
  match m with
  | LEmptyMem => (""%string, LENil)
  | LUpdateT a' _ _ m' => LqueryF a m'
  | LUpdateF a' var body m' => if Nat.eq_dec a a' then (var, body)
                              else LqueryF a m'
  end.


Fixpoint Lfreshaux (m : LMem) : address :=
  match m with
  | LEmptyMem => 1
  | LUpdateT _ _ _ m' => S (Lfreshaux m')
  | LUpdateF _ _ _ m' => S (Lfreshaux m')
  end.


Definition LfreshT (m : LMem) : (address * LMem) :=
  let f := Lfreshaux m in
    (f, LUpdateT f (I 0 TgNil) (LEV LENil LVnil) m).


Definition LfreshF (m : LMem) (v : string) (b : LE) : (address * LMem) :=
  let f := Lfreshaux m in
    (f, LUpdateF f v b m).


Reserved Notation "'[' x ':=' s ']' t" (at level 20, x constr).


Fixpoint substitution (var : string) (y : LE)  (e : LE) : LE :=
 match e with
 | LENil => e
 | LENum n => e
 | LEPlus e1 e2 => LEPlus ([var := y] e1) ([var := y] e2)
 | LENew => e
 | LETAddr a => e
 | LEFAddr a => e
 | LEGet e1 e2 => LEGet ([var := y] e1) ([var := y] e2)
 | LESet e1 e2 e3 => LESet ([var := y] e1) ([var := y] e2) ([var := y] e3)
 | LEVar var' => if string_dec var var' then y else e
 | LEFun var' body => if string_dec var var' then e
                       else LEFun var' ([var := y] body)
 | LEApp e1 e2 => LEApp ([var := y] e1) ([var := y] e2)
end
where "'[' x ':=' s ']' t" := (substitution x s t)
.


(*
** Bigstep semantics for Lua expressions
*)
Reserved Notation "m '/' e ==> m1 '/' e1"
(at level 40, e at level 39, m1 at level 39, e1 at level 39).

Inductive Lstep : LMem -> LE -> LMem -> LE -> Prop :=
| LStValue : forall m e, LValue e -> m / e ==> m / e
| LStPlus : forall m e1 e2 m' n1 m'' n2,
    m / e1 ==> m' / (LENum n1) ->
    m' / e2 ==> m'' / (LENum n2) ->
    m / LEPlus e1 e2 ==> m'' / LENum (n1 + n2)
| LStCstr : forall m m' free,
    (free, m') = LfreshT m ->
    m / LENew ==> m' / LETAddr free
| LStGet : forall m e1 m' a e2 m'' idx,
    m / e1 ==> m' / LETAddr a ->
    m' / e2 ==> m'' / idx ->
    m / LEGet e1 e2 ==> m'' / LqueryT a idx m''
| LStSet : forall m e1 m' a e2 m'' idx e3 v m''',
    m / e1 ==> m' / LETAddr a ->
    m' / e2 ==> m'' / idx ->
    m'' / e3 ==> m''' / LEV2Val v ->
    m / LESet e1 e2 e3 ==> LUpdateT a (LToIndex idx) v m''' / LENil
| LStFun : forall m m' v b free,
    (free, m') = LfreshF m v b ->
    m / LEFun v b ==> m' / LEFAddr free
| LStApp : forall m e1 a var body e2 m' m'' v m''' res,
     m / e1 ==> m' / LEFAddr a ->
     m' / e2 ==> m'' / v ->
     (var, body) = LqueryF a m'' ->
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


Lemma auxmem : forall a m m' v v' e e',
  LfreshF m v e = (a, m') ->
  LqueryF a m' = (v', e') ->
  v = v' /\ e = e'.
Proof.
  intros * Hf Hq.
  unfold LfreshF in Hf. inversion Hf; subst.
  simpl in Hq.
  destruct (Nat.eq_dec (Lfreshaux m) (Lfreshaux m)); try easy.
  intuition; congruence.
Qed.


Example L2 : exists m,
    LEmptyMem / LEApp (LEFun "x" (LEVar "x")) (LENum 10) ==>
    m / LENum 10.
Proof. 
  destruct (LfreshF LEmptyMem "x" (LEVar "x")) eqn:Heq.
  destruct (LqueryF a l) eqn:Heq'.
  specialize (auxmem _ _ _ _ _ _ _ Heq Heq') as [? ?]; subst.
  eexists.
  eauto using Lstep, LValue.
Qed.


Lemma L2LirValue : forall e, LValue e -> Value (Lua2Lir e).
Proof.
  intros e HV.
  inversion HV; simpl; subst; eauto using Value.
Defined.


Inductive Lmem_correct : LMem -> Prop :=
| LMCE : Lmem_correct LEmptyMem
| LMCU : forall a idx v m,
     LEWT MEmpty (LEV2Val v) ->
     Lmem_correct m ->
     Lmem_correct (LUpdateT a idx v m)
| LMCF : forall a var body m,
     LEWT (var |=> IRTStar; MEmpty) body ->
     Lmem_correct m ->
     Lmem_correct (LUpdateF a var body m)
.


Lemma mem_correct_freshT : forall m m' free,
  Lmem_correct m -> (free,m') = LfreshT m -> Lmem_correct m'.
Proof.
  unfold LfreshT. intros m m' free Hmc Heq. inversion Heq.
  eauto using Lmem_correct,LEWT.
Qed.


Lemma mem_correct_freshF : forall m m' free var body,
  LEWT (var |=> IRTStar; MEmpty) body ->
  Lmem_correct m ->
  (free,m') = LfreshF m var body ->
  Lmem_correct m'.
Proof.
  unfold LfreshF. intros * HWT Hmc Heq. inversion Heq. subst.
  apply LMCF; trivial.
Qed.


Lemma LMCqueryT : forall a v m, LValue (LqueryT a v m).
Proof.
  intros.
  induction m; eauto using LValue.
  destruct l. simpl.
  breakIndexDec; trivial.
Qed.


Lemma LMCqueryF : forall a m var body,
    (var, body) = LqueryF a m ->
    Lmem_correct m ->
    LEWT (var |=> IRTStar; MEmpty) body.
Proof.
  intros * Heq HMc. induction m.
  - inversion Heq; subst. auto using LEWT.
  - inversion HMc; subst.
    auto.
  - inversion HMc; subst.
    simpl in Heq.
    breakIndexDec; auto.
    inversion Heq; subst. trivial.
Qed.


Lemma LMCWT : forall a v m, Lmem_correct m -> LEWT MEmpty (LqueryT a v m).
Proof.
  intros a v m H.
  induction H; eauto using LEWT.
  simpl. breakIndexDec; auto.
Qed.


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
  induction HSt; inversion HWT; subst;
  try (repeat split; try apply HM; eauto using LValue; fail);
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
      HFr: _ = LfreshT ?M |- _ ] =>
     specialize (mem_correct_freshT _ _ _ HM HFr); clear HFr; intros
  | [ HM: Lmem_correct ?M,
      HFr: _ = LfreshF ?M _ ?b,
      HTy: LEWT _ ?b |- _ ] =>
     specialize (mem_correct_freshF _ _ _ _ _ HTy HM HFr); intros
  end;
  eauto using LValue, LEWT,Lmem_correct, LMCqueryT, LMCqueryF, LMCWT,
              subst_WT.
Qed.


Fixpoint MLua2Lir (m : LMem) : Mem :=
  match m with
  | LEmptyMem => EmptyMem
  | LUpdateT a n (LEV v vv) m =>
      UpdateT a n (EV (Lua2Lir v) (L2LirValue v vv)) (MLua2Lir m)
  | LUpdateF a var body m =>
      UpdateF a var
       (IRELet var IRTStar (IREVar var) (Lua2Lir body)) (MLua2Lir m)
  end.


Lemma Lua2LirTypeAux : forall Γ e,
  LEWT Γ e -> Γ |= Lua2Lir e : IRTStar.
Proof.
  intros Γ e.
  generalize dependent Γ.
  induction e; intros Γ HLE; inversion HLE; subst; simpl;
  eauto 7 using IRTyping, eq_refl, inclusion_typing,
    inclusion_shadow', InEq.
Qed.


Corollary Lua2LirType : forall e,
    LEWT MEmpty e ->  MEmpty |= Lua2Lir e : IRTStar.
Proof. eapply Lua2LirTypeAux. Qed.


Lemma L2LirQueryT : forall mem a idx,
    Lua2Lir (LqueryT a idx mem) =
    queryT a (Lua2Lir idx) (MLua2Lir mem).
Proof.
  intros mem a idx.
  induction mem; trivial.
  destruct l. simpl. destruct (Nat.eq_dec a a0); subst; trivial.
  rewrite <- LuaIndex.
  destruct (Index_dec (LToIndex idx) i); subst; trivial.
Qed.


Lemma L2LirQueryF : forall var body a m,
  (var, body) = LqueryF a m ->
  queryF a (MLua2Lir m) =
        (var, IRELet var IRTStar (IREVar var) (Lua2Lir body)).
Proof.
  intros * HQ.
  induction m.
  - inversion HQ; subst. trivial.
  - destruct l. eauto.
  - simpl. simpl in HQ.
    breakIndexDec; eauto.
    congruence.
Qed.


Lemma L2LirFreshaux : forall m, Lfreshaux m = freshaux (MLua2Lir m).
Proof.
  induction m; trivial.
  - destruct l. simpl. congruence.
  -simpl. congruence.
Qed.


Lemma L2LirFreshT : forall free m m',
  (free, m') = LfreshT m -> (free, MLua2Lir m') = freshT (MLua2Lir m).
Proof.
  intros free m m' H.
  unfold LfreshT in H. inversion H; subst.
  unfold freshT.
  simpl. f_equal. apply L2LirFreshaux.
  simpl. f_equal. apply L2LirFreshaux.
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


(*
** If a Lua program results in a value,
** its translation to Lir results in the
** Lir translation of the final value.
*)
Theorem SimLua : forall e m v m',
    Lmem_correct m ->
    LEWT MEmpty e ->
    m /e ==> m' / v  ->
    bigStep (MLua2Lir m) (Lua2Lir e)
            (MLua2Lir m') (Lua2Lir v).
Proof.
  intros e m v m' HMC HWT HSt.
  induction HSt; inversion HWT; subst;
  repeat LmemC;
  eauto using bigStep, L2LirValue, L2LirFreshT, L2LirQueryT.

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
    destruct v.
    eapply BStBox.
    eapply BStSet; eauto.
    eapply BStUnbox.
    replace (IREBox TgTbl (IRETAddr a)) with (Lua2Lir (LETAddr a))
      by trivial. eauto.

  - simpl. eapply BStBox. eapply BStFun.
    unfold freshF. unfold LfreshF in H.    
    inversion H; subst.
    f_equal. apply L2LirFreshaux.
    simpl.
    f_equal. apply L2LirFreshaux.
  
  - specialize (L2LirQueryF _ _ _ _ H) as ?.
    simpl. eapply BStFunapp; eauto using bigStep.
    simpl. destruct (string_dec var var); try easy.
    specialize (luaPreservation _ _ _ _ H0 H4 HSt2) as [? [? ?]].
    eapply BStLet.
    + eauto using bigStep, L2LirValue.
    + eapply IHHSt3 in H1.
      * rewrite L2LirSubst in H1; trivial.
      * eauto using subst_WT, LMCqueryF.
Qed.



