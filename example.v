Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Coq.Program.Equality.

Require Import LIR.maps.
Require Import LIR.pallene.
Require Import LIR.lir.

(*
  A nice example of λ-Pallene code:

  let A:tbl[tbl[int]] = {} : tbl[tbl[int]] in
  let B:tbl[int] = (A as tbl[int]) in
    A[1] = B; B[2] = 10; A[1][2]
*)


Definition example :=
    PELet ("A":string) (PTArr (PTArr PTInt)) (PENew (PTArr PTInt))
    (PELet ("B":string) (PTArr PTInt)
                        (PECast (PEVar ("A":string)) (PTArr PTInt))
     (PELet ("":string) PTNil
       (PESet (PEVar ("A":string)) (PENum 1) (PEVar ("B":string)))
    (PELet ("":string) PTNil
       (PESet (PEVar ("B":string)) (PENum 2) (PENum 10))
       (PEGet (PEGet (PEVar ("A":string)) (PENum 1)) (PENum 2))))).
       

(* Example is well typed with type int *)
Goal typeOf MEmpty example = Some PTInt.
Proof. trivial. Qed.


(*
** Multistep
*)
Reserved Notation "m '/' e '-p->*' m1 '/' e1"
(at level 40, e at level 39, m1 at level 39, e1 at level 39).
Reserved Notation "m '/' e '-p->*' 'fail'"
(at level 40, e at level 39).

Inductive multistep : PMem -> PE -> PMem -> PE -> Prop :=
| MStRefl : forall m e, m / e -p->* m / e
| MStMStep : forall m e m' e' m'' e'',
    m / e -p-> m' / e' ->
    m' / e' -p->* m'' / e'' ->
    m / e -p->* m'' / e''

where "m / e -p->* m1 / e1" := (multistep m e m1 e1)
.

(* example evaluates to 10 *)
Lemma run : exists m, PEmptyMem / example -p->* m / (PENum 10).
Proof with eauto 10 using pstep, PValue.
  eexists.
  unfold example.
  eapply MStMStep.
  { eapply PStLet1. eapply PStNew. unfold PfreshT. simpl. eauto. }
  eapply MStMStep...  (* Let *)
  eapply MStMStep.
  { eapply PStLet1. simpl. eapply PStCast; eauto using PValue.
    discriminate. simpl. trivial. }
  simpl.
  eapply MStMStep...  (* Let *)
  eapply MStMStep.
  { eapply PStLet1. simpl. eapply PStSet. auto using PValue. }
  simpl.
  eapply MStMStep...  (* Let *)
  eapply MStMStep.
  { eapply PStLet1. eapply PStSet. auto using PValue. }
  eapply MStMStep...  (* Let *)
  eapply MStMStep...  (* Get *)
  simpl.
  destruct (lir.Index_dec (PToIndex 1) (PToIndex 2)); try easy.
  destruct (lir.Index_dec (PToIndex 1) (PToIndex 1)); try easy.
  eapply MStMStep.
  { eapply PStGet1. eapply PStCast; auto using PValue; easy. }
  eapply MStMStep...  (* Get *)
  simpl.
  destruct (lir.Index_dec (PToIndex 2) (PToIndex 2)); try easy.
  eapply MStMStep.
  { eapply PStCast; auto using PValue; easy. }
  eauto using multistep.
  Unshelve. all: auto using PValue.
Qed.

