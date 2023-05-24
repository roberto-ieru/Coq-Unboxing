(*
  A nice example of λ-Pallene code:

  let A:tbl[tbl[int]] = {} : tbl[tbl[int]] in
  let B:tbl[int] = (A as tbl[int]) in
    A[1] = B; B[2] = 10; A[1][2]

  It types and reduces to 10.
*)


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

(* Sequence 'operator' e1 ; e2 *)
Definition PESeq (e1 e2 : PE) : PE := PELet ("":string) PTNil e1 e2.

Definition example :=
    PELet ("A":string) (PTArr (PTArr PTInt)) (PENew (PTArr PTInt))
    (PELet ("B":string) (PTArr PTInt)
                        (PECast (PEVar ("A":string)) (PTArr PTInt))
     (PESeq
       (PESet (PEVar ("A":string)) (PENum 1) (PEVar ("B":string)))
      (PESeq
       (PESet (PEVar ("B":string)) (PENum 2) (PENum 10))
       (PEGet (PEGet (PEVar ("A":string)) (PENum 1)) (PENum 2))))).


(*
** Example is well typed with type int
*)
Goal PtypeOf MEmpty example = Some PTInt.
Proof. trivial. Qed.


(*
** Example evaluates to 10
*)
Lemma run : exists m, PEmptyMem / example -p->* m / (PENum 10).
Proof with eauto 10 using pstep, PValue.
  eexists.
  unfold example.
  eapply PMStMStep.
  { eapply PStLet1. eapply PStNew. unfold PfreshT. simpl. eauto. }
  eapply PMStMStep...  (* Let *)
  eapply PMStMStep.
  { eapply PStLet1. simpl. eapply PStCast; eauto using PValue.
    discriminate. simpl. trivial. }
  simpl.
  eapply PMStMStep...  (* Let *)
  eapply PMStMStep.
  { eapply PStLet1. simpl. eapply PStSet. auto using PValue. }
  simpl.
  eapply PMStMStep...  (* Let *)
  eapply PMStMStep.
  { eapply PStLet1. eapply PStSet. auto using PValue. }
  eapply PMStMStep...  (* Let *)
  eapply PMStMStep...  (* Get *)
  simpl.
  eapply PMStMStep.
  { eapply PStGet1. eapply PStCast; auto using PValue; easy. }
  eapply PMStMStep...  (* Get *)
  simpl.
  eapply PMStMStep.
  { eapply PStCast; auto using PValue; easy. }
  eauto using Pmultistep.
  Unshelve. all: auto using PValue.
Qed.

