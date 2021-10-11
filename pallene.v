Require Import Coq.Logic.Decidable.
Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Import Lia.

Require Import LIR.lir.


Inductive TPall : Set :=
| TPstar : TPall | TPnil : TPall | TPint : TPall
| TParr : TPall -> TPall | TPfun : TPall -> TPall -> TPall
.


Inductive EPall : Set :=
| EPnil : EPall
| EPnum : nat -> EPall
| EPplus : EPall -> EPall -> EPall
| EPcntr : TPall -> EPall
| EPindx : EPall -> EPall -> EPall
| EPassg : EPall -> EPall -> EPall -> EPall
| EPvar : string -> EPall
| EPcall :  EPall -> EPall -> EPall
| EPfunc : string -> TPall -> EPall -> EPall
| EPcast : EPall -> TPall -> EPall
.


Fixpoint TP2FCT (t : TPall) : FCType :=
  match t with
  | TPstar => Tstar
  | TPnil => Tgnil
  | TPint => Tgint
  | TParr _ => Tgtbl
  | TPfun _ _ =>  Tgfun
  end.


Fixpoint Cast (t1 t2 : FCType) (e : LirExp) : LirExp :=
  match t1, t2 with
  | Tstar, Tstar => e
  | Tstar, Ttag t => Eunbox t e
  | Ttag t, Tstar => Ebox t e
  | Ttag t1', Ttag t2' => if dec_Tag t1' t2' then e
                            else Ebox t1' (Eunbox t2' e)
  end.
 

Fixpoint Pall2Lir (e : EPall) : LirExp :=
  match e with
  | EPnil => Enil
  | EPnum a => Enum a
  | EPplus e1 e2 => Eplus (Pall2Lir e1) (Pall2Lir e2)
  | EPcntr => Ecstr
  | EPindx e1 e2 =>  Eindx (Pall2Lir e1) (Pall2Lir e2)
  | EPassg e1 e2 e3 : Eassg  (Pall2Lir e1) (Pall2Lir e2) (Pall2Lir e3)
  | EPvar v => Evar v
  | EPcall :w
:  EPall -> EPall -> EPall
  | EPfunc : string -> TPall -> EPall -> EPall
  | EPcast : EPall -> TPall -> EPall
  end.
