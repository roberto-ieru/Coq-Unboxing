
Print nat. 

Print Nat.add.

Lemma L1 : forall n, 0 + n = n.
Proof.
  intro n.
  simpl. reflexivity.
Qed.


Lemma L2 : forall n, n + 0 = n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.


Lemma L3 : nat.
Proof. apply 0. Qed.
