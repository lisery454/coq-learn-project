Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

Example le_3_5 : 3 <= 5.

Proof.

apply le_S.
apply le_S.
apply le_n.

Qed.

Inductive lt : nat -> nat -> Prop :=
    | lt_n (n :nat): lt n (S n)
    | lt_S (n m :nat): lt n m -> lt n (S m).

Example lt_3_5: lt 3 5.

Proof.

apply lt_S.
apply lt_n.

Qed.


Inductive gt : nat -> nat -> Prop :=
    | gt_n (n :nat): gt (S n) n
    | gt_S (n m :nat): gt n m -> gt (S n) m.

Theorem gt_test: gt 2023 1.
Proof.

do 2021 (apply gt_S).

apply gt_n.

Qed.





