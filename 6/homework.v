Theorem test : forall P Q R : Prop, (P -> Q -> R) -> (P -> Q) -> P -> R.

Proof.

intros.

apply H.

- apply H1.

- apply H0. apply H1.

Qed.


Ltac reduce := 
    repeat match goal with
    | [_ : ?P |- ?P] => assumption
    | [H : _/\_ |- _] => destruct H
    | [H : _\/_ |- _] => destruct H
    | [H1: ?P -> ?Q, H2: ?P |- _] => apply H1 in H2
    | [H: ?P |- ?P \/ ?Q] => intros; left; apply H
    | [H: ?P |- ?Q \/ ?P] => intros; right; apply H
    | [|- _/\_] => constructor
    | [|- _->_] => intro
    | [|- forall _, _] => intro
    end.

Theorem test1 : forall P Q : Prop,(P -> P \/Q) /\ (Q -> P\/ Q).
Proof.
reduce.
Qed.
Theorem test2 : forall P Q R : Prop, P /\ Q -> Q /\ P.
Proof.
reduce.
Qed.
Theorem test3 : forall P Q R : Prop, P \/ Q -> Q \/ P.
Proof.
reduce.
Qed.
Theorem test4 : forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
reduce.
Qed.
Theorem test5 : forall P Q R : Prop, P -> Q /\ R -> (P -> Q) /\ (P -> R).
Proof.
reduce.
Qed.


Ltac reduce2 := 
    repeat match goal with
    | [_ : ?P |- ?P] => assumption
    | [|- _ (S _ ) _ = S _] => simpl
    | [H1: ?P = ?Q |- _ ?P = _ ?Q] => rewrite H1
    | [|- forall n, _] => intro;induction n
    | [|-_] => reflexivity
    end.

Theorem minus_n_n : forall n : nat,  n - n = 0.
Proof.
reduce2.
Qed.
Theorem mul_0_r : forall n:nat,  n * 0 = 0.
Proof.
reduce2.
Qed.
Theorem mul_1_r : forall n:nat,  n * 1 = n.
Proof.
reduce2.
Qed.
Theorem plus_1_r : forall n:nat,  n + 1 = S n.
Proof.
reduce2.
Qed.

