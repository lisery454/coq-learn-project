Theorem conjunction : forall P Q :Prop,
    P -> Q -> P /\ Q.

Proof.

intros P Q HP HQ.

split.

- apply HP.

- apply HQ.

Qed.


Theorem disjunction1 : forall P Q :Prop,
    P -> P \/ Q.

Proof.

intros.

left.

- apply H.

Qed.

Theorem disjunction2 : forall P Q :Prop,
    Q -> P \/ Q.

Proof.

intros.

right.

- apply H.

Qed.

Theorem disjunction : forall P Q :Prop,
    (P -> P \/ Q) /\ (Q -> P \/ Q).

Proof.

(* intuition. *)

intros.

split.

- apply disjunction1.

- apply disjunction2.

Qed.


Theorem exist: exists n : nat, n * n = 9.
Proof.

exists 3.

reflexivity.
    
Qed.

Theorem and_comm: forall a b :bool, andb a b = andb b a.
Proof.

intros. destruct a.
- destruct b. 
    + reflexivity.
    + simpl. reflexivity.
- destruct b.
    + reflexivity.
    + reflexivity.
    
Qed.

Theorem and_comm': forall a b :bool, andb a b = andb b a.
Proof.

intros [] [].
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
    
Qed.

Theorem implication: forall P Q R: Prop,
    (P -> Q) -> (Q -> R) -> P -> R .

Proof.

intros.

(* apply H0. apply H. apply H1. *)

apply H in H1. apply H0 in H1. apply H1.
    
Qed.

Theorem test : le 2 5 .
Proof.

repeat constructor.
    
Qed.

Theorem ge0: forall n : nat,
    ge (S n) 0 .
Proof.

intros. 
induction n as [|n' IHn'];

(* - constructor. constructor.

- constructor. apply IHn'. *)

[ constructor; constructor | constructor; apply IHn'].
    
Qed.

Ltac des_bool :=
    match goal with
    | [ |- forall x : bool, _] => intro x; destruct x; reflexivity
    end.

Theorem andb_id: forall a : bool,
    andb a a = a.
Proof.

des_bool.
    
Qed.

Ltac reduce := 
    repeat match goal with
    | [_ : ?P |- ?P] => assumption
    | [H : _/\_ |- _] => destruct H
    | [H : _\/_ |- _] => destruct H
    | [H1: ?P -> ?Q, H2: ?P |- _] => apply H1 in H2
    | [|- _/\_] => constructor
    | [|- _->_] => intro
    | [|- forall _, _] => intro
    end.

Theorem conj_disj: forall P Q : Prop,
    (P\/Q)/\(P->Q)->Q.
Proof.
reduce.
Qed.





