Inductive div3 : nat -> Prop :=
    | D1 : div3 0
    | D2 (n: nat)(H: div3 n) : div3 (S(S(S n))).

Example test : div3 6.
Proof. 
apply(D2 3 (D2 0 D1)).
Qed.

Theorem mult_0_r: forall n : nat, n * 0 = 0 .
Proof.
intro n.

induction n as [ | m IHm].
-reflexivity.
-simpl. 
rewrite IHm. reflexivity.

Qed.


Theorem mult_1_r: forall n : nat, n * 1 = n.
Proof.
intro n.

induction n as [ | m IHm].
-simpl. reflexivity.
-simpl. 
rewrite IHm. reflexivity.

Qed.

Theorem plus_n_Sm : forall n m :nat,
    S (n + m) = n + (S m).
Proof.

intros n m.

induction n as [ | n' IHn'].
-reflexivity.
-simpl. rewrite IHn'. reflexivity.

Qed.

Theorem plus_n_0: forall n : nat ,
    n = n + 0.
Proof.

intro n.
induction n as [ | n' IHn'].
-reflexivity.
-simpl. rewrite <- IHn'. simpl. reflexivity.

Qed.

Print nat.
Theorem add_comm: forall n m :nat,
    n + m = m + n.
Proof.

intros n m.

induction n as [ | n' IHn'].
- simpl. apply plus_n_0. 
- simpl. rewrite IHn'. apply plus_n_Sm. 
    
Qed.

Print list.

Theorem app_nil : forall l : list nat,
    app l nil = l.   
Proof.
intro l. 
induction l as [ | h l' IHl'].
- reflexivity.
- simpl. Print app. rewrite IHl'. reflexivity.
    
Qed.


Theorem le_transitivity: forall m n p : nat,
    le m n -> le n p -> le m p.
Proof.

intros m n p H1 H2.

induction H2.

- apply H1.

- apply le_S. apply IHle.  

Qed.



