Inductive le : nat -> nat -> Prop :=
    | lem (m : nat) : le m m
    | leS (m n : nat) (H : le m n) : le m (S n).

Lemma le_p_1: forall m p, 
    le m (p+m).
Proof.

intros.

induction p.

- simpl. apply lem.

- simpl. apply leS. assumption.
    
Qed.

Theorem plus_n_0: forall n : nat ,
    n = n + 0.
Proof.

intro n.
induction n as [ | n' IHn'].
-reflexivity.
-simpl. rewrite <- IHn'. simpl. reflexivity.

Qed.

Theorem add_comm: forall n m :nat,
    n + m = m + n.
Proof.

intros n m.

induction n as [ | n' IHn'].
- simpl. apply plus_n_0. 
- simpl. rewrite IHn'. apply plus_n_Sm. 
    
Qed.

Theorem le_p :  forall m n p, 
    le m n -> le m (p + n).
Proof.
intros.

induction H.

- apply le_p_1.

- simpl. rewrite add_comm. simpl. apply leS. 
    rewrite add_comm. assumption.

Qed.

Theorem mul_4_r: forall n:nat,
    n * 4 = n + n + n + n.
Proof.
intros.
induction n.
- simpl. reflexivity.
- simpl. f_equal. rewrite add_comm. simpl. f_equal.
    rewrite (add_comm n (S n)). rewrite add_comm. simpl.
    f_equal. rewrite (add_comm (n + n) (S n)) . simpl.
    f_equal. rewrite (add_comm n (n + n)). assumption.

Qed.

Inductive natlist : Type :=
    | nil
    | cons (n: nat) (l: natlist).

Notation "n :: m"  := (cons n m)
    (at level 60, right associativity).
Notation "[]" := nil.

Notation "[ x ; .. ; y ]" := 
    (cons x .. (cons y nil) ..).

Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | n::l1' => n :: (app l1' l2)
    end.

Notation "x ++ y" := (app x y) 
 (at level 60, right associativity).

Theorem app_assoc: forall l1 l2 l3: natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.

intros.

induction l1.

- simpl. reflexivity. 

- simpl. f_equal. assumption. 
    
Qed.
