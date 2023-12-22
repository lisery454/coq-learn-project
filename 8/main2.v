Require Import Nat.
Require Import List.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := 
    (cons x .. (cons y nil) ..).

Lemma mul_0_r : forall n : nat, n * 0 = 0.
Proof.
intros.
induction n.
- reflexivity.
- simpl. apply IHn.
Qed.

Lemma mul_1_r : forall n : nat, n * 1 = n.
Proof.
intros.
induction n.
- reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed.

Inductive last : nat -> list nat -> Prop :=
    | last_1 (m: nat) : last m [m]
    | last_2 (m n: nat) (l: list nat) (H: last m l): last m (n::l).


Inductive btree : Set :=
    | leaf : btree
    | node : nat->btree->btree->btree.

Require Import Coq.Bool.Bool.

Fixpoint occor(n: nat)(t: btree): bool :=
    match t with
    | leaf => false
    | node m l r => if m =? n then true
                    else (occor n l) || (occor n r)
    end.




    




