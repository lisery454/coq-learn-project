Require Import Arith.
Notation "n :: m"  := (cons n m)
    (at level 60, right associativity).

Notation "x ++ y" := (app x y) 
 (at level 60, right associativity).

Notation "[]" := nil.

Notation "[ x ; .. ; y ]" := 
    (cons x .. (cons y nil) ..).

Fixpoint ismemeber (a: nat) (l : list nat) : bool :=
    match l with
    | [] => false
    | n::l' => if n =? a then true 
                        else ismemeber a l'
    end.

Fixpoint inter (l1 l2 : list nat): list nat :=
    match l1 with
    | [] => []
    | n::k => if ismemeber n l2 then n::(inter k l2)
                                else (inter k l2)
    end.


Inductive subseq : list nat -> list nat -> Prop :=
    | D1 (l: list nat): subseq nil l
    | D2 (l1 l2: list nat)(n : nat)(H: subseq l1 l2) : subseq l1 (n::l2)
    | D3 (l1 l2: list nat)(n : nat)(H: subseq l1 l2) : subseq (n::l1) (n::l2).

Theorem reflexivity_subseq: forall l : list nat, 
    subseq l l.
Proof.

intros.

induction l.

- apply D1.
- apply D3. apply IHl.

    
Qed.

Lemma list_add_nil : forall (l: list nat), l ++ [] = l.

Proof.
intros.
induction l.
- reflexivity.
- simpl. rewrite IHl. reflexivity. 
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),  subseq l1 l2 ->  subseq l1 (l2 ++ l3).

Proof.
intros.
induction H.
- apply D1.
- simpl. apply D2. apply IHsubseq.
- simpl. apply D3. apply IHsubseq.
Qed.

Lemma subseq_nil: forall l, subseq l [] -> l = [].
Proof.

intros. induction l.
- reflexivity.
- inversion H. 
    
Qed.









