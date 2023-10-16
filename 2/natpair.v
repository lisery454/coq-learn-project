Inductive natpair : Type :=
    |pair (n1 n2 : nat).

Check (pair 1 2).

Check pair.

Notation "( x , y )" := (pair x y).

Check (1,2).

Definition proj1(p: natpair) : nat := 
    match p with
    | (x, y) => x
    end.

Definition proj2(p: natpair) : nat := 
    match p with
    | (x, y) => y
    end.