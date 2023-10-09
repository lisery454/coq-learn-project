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

Inductive natlist : Type :=
    | nil
    | cons (n: nat) (l: natlist).

Check (cons).

Check (cons 1 (cons 2 (cons 3 nil))).

Notation "n :: m"  := (cons n m)
    (at level 60, right associativity).

Check 1 :: 2 :: 3 :: 4 :: nil.

Notation "[]" := nil.

Notation "[ x ; .. ; y ]" := 
    (cons x .. (cons y nil) ..).

Check [1;2;3;4].

Definition mylist := [1;2;3;4].

Check mylist.

Fixpoint repeat (n : nat)(count : nat) :natlist :=
    match count with 
    | O => nil
    | S c => n :: (repeat n c)
    end.

Compute (repeat 10 12).

Fixpoint length (l : natlist) : nat :=
    match l with
    | nil => O
    | cons p q => S (length q)
    end.

Compute (length (repeat 2 5)).

Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | n::l1' => app l1' (n::l2)
    end.

Compute (app (repeat 1 3) (repeat 3 2)).

Notation "x ++ y" := (app x y) 
 (at level 60, right associativity).

Compute ((repeat 1 3) ++ (repeat 3 2)).

Fixpoint reverse (l : natlist) : natlist :=
    match l with
    | nil => nil
    | n::l' => (reverse l') ++ ([n])
    end.
    
(* ? *)
Compute (reverse([1;2;3;4])).

Fixpoint createList(n : nat) : natlist :=
    match n with
    | O => nil
    | S(n') => (createList n') ++ [n]
    end.

Compute (createList(4)).

Fixpoint createList'(n : nat) : natlist :=
    match n with 
    | O => nil
    | S(n') => [n] ++ (createList' n') ++ [n]
    end.

Compute (createList'(4)).

