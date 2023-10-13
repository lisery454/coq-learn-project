Require Import Arith.

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
    | n::l1' => n :: (app l1' l2)
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

Compute (1+3).

Fixpoint fib_direct (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => match n' with
                | 0 => 1
                | S n'' => fib_direct n' + fib_direct n''
              end
  end.

(* why *)
(* Fixpoint fibnat (n: nat) : nat :=
    match n with
    | O => O
    | S O => S O
    | S(S p as a) => (fibnat p) + (fibnat(a))
    end.

Compute (fibnat(10)). *)

Compute (fib_direct(10)).

Fixpoint fib (n: nat) : natlist :=
    match n with
    | 0 => [fib_direct 0]
    | S n' => (fib n') ++ [fib_direct n]
    end.

Compute (fib 8).

(* Fixpoint F (n: nat) : nat :=
    match n with
    | 0 => 1
    | S n' =>   match n' with
                | 0 => 1
                | S n'' =>  match n'' with
                            | 0 => 1
                            | S n''' => F n' + F n'' + F n'''
                            end
                end
    end. *)

Fixpoint F (n: nat) : nat :=
    match n with
    | 0 => 1
    | 1 => 1
    | 2 => 1
    | S(S(S n' as n'') as n''') => F n' + F n'' + F n'''
    end.

Compute (F 3).

Fixpoint Seq (n: nat) :natlist :=
    match n with
    | 0 => 0::[F 0]
    | S n' => (Seq n') ++ n::[F n]
    end.

Compute (Seq 10).

Fixpoint total (list: natlist) :nat :=
    match list with
    | nil => 0
    | n::list' => n + (total list')
    end.

Compute (total [1;2;3;4;5;6;7]).

Compute (max 1 2).

Fixpoint max (list: natlist) :nat :=
    match list with
    | nil => 0
    | n::list' => (Nat.max n (max list'))
    end.

Compute (max [1;6;3;5;7;9;2]).