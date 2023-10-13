Require Import Arith.

Inductive btree : Type  :=
    | nil
    | bind (t1: btree)(t2: btree)(n: nat).

(* Compute (Nat.eqb 1 1). *)

(* Compute (orb true false). *)

Fixpoint occur (n: nat)(t: btree) : bool :=
    match t with
    | nil => false
    | bind t1 t2 q => orb (Nat.eqb n q) (orb (occur n t1) (occur n t2))
    end.

(* Compute (occur 1 (bind (bind nil nil 2) (nil) 2)). *)

(* Compute (1+1). *)

Fixpoint isEven (n: nat) :nat :=
    match n with
    | O => 1
    | S O => 0
    | S(S q) => isEven q
    end.

Fixpoint countEven (t: btree) :nat :=
    match t with
    | nil => 0
    | bind t1 t2 q => (isEven q) + (countEven t1) + (countEven t2)
    end.

(* Compute (countEven (bind (bind nil nil 1) (nil) 2)). *)

Fixpoint sum (t: btree) :nat :=
    match t with
    | nil => 0
    | bind t1 t2 q => q + (sum t1) + (sum t2)
    end.

Compute (sum (bind (bind nil nil 1) (nil) 2)).



