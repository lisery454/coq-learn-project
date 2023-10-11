Inductive nat : Type :=
    | o
    | S (n : nat).

Check o.

Check (S (S o)).

Check S.

Definition pred (n : nat) : nat :=
    match n with 
    | o => o
    | S(p) => p
    end.

Compute (pred (S (S o))).

Fixpoint is_odd (n : nat) : bool :=
    match n with
    | o => false
    | S(o) => true
    | S(S(p)) => is_odd(p)
    end.

Compute (is_odd(S(S(o)))).

Fixpoint is_even (n : nat) : bool :=
    match n with
    | o => true
    | S(o) => false
    | S(S(p)) => is_even(p)
    end.

Compute (is_even(S(S(o)))).

Fixpoint add (n1 : nat) (n2 : nat) : nat :=
    match n1 with
    | o => n2
    | S(p) => add p (S(n2)) 
    end.

Compute (add(S(S(o)))(S(S(o)))).

Fixpoint sub (n1 : nat) (n2 : nat) : nat :=
    match n1, n2 with
    | o, _ => o
    | _, o => n1
    | S(p), S(q) => sub p q
    end.

Compute (sub(S(S(S(o))))(S(o))).

Fixpoint is_equal (n1 : nat) (n2 : nat) : bool :=
    match n1, n2 with
    | o, o => true
    | o, S(_) => false
    | S(_), o => false 
    | S(p), S(q) => is_equal p q
    end.

Compute (is_equal(S(S(S(o))))(S(o))).

Definition is_equal_2 (n1 : nat) (n2 : nat) : bool :=
    match sub n1 n2, sub n2 n1 with
    | o, o => true
    | _, _ => false
    end.

Compute (is_equal_2 (S o) (S o) ).

Fixpoint is_less_equal (n1 : nat) (n2 : nat) : bool :=
    match n1, n2 with 
    | o, _ => true
    | S(_), o => false 
    | S(p), S(q) => is_less_equal p q
    end.

Fixpoint is_less (n1 : nat) (n2 : nat) : bool :=
    match n1, n2 with 
    | o, o => false
    | o, S(_) => true
    | S(_), o => false 
    | S(p), S(q) => is_less p q
    end.

Fixpoint is_great_equal (n1 : nat) (n2 : nat) : bool :=
    match n1, n2 with 
    | _, o => true
    | o, S(_) => false 
    | S(p), S(q) => is_great_equal p q
    end.

Fixpoint is_great (n1 : nat) (n2 : nat) : bool :=
    match n1, n2 with 
    | o, o => false
    | S(_), o => true
    | o, S(_) => false 
    | S(p), S(q) => is_great p q
    end.

(* Definition gtb (n : nat) (m : nat) : bool :=
    match sub n m with 
    | o => false
    | S(_) => true
    end.

Compute (gtb (S(o)) (S(o))). *)

Fixpoint mult (n: nat) (m: nat): nat := 
    match n, m with
    | o, _ => o
    | _, o => o
    | S(p), S(q) => S (add (mult p q) (add p q))
    end.

Compute (mult (S(S(o))) (S(S(S(o))))).
Compute (mult (S(S(o))) (S(o))).


Fixpoint exp (n: nat) (m: nat): nat :=
    match m with
    | o => S(o)
    | S(p) => mult (exp n p) n
    end.

Compute (exp (S(S(o))) (S(S(S(o))))).
Compute (mult (S(S(o))) (o)).

Fixpoint fact (n: nat): nat :=
    match n with
    | o => S(o)
    | S(q) => mult (fact q) n
    end.

Compute (fact (S(S(S(o))))).
